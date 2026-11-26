import PastaLean.Imports
import PastaLean.Codegen
import PastaLean.PyGens.Basic
import PastaLean.PyGens.Core.Utils
import TypeInfer

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-- Keyword-argument object in Python call JSON. -/
abbrev PyKeywordArgs := Std.TreeMap.Raw String Json compare

/-- The Lean type of a `PyType`, with `float` resolved against the current numeric mode. -/
def pyTypeSyntax? (t : TypeInfer.PyType) : PygenM (Option (TSyntax `term)) := do
  let floatTy : TSyntax `term ← match ← getNumericMode with
    | .exact => pure (mkIdent (if (← getRealContext) then ``Real else ``Rat))
    | .approx => pure (mkIdent ``Float)
  TypeInfer.toTypeSyntax? floatTy t

/-- Split a `defaultdict[k, v]` annotation node into its key and value annotations. -/
def defaultDictAnnParts? (ann : Json) : Option (Json × Json) :=
  if jsonNodeType? ann != some "Subscript" then none
  else match (ann.getObjVal? "value").toOption, (ann.getObjVal? "slice").toOption with
    | some value, some slice =>
        if value.getObjValAs? String "id" != .ok "defaultdict" then none
        else if jsonNodeType? slice != some "Tuple" then none
        else
          let elts := (slice.getObjValAs? (Array Json) "elts").toOption.getD #[]
          match elts[0]?, elts[1]? with
          | some k, some v => some (k, v)
          | _, _ => none
    | _, _ => none

/-- Like `pyTypeSyntax?` but run-suffixes user-class names (`ListNode` → `ListNode'rn` in the run
twin) — `TypeInfer`'s emitter is context-free, so a class inside a `_ty` (`Option ListNode`,
`List TreeNode`) would otherwise stay unsuffixed and clash with the suffixed struct. -/
partial def runAwareTypeSyntax? (t : TypeInfer.PyType) : PygenM (Option (TSyntax `term)) := do
  match t with
  | .cls c => return some (mkIdent (← suffixIfUserName c).toName)
  | .opt e => match ← runAwareTypeSyntax? e with | some s => return some (← `(Option $s)) | none => return none
  | .list e => match ← runAwareTypeSyntax? e with | some s => return some (← `(List $s)) | none => return none
  | .set e => match ← runAwareTypeSyntax? e with | some s => return some (← `(PastaLean.PySet $s)) | none => return none
  | other => pyTypeSyntax? other

/-- Emit a type from an annotation, honouring the `_seq: "array"` marker the eligibility pass stamps
on each `list[...]` level: an `array_ok` list becomes `Array` (recursively, so `list[list[int]]` →
`Array (Array Int)`) in the runnable twin. The marker has no `PyType` slot, so `pyTypeSyntax? ∘
ofAnnotation` would drop it — hence this reads it off the annotation directly, falling back to the
`PyType` path for un-marked (or non-`list`) levels. -/
partial def seqAwareTypeSyntax? (ann : Json) : PygenM (Option (TSyntax `term)) := do
  let isArrList := (ann.getObjValAs? String "node_type" == .ok "Subscript")
    && ((ann.getObjVal? "value").toOption.any (·.getObjValAs? String "id" |>.toOption |>.any (· == "list")))
    && (ann.getObjValAs? String "_seq" == .ok "array")
  if isArrList && (← getNumericMode) == .approx then
    match ann.getObjVal? "slice" with
    | .ok elemAnn =>
        match ← seqAwareTypeSyntax? elemAnn with
        | some et => return some (← `(Array $et))
        | none => runAwareTypeSyntax? (TypeInfer.ofAnnotation ann)
    | _ => runAwareTypeSyntax? (TypeInfer.ofAnnotation ann)
  else runAwareTypeSyntax? (TypeInfer.ofAnnotation ann)

/-- The Lean type stamped on a node by the inference pass (`_ty`), if any. `_ty` is an annotation
node, so it round-trips through `PyType` and the full emitter — covering lists, dicts, tuples and
`Optional`, not just the shapes the annotation reader handles directly. -/
def stampedTypeSyntax? (node : Json) : PygenM (Option (TSyntax `term)) := do
  match jsonFieldOption node "_ty" with
  | some ann =>
      -- `defaultdict[k, v]` is backed by `PyDefaultDict`; `PyType` models it as a plain dict, so
      -- round-tripping it through the emitter would wrongly yield `Std.HashMap`.
      match defaultDictAnnParts? ann with
      | some (k, v) =>
          match ← pyTypeSyntax? (TypeInfer.ofAnnotation k), ← pyTypeSyntax? (TypeInfer.ofAnnotation v) with
          | some kt, some vt => return some (← `(Libraries.collections.PyDefaultDict $kt $vt))
          | _, _ => return none
      | none => seqAwareTypeSyntax? ann
  | none => return none

/-- Infer a simple runtime type from a value expression when the shape is obvious. -/
def inferSimpleValueTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) :=
  pyTypeSyntax? (TypeInfer.ofValue json)

/-- Infer a simple iterable element type from obvious literal iterables. -/
def inferIterableElemTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  -- Iterating a `String` yields `Char`, not a one-character `String`.
  match TypeInfer.ofValue json with
  | .str => return some (mkIdent ``Char)
  | t => pyTypeSyntax? t.elemType

/-- Read the positional parameter names from a lambda node without depending on `FuncDef.lean`. -/
def lambdaArgIdents (json : Json) : PygenM (Array (TSyntax `ident)) := do
  let .ok argsJson := json.getObjValAs? Json "args" | throwError
    s!"Lambda node does not have an 'args' field or it is not a JSON value: {json}"
  let .ok argsArray := argsJson.getObjValAs? (Array Json) "args" | throwError
    s!"Lambda args does not have an 'args' field or it is not a JSON array: {argsJson}"
  argsArray.mapM fun argJson => do
    let .ok argName := argJson.getObjValAs? String "arg" | throwError
      s!"Lambda argument does not have an 'arg' field or it is not a string: {argJson}"
    pure (mkIdent argName.toName)

/--
Stamp a binary lambda with either concrete runtime types or `_` placeholders so overloaded
operators inside higher-order calls elaborate more predictably.
-/
def typedBinaryLambdaCode (funcJson : Json) (fallback : TSyntax `term)
    (paramTy? : Option (TSyntax `term)) : PygenM (TSyntax `term) := do
  unless funcJson.getObjValAs? String "node_type" == .ok "Lambda" do
    return fallback
  let argIdents ← lambdaArgIdents funcJson
  unless argIdents.size == 2 do
    return fallback
  let .ok bodyJson := funcJson.getObjValAs? Json "body" | throwError
    s!"Lambda node does not have a 'body' field or it is not a JSON value: {funcJson}"
  let bodyStx ← getCode bodyJson `term
  let arg0 := argIdents[0]!
  let arg1 := argIdents[1]!
  let paramTy ← match paramTy? with
    | some stx => pure stx
    | none => `(_)
  `(fun ($arg0 : $paramTy) ↦ fun ($arg1 : $paramTy) ↦ $bodyStx)

/-- A value-and-mutate method resolved for its actual argument count: the `(value, rest)` runtime
pair plus how many of the args `rest` consumes (`value` always takes them all). `pop` is
index-based on a list/set (0-1 args) but key-based on a dict (`pop(key, default)`, 2 args); a
2-arg pop is unambiguously the dict form, whose `rest` drops the default and keeps only the key. -/
def valueAndMutateMethod? (attr : String) (argc : Nat) : Option (Lean.Name × Lean.Name × Nat) :=
  match attr with
  | "pop"     =>
      if argc == 2 then some (``PastaLean.pyDictPopValue, ``PastaLean.pyDictPopRest, 1)
      else if argc ≤ 1 then some (``PastaLean.pyPopValue, ``PastaLean.pyPopRest, argc)
      else none
  | "popleft" => if argc == 0 then some (``PastaLean.pyPopLeftValue, ``PastaLean.pyPopLeftRest, 0) else none
  -- `d.setdefault(key, default)`: value is `d[key]`-or-default (`pyGetD`), rest inserts when absent.
  | "setdefault" => if argc == 2 then some (``PastaLean.pyGetD, ``PastaLean.pyDictSetdefaultRest, 2) else none
  | _         => none

/-- Swap the `(value, rest)` pop pair to its O(1) `Array` variant when the receiver is `array_ok`
(the substitution table, `PastaLean/PyVerify/Twin/Table.lean`). -/
def arrayPopFns (valueFn restFn : Lean.Name) : Lean.Name × Lean.Name :=
  (Twin.runPrim valueFn, Twin.runPrim restFn)

/-- Recognize `container.<m>(args…)` for a value-and-mutate method `m` on an already-declared
mutable variable. Returns the runtime pair, the receiver, the value-form args, and the rest-form
args (a prefix). A freshly-seen receiver is not a mutation site, so it returns `none`. -/
def popCallParts? (value : Json) :
    PygenM (Option ((Lean.Name × Lean.Name) × TSyntax `ident × Array (TSyntax `term) × Array (TSyntax `term))) := do
  unless jsonNodeType? value == some "Call" do return none
  let .ok funcJson := value.getObjVal? "func" | return none
  unless jsonNodeType? funcJson == some "Attribute" do return none
  let .ok attr := funcJson.getObjValAs? String "attr" | return none
  let args := (value.getObjValAs? (Array Json) "args").toOption.getD #[]
  let some (valueFn, restFn, restArgc) := valueAndMutateMethod? attr args.size | return none
  let .ok receiverJson := funcJson.getObjVal? "value" | return none
  unless jsonNodeType? receiverJson == some "Name" do return none
  let receiverIdent ← getCode receiverJson `ident
  unless (← hasVar receiverIdent.getId) do return none
  -- `d.pop(key)` (1 arg) on a known dict is the DICT pop, not the 1-arg list pop `valueAndMutateMethod?`
  -- defaults to (that shares the name).
  let (valueFn, restFn, restArgc) ←
    if attr == "pop" && args.size == 1 && (← jsonIsDictExpr receiverJson) then
      pure (``PastaLean.pyDictKeyPopValue, ``PastaLean.pyDictKeyPopRest, 1)
    else if (value.getObjValAs? String "_seq" == .ok "array") && (← getNumericMode) == .approx then
      let (vf, rf) := arrayPopFns valueFn restFn
      pure (vf, rf, restArgc)
    else pure (valueFn, restFn, restArgc)
  let argCodes ← args.mapM (getCode · `term)
  return some ((valueFn, restFn), receiverIdent, argCodes, argCodes.extract 0 restArgc)

/-- Like `popCallParts?` but for a receiver that is a single-level subscript on a mutable Name
(`d[c].popleft()`, `g[f].pop()`): returns the runtime pair, the base container ident, the index
term, and the value/rest args. The update must rebuild `base[idx]` via `pySetItem`, not reassign a
plain ident. -/
def popCallSubscriptParts? (value : Json) :
    PygenM (Option ((Lean.Name × Lean.Name) × TSyntax `ident × TSyntax `term × Array (TSyntax `term) × Array (TSyntax `term))) := do
  unless jsonNodeType? value == some "Call" do return none
  let .ok funcJson := value.getObjVal? "func" | return none
  unless jsonNodeType? funcJson == some "Attribute" do return none
  let .ok attr := funcJson.getObjValAs? String "attr" | return none
  let args := (value.getObjValAs? (Array Json) "args").toOption.getD #[]
  let some (valueFn, restFn, restArgc) := valueAndMutateMethod? attr args.size | return none
  let .ok receiverJson := funcJson.getObjVal? "value" | return none
  unless jsonNodeType? receiverJson == some "Subscript" do return none
  let .ok baseJson := receiverJson.getObjVal? "value" | return none
  let .ok sliceJson := receiverJson.getObjVal? "slice" | return none
  -- Only a plain `base[idx]` with `base` a mutable Name (not a slice, not a nested subscript).
  unless jsonNodeType? baseJson == some "Name" do return none
  if jsonNodeType? sliceJson == some "Slice" then return none
  let baseIdent ← getCode baseJson `ident
  unless (← hasVar baseIdent.getId) do return none
  let idxTerm ← getCode sliceJson `term
  let argCodes ← args.mapM (getCode · `term)
  return some ((valueFn, restFn), baseIdent, idxTerm, argCodes, argCodes.extract 0 restArgc)

/-- A user value+mutate method (`x = uf.union(a,b)`): the method returns `(value, self)`, so the
value is `(C.union uf a b).1` and the mutation reassigns `uf := (C.union uf a b).2`. Both read the
original receiver (bound-then-updated by the caller), so the pure method is evaluated twice. -/
def userValueMutatorRhsLowering? (value : Json) :
    PygenM (Option (TSyntax `term × TSyntax `doElem)) := do
  unless jsonNodeType? value == some "Call" do return none
  unless (value.getObjValAs? Bool "_is_value_mutator").toOption.getD false do return none
  let .ok funcJson := value.getObjVal? "func" | return none
  unless jsonNodeType? funcJson == some "Attribute" do return none
  let .ok attr := funcJson.getObjValAs? String "attr" | return none
  let .ok cls := value.getObjValAs? String "_receiver_class" | return none
  let .ok receiverJson := funcJson.getObjVal? "value" | return none
  unless jsonNodeType? receiverJson == some "Name" do return none
  let receiverIdent ← getCode receiverJson `ident
  unless (← hasVar receiverIdent.getId) do return none
  let args := (value.getObjValAs? (Array Json) "args").toOption.getD #[]
  let argCodes ← args.mapM (getCode · `term)
  let methodIdent : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
  let call ← `($methodIdent $receiverIdent $argCodes*)
  let valueTerm ← `($call |>.1)
  let update ← `(doElem| $receiverIdent:ident := $call |>.2)
  return some (valueTerm, update)

/-- Lower a call that both mutates its receiver and yields a value into a `(value, update)`
pair. They each read the *original* container, so the caller binds `value` first, then runs
`update`. Covers `container.pop(idx?)` and `deque.popleft()`, on a Name or `base[idx]` receiver. -/
def mutatingCallRhsLowering? (value : Json) :
    PygenM (Option (TSyntax `term × TSyntax `doElem)) := do
  if let some res ← userValueMutatorRhsLowering? value then return some res
  if let some ((valueFn, restFn), baseIdent, idxTerm, valueArgs, restArgs) ← popCallSubscriptParts? value then
    -- `d[c].popleft()`: read the list at `d[c]`, take its value, and rebuild `d` with the rest.
    let getIdent := mkIdent ``PastaLean.pyGetItem
    let setIdent := mkIdent ``PastaLean.pySetItem
    let recvTerm ← `($getIdent $baseIdent $idxTerm)
    let valueTerm ← `($(mkIdent valueFn) $recvTerm $valueArgs*)
    let update ← `(doElem| $baseIdent:ident := $setIdent $baseIdent $idxTerm ($(mkIdent restFn) $recvTerm $restArgs*))
    return some (valueTerm, update)
  match ← popCallParts? value with
  | none =>
      -- A library member that both mutates its first arg and returns a value (`x = heapq.heappop(h)`),
      -- read from the `Libraries` mutator spec so no library names live in codegen.
      match (value.getObjVal? "func").toOption.bind libraryMutatorOf? |>.bind (·.valueRest?) with
      | some (valFn, restFn) =>
          match value.getObjValAs? (Array Json) "args" with
          | .ok args =>
              if args.size == 0 then return none
              let container := args[0]!
              let argsCodes ← args.mapM (getCode · `term)
              let valueTerm ← `($(mkIdent valFn) $argsCodes*)
              match jsonNodeType? container with
              -- `x = heapq.heappop(h)` on a plain heap variable: rebind it to the rest.
              | some "Name" =>
                  let recvIdent ← getCode container `ident
                  let update ← `(doElem| $recvIdent:ident := $(mkIdent restFn) $argsCodes*)
                  return some (valueTerm, update)
              -- `heappop(self.small)` on an attribute heap (value semantics): rebuild the object with
              -- the popped-rest field (`self := { self with small := pyHeappopRest self.small }`).
              | some "Attribute" =>
                  if ← getHeapMode then return none  -- heap object refs need a pointer-write; skip
                  match container.getObjVal? "value", container.getObjValAs? String "attr" with
                  | .ok recv, .ok attr =>
                      if jsonNodeType? recv == some "Name" then
                        let recvIdent ← getCode recv `ident
                        let attrId := mkIdent attr.toName
                        let restApplied ← `($(mkIdent restFn) $argsCodes*)
                        let fields := #[← `(Lean.Parser.Term.structInstField| $attrId:ident := $restApplied)]
                        let update ← `(doElem| $recvIdent:ident := { $recvIdent:term with $fields:structInstField,* })
                        return some (valueTerm, update)
                      else return none
                  | _, _ => return none
              | _ => return none
          | _ => return none
      | none => return none
  | some ((valueFn, restFn), receiverIdent, valueArgs, restArgs) =>
      let valueIdent := mkIdent valueFn
      let restIdent := mkIdent restFn
      let valueTerm ← `($valueIdent $receiverIdent $valueArgs*)
      let update ← `(doElem| $receiverIdent:ident := $restIdent $receiverIdent $restArgs*)
      return some (valueTerm, update)

end PastaLean
