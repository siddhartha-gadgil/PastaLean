import Mathlib
import PastaLean.Codegen
import PastaLean.PyGens.Basic

open Lean Meta Elab Term Qq Std

namespace PastaLean

open Lean.Parser.Term

def withFreshVariables {α : Type} (x : PygenM α) : PygenM α :=
  withPygenStateField
    (·.varNames)
    (fun st varNames => { st with varNames := varNames })
    (HashSet.emptyWithCapacity 100) <|
  withPygenStateField
    (·.heapVarClasses)
    (fun st v => { st with heapVarClasses := v })
    [] <|
  withPygenStateField
    (·.heapVarContainers)
    (fun st v => { st with heapVarContainers := v })
    [] <|
  withPygenStateField
    (·.heapCellVars)
    (fun st v => { st with heapCellVars := v })
    [] <|
  withPygenStateField
    (·.heapCellContainers)
    (fun st v => { st with heapCellContainers := v })
    [] <|
  withPygenStateField
    (·.setVars)
    (fun st setVars => { st with setVars := setVars })
    (HashSet.emptyWithCapacity 16)
    x

/--
Append one generated command into an accumulator, flattening null-node wrappers that
represent "many commands" or "no commands" from an earlier lowering pass.
-/
def appendCommandSyntax (cmds : Array (TSyntax `command)) (cmd : TSyntax `command) :
    Array (TSyntax `command) :=
  if cmd.raw.isOfKind nullKind then
    cmds ++ cmd.raw.getArgs.map (fun arg => ⟨arg⟩)
  else
    cmds.push cmd

/--
Append one generated `doElem` into an accumulator, flattening null-node wrappers that
represent "many doElems" from a lowering that produced several sibling statements (e.g.
tuple-unpack assignment). Flattening keeps the bindings as siblings in the enclosing `do`
rather than scoping them inside a nested `do` block.
-/
def appendDoElems (elems : Array (TSyntax `doElem)) (elem : TSyntax `doElem) :
    Array (TSyntax `doElem) :=
  if elem.raw.isOfKind nullKind then
    elems ++ elem.raw.getArgs.map (fun arg => ⟨arg⟩)
  else
    elems.push elem

/-- Pick a fresh local name for generated bindings. -/
partial def freshName (base : Name) (idx : Nat := 1) : PygenM Name := do
  let candidate :=
    if idx == 0 then base else base.appendIndexAfter idx
  if ← hasVar candidate then
    freshName base (idx + 1)
  else
    addVar candidate
    pure candidate

def isMainGuardTest (json : Json) : Bool :=
  match json.getObjValAs? String "node_type" with
  | .ok "Compare" =>
      match json.getObjValAs? String "op", json.getObjValAs? Json "left", json.getObjValAs? Json "right" with
      | .ok "eq", .ok leftJson, .ok rightJson =>
          match leftJson.getObjValAs? String "node_type", leftJson.getObjValAs? String "id",
              rightJson.getObjValAs? String "node_type", rightJson.getObjValAs? Json "value" with
          | .ok "Name", .ok "__name__", .ok "Constant", .ok (.str "__main__") => true
          | _, _, _, _ => false
      | _, _, _ => false
  | _ => false

/-- Detect a `range(...)` iterable, which is lowered directly to `pyRange` (already a `List Int`)
rather than being normalized through `pyIter`. The annotation pre-pass rewrites `range(...)`
calls to a dedicated `Range` node; a raw `Call` to `range` is also recognized defensively. -/
def isRangeIter (iterJson : Json) : Bool :=
  match iterJson.getObjValAs? String "node_type" with
  | .ok "Range" => true
  | .ok "Call" =>
      match iterJson.getObjValAs? Json "func" with
      | .ok funcJson =>
          funcJson.getObjValAs? String "node_type" == .ok "Name" &&
            funcJson.getObjValAs? String "id" == .ok "range"
      | _ => false
  | _ => false

/-- Lower a `for`/comprehension iterable to a Lean term that can be iterated as a `List`.

`range(...)` lowers directly to `pyRange` (already a `List Int`). Every other iterable is
normalized through `pyIter`, so the element type is governed uniformly by the `PyIterable`
instances: a `String` yields one-character `String`s, a `Std.HashMap` yields its keys, a `List`
is unchanged. This is what makes iteration over a string behave like Python (`for c in s` binds
length-1 strings, not `Char`s) and keeps loop bodies interoperable with string literals. -/
def rangeIterSyntax (iterJson : Json) : PygenM (TSyntax `term) := do
  let .ok iterNodeType := iterJson.getObjValAs? String "node_type" | throwError
    s!"For iterator is missing a node_type field: {iterJson}"
  if iterNodeType == "Range" then
    -- The pre-pass already produced a `Range` node; lower it straight to `pyRange`.
    getCode iterJson `term
  else if iterNodeType == "Call" &&
      (iterJson.getObjValAs? Json "func").toOption.any
        (fun f => f.getObjValAs? String "id" == .ok "range") then
    -- Defensive path for a raw `range(...)` call that escaped the pre-pass rewrite.
    let funcJson := (iterJson.getObjVal? "func").toOption.getD (Json.mkObj [])
    let argsJson := (iterJson.getObjVal? "args").toOption.getD (Json.arr #[])
    let keywordsJson := (iterJson.getObjVal? "keywords").toOption.getD (Json.mkObj [])
    let rangeJson := Json.mkObj [
      ("node_type", Json.str "Range"),
      ("func", funcJson),
      ("args", argsJson),
      ("keywords", keywordsJson)
    ]
    getCode rangeJson `term
  else
    `($(mkIdent ``pyIter) $(← getCode iterJson `term))

/-- Reusable syntax nodes for boolean literals in generated terms. -/
def trueTerm : TSyntax `term := mkIdent ``true

def falseTerm : TSyntax `term := mkIdent ``false

/-- Read the `node_type` tag from a JSON AST node when present. -/
def jsonNodeType? (json : Json) : Option String :=
  json.getObjValAs? String "node_type" |>.toOption

/--
Reformat a list of Json to an object with `node_type` the `node_type` of the original list's
first element with "Head_" prefixed, and `rest` the remaining statements.
-/
def splitList : List Json -> PygenM Json
| [] => throwError "Cannot split an empty list"
| (first :: rest) => do
    let .ok nodeType := first.getObjValAs? String "node_type" | throwError
      s!"First element of list does not have a 'node_type' field or it is not a string: {first}"
    let newNodeType := "Head_" ++ nodeType
    let newJson := first.mergeObj (Json.mkObj [("node_type", newNodeType), ("rest", toJson rest)])
    return newJson

/-- Try to compile a function body as one pure term by threading the remaining statements
through `Head_*` nodes. -/
def pureFunctionBodySyntax (bodyElems : Array Json) : PygenM (TSyntax `term) := do
  let spl ← splitList bodyElems.toList
  withoutCheck do
    getCode spl `term

mutual

/--
Check whether a statement list definitely returns on every path without needing any outer
continuation. This is used to decide whether nested control-flow can stay in the pure
threaded lowering, or whether we should fall back to the monadic statement path instead.
-/
partial def statementListDefinitelyReturns : List Json → Bool
| [] => false
| stmt :: rest =>
    if statementDefinitelyReturns stmt then
      true
    else
      statementListDefinitelyReturns rest

/-- Check whether one statement definitely returns on every path. -/
partial def statementDefinitelyReturns (stmt : Json) : Bool :=
  match jsonNodeType? stmt with
  | some "Return" => true
  | some "Raise" => true
  | some "If" =>
      match stmt.getObjValAs? (Array Json) "body", stmt.getObjValAs? (Array Json) "orelse" with
      | .ok bodyElems, .ok orelseElems =>
          !orelseElems.isEmpty &&
            statementListDefinitelyReturns bodyElems.toList &&
            statementListDefinitelyReturns orelseElems.toList
      | _, _ => false
  | some "Try" =>
      match stmt.getObjValAs? (Array Json) "body",
          stmt.getObjValAs? (Array Json) "handlers",
          stmt.getObjValAs? (Array Json) "orelse" with
      | .ok bodyElems, .ok handlerElems, .ok orelseElems =>
          let bodyReturns := statementListDefinitelyReturns (bodyElems.toList ++ orelseElems.toList)
          let handlersReturn :=
            handlerElems.toList.all fun handlerJson =>
              match handlerJson.getObjValAs? (Array Json) "body" with
              | .ok handlerBody => statementListDefinitelyReturns handlerBody.toList
              | .error _ => false
          bodyReturns && handlersReturn
      | _, _, _ => false
  | some "Match" =>
      match stmt.getObjValAs? (Array Json) "cases" with
      | .ok cases =>
          -- All cases must return AND the last case must be irrefutable (covers all inputs)
          let allCasesReturn := cases.toList.all fun caseJson =>
            match caseJson.getObjValAs? (Array Json) "body" with
            | .ok bodyElems => statementListDefinitelyReturns bodyElems.toList
            | .error _ => false
          let lastCaseExhaustive := match cases.toList.getLast? with
            | none => false
            | some lastCase =>
                let guardAbsent := match lastCase.getObjValAs? Json "guard" with
                  | .ok .null => true
                  | .error _ => true
                  | _ => false
                match guardAbsent, lastCase.getObjVal? "pattern" with
                | true, .ok patternJson =>
                    match patternJson.getObjValAs? String "node_type" with
                    | .ok "MatchAs" => true
                    | .ok "MatchStar" => true
                    | _ => false
                | _, _ => false
          allCasesReturn && lastCaseExhaustive
      | _ => false
  | _ => false

end

/-- Does the subtree contain a reachable `return` (not descending into a nested def/lambda/class,
which own their returns)? -/
partial def stmtHasReachableReturn (json : Json) : Bool :=
  match json.getObjValAs? String "node_type" with
  | .ok "FunctionDef" | .ok "AsyncFunctionDef" | .ok "Lambda" | .ok "ClassDef" => false
  | .ok "Return" => true
  | _ => match json with
    | .arr xs => xs.any stmtHasReachableReturn
    | .obj fs => fs.toList.any (fun (_, v) => stmtHasReachableReturn v)
    | _ => false

/-- Compile a function body statement-by-statement into `doElem`s for the monadic fallback path. -/
def monadicFunctionBodySyntax (bodyElems : Array Json) : PygenM (Array (TSyntax `doElem)) := do
  let mut bodyStxArray := #[]
  let mut broke := false
  for elem in bodyElems do
    let elemStx ← withoutCheck do
      getCode elem `doElem
    bodyStxArray := appendDoElems bodyStxArray elemStx
    if statementDefinitelyReturns elem then
      broke := true
      break
  -- A function that returns a value only via an early `return` inside a loop/branch
  -- (`while …: return x`) falls off the end; Python returns `None`, but the Lean do-block would end
  -- with the loop's `Unit`. Append a fallback `return default` (its type pinned by the real returns)
  -- so it type-checks. Only when the body actually has a return, so `Unit` functions are untouched.
  unless broke do
    if bodyElems.any stmtHasReachableReturn then
      bodyStxArray := bodyStxArray.push (← `(doElem| return default))
  return bodyStxArray

/-- Build a Lean conjunction term. -/
def andTerm (lhs rhs : TSyntax `term) : PygenM (TSyntax `term) := do
  `($lhs && $rhs)

/-- Build a Lean disjunction term. -/
def orTerm (lhs rhs : TSyntax `term) : PygenM (TSyntax `term) := do
  `($lhs || $rhs)

/-- Read an optional JSON field and treat explicit `null` the same as an absent value. -/
def jsonFieldOption (json : Json) (field : String) : Option Json :=
  match json.getObjValAs? Json field |>.toOption with
  | some .null => none
  | other => other

/-- Recursively check whether a JSON subtree contains any node type from `targets`. -/
partial def jsonContainsNodeType (json : Json) (targets : List String) : Bool :=
  let currentMatches :=
    match json.getObjValAs? String "node_type" with
    | .ok nodeType => targets.contains nodeType
    | .error _ => false
  if currentMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any (fun elem => jsonContainsNodeType elem targets)
    | .obj fields => fields.toList.any (fun (_, value) => jsonContainsNodeType value targets)
    | _ => false

/-- Recursively check whether a JSON subtree is marked as using translated exceptions. -/
partial def jsonUsesExceptionEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "except" => true
    | _ =>
        match json.getObjValAs? String "node_type" with
        | .ok nodeType => nodeType == "Try" || nodeType == "Raise"
        | .error _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any jsonUsesExceptionEffect
    | .obj fields => fields.toList.any (fun (_, value) => jsonUsesExceptionEffect value)
    | _ => false

/-- Recursively check whether a JSON subtree is marked as using translated `IO` effects. -/
partial def jsonUsesIOEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "io" => true
    | _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any jsonUsesIOEffect
    | .obj fields => fields.toList.any (fun (_, value) => jsonUsesIOEffect value)
    | _ => false

/-- Recursively check whether a JSON subtree uses the heap (`--heap`): a class instantiation
(`_class_ctor`), an instance-method call (`_receiver_class`), a heap-effectful call (`_heap_call`),
or a mutable-container literal (`List`/`Dict`/`Set`). Such code must run in `HeapM`. -/
partial def jsonUsesHeapEffect (json : Json) : Bool :=
  let direct := (json.getObjValAs? String "_class_ctor").toOption.isSome
             || (json.getObjValAs? String "_receiver_class").toOption.isSome
             || (json.getObjValAs? Bool "_heap_call").toOption.getD false
             || (match json.getObjValAs? String "node_type" with
                 | .ok nt => nt == "List" || nt == "Dict" || nt == "Set"
                 | _ => false)
  if direct then true
  else match json with
    | .arr elems => elems.toList.any jsonUsesHeapEffect
    | .obj fields => fields.toList.any (fun (_, value) => jsonUsesHeapEffect value)
    | _ => false

/-- Whether a statement list touches the heap and therefore should run in `HeapM`. -/
def bodyNeedsHeapMonad (bodyElems : Array Json) : Bool :=
  bodyElems.toList.any jsonUsesHeapEffect

/-- The tier-selection guard: `--heap` is on AND this body touches the heap, so it runs in the
`HeapM`/`PyHeapIO`/`PyHeapProofM` tier instead of the value-mode monads. -/
def needsHeapMonad (bodyElems : Array Json) : PygenM Bool :=
  return (← getHeapMode) && bodyNeedsHeapMonad bodyElems

/-- Under `--heap`, if `json` accesses a mutable container held by reference — a `self.f`/`obj.f`
where `f` is a registered container field — return the code for that `Ref (List …)`/`Ref (HashMap …)`.
The caller then dereferences (`(← readRef …)`) to read it, or `modifyRef`s it to mutate in place.
`none` for non-container accesses (so they keep their ordinary lowering). -/
def heapContainerRef? (json : Json) : PygenM (Option (TSyntax `term)) := do
  unless ← getHeapMode do return none
  match jsonNodeType? json with
  | some "Name" =>
      let .ok id := json.getObjValAs? String "id" | return none
      -- A container variable CELL (`Ref (Ref T)`) presents its inner object-ref via one deref.
      if ← isHeapCellContainer id.toName then
        return some (← `((← PastaLean.readRefM $(mkIdent id.toName))))
      -- A local/parameter that holds a container by reference IS the ref.
      if ← isHeapVarContainer id.toName then return some (mkIdent id.toName) else return none
  | some "Attribute" =>
      -- `self.f`/`obj.f` where `f` is a registered container field → the field value `(← recv ~> f)`.
      let some valueJson := (json.getObjVal? "value").toOption | return none
      let .ok attr := json.getObjValAs? String "attr" | return none
      unless jsonNodeType? valueJson == some "Name" do return none
      let .ok recvId := valueJson.getObjValAs? String "id" | return none
      let cls? ← if recvId == "self" then (if ← getHeapSelfRef then getCurrentClass else pure none)
                 else heapVarClassOf? recvId.toName
      let some cls := cls? | return none
      unless ← isContainerField cls attr do return none
      return some (← `((← ($(mkIdent recvId.toName) ~> $(mkIdent attr.toName)))))
  | some "Call" =>
      -- A call whose callee returns a mutable container hands back the object-ref (`Ref (List …)`);
      -- treat it as a container-ref so inline consumption (`len(f())`, `f()[0]`, `for _ in f()`)
      -- dereferences it. The call self-awaits via `_heap_call`, so `getCode` yields `(← f …)`.
      if (json.getObjValAs? Bool "_returns_container").toOption.getD false then
        return some (← getCode json `term)
      else return none
  | _ => return none

/-- Under `--heap`, if `json` reads a mutable container held by reference, return the dereferenced
container `(← readRef …)`, ready to be read (indexed / iterated / `len`-ed); `none` otherwise. The
in-place mutation sites use `heapContainerRef?` directly, since they need the ref for `modifyRef`. -/
def heapContainerDeref? (json : Json) : PygenM (Option (TSyntax `term)) := do
  match ← heapContainerRef? json with
  | some refCode => return some (← `((← PastaLean.readRefM $refCode)))
  | none => return none

/-- Under `--heap`, the fully-dereferenced VALUE form of an expression that is (or structurally
contains) container object-refs, for a position that consumes it *by value* — printing, stringifying.
A container-ref (`Name`/`Attribute`/`Call`) becomes `(← readRefM …)`; a `Tuple`/`List` literal is
rebuilt with each element value-dereferenced (so `print((xs, ys))` shows contents, not `Ref` addrs).
`none` when nothing needs dereferencing, so the ordinary lowering (which already yields a value) is
kept and value mode stays byte-identical. -/
partial def heapValueDeref? (json : Json) : PygenM (Option (TSyntax `term)) := do
  unless ← getHeapMode do return none
  match jsonNodeType? json with
  | some "Tuple" =>
      let some elts := (json.getObjValAs? (Array Json) "elts").toOption | return none
      if elts.isEmpty then return none
      let mut anyDeref := false
      let mut outElts : Array (TSyntax `term) := #[]
      for e in elts do
        match ← heapValueDeref? e with
        | some d => anyDeref := true; outElts := outElts.push d
        | none => outElts := outElts.push (← getCode e `term)
      unless anyDeref do return none
      -- Right-nested `Prod`, matching `tupleSyntax`'s `buildTuple`.
      let mut acc := outElts.back!
      for e in outElts.pop.toList.reverse do
        acc ← `(($e, $acc))
      return some acc
  | some "List" | some "Dict" | some "Set" =>
      -- A container LITERAL under `--heap` is `getCode`'d to an allocated `Ref`; in a value position
      -- (print/stringify) dereference it so the CONTENTS are consumed, not the `Ref` address — uniform
      -- with a container-ref var, whose value form is likewise `(← readRefM <ref>)`.
      return some (← `((← PastaLean.readRefM $(← getCode json `term))))
  | _ => heapContainerDeref? json

/-- Deref every container-ref / container-literal positional arg to its contents. A builtin
(`sum`, `min`, `sorted`, `zip`, …) consumes its iterable *by value*, so under `--heap` a ref arg
must be read first; a user function, by contrast, receives the ref (its `--heap` calling
convention), so this is applied only in builtin lowerings. `argsCodes` is the already-lowered code
for `argsArray`; a non-container arg (and all of value mode) is returned untouched. -/
def derefBuiltinArgCodes (argsArray : Array Json) (argsCodes : Array (TSyntax `term)) :
    PygenM (Array (TSyntax `term)) := do
  unless ← getHeapMode do return argsCodes
  let mut out := argsCodes
  for i in [0:argsArray.size] do
    if h : i < out.size then
      if let some argJson := argsArray[i]? then
        if let some deref ← heapValueDeref? argJson then
          out := out.set i deref
  return out

/-- Detect whether a statement list uses translated exceptions and therefore should not run under `Id`. -/
def bodyNeedsExceptionMonad (bodyElems : Array Json) : Bool :=
  bodyElems.toList.any jsonUsesExceptionEffect

/-- Detect whether a statement list uses translated `IO` effects and therefore should run under `IO`. -/
def bodyNeedsIOMonad (bodyElems : Array Json) : Bool :=
  bodyElems.toList.any jsonUsesIOEffect

/-- Values using either translated exceptions or translated `IO` require monadic binding in `do`. -/
def jsonUsesMonadicEffect (json : Json) : Bool :=
  jsonUsesExceptionEffect json || jsonUsesIOEffect json

/-- Check if we should use the proof monad (PyProofM) instead of IO.
In exact mode, we want to generate code that uses the proof-oriented state monad
for IO operations, making input/output observable and provable. -/
def shouldUseProofMonad : PygenM Bool := do
  let numMode ← getNumericMode
  return numMode == .exact

/-- Sequence a list of `doElem`s into one `doElem`, using `fallback` for the empty case. -/
def sequenceDoElems (elems : Array (TSyntax `doElem)) (fallback : TSyntax `doElem) :
    PygenM (TSyntax `doElem) := do
  if elems.isEmpty then
    return fallback
  `(doElem| do
    $[$elems:doElem]*)

/-- Emit an explicit no-op statement inside `do` notation. -/
def noopDoElemSyntax : PygenM (TSyntax `doElem) := do
  `(doElem| let _ := ())

/--
A Python name is module-private when it starts with an underscore but is **not** a dunder.
This matches what `from module import *` excludes:

  - `foo`      → public
  - `_foo`     → private (single-underscore "internal use" convention)
  - `__foo`    → private (double underscore, no trailing — strong private / name-mangled)
  - `__foo__`  → public  (dunder: `__init__`, `__name__`, ... are the public protocol)

Private names map to a Lean `private def` so they cannot be imported from other modules.
-/
def pythonNameIsPrivate (name : String) : Bool :=
  name.startsWith "_"
    && name != "_"                                  -- bare `_` is the wildcard
    && !(name.startsWith "__" && name.endsWith "__") -- `__dunder__` is public

/-- The `visibility` slot of `declModifiers`, whose shape is
`docComment? attributes? visibility? noncomputable? unsafe? (partial|nonrec)?`. -/
private def declModifiersVisibilityIdx : Nat := 2

/-- Splice a `private` modifier into an existing `def`/declaration command.

`private` is a `declModifiers` prefix the parser only accepts directly before `def`, so we harvest
the modifier from a throwaway declaration and set it into the target's `declModifiers`. Only the
visibility slot is overwritten: replacing the whole node would drop `partial`/`noncomputable`.
Non-declaration commands are unchanged. -/
def makeCommandPrivate (cmd : TSyntax `command) : PygenM (TSyntax `command) := do
  let template ← `(command| private def __PastaLean_priv_tmpl := ())
  let privVisibility := match template.raw with
    | .node _ ``Lean.Parser.Command.declaration #[.node _ _ mods, _] =>
        mods[declModifiersVisibilityIdx]!
    | _ => Syntax.missing
  match cmd.raw with
  | .node info ``Lean.Parser.Command.declaration #[.node modInfo modKind mods, decl] =>
      let mods := mods.set! declModifiersVisibilityIdx privVisibility
      return ⟨.node info ``Lean.Parser.Command.declaration #[.node modInfo modKind mods, decl]⟩
  | _ => return cmd

/--
Prefix a top-level `def` command with `private` when its Python `name` follows the
leading-underscore privacy convention, so it cannot be imported from other modules
(matching Python's intent). Names are otherwise preserved verbatim (`_foo` stays `_foo`).
Null-node command wrappers (multiple commands) are returned unchanged.
-/
def applyPrivacy (name : String) (cmd : TSyntax `command) : PygenM (TSyntax `command) := do
  if pythonNameIsPrivate name && !cmd.raw.isOfKind nullKind then
    makeCommandPrivate cmd
  else
    pure cmd


end PastaLean
