import PastaLean.Imports
import PastaLean.Codegen
import PastaLean.PyGens.Basic
import PastaLean.PyGens.Attributes
import PastaLean.PyGens.Calls.CallEffects
import PastaLean.PyGens.Calls.CallShared
import PastaLean.PyGens.Calls.SpecialCalls

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-- Local effect probe for early string-lowering code, before the general call helpers below. -/
partial def stringJsonUsesExceptionEffect (json : Json) : Bool :=
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
    | .arr elems => elems.toList.any stringJsonUsesExceptionEffect
    | .obj fields => fields.toList.any (fun (_, value) => stringJsonUsesExceptionEffect value)
    | _ => false

/-- Local effect probe for `IO`-bearing string pieces such as `input()` inside f-strings. -/
partial def stringJsonUsesIOEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "io" => true
    | _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any stringJsonUsesIOEffect
    | .obj fields => fields.toList.any (fun (_, value) => stringJsonUsesIOEffect value)
    | _ => false

/-- Detect whether an early string subtree contains any translated monadic effect. -/
def stringJsonUsesMonadicEffect (json : Json) : Bool :=
  stringJsonUsesExceptionEffect json || stringJsonUsesIOEffect json

@[pygen "FormattedValue"]
def formattedValueSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
    let valueCode ← getCode valueJson `term
    let toStringIdent := mkIdent ``toString
    if stringJsonUsesMonadicEffect valueJson then
      let binder := mkIdent `__py_fmt
      let stringIdent := mkIdent ``String
      let effectTy ←
        if stringJsonUsesExceptionEffect valueJson then
          let exceptIdent := mkIdent ``PastaLean.PyExcept
          `($exceptIdent $stringIdent)
        else
          let ioIdent := mkIdent ``IO
          `($ioIdent $stringIdent)
      `(((do
            let $binder:ident ← $valueCode:term
            return ($toStringIdent $binder:term)) :
          $effectTy))
    else
      `($toStringIdent $valueCode)
  | _, _ => throwError s!"Unsupported syntax category for FormattedValue node"

/-- If `json` is a string-literal `Constant`, return its text (the literal pieces of an
f-string). Otherwise `none` — those pieces are interpolated values. -/
def jsonStringLiteral? (json : Json) : Option String :=
  match json.getObjValAs? String "node_type" with
  | .ok "Constant" =>
      match json.getObjVal? "value" with
      | .ok (.str s) => some s
      | _ => none
  | _ => none

/-- Escape a literal chunk so it is safe inside a Lean interpolated string `s!"…"`: backslash,
double quote and the interpolation braces are escaped, and control characters spelled out. -/
def escapeInterpChunk (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
      | '\\' => "\\\\"
      | '"' => "\\\""
      | '{' => "\\{"
      | '}' => "\\}"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | '\r' => "\\r"
      | _ => c.toString)) ""

/-- The term placed inside `{…}` for an interpolated f-string slot. For a `FormattedValue` the
inner value is used directly (Lean's `s!` applies `toString`); anything else is lowered as-is. -/
def joinedInterpTerm (valueJson : Json) : PygenM (TSyntax `term) := do
  match valueJson.getObjValAs? String "node_type" with
  | .ok "FormattedValue" =>
      let innerCode ← match valueJson.getObjVal? "value" with
        | .ok inner => getCode inner `term
        | .error _ => getCode valueJson `term
      -- A `:.Nf`-style format spec wraps the value in `pyFormatSpec`, which returns the formatted
      -- String (and `s!`'s `toString` on a String is the identity).
      match valueJson.getObjValAs? String "format_spec" with
      | .ok spec =>
          let fmtIdent := mkIdent ``PastaLean.pyFormatSpec
          let specLit := Syntax.mkStrLit spec
          `($fmtIdent $innerCode $specLit)
      | .error _ => pure innerCode
  | _ => getCode valueJson `term

/-- Build a Lean interpolated string `s!"lit{e}lit…"` from the literal/interpolation pieces of an
f-string. `chunks` has exactly one more element than `interps` and they alternate
`chunk₀ interp₀ chunk₁ … interpₙ₋₁ chunkₙ`. -/
def mkInterpolatedStr (chunks : Array String) (interps : Array (TSyntax `term)) :
    TSyntax `term := Id.run do
  let n := interps.size
  let mut children : Array Syntax := #[]
  for i in [0:n+1] do
    let text := escapeInterpChunk (chunks[i]!)
    let atomStr :=
      if i == 0 then "\"" ++ text ++ "{"
      else if i == n then "}" ++ text ++ "\""
      else "}" ++ text ++ "{"
    children := children.push
      (Syntax.node SourceInfo.none `interpolatedStrLitKind #[Syntax.atom SourceInfo.none atomStr])
    if i < n then
      children := children.push interps[i]!.raw
  let interpNode := Syntax.node SourceInfo.none `interpolatedStrKind children
  ⟨Syntax.node SourceInfo.none (Name.mkSimple "termS!_")
    #[Syntax.atom SourceInfo.none "s!", interpNode]⟩

@[pygen "JoinedStr"]
def joinedStrSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valuesJson := json.getObjValAs? Json "values" | throwError
      s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
    let valuesArray ← match valuesJson with
      | .arr arr => pure arr
      | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
    -- The common, all-pure case lowers to a readable `s!"…{e}…"` interpolation. Effectful
    -- pieces (e.g. `← input()` inside an f-string) can't sit inside `s!`, so those fall back to
    -- the `do`-bound append chain below.
    if !valuesArray.any stringJsonUsesMonadicEffect then
      let mut chunks : Array String := #[]
      let mut interps : Array (TSyntax `term) := #[]
      let mut buf : String := ""
      for valueJson in valuesArray do
        match jsonStringLiteral? valueJson with
        | some s => buf := buf ++ s
        | none =>
            chunks := chunks.push buf
            buf := ""
            interps := interps.push (← joinedInterpTerm valueJson)
      chunks := chunks.push buf
      if interps.isEmpty then
        return Syntax.mkStrLit chunks[0]!
      return mkInterpolatedStr chunks interps
    let appendIdent := mkIdent ``String.append
    let valuesCodes ← valuesArray.mapM (fun valueJson => getCode valueJson `term)
    let mut res : TSyntax `term ← `("")
    let mut bindings : Array (TSyntax `doElem) := #[]
    for idx in [0:valuesCodes.size] do
      let valueJson := valuesArray[idx]!
      let valueCode := valuesCodes[idx]!
      if stringJsonUsesMonadicEffect valueJson then
        let binder := mkIdent (s!"p'_join{idx}").toName
        bindings := bindings.push (← `(doElem| let $binder:ident ← $valueCode:term))
        res ← `($appendIdent $res $binder:term)
      else
        res ← `($appendIdent $res $valueCode)
    if bindings.isEmpty then
      return res
    let stringIdent := mkIdent ``String
    let effectTy ←
      if stringJsonUsesExceptionEffect json then
        let exceptIdent := mkIdent ``PastaLean.PyExcept
        `($exceptIdent $stringIdent)
      else
        let ioIdent := mkIdent ``IO
        `($ioIdent $stringIdent)
    `(((do
          $[$bindings:doElem]*
          return $res:term) :
        $effectTy))
  | _, _ => throwError s!"Unsupported syntax category for JoinedStr node"

/-- Fold a binary runtime function `fn` over `args` (length ≥ 2), associating per `dir`. A right
fold builds `fn a₁ (fn a₂ (… (fn aₙ₋₁ aₙ)))`; a left fold builds `fn (… (fn a₁ a₂) …) aₙ`. Drives
the variadic-builtin lowering (e.g. `zip`) from `variadicFoldBuiltin?`. -/
def foldBinaryOverArgs (fn : TSyntax `term) (dir : BuiltinFoldDir) (args : Array (TSyntax `term)) :
    PygenM (TSyntax `term) := do
  match dir with
  | .right =>
      let mut acc := args[args.size - 1]!
      for i in (List.range (args.size - 1)).reverse do
        acc ← `($fn $(args[i]!) $acc)
      pure acc
  | .left =>
      let mut acc := args[0]!
      for i in [1:args.size] do
        acc ← `($fn $acc $(args[i]!))
      pure acc

/-- Map a bare Python builtin function name to the Lean runtime symbol when it is used as a value. -/
def mappedCallableValueCode (json : Json) : PygenM (TSyntax `term) := do
  match ← jsonLibraryMappedName? json with
  | some leanName =>
      pure (mkIdent leanName : TSyntax `term)
  | none =>
      match json.getObjValAs? String "node_type", json.getObjValAs? String "id" with
      | .ok "Name", .ok funcName =>
          match ← builtinMappedName? funcName with
          | some mappedName => pure (mkIdent mappedName : TSyntax `term)
          | none =>
              let mappedName ← leanName funcName.toName
              pure (mkIdent mappedName : TSyntax `term)
      | _, _ =>
          getCode json `term

/-- Lower `min(...)` / `max(...)` (`which` is `"min"` or `"max"`). Handles a single iterable
(`min(xs)`), several positionals gathered into a list (`min(a, b, c)`), and the optional
`key=f` keyword (→ `pyMinBy`/`pyMaxBy`). -/
def lowerMinMaxCall (which : String) (argsArray : Array Json) (argsCodes : Array (TSyntax `term))
    (keyWordsMap : PyKeywordArgs) : PygenM (TSyntax `term) := do
  for (kwName, _) in keyWordsMap.toList do
    unless kwName == "key" || kwName == "default" do
      throwError s!"{which}() keyword argument '{kwName}' is not supported yet."
  unless argsArray.size ≥ 1 do
    throwError s!"{which}() expects at least one argument."
  let keyOpt := keyWordsMap.get? "key"
  -- `min(xs, default=d)` returns `d` for an empty iterable rather than raising.
  let defaultCode ← match keyWordsMap.get? "default" with
    | some d => some <$> getCode d `term
    | none => pure none
  -- A single container-ref iterable (`min(xs)`) is consumed by value, so deref it under `--heap`.
  let argsCodes ← derefBuiltinArgCodes argsArray argsCodes
  buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
    let iterable ← if resolvedArgs.size == 1 then pure resolvedArgs[0]!
      else `([$resolvedArgs,*])
    let base ← match keyOpt with
      | none =>
          let fn := mkIdent (if which == "min" then ``pyMin else ``pyMax)
          `($fn $iterable)
      | some kJson =>
          let keyCode ← mappedCallableValueCode kJson
          let fn := mkIdent (if which == "min" then ``pyMinBy else ``pyMaxBy)
          `($fn $keyCode $iterable)
    match defaultCode with
    | some d => `(if $(mkIdent ``PastaLean.pyLen) $iterable == (0 : Int) then $d else $base)
    | none => pure base

/-- Resolve the class of a method-call receiver `recv.m(...)`: `self` inside a class body resolves
to the class being lowered; otherwise fall back to the unique registered class that declares a
method named `attr`. `none` when it can't be determined (an unknown/ambiguous method). -/
def resolveReceiverClass? (valueJson : Json) (attr : String) : PygenM (Option String) := do
  if jsonNodeType? valueJson == some "Name"
      && valueJson.getObjValAs? String "id" == .ok "self" then
    match (← get).currentClass with
    | some c => return some c
    | none => pure ()
  classOfMethod? attr

/-- Store `newVal` back into the receiver an in-place method mutated. `xs` ⇒ `xs := newVal`;
`g[i]` ⇒ `g := pySetItem g i newVal` (recursing for `g[i][j]`). -/
partial def assignBackToReceiver (recvJson : Json) (newVal : TSyntax `term) :
    PygenM (TSyntax `doElem) := do
  match jsonNodeType? recvJson with
  | some "Name" =>
      let recvIdent ← getCode recvJson `ident
      `(doElem| $recvIdent:ident := $newVal)
  | some "Subscript" =>
      let .ok containerJson := recvJson.getObjValAs? Json "value" | throwError
        s!"Subscript receiver is missing a 'value' field: {recvJson}"
      let .ok sliceJson := recvJson.getObjValAs? Json "slice" | throwError
        s!"Subscript receiver is missing a 'slice' field: {recvJson}"
      if jsonNodeType? sliceJson == some "Slice" then
        throwError "A mutating method on a slice receiver (`xs[a:b].append(v)`) is not supported."
      let indexTerm ← getCode sliceJson `term
      let containerTerm ← getCode containerJson `term
      let setItemIdent := mkIdent ``PastaLean.pySetItem
      assignBackToReceiver containerJson (← `($setItemIdent $containerTerm $indexTerm $newVal))
  | some "Attribute" =>
      -- `self.small.append(v)` / `heappush(self.small, x)`: rebuild the field via record update
      -- (`self := { self with small := newVal }`), like an attribute assignment.
      if (selfAttrTarget? recvJson).isSome && (← hasVar `self) then
        selfRecordUpdateDoElem (selfAttrTarget? recvJson).get! newVal
      else
        let .ok recv := recvJson.getObjVal? "value" | throwError s!"Attribute receiver missing 'value': {recvJson}"
        let .ok attr := recvJson.getObjValAs? String "attr" | throwError s!"Attribute receiver missing 'attr': {recvJson}"
        attrRecordUpdateDoElem recv attr newVal (recvJson.getObjValAs? Bool "_unwrap_opt" == .ok true)
  | _ =>
      throwError "A mutating method needs a variable, subscript, or attribute receiver (`xs.append(v)`, \
        `g[i].append(v)`, `self.h.append(v)`) under value semantics."

/-- Lower an in-place mutator `recv.m(args)` by rebuilding `recv` from `mkNewValue recv` and storing
it back, so `g[i].append(v)` becomes `g := pySetItem g i (pyAppend g[i] v)` rather than a no-op. -/
def mutatingMethodDoElem (recvJson : Json)
    (mkNewValue : TSyntax `term → PygenM (TSyntax `term)) : PygenM (TSyntax `doElem) := do
  -- Under `--heap`, a mutable container held by reference is mutated in place through the ref:
  -- `xs.append(v)` → `modifyRef <xs-ref> (fun l => pyAppend l v)` (no rebuild-and-reassign).
  if let some refCode ← heapContainerRef? recvJson then
    let lVar := mkIdent `__hc_l
    let newVal ← mkNewValue lVar
    -- A `newVal` with a `(← …)` await (`g[i].append(Node())` → `pyAppend l (← Node.new)`; a heap
    -- read `dictionary[idx]`) can't sit inside `modifyRefM`'s `fun l => …` — the await cannot lift
    -- over the lambda binder. Read-then-write instead, so the awaits stay in the enclosing `do`.
    if syntaxHasLift newVal then
      return ← `(doElem| do
        let $lVar ← PastaLean.readRefM $refCode
        PastaLean.writeRefM $refCode $newVal)
    return ← `(doElem| PastaLean.modifyRefM $refCode (fun $lVar => $newVal))
  let recvTerm ← getCode recvJson `term
  assignBackToReceiver recvJson (← mkNewValue recvTerm)

/-- An in-place mutating method used AS A STATEMENT: the runtime function that rebuilds the receiver
(`recv := fn recv args…`) and the accepted positional-arg counts. Pure mutators (`append`, `clear`,
…) and value+rest mutators (`pop`, `popleft`) are handled uniformly — in statement position both
drop any return value and just rebuild the receiver. The arity guard keeps a user method of the same
name (`tree.update(i, v)`) from being hijacked. `sort` (kwargs) and dict `get` stay separate. -/
def statementMutatorRebuild? (attr : String) : Option (Lean.Name × List Nat) :=
  match attr with
  | "append"     => some (``pyAppend,      [1])
  | "appendleft" => some (``pyAppendLeft,  [1])
  | "extend"     => some (``pyExtend,      [1])
  | "update"     => some (``pyUpdate,      [1])
  | "clear"      => some (``pyClear,       [0])
  | "reverse"    => some (``pyReverse,     [0])
  | "insert"     => some (``pyInsert,      [2])
  | "add"        => some (``pySetAdd,      [1])
  | "discard"    => some (``pySetDiscard,  [1])
  | "remove"     => some (``pySetRemove,   [1])
  | "pop"        => some (``pyPopRest,     [0, 1])
  | "popleft"    => some (``pyPopLeftRest, [0])
  | "setdefault" => some (``pyDictSetdefaultRest, [2])
  | _            => none

/-- A `SortedList` instance method (`sl.add`, `sl.bisect_left`, `sl.remove`, …) resolved to its
runtime function when the receiver `recvJson` is a variable flagged as holding a SortedList. `none`
otherwise — so a plain `bisect.bisect_left(xs, x)` or a set's `add`/`remove` is untouched. The
name map itself lives in the Libraries layer; codegen only supplies the receiver-type gate. -/
def sortedVarMethod? (attr : String) (recvJson : Json) : PygenM (Option Lean.Name) := do
  match recvJson.getObjValAs? String "id" with
  | .ok id => if ← isSortedVar id.toName then return Libraries.sortedListMethod? attr else return none
  | _ => return none

/-- A method on a library-owned object (`m.hexdigest()` where `m = hashlib.md5()`), resolved through
the owning library. Gated on the receiver being a variable tagged with that module, so a colliding
name (`update`, also dict/set) still resolves normally for every other receiver. Same shape as
`sortedVarMethod?`: the map lives in Libraries, codegen supplies only the receiver gate. -/
def libObjVarMethod? (attr : String) (recvJson : Json) : PygenM (Option Lean.Name) := do
  match recvJson.getObjValAs? String "id" with
  | .ok id =>
      match ← libObjVarModule? id.toName with
      | some m => return Libraries.libraryMethod? m attr
      | none => return none
  | _ => return none

/-- `bisect_left/right(range(a, b, c), x, key=f)` searches the range LAZILY (O(log n) `key` calls)
instead of materializing it and mapping `key` over every element (O(n), and impossible for a range up
to `10**9`). Returns the range-variant runtime name and the args with the range replaced by its
`start, stop, step`; `none` if the first arg isn't a plain `range(...)`. -/
def bisectRangeKeyed? (member : String) (argsArray : Array Json) (allArgs : Array (TSyntax `term)) :
    PygenM (Option (Lean.Name × Array (TSyntax `term))) := do
  let rv? : Option Lean.Name :=
    if member == "bisect_left" then some ``Libraries.bisect.pyBisectLeftRangeKey
    else if member == "bisect" || member == "bisect_right" then some ``Libraries.bisect.pyBisectRightRangeKey
    else none
  let some rv := rv? | return none
  let some firstArg := argsArray[0]? | return none
  -- The pre-pass turns `range(...)` into a `Range` node (func `range`, `args` its bounds).
  unless jsonNodeType? firstArg == some "Range" do return none
  let rargs := (firstArg.getObjValAs? (Array Json) "args").toOption.getD #[]
  let zero ← `((0 : Int)); let one ← `((1 : Int))
  let (startT, stopT, stepT) ← match rargs.size with
    | 0 => return none
    | 1 => pure (zero, ← getCode rargs[0]! `term, one)
    | 2 => pure (← getCode rargs[0]! `term, ← getCode rargs[1]! `term, one)
    | _ => pure (← getCode rargs[0]! `term, ← getCode rargs[1]! `term, ← getCode rargs[2]! `term)
  return some (rv, #[startT, stopT, stepT] ++ allArgs.extract 1 allArgs.size)

/-- The class to construct for a call `f(...)` whose callee is the `Name` `funcName`: a registered
class (`C(..)`), or `cls(..)` inside a class body (classmethod sugar). `none` for ordinary calls. -/
def constructorClassOfName? (funcName : String) : PygenM (Option String) := do
  if ← isRegisteredClass funcName then return some funcName
  if funcName == "cls" then return (← get).currentClass
  return none

/-- True when `name` already resolves to some existing global (a Mathlib/Lean/PastaLean
declaration) — i.e. a bare reference to it would be an ambiguous clash. A fresh user name (a
recursive helper, an ordinary function) resolves to nothing here, since user defs are not in the
codegen environment. -/
def nameClashesWithGlobal (name : String) : PygenM Bool :=
  return !(← resolveGlobalName name.toName).isEmpty

/-- The Lean callee term for a call to the user function `funcName` (after run-suffix + `leanName`).
Only when the name *actually collides* with an existing global (`dist` → `Dist.dist`, `gcd` → …) is
it `_root_`-qualified, so it resolves to the user's own definition rather than the Mathlib export.
A non-clashing name (including a recursive self-call like `fibonacci`, which is not yet in the
environment) is left bare — qualifying it would break the recursive reference. This is the general
fix for user-name-vs-Mathlib clashes, without wrapping the program in a namespace. -/
def userCallIdent (funcName : String) : PygenM (TSyntax `term) := do
  let mapped ← leanName (← suffixIfUserName funcName).toName
  -- User defs live in `namespace PastaLean.User.<path>`, so a bare call resolves to the user's own
  -- function by namespace precedence — no `_root_` needed (it misfired for globals under a namespace).
  return (mkIdent mapped : TSyntax `term)

/-- If a `key=` argument calls a member a library declares as a comparator-to-key wrapper, the
comparator it wraps. The wrapper has no runtime object here, so the sort routes to `pySortByCmp`.
Which members qualify is declared by the library (`Behaviour.cmpKeyWrapper`), not listed here. -/
def cmpKeyComparator? (keyJson : Json) : Option Json := do
  guard (jsonNodeType? keyJson == some "Call")
  let func ← (keyJson.getObjVal? "func").toOption
  let memberName ←
    (func.getObjValAs? String "library_member").toOption
      <|> (func.getObjValAs? String "id").toOption
      <|> (func.getObjValAs? String "attr").toOption
  guard (Libraries.isCmpKeyWrapper memberName)
  let args ← (keyJson.getObjValAs? (Array Json) "args").toOption
  args[0]?

/-- The sort term for a `key=`/`reverse=` pair, over an already-lowered receiver. Shared by
`sorted(...)` and `list.sort(...)` so both support `cmp_to_key` identically. -/
def sortWithKeyTerm (keyOpt revOpt : Option Json) (recv : TSyntax `term) : PygenM (TSyntax `term) := do
  let revCode ← match revOpt with
    | some rJson => getCode rJson `term
    | none => `(false)
  match keyOpt.bind cmpKeyComparator? with
  | some cmpJson =>
      let cmpCode ← mappedCallableValueCode cmpJson
      `($(mkIdent ``pySortByCmp) $cmpCode $revCode $recv)
  | none =>
      let keyCode ← match keyOpt with
        | some kJson => mappedCallableValueCode kJson
        | none => `(fun x => x)
      `($(mkIdent ``pySortBy) $keyCode $revCode $recv)

/-- In a Prop context (a contract), lower `all(p for t in it)` to `∀ t ∈ pyIter it, p` and `any` to
`∃`, instead of the `Bool` `pyAll (… decide p)` — whose `decide`/fold hide the quantifier from the
tactics, making such a contract true but unprovable. Comprehension `ifs` become guards for `all`
(`c → p`) and conjuncts for `any`. `none` (→ `Bool` lowering) for any other shape. -/
def quantifiedAllAnyProp? (funcName : String) (callJson : Json) :
    PygenM (Option (TSyntax `term)) := do
  unless ← getPropCondition do return none
  unless isQuantifiedAllAnyJson callJson do return none
  let .ok (args : Array Json) := callJson.getObjValAs? (Array Json) "args" | return none
  let argJson := args[0]!
  let .ok (generators : Array Json) := argJson.getObjValAs? (Array Json) "generators" | return none
  let gen := generators[0]!
  let .ok target := gen.getObjVal? "target" | return none
  let .ok iter := gen.getObjVal? "iter" | return none
  let .ok elt := argJson.getObjVal? "elt" | return none
  let ifs := (gen.getObjValAs? (Array Json) "ifs").toOption.getD #[]
  let iterCode ← getCode iter `term
  withFixedVariables do
    let targetIdent ← getCode target `ident
    addVar targetIdent.getId
    let mut body ← withPropCondition true (getCode elt `term)
    for ifJson in ifs.reverse do
      let guard ← withPropCondition true (getCode ifJson `term)
      body ← if funcName == "all" then `($guard → $body) else `($guard ∧ $body)
    let iterList ← `($(mkIdent ``PastaLean.pyIter) $iterCode)
    if funcName == "all" then
      return some (← `(∀ $targetIdent:ident ∈ $iterList, $body))
    else
      return some (← `(∃ $targetIdent:ident ∈ $iterList, $body))


def callSyntaxTerm (json : Json) : PygenM (TSyntax `term) := do
    let .ok funcJson := json.getObjValAs? Json "func" | throwError
      s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
    let .ok argsJson := json.getObjValAs? Json "args" | throwError
      s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
    let argsArray ← match argsJson with
      | .arr arr => pure arr
      | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
    if let some nonFinite ← nonFiniteFloatTerm? funcJson argsArray then
      -- Ascribe the polymorphic sentinel to its inferred `_ty` when TypeInfer pinned one (e.g. a
      -- `float('inf')` element of a list appended to a `list[int]` slot → `(pyNonFinite "inf" : ℤ)`),
      -- so it does not default to `ℚ`.
      match ← (jsonFieldOption json "_ty").mapM (fun ann => pyTypeSyntax? (TypeInfer.ofAnnotation ann)) with
      | some (some tyStx) => return ← `(($nonFinite : $tyStx))
      | _ => return nonFinite
    let mut argsCodes ← argsArray.mapM (fun argJson => getCode argJson `term)

    let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
      s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
    let .ok keyWordsMap := keyWordsJson.getObj? | throwError
      s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"

    let mut allArgs : Array (TSyntax `term) := #[]
    let mut allArgJsons : Array Json := #[]
    let mut funcIdent : TSyntax `term ← `("")

    match ← lowerSpecialCallTerm? funcJson argsArray argsCodes keyWordsMap with
    | some lowered => return lowered
    | none => pure ()

    match ← jsonLibraryMappedName? funcJson with
    | some leanName =>
        funcIdent := (mkIdent leanName : TSyntax `term)
    | none =>
      if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
        let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
          s!"Attribute node missing 'value' field: {funcJson}"
        let .ok attr := funcJson.getObjValAs? String "attr" | throwError
          s!"Attribute node missing 'attr' field: {funcJson}"

        -- `ClassName.method(args)` (static/classmethod/unbound) -> `C.method args`, no receiver.
        if let some cls := (json.getObjValAs? String "_static_class").toOption then
          let methodIdent : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
          let build : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolved => do
            let mut t ← `($methodIdent $resolved*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← getCode kwValueJson `term
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            pure t
          if argsArray.toList.any basicJsonUsesIOEffect then
            return ← buildIOPureApplicationFromArgs argsArray argsCodes build
          else
            return ← build argsCodes

        -- A method call on a known class instance (`_receiver_class` stamped by py2lean) dispatches
        -- to `C.attr recv args` and takes precedence over the builtin-method special-cases below,
        -- so a user method may shadow a builtin name (`get`, `pop`, …).
        if let some cls := (json.getObjValAs? String "_receiver_class").toOption then
          let heap ← getHeapMode
          if (json.getObjValAs? Bool "_is_mutator").toOption.getD false && !heap then
            throwError s!"Mutating method '{attr}' cannot be used as an expression under value \
              semantics; call it as a statement on its own line."
          let valCode ← getCode valueJson `term
          let attrId := mkIdent attr.toName
          -- Non-heap: dispatch via Lean DOT-NOTATION `recv.attr args` (not `Cls.attr recv args`), which
          -- resolves `attr` in the receiver's structure namespace and WALKS `extends`, so an inherited
          -- method (`class B(A); b.func()` where `func` lives in `A`) resolves to `A.func`, and the `'rn`
          -- twin is picked from the receiver value's type. Heap keeps the qualified `Cls.attr recv` form:
          -- there the receiver is a `Ref C`, so dot-notation would look `attr` up on `Ref`, not `C`.
          let methodIdent : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
          let allJsons := #[valueJson] ++ argsArray
          let allCodes := #[valCode] ++ argsCodes
          let build : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolved => do
            let recv := resolved[0]!
            let args := resolved.extract 1 resolved.size
            let mut t ← `($recv.$attrId $args*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← getCode kwValueJson `term
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            pure t
          -- Under `--heap`, `C.m recv args : HeapM Val ret` — await it inline (the `←` lifts into the
          -- enclosing method/function `do`-block).
          if heap then
            -- Inline any IO await in the receiver/args (`recv.m(int(input()))`) so it lifts into the
            -- enclosing do-block rather than being spliced as a raw `IO _` action into a value position.
            let recvCode ← inlineEffectfulTerm valueJson
            let inlineArgs ← argsArray.mapM inlineEffectfulTerm
            let mut t ← `($methodIdent $recvCode $inlineArgs*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← inlineEffectfulTerm kwValueJson
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            return ← `((← $t))
          if allJsons.toList.any basicJsonUsesIOEffect then
            return ← buildIOPureApplicationFromArgs allJsons allCodes build
          else
            return ← build allCodes

        if attr == "get" then
          unless keyWordsMap.isEmpty do
            throwError "get() calls with keyword arguments are not supported yet."
          let valCode ← getCode valueJson `term
          match argsArray.size with
          | 1 =>
              let keyCode ← getCode argsArray[0]! `term
              let pyGetOptIdent := mkIdent ``pyGetOpt?
              return ← `($pyGetOptIdent $valCode $keyCode)
          | 2 =>
              let keyCode ← getCode argsArray[0]! `term
              let defaultCode ← getCode argsArray[1]! `term
              let pyGetDIdent := mkIdent ``pyGetD
              return ← `($pyGetDIdent $valCode $keyCode $defaultCode)
          | _ =>
              throwError "get() expects one or two positional arguments."

        if attr == "sort" then
          throwError "sort() is only supported as a statement; use sorted(x) in expressions."

        if attr == "format" then
          -- `"… {} …".format(a, b)`: stringify each argument and fill the `{}` placeholders.
          unless keyWordsMap.isEmpty do
            throwError "str.format() keyword arguments are not supported yet."
          let receiverCode ← getCode valueJson `term
          let stringifyIdent := mkIdent ``PastaLean.pyStringify
          let formatIdent := mkIdent ``PastaLean.pyStrFormat
          return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
            let stringified ← resolvedArgs.mapM (fun a => `($stringifyIdent $a))
            `($formatIdent $receiverCode [$stringified,*])

        -- `pop` both returns a value and mutates its receiver, which a pure term cannot express.
        -- Refuse it in expression position so the pure-function path falls back to the monadic
        -- lowering, where `x = container.pop(...)` is handled as a statement (value bind +
        -- container update). `pop` in any other expression position stays a clear error.
        if attr == "pop" then
          throwError "pop() returns a value *and* mutates its receiver; it is only supported as \
            a direct assignment `x = container.pop(...)`, not as a sub-expression."

        let valCode ← getCode valueJson `term
        allArgs := allArgs.push valCode
        allArgJsons := allArgJsons.push valueJson

        match (← sortedVarMethod? attr valueJson) <|> (← libObjVarMethod? attr valueJson)
              <|> pythonMethodMap attr with
        | some funcName =>
            funcIdent := mkIdent funcName
            -- Under `--heap`, a runtime method that CONSUMES a container arg (`sep.join(xs)` →
            -- `pyStringJoin sep xs`) needs that arg dereferenced when it's held by reference — the
            -- deref only fires on a heap container arg, leaving scalars/strings untouched.
            argsCodes ← derefBuiltinArgCodes argsArray argsCodes
        | none =>
            -- A user-defined method `recv.m(args)` -> `C.m recv args` (receiver already pushed).
            -- Prefer the py2lean stamp (`_receiver_class`/`_is_mutator`); fall back to the registry.
            let cls? ← match (json.getObjValAs? String "_receiver_class").toOption with
              | some c => pure (some c)
              | none => resolveReceiverClass? valueJson attr
            match cls? with
            | some cls =>
                let isMut ← match (json.getObjValAs? Bool "_is_mutator").toOption with
                  | some b => pure b
                  | none => methodIsMutator cls attr
                if isMut then
                  throwError s!"Mutating method '{attr}' cannot be used as an expression under \
                    value semantics; call it as a statement on its own line."
                funcIdent := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
            | none =>
                throwError s!"Unsupported Python method '{attr}' encountered in Call node."
      else
        -- Inside a memoized function's body, a recursive self-call lowers to the monadic `StateM`
        -- worker `(← fooMemo'rn args)`, so the recursion threads the shared cache. Do-notation hoists
        -- the `(←…)` to a bind in the enclosing do-block (the memoized body is a `do`).
        if let some (memoName, memoWorker) ← getMemoizeSelf then
          if funcJson.getObjValAs? String "id" == .ok memoName
             && funcJson.getObjValAs? String "node_type" == .ok "Name" then
            let argCodes ← argsArray.mapM (fun a => getCode a `term)
            return ← `((← $(mkIdent memoWorker) $argCodes*))
        match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok "print" => do
            let supportedKeywords := ["sep", "end"]
            for (kwName, _) in keyWordsMap.toList do
              unless supportedKeywords.contains kwName do
                throwError s!"print() keyword argument '{kwName}' is not supported yet."
            -- Mode-dependent print: proof mode uses pyPrintProof (accumulates output to state),
            -- run mode uses pyPrintIO (real IO), and fallback exact mode uses pyPrintNoop (discards).
            -- IO-effect args (`input()`) are still hoisted and run by `buildIOActionApplicationFromArgs`.
            let printFn ← if (← shouldUseProofMonad) then
                pure (mkIdent ``PastaLean.ProofMode.pyPrintProof)
              else if (← getNumericMode) == .exact then
                pure (mkIdent `pyPrintNoop)
              else
                pure (mkIdent `pyPrintIO)
            return ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let printArgs ← buildPrintArgsList argsArray resolvedArgs
              match keyWordsMap.get? "sep", keyWordsMap.get? "end" with
              | none, none =>
                  `($printFn $printArgs)
              | _, _ =>
                  let sepCode ← match keyWordsMap.get? "sep" with
                    | some sepJson => getCode sepJson `term
                    | none => `(" ")
                  let endCode ← match keyWordsMap.get? "end" with
                    | some endJson => getCode endJson `term
                    | none => `("\n")
                  `($printFn $printArgs $sepCode $endCode)
        | .ok "Name", .ok "input" => do
            unless keyWordsMap.isEmpty do
              throwError "input() keyword arguments are not supported yet."
            unless argsArray.size ≤ 1 do
              throwError "input() expects zero or one positional argument."
            -- Choose between proof mode (PyProofM) and run mode (IO) input
            let inputIdent ← if (← shouldUseProofMonad) then
                pure (mkIdent ``PastaLean.ProofMode.pyInputProof)
              else
                pure (mkIdent ``pyInputIO)
            return ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              match resolvedArgs.size with
              | 0 => `($inputIdent "")
              | 1 =>
                  let arg0 := resolvedArgs[0]!
                  `($inputIdent $arg0)
              | _ => throwError "input() expects zero or one positional argument."
        | .ok "Name", .ok "int" => do
            unless keyWordsMap.isEmpty do
              throwError "int() keyword arguments are not supported yet."
            -- `int()` with no argument is Python's `0`.
            if argsArray.isEmpty then return ← `((0 : Int))
            unless argsArray.size == 1 || argsArray.size == 2 do
              throwError "int() expects one or two positional arguments."
            -- `int(a > b)` casts a VALUE, so its argument is `Bool`, not `Prop`, even inside an `if`
            -- test (`if int(cmp):`) — re-lower in value context so a comparison becomes `Bool`.
            let intArgsCodes ← withPropCondition false (argsArray.mapM (getCode · `term))
            return ← buildIOPureApplicationFromArgs argsArray intArgsCodes fun resolvedArgs => do
              -- `int(s, base)` parses a string in the given radix; `int(x)` is the plain cast.
              if resolvedArgs.size == 2 then
                `($(mkIdent ``pyIntBase) $(resolvedArgs[0]!) $(resolvedArgs[1]!))
              else
                `($(mkIdent ``pyInt) $(resolvedArgs[0]!))
        | .ok "Name", .ok "str" => do
            unless keyWordsMap.isEmpty do
              throwError "str() keyword arguments are not supported yet."
            return ← match argsArray.size with
            | 0 => `("")
            | 1 => do
                let pyStrIdent := mkIdent ``pyStr
                let argsCodes ← derefBuiltinArgCodes argsArray argsCodes
                buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                  let arg0 := resolvedArgs[0]!
                  `($pyStrIdent $arg0)
            | _ =>
                throwError "str() expects zero or one positional argument."
        | .ok "Name", .ok "list" => do
            unless keyWordsMap.isEmpty do
              throwError "list() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "list() currently expects exactly one positional argument."
            let pyListIdent := mkIdent ``pyList
            argsCodes ← derefBuiltinArgCodes argsArray argsCodes
            return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyListIdent $arg0)
        | .ok "Name", .ok "isinstance" => do
            unless argsArray.size == 2 do
              throwError "isinstance() expects exactly two positional arguments."
            let xCode ← getCode argsArray[0]! `term
            let tJson := argsArray[1]!
            -- `isinstance(x, (t₁, …, tₙ))` — a tuple of types means "any of".
            if tJson.getObjValAs? String "node_type" == .ok "Tuple" then
              let elts := (tJson.getObjValAs? (Array Json) "elts").toOption.getD #[]
              let tags ← elts.filterMapM pyTypeNameTag?
              unless tags.size == elts.size do
                throwError "isinstance(): only builtin types (int/float/str/bool/list/dict/tuple/set) are supported."
              return ← `($(mkIdent ``PastaLean.pyIsInstanceAny) $xCode [$tags,*])
            match ← pyTypeNameTag? tJson with
            | some tag => return ← `($(mkIdent ``PastaLean.pyIsInstance) $xCode $tag)
            | none =>
                throwError "isinstance(): only builtin types (int/float/str/bool/list/dict/tuple/set) are supported."
        | .ok "Name", .ok "map" => do
            unless keyWordsMap.isEmpty do
              throwError "map() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "map() currently expects exactly two positional arguments."
            let pyMapIdent := mkIdent ``pyMap
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let iterCode := (← heapValueDeref? argsArray[1]!).getD argsCodes[1]!
            let adjustedCodes := #[funcCode, iterCode]
            return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyMapIdent $f $xs)
        | .ok "Name", .ok "filter" => do
            unless keyWordsMap.isEmpty do
              throwError "filter() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "filter() currently expects exactly two positional arguments."
            let pyFilterIdent := mkIdent ``pyFilter
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let iterCode := (← heapValueDeref? argsArray[1]!).getD argsCodes[1]!
            let adjustedCodes := #[funcCode, iterCode]
            return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyFilterIdent $f $xs)
        | .ok "Name", .ok "sorted" => do
            -- `sorted(iterable)` → `pySort`; `sorted(iterable, key=f, reverse=b)` → `pySortBy`.
            -- Only `key`/`reverse` keywords are meaningful for Python's `sorted`.
            for (kwName, _) in keyWordsMap.toList do
              unless kwName == "key" || kwName == "reverse" do
                throwError s!"sorted() keyword argument '{kwName}' is not supported yet."
            unless argsArray.size == 1 do
              throwError "sorted() expects exactly one positional argument (the iterable)."
            -- The iterable is consumed by value; deref a container-ref under `--heap`.
            argsCodes ← derefBuiltinArgCodes argsArray argsCodes
            match keyWordsMap.get? "key", keyWordsMap.get? "reverse" with
            | none, none =>
                let pySortIdent := mkIdent ``pySort
                return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                  `($pySortIdent $(resolvedArgs[0]!))
            | keyOpt, revOpt =>
                return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                  sortWithKeyTerm keyOpt revOpt (resolvedArgs[0]!)
        | .ok "Name", .ok "round" => do
            -- `round(x)` returns an `int` (banker's rounding); `round(x, n)` returns a `float`.
            unless keyWordsMap.isEmpty do
              throwError "round() keyword arguments are not supported yet."
            match argsArray.size with
            | 1 =>
                return ← buildIOPureApplicationFromArgs argsArray argsCodes fun r => do
                  `($(mkIdent ``pyRound) $(r[0]!))
            | 2 =>
                return ← buildIOPureApplicationFromArgs argsArray argsCodes fun r => do
                  `($(mkIdent ``pyRoundDigits) $(r[0]!) $(r[1]!))
            | _ => throwError "round() expects one or two arguments."
        | .ok "Name", .ok "min" => return ← lowerMinMaxCall "min" argsArray argsCodes keyWordsMap
        | .ok "Name", .ok "max" => return ← lowerMinMaxCall "max" argsArray argsCodes keyWordsMap
        | .ok "Name", .ok "next" =>
            -- `next(it)` / `next(it, default)`. Our comprehensions/`iter(...)` are eager `List`s, so
            -- this is the first element (or the default when empty).
            unless keyWordsMap.isEmpty do throwError "next() keyword arguments are not supported."
            argsCodes ← derefBuiltinArgCodes argsArray argsCodes
            return ← buildIOPureApplicationFromArgs argsArray argsCodes fun r => do
              let iter ← `($(mkIdent ``PastaLean.pyIter) $(r[0]!))
              match r[1]? with
              | some d => `(($iter).headD $d)
              | none   => `(($iter).headD default)
        | .ok "Name", .ok funcName =>
            -- `any`/`all` test each element's TRUTHINESS, so lower the iterable argument in a
            -- truthiness context — a `BoolOp` element (`x and y` on mixed-type operands) then stays a
            -- `Bool` (`pyTruthy x && y`) instead of the value form whose branches don't unify.
            if (funcName == "any" || funcName == "all") && argsArray.size == 1 && keyWordsMap.isEmpty then
              -- In a contract this becomes a real `∀`/`∃`; outside one, keep the `Bool` fold.
              if let some quantified ← quantifiedAllAnyProp? funcName json then
                return quantified
              if let some mapped ← builtinMappedName? funcName then
                let argCode ← withTruthinessContext true (getCode argsArray[0]! `term)
                return ← `($(mkIdent mapped) $argCode)
            -- Under `--heap`, `len(x)` on a container held by reference dereferences it first.
            if funcName == "len" && argsArray.size == 1 then
              if let some deref ← heapContainerDeref? argsArray[0]! then
                return ← `($(mkIdent ``pyLen) $deref)
            -- Class instantiation `C(args)` (or `cls(args)` in a classmethod) -> `C.mk args`.
            -- Prefer the py2lean dispatch stamp (`_class_ctor`); fall back to the local registry.
            match ← (do match (json.getObjValAs? String "_class_ctor").toOption with
                        | some c => pure (some c) | none => constructorClassOfName? funcName) with
            | some cls =>
              let ctorId : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName "new")
              -- Under `--heap`, `C.new args : HeapM Val (Ref C)` — await it inline.
              if ← getHeapMode then
                -- Inline any IO await in an argument (`C(int(input()))`) so it lifts into the enclosing
                -- do-block rather than being spliced as a raw `IO _` action into a value position.
                let inlineArgs ← argsArray.mapM inlineEffectfulTerm
                let mut t ← `($ctorId $inlineArgs*)
                for (kwName, kwValueJson) in keyWordsMap.toList do
                  let kwValueCode ← inlineEffectfulTerm kwValueJson
                  t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
                return ← `((← $t))
              funcIdent := ctorId
            | none =>
            -- Variadic builtins that fold a binary runtime function over their args (e.g. `zip`)
            -- are handled generically from the `variadicFoldBuiltin?` registry — one handler for
            -- all of them, so a new such builtin is a registry row, not a branch here.
            if let some (foldFn, dir) := variadicFoldBuiltin? funcName then
              unless keyWordsMap.isEmpty do
                throwError s!"{funcName}() keyword arguments are not supported yet."
              -- `zip(*rows)` is a transpose, not a fold over several iterables: one starred arg.
              if funcName == "zip" && argsArray.size == 1
                  && jsonNodeType? argsArray[0]! == some "Starred" then
                let .ok inner := argsArray[0]!.getObjVal? "value" | throwError
                  s!"Starred argument is missing a 'value': {argsArray[0]!}"
                let innerCode := (← heapValueDeref? inner).getD (← getCode inner `term)
                return ← `($(mkIdent ``PastaLean.pyZipStar) $innerCode)
              unless argsArray.size ≥ 2 do
                throwError s!"{funcName}() expects at least two arguments."
              let foldIdent := mkIdent foldFn
              argsCodes ← derefBuiltinArgCodes argsArray argsCodes
              return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                foldBinaryOverArgs foldIdent dir resolvedArgs
            else match ← builtinMappedName? funcName with
            | some mappedName =>
                -- A mapped builtin (`sum`, `reversed`, `enumerate`, …) consumes its iterable by value;
                -- deref container-ref args so it sees contents, not the `Ref` (a user call keeps the
                -- ref — its `--heap` calling convention). No-op off `--heap` / for non-container args,
                -- so the shared application tail below is otherwise unchanged.
                argsCodes ← derefBuiltinArgCodes argsArray argsCodes
                funcIdent := (mkIdent mappedName : TSyntax `term)
            | none =>
                funcIdent ← userCallIdent funcName
        | _, _ =>
            funcIdent ← getCode funcJson `term

    for argCode in argsCodes do
      allArgs := allArgs.push argCode
    for argJson in argsArray do
      allArgJsons := allArgJsons.push argJson

    -- A 0-arg call `f()` where `f` is a *local* callable (a loop/param/let-bound value holding one of
    -- the `fun () ↦ …` thunks our lambdas lower to) applies it to `Unit`, so emit `f ()`. A
    -- 0-parameter top-level `def foo := …` is a value (not a thunk), a class constructor is `C.new`,
    -- and a builtin has its own lowering — none of those take the `()`, so they stay bare.
    if argsArray.isEmpty && keyWordsMap.isEmpty then
      match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok nm =>
          let isCtor := (json.getObjValAs? String "_class_ctor").toOption.isSome
                        || (← constructorClassOfName? nm).isSome
          let isUserFn := (← userNamesRef.get).contains nm
          let isBuiltin := (← builtinMappedName? nm).isSome
          if !isCtor && !isUserFn && !isBuiltin then allArgs := allArgs.push (← `(()))
      -- `expr()` where `expr` is itself a call (`make_counter()()`, `build(a,b)()`) applies the
      -- 0-arg closure `expr` returned — that closure is a `fun () ↦ …` thunk, so pass it `Unit`.
      | .ok "Call", _ => allArgs := allArgs.push (← `(()))
      | _, _ => pure ()

    -- A `key=` callback routes to the member's declared keyed shim variant (`Behaviour.keyedVariant`),
    -- whose `key` parameter the named arg then binds — no member name is hardcoded here.
    if (keyWordsMap.get? "key").isSome then
      let member := (funcJson.getObjValAs? String "library_member").toOption.getD
        ((funcJson.getObjValAs? String "id").toOption.getD "")
      if let some (rv, newArgs) ← bisectRangeKeyed? member argsArray allArgs then
        funcIdent := mkIdent rv
        allArgs := newArgs
      else if let some keyed := (Libraries.bareBehaviour? member).bind (·.keyedVariant) then
        funcIdent := mkIdent keyed
    let buildApplied : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolvedArgs => do
      -- Named args go in the SAME application as the positionals (`f a b (k := v)`), NOT applied to
      -- `(f a b)` — for a shim whose remaining params have defaults, `f a b` is already a complete
      -- value, so `(f a b) (lo := …)` fails with "Invalid argument name" (`bisect_right(s, x, lo=…)`).
      -- Named args go in the SAME application spine (`f a b (k := v)`), so a shim with defaulted
      -- params (`bisect_right(s, x, lo=…)`) binds them instead of applying to the already-complete
      -- `(f a b)`. Handled explicitly for 1–2 kwargs (the common `lo=`/`hi=`/`key=`/`reverse=`); 3+
      -- falls to the fold (rare, and only fails when every remaining param has a default).
      match keyWordsMap.toList with
      | [] => `($funcIdent $resolvedArgs*)
      | [(n, v)] =>
          let a ← getCode v `term
          `($funcIdent $resolvedArgs* ($(mkIdent n.toName) := $a))
      | [(n1, v1), (n2, v2)] =>
          let a ← getCode v1 `term
          let b ← getCode v2 `term
          `($funcIdent $resolvedArgs* ($(mkIdent n1.toName) := $a) ($(mkIdent n2.toName) := $b))
      | kwPairs =>
          let mut t ← `($funcIdent $resolvedArgs*)
          for (kwName, kwValueJson) in kwPairs do
            let kwValueCode ← getCode kwValueJson `term
            t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
          return t

    let applied ← if allArgJsons.toList.any basicJsonUsesIOEffect then
        buildIOPureApplicationFromArgs allArgJsons allArgs buildApplied
      else buildApplied allArgs
    -- A call to a heap-effectful user function returns a `HeapM` action; await it inline.
    if json.getObjValAs? Bool "_heap_call" == .ok true then return ← `((← $applied))
    return applied

def callSyntaxDoElem (json : Json) : PygenM (TSyntax `doElem) := do
    let .ok funcJson := json.getObjValAs? Json "func" | throwError
      s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
    let .ok argsJson := json.getObjValAs? Json "args" | throwError
      s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
    let argsArray ← match argsJson with
      | .arr arr => pure arr
      | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
    let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
      s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
    let .ok keyWordsMap := keyWordsJson.getObj? | throwError
      s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"

    let mut argsCodes ← argsArray.mapM (fun argJson => getCode argJson `term)

    let mut allArgs : Array (TSyntax `term) := #[]
    let mut allArgJsons : Array Json := #[]
    let mut funcIdent : TSyntax `term ← `("")

    match ← lowerSpecialCallDoElem? funcJson argsArray argsCodes keyWordsMap with
    | some lowered => return lowered
    | none => pure ()

    match ← jsonLibraryMappedName? funcJson with
    | some leanName =>
        funcIdent := (mkIdent leanName : TSyntax `term)
    | none =>
      if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
        let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
          s!"Attribute node missing 'value' field: {funcJson}"
        let .ok attr := funcJson.getObjValAs? String "attr" | throwError
          s!"Attribute node missing 'attr' field: {funcJson}"

        -- `ClassName.method(args)` (static/classmethod/unbound) as a statement.
        if let some cls := (json.getObjValAs? String "_static_class").toOption then
          let methodIdent : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
          let build : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolved => do
            let mut t ← `($methodIdent $resolved*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← getCode kwValueJson `term
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            pure t
          if argsArray.toList.any basicJsonUsesIOEffect then
            let t ← buildIOPureApplicationFromArgs argsArray argsCodes build
            return ← `(doElem| let _ ← $t:term)
          else
            let t ← build argsCodes
            if basicJsonUsesMonadicEffect json then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)

        -- A method call on a known class instance (`_receiver_class` stamped by py2lean) dispatches
        -- here, taking precedence over the builtin-method special-cases. A mutator on a bare
        -- variable reassigns it (`obj := C.m obj args`); a getter is run/bound like any call.
        if let some cls := (json.getObjValAs? String "_receiver_class").toOption then
          let methodIdent : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
          -- Under `--heap` the receiver is a `Ref C` and the method (mutator or getter) is a `HeapM`
          -- action: run it, discarding the result — mutation happens through the ref, so there is no
          -- receiver reassignment (and the receiver may be any ref expression, not just a variable).
          if ← getHeapMode then
            -- Inline any IO await in the receiver/args (`recv.m(int(input()))`) so it lifts into the
            -- enclosing do-block rather than being spliced as a raw `IO _` action into a value position.
            let valCode ← inlineEffectfulTerm valueJson
            let inlineArgs ← argsArray.mapM inlineEffectfulTerm
            let mut t ← `($methodIdent $valCode $inlineArgs*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← inlineEffectfulTerm kwValueJson
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            return ← `(doElem| let _ ← $t:term)
          if (json.getObjValAs? Bool "_is_value_mutator").toOption.getD false then
            -- Value+mutate method as a bare statement: reassign the receiver, drop the value.
            if jsonNodeType? valueJson == some "Name" then
              let targetIdent ← getCode valueJson `ident
              return ← `(doElem| $targetIdent:ident := ($methodIdent $targetIdent $argsCodes*).2)
            else
              throwError s!"Value-mutating method '{attr}' on a non-variable receiver is not \
                supported under value semantics."
          if (json.getObjValAs? Bool "_is_mutator").toOption.getD false then
            if jsonNodeType? valueJson == some "Name" then
              let targetIdent ← getCode valueJson `ident
              return ← `(doElem| $targetIdent:ident := $methodIdent $targetIdent $argsCodes*)
            else
              throwError s!"Mutating method '{attr}' on a non-variable receiver is not supported \
                under value semantics."
          let valCode ← getCode valueJson `term
          let allJsons := #[valueJson] ++ argsArray
          let allCodes := #[valCode] ++ argsCodes
          let build : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolved => do
            let mut t ← `($methodIdent $resolved*)
            for (kwName, kwValueJson) in keyWordsMap.toList do
              let kwValueCode ← getCode kwValueJson `term
              t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
            pure t
          if allJsons.toList.any basicJsonUsesIOEffect then
            let t ← buildIOPureApplicationFromArgs allJsons allCodes build
            return ← `(doElem| let _ ← $t:term)
          else
            let t ← build allCodes
            if basicJsonUsesMonadicEffect json then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)

        -- Any in-place mutating method as a bare statement (`stk.pop()`, `xs.append(v)`, `s.add(x)`,
        -- `xs.insert(i, v)`, …): rebuild the receiver and drop the return value. One path for all;
        -- a value+rest method's `restFn` is the rebuild. Also handles a subscript receiver
        -- (`g[i].append(v)`) via `mutatingMethodDoElem`. The arity guard avoids claiming a like-named
        -- user method.
        if let some (rebuildFn, arities) := statementMutatorRebuild? attr then
          if keyWordsMap.isEmpty && arities.contains argsArray.size then
            let argCodes ← argsArray.mapM (fun argJson => getCode argJson `term)
            -- A SortedList receiver: `add`/`remove`/`discard` share names with the set methods but must
            -- maintain sort order (they otherwise default to set semantics — dedup, no ordering). The
            -- runtime name comes from the Libraries layer; codegen only supplies the receiver gate.
            -- An `array_ok`-stamped receiver (runnable twin) uses the O(1) `Array` variant.
            let rebuildFn ←
              if let some fn ← sortedVarMethod? attr valueJson then
                pure fn
              -- A library-owned object receiver (`m.update(chunk)` where `m = hashlib.md5()`) owns
              -- the name too — `update` otherwise rebuilds through the dict/set `pyUpdate`.
              else if let some fn ← libObjVarMethod? attr valueJson then
                pure fn
              -- `d.pop(key)` on a dict removes the key (shares the name with 1-arg `list.pop(i)`);
              -- route it to the polymorphic dict rebuild when the receiver is known to be a dict.
              else if attr == "pop" && argsArray.size == 1 && (← jsonIsDictExpr valueJson) then
                pure ``PastaLean.pyDictKeyPopRest
              else if (json.getObjValAs? String "_seq" == .ok "array") && (← getNumericMode) == .approx then
                pure (match attr with
                  | "append" => ``PastaLean.pyArrayAppend
                  | "extend" => ``PastaLean.pyArrayExtend
                  | "reverse" => ``PastaLean.pyArrayReverse
                  | "insert" => ``PastaLean.pyArrayInsert
                  | "pop" => ``PastaLean.pyArrayPopRest
                  | "popleft" => ``PastaLean.pyArrayPopLeftRest
                  | _ => rebuildFn)
              else pure rebuildFn
            let fnIdent := mkIdent rebuildFn
            return ← mutatingMethodDoElem valueJson fun recv => `($fnIdent $recv $argCodes*)

        if attr == "get" then
          unless keyWordsMap.isEmpty do
            throwError "get() calls with keyword arguments are not supported yet."
          let valCode ← getCode valueJson `term
          let t ← match argsArray.size with
            | 1 =>
                let keyCode ← getCode argsArray[0]! `term
                let pyGetOptIdent := mkIdent ``pyGetOpt?
                `($pyGetOptIdent $valCode $keyCode)
            | 2 =>
                let keyCode ← getCode argsArray[0]! `term
                let defaultCode ← getCode argsArray[1]! `term
                let pyGetDIdent := mkIdent ``pyGetD
                `($pyGetDIdent $valCode $keyCode $defaultCode)
            | _ =>
                throwError "get() expects one or two positional arguments."
          return ← `(doElem| let _ := $t)

        -- A library-declared no-op method (e.g. functools' `f.cache_clear()`): lower to the
        -- library's no-op value. The set lives in the library, not here (see `libraryNoopMethod?`).
        if let some noopFn := Libraries.libraryNoopMethod? attr then
          let noopIdent := mkIdent noopFn
          return ← `(doElem| let _ := $noopIdent)

        if attr == "sort" then
          -- In-place `list.sort()`: lower to a reassignment of the (immutable-value) list.
          -- Supports Python's `key=` / `reverse=` keywords; rejects positional args.
          for (kwName, _) in keyWordsMap.toList do
            unless kwName == "key" || kwName == "reverse" do
              throwError s!"sort() keyword argument '{kwName}' is not supported yet."
          unless argsArray.isEmpty do
            throwError "sort() expects no positional arguments."
          -- Rebuild the receiver (a Name, `d[i]`, or `self.x`) via `mutatingMethodDoElem`, so
          -- `d[i].sort()` becomes `d := pySetItem d i (pySort d[i])`, not an invalid `d[i] := …`.
          match keyWordsMap.get? "key", keyWordsMap.get? "reverse" with
          | none, none =>
              let pySortIdent := mkIdent ``pySort
              return ← mutatingMethodDoElem valueJson (fun recv => `($pySortIdent $recv))
          | keyOpt, revOpt =>
              return ← mutatingMethodDoElem valueJson (fun recv => sortWithKeyTerm keyOpt revOpt recv)

        let valCode ← getCode valueJson `term
        allArgs := allArgs.push valCode
        allArgJsons := allArgJsons.push valueJson

        match (← sortedVarMethod? attr valueJson) <|> pythonMethodMap attr with
        | some funcName =>
            funcIdent := mkIdent funcName
        | none =>
            -- User method in statement position. A mutator on a bare variable receiver reassigns
            -- it (`obj := C.m obj args`, value semantics); a getter falls through to `C.m recv …`.
            let cls? ← match (json.getObjValAs? String "_receiver_class").toOption with
              | some c => pure (some c)
              | none => resolveReceiverClass? valueJson attr
            match cls? with
            | some cls =>
                let isMut ← match (json.getObjValAs? Bool "_is_mutator").toOption with
                  | some b => pure b
                  | none => methodIsMutator cls attr
                let isValMut ← match (json.getObjValAs? Bool "_is_value_mutator").toOption with
                  | some b => pure b
                  | none => methodIsValueMutator cls attr
                if isValMut then
                  -- Value+mutate method in statement position: reassign the receiver, drop the
                  -- returned value (`uf.union(a,b)` → `uf := (C.union uf a b).2`).
                  if jsonNodeType? valueJson == some "Name" then
                    let targetIdent ← getCode valueJson `ident
                    let methodIdent := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
                    return ← `(doElem| $targetIdent:ident := ($methodIdent $targetIdent $argsCodes*).2)
                  else
                    throwError s!"Value-mutating method '{attr}' on a non-variable receiver is not \
                      supported under value semantics."
                else if isMut then
                  if jsonNodeType? valueJson == some "Name" then
                    let targetIdent ← getCode valueJson `ident
                    let methodIdent := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
                    return ← `(doElem| $targetIdent:ident := $methodIdent $targetIdent $argsCodes*)
                  else
                    throwError s!"Mutating method '{attr}' on a non-variable receiver is not \
                      supported under value semantics."
                else
                  funcIdent := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
            | none =>
                throwError s!"Unsupported Python method '{attr}' encountered in Call node."
      else
        match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok "print" => do
            let supportedKeywords := ["sep", "end"]
            for (kwName, _) in keyWordsMap.toList do
              unless supportedKeywords.contains kwName do
                throwError s!"print() keyword argument '{kwName}' is not supported yet."
            -- Mode-dependent print: proof mode uses pyPrintProof, run mode uses pyPrintIO,
            -- fallback exact mode uses pyPrintNoop. IO-effect args are hoisted either way.
            let printFn ← if (← shouldUseProofMonad) then
                pure (mkIdent ``PastaLean.ProofMode.pyPrintProof)
              else if (← getNumericMode) == .exact then
                pure (mkIdent `pyPrintNoop)
              else
                pure (mkIdent `pyPrintIO)
            let t ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let printArgs ← buildPrintArgsList argsArray resolvedArgs
              match keyWordsMap.get? "sep", keyWordsMap.get? "end" with
              | none, none =>
                  `($printFn $printArgs)
              | _, _ =>
                  let sepCode ← match keyWordsMap.get? "sep" with
                    | some sepJson => getCode sepJson `term
                    | none => `(" ")
                  let endCode ← match keyWordsMap.get? "end" with
                    | some endJson => getCode endJson `term
                    | none => `("\n")
                  `($printFn $printArgs $sepCode $endCode)
            return ← `(doElem| let _ ← $t:term)
        | .ok "Name", .ok "input" => do
            unless keyWordsMap.isEmpty do
              throwError "input() keyword arguments are not supported yet."
            unless argsArray.size ≤ 1 do
              throwError "input() expects zero or one positional argument."
            -- Choose between proof mode (PyProofM) and run mode (IO) input
            let inputIdent ← if (← shouldUseProofMonad) then
                pure (mkIdent ``PastaLean.ProofMode.pyInputProof)
              else
                pure (mkIdent ``pyInputIO)
            let t ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              match resolvedArgs.size with
              | 0 => `($inputIdent "")
              | 1 =>
                  let arg0 := resolvedArgs[0]!
                  `($inputIdent $arg0)
              | _ => throwError "input() expects zero or one positional argument."
            return ← `(doElem| let _ ← $t:term)
        | .ok "Name", .ok "int" => do
            unless keyWordsMap.isEmpty do
              throwError "int() keyword arguments are not supported yet."
            unless argsArray.size == 1 || argsArray.size == 2 do
              throwError "int() expects one or two positional arguments."
            let t ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              if resolvedArgs.size == 2 then
                `($(mkIdent ``pyIntBase) $(resolvedArgs[0]!) $(resolvedArgs[1]!))
              else
                `($(mkIdent ``pyInt) $(resolvedArgs[0]!))
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "str" => do
            unless keyWordsMap.isEmpty do
              throwError "str() keyword arguments are not supported yet."
            let t ← match argsArray.size with
              | 0 => `("")
              | 1 =>
                  let pyStrIdent := mkIdent ``pyStr
                  buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                    let arg0 := resolvedArgs[0]!
                    `($pyStrIdent $arg0)
              | _ =>
                  throwError "str() expects zero or one positional argument."
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "list" => do
            unless keyWordsMap.isEmpty do
              throwError "list() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "list() currently expects exactly one positional argument."
            let pyListIdent := mkIdent ``pyList
            let t ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyListIdent $arg0)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "map" => do
            unless keyWordsMap.isEmpty do
              throwError "map() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "map() currently expects exactly two positional arguments."
            let pyMapIdent := mkIdent ``pyMap
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let iterCode := (← heapValueDeref? argsArray[1]!).getD argsCodes[1]!
            let adjustedCodes := #[funcCode, iterCode]
            let t ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyMapIdent $f $xs)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "filter" => do
            unless keyWordsMap.isEmpty do
              throwError "filter() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "filter() currently expects exactly two positional arguments."
            let pyFilterIdent := mkIdent ``pyFilter
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let iterCode := (← heapValueDeref? argsArray[1]!).getD argsCodes[1]!
            let adjustedCodes := #[funcCode, iterCode]
            let t ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyFilterIdent $f $xs)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok funcName =>
            match ← (do match (json.getObjValAs? String "_class_ctor").toOption with
                        | some c => pure (some c) | none => constructorClassOfName? funcName) with
            | some cls =>
              let ctorId : TSyntax `term := mkIdent (Name.mkStr (← suffixIfUserName cls).toName "new")
              -- Under `--heap`, a bare `C(args)` statement runs the `HeapM` alloc, discarding the ref.
              if ← getHeapMode then
                -- Inline any IO await in an argument (`C(int(input()))`) so it lifts into the enclosing
                -- do-block rather than being spliced as a raw `IO _` action into a value position.
                let inlineArgs ← argsArray.mapM inlineEffectfulTerm
                let mut t ← `($ctorId $inlineArgs*)
                for (kwName, kwValueJson) in keyWordsMap.toList do
                  let kwValueCode ← inlineEffectfulTerm kwValueJson
                  t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
                return ← `(doElem| let _ ← $t:term)
              funcIdent := ctorId
            | none =>
            match ← builtinMappedName? funcName with
            | some mappedName =>
                -- Deref container-ref args for a mapped builtin (consumed by value); see the term
                -- handler above. No-op off `--heap` / for non-container args.
                argsCodes ← derefBuiltinArgCodes argsArray argsCodes
                funcIdent := (mkIdent mappedName : TSyntax `term)
            | none =>
                funcIdent ← userCallIdent funcName
        | _, _ =>
            funcIdent ← getCode funcJson `term

    for argCode in argsCodes do
      allArgs := allArgs.push argCode
    for argJson in argsArray do
      allArgJsons := allArgJsons.push argJson

    -- A 0-arg call `f()` where `f` is a *local* callable (a loop/param/let-bound value holding one of
    -- the `fun () ↦ …` thunks our lambdas lower to) applies it to `Unit`, so emit `f ()`. A
    -- 0-parameter top-level `def foo := …` is a value (not a thunk), a class constructor is `C.new`,
    -- and a builtin has its own lowering — none of those take the `()`, so they stay bare.
    if argsArray.isEmpty && keyWordsMap.isEmpty then
      match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok nm =>
          let isCtor := (json.getObjValAs? String "_class_ctor").toOption.isSome
                        || (← constructorClassOfName? nm).isSome
          let isUserFn := (← userNamesRef.get).contains nm
          let isBuiltin := (← builtinMappedName? nm).isSome
          if !isCtor && !isUserFn && !isBuiltin then allArgs := allArgs.push (← `(()))
      -- `expr()` where `expr` is itself a call (`make_counter()()`, `build(a,b)()`) applies the
      -- 0-arg closure `expr` returned — that closure is a `fun () ↦ …` thunk, so pass it `Unit`.
      | .ok "Call", _ => allArgs := allArgs.push (← `(()))
      | _, _ => pure ()

    -- A `key=` callback routes to the member's declared keyed shim variant (`Behaviour.keyedVariant`),
    -- whose `key` parameter the named arg then binds — no member name is hardcoded here.
    if (keyWordsMap.get? "key").isSome then
      let member := (funcJson.getObjValAs? String "library_member").toOption.getD
        ((funcJson.getObjValAs? String "id").toOption.getD "")
      if let some (rv, newArgs) ← bisectRangeKeyed? member argsArray allArgs then
        funcIdent := mkIdent rv
        allArgs := newArgs
      else if let some keyed := (Libraries.bareBehaviour? member).bind (·.keyedVariant) then
        funcIdent := mkIdent keyed
    let buildApplied : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolvedArgs => do
      -- Named args go in the SAME application as the positionals (`f a b (k := v)`), NOT applied to
      -- `(f a b)` — for a shim whose remaining params have defaults, `f a b` is already a complete
      -- value, so `(f a b) (lo := …)` fails with "Invalid argument name" (`bisect_right(s, x, lo=…)`).
      -- Named args go in the SAME application spine (`f a b (k := v)`), so a shim with defaulted
      -- params (`bisect_right(s, x, lo=…)`) binds them instead of applying to the already-complete
      -- `(f a b)`. Handled explicitly for 1–2 kwargs (the common `lo=`/`hi=`/`key=`/`reverse=`); 3+
      -- falls to the fold (rare, and only fails when every remaining param has a default).
      match keyWordsMap.toList with
      | [] => `($funcIdent $resolvedArgs*)
      | [(n, v)] =>
          let a ← getCode v `term
          `($funcIdent $resolvedArgs* ($(mkIdent n.toName) := $a))
      | [(n1, v1), (n2, v2)] =>
          let a ← getCode v1 `term
          let b ← getCode v2 `term
          `($funcIdent $resolvedArgs* ($(mkIdent n1.toName) := $a) ($(mkIdent n2.toName) := $b))
      | kwPairs =>
          let mut t ← `($funcIdent $resolvedArgs*)
          for (kwName, kwValueJson) in kwPairs do
            let kwValueCode ← getCode kwValueJson `term
            t ← `($t ($(mkIdent kwName.toName):ident := $kwValueCode))
          return t

    if allArgJsons.toList.any basicJsonUsesIOEffect then
      let t ← buildIOPureApplicationFromArgs allArgJsons allArgs buildApplied
      `(doElem| let _ ← $t:term)
    else
      let t ← buildApplied allArgs
      -- A heap-effectful user function returns a `HeapM` action, so run it (`let _ ← …`).
      if basicJsonUsesMonadicEffect json || json.getObjValAs? Bool "_heap_call" == .ok true then
        `(doElem| let _ ← $t:term)
      else
        `(doElem| let _ := $t)

@[pygen "Call"]
def callSyntax : (kind : SyntaxNodeKind) → Json → PygenM (TSyntax kind)
  | `term, json => callSyntaxTerm json
  | `doElem, json => callSyntaxDoElem json
  | _, _ => throwError s!"Unsupported syntax category for Call node"

@[pygen "Attribute"]
def attributeSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    if let some t ← libraryNonFiniteTerm? json then return t
    match ← jsonLibraryMappedName? json with
    | some leanName =>
        pure (mkIdent leanName)
    | none =>
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Attribute node does not have a 'value' field or it is not a JSON value: {json}"
        let .ok attr := json.getObjValAs? String "attr" | throwError
          s!"Attribute node does not have an 'attr' field or it is not a string: {json}"
        let attrId := mkIdent attr.toName
        -- `int.__and__` / `int.__add__` etc. used as a bound operator function (e.g.
        -- `reduce(int.__and__, xs)`): emit the binary-operator lambda, not a bogus `int.__and__` ident.
        if valueJson.getObjValAs? String "node_type" == .ok "Name" then
          if #["int","float","bool","str","bytes"].contains
              ((valueJson.getObjValAs? String "id").toOption.getD "") then
            match attr with
            | "__and__" => return ← `(fun a b => PastaLean.pyBitAnd a b)
            | "__or__"  => return ← `(fun a b => PastaLean.pyBitOr a b)
            | "__xor__" => return ← `(fun a b => PastaLean.pyBitXor a b)
            | "__add__" => return ← `(fun a b => a +ₚ b)
            | "__sub__" => return ← `(fun a b => a -ₚ b)
            | "__mul__" => return ← `(fun a b => a *ₚ b)
            | _ => pure ()
        -- Under `--heap`, dereference a heap-object receiver before projecting the field: `self` in a
        -- method body (`self : Ref C`), or any local/param known to hold a heap object (`p.x`).
        if ← getHeapMode then
          if valueJson.getObjValAs? String "node_type" == .ok "Name" then
            let vid := (valueJson.getObjValAs? String "id").toOption.getD ""
            let selfRef ← getHeapSelfRef
            let cls? ← heapVarClassOf? vid.toName
            let isHeapRecv := if vid == "self" then selfRef else cls?.isSome
            if isHeapRecv then
              return ← `((← $(mkIdent vid.toName) ~> $attrId))
        let valueCode ← getCode valueJson `term
        -- `_unwrap_opt` (TypeInfer): the receiver is `Option _`, so unwrap before projecting the field
        if json.getObjValAs? Bool "_unwrap_opt" == .ok true then
          -- Under `--heap` the unwrapped value is a `Ref Node` (an `Option (Ref Node)` list element,
          -- `node.children[i].cnt`), so deref-and-project (`~>`). Match on the `Option` rather than
          -- `getD default`: a `None` there would deref a bogus DEFAULT ref (address 0 — another cell of
          -- a different kind) when a short-circuited `and` guard (`child and child.cnt`) still evaluates
          -- it; `none => pure default` returns the field default without touching the heap.
          if ← getHeapMode then
            `((← (($valueCode).elim (pure default) (fun __r => __r ~> $attrId))))
          else
            `((($valueCode).getD default).$attrId)
        else
          `($valueCode.$attrId)
  | `ident, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName =>
        pure (mkIdent leanName)
    | none =>
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Attribute node does not have a 'value' field or it is not a JSON value: {json}"
        let .ok attr := json.getObjValAs? String "attr" | throwError
          s!"Attribute node does not have an 'attr' field or it is not a string: {json}"
        let id ← getCode valueJson `ident
        return mkIdent <| id.getId ++ attr.toName
  | _, _ => throwError s!"Unsupported syntax category for Attribute node"

end PastaLean
