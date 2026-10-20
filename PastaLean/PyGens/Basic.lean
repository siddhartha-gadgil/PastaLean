import PastaLean.Imports
import Libraries.Registry
import PastaLean.Codegen
import PastaLean.PyAPI
import PastaLean.PyGens.Attributes
import PastaLean.PyAPI.BuiltinRegistry
open Lean Meta Elab Term Qq Std

namespace PastaLean

def intToStx (n : Int) : MetaM <| TSyntax `term := do
  let intIdent := mkIdent ``Int
  if n < 0 then
    -- Ascribe negatives to `Int` too — a bare `- 1` otherwise defaults to `Neg ℚ`, which e.g. types
    -- a `x[-1]` index as `ℚ` and fails `PyGetItem (List _) Int _`.
    let nStx := Syntax.mkNumLit (toString (-n))
    `((- $nStx : $intIdent))
  else
    let nStx := Syntax.mkNumLit (toString (n))
    `(($nStx : $intIdent))

/-- If a subscript slice is a dict tuple-key access (`d[i, j]` meaning `d[(i, j)]`, marked
`_dict_tuple_key` by TypeInfer when the container is a dict), build the `(i, j, …)` tuple key term;
otherwise `none` (a numpy-style multi-index or a plain index). -/
def dictTupleKeyTerm? (sliceJson : Json) : PygenM (Option (TSyntax `term)) := do
  if sliceJson.getObjValAs? Bool "_dict_tuple_key" == .ok true then
    match sliceJson.getObjValAs? (Array Json) "elts" with
    | .ok elts =>
        if elts.isEmpty then return none
        let keyTerms ← elts.mapM (fun e => getCode e `term)
        let mut key := keyTerms[keyTerms.size - 1]!
        for t in keyTerms.toList.dropLast.reverse do
          key ← `(($t, $key))
        return some key
    | _ => return none
  else return none

def numToStx (mantissa : Int) (exponent : Nat) : MetaM <| TSyntax `term := do
  match exponent with
    | 0 => intToStx mantissa
    | k + 1 =>
      if mantissa % 10 = 0 then
        numToStx (mantissa / 10) k
      else
        -- A bare signed numeral ascribed to `Rat` (not via `intToStx`, whose `: Int` ascription
        -- would nest awkwardly as `((-15 : Int) : Rat)`).
        let mantAbs := Syntax.mkNumLit (toString mantissa.natAbs)
        let mantissaStx ← if mantissa < 0 then `(- $mantAbs:num) else pure (⟨mantAbs⟩ : TSyntax `term)
        let exponentStx := Syntax.mkNumLit (toString <| (10).pow exponent)
        let ratIdent := mkIdent ``Rat
        `(($mantissaStx : $ratIdent) / $exponentStx)

/-- Render `magnitude × 10⁻ᵉˣᵖᵒⁿᵉⁿᵗ` as a plain decimal string (e.g. `magnitude = 25`,
`exponent = 2` ↦ `"0.25"`). Mirrors how `Float.ofScientific magnitude true exponent` is valued,
so the resulting decimal literal is exactly equal to the old desugared form. -/
def floatDecimalString (magnitude exponent : Nat) : String :=
  let digits := toString magnitude
  if exponent == 0 then
    digits ++ ".0"
  else
    -- Left-pad so there is at least one digit before the decimal point.
    let padded :=
      if digits.length ≤ exponent then
        String.ofList (List.replicate (exponent + 1 - digits.length) '0') ++ digits
      else
        digits
    let chars := padded.toList
    let cut := chars.length - exponent
    String.ofList (chars.take cut) ++ "." ++ String.ofList (chars.drop cut)

/-- Preserve Python float literals as Lean `Float`s, even with a trailing `.0`.

Keep scientific notation as `Float.ofScientific magnitude true exponent`; otherwise emit a
decimal literal ascribed to `Float` (e.g. `(0.25 : Float)`). The ascription is needed because a
bare decimal literal would otherwise resolve to `Rat`. -/
def floatNumToStx (mantissa : Int) (exponent : Nat) (scientific : Bool) :
    MetaM <| TSyntax `term := do
  let magnitude := Int.natAbs mantissa
  -- Default `exact` mode lowers a Python float to an exact `ℚ` (provable + computable); `approx`
  -- mode keeps `Float` (today's behavior).
  let mode ← getNumericMode
  -- Inside a real-valued function (exact mode), a float literal is `ℝ` so it composes with the
  -- transcendental results in that function; otherwise exact mode uses `ℚ`.
  let exactTy : Name := if (← getRealContext) then ``Real else ``Rat
  let base ←
    if scientific then
      let magnitudeStx := Syntax.mkNumLit (toString magnitude)
      let exponentStx := Syntax.mkNumLit (toString exponent)
      match mode with
      | .approx =>
        let floatScientificIdent := mkIdent ``Float.ofScientific
        `($floatScientificIdent $magnitudeStx true $exponentStx)
      | .exact =>
        let ofSciIdent := mkIdent ``OfScientific.ofScientific
        let exactIdent := mkIdent exactTy
        `(($ofSciIdent $magnitudeStx true $exponentStx : $exactIdent))
    else
      let sciLit := Syntax.mkScientificLit (floatDecimalString magnitude exponent)
      let tyIdent := match mode with | .approx => mkIdent ``Float | .exact => mkIdent exactTy
      `(($sciLit : $tyIdent))
  if mantissa < 0 then
    `(- $base:term)
  else
    pure base

/-- An integer literal emitted at the numeric-mode float type (`(0 : ℚ)`/`ℝ`/`Float`). Used for an
int literal that TypeInfer stamped `_ty = float` — a float-container element like the `0` in
`[0]*n` where the list later holds floats, so the list is `List ℚ` not `List Int`. -/
def intAsFloatStx (n : Int) : MetaM <| TSyntax `term := do
  let mode ← getNumericMode
  let real ← getRealContext
  let ty : Name := match mode with
    | .approx => ``Float
    | .exact => if real then ``Real else ``Rat
  let nAbs := Syntax.mkNumLit (toString n.natAbs)
  let lit : TSyntax `term ← if n < 0 then `(- $nAbs:num) else pure ⟨nAbs⟩
  `(($lit : $(mkIdent ty)))

/-- Whether a node's inference stamp (`_ty`) is the scalar `float` annotation. -/
def stampedFloat (json : Json) : Bool :=
  (json.getObjVal? "_ty").toOption.any (·.getObjValAs? String "id" == .ok "float")

@[pygen "Constant"]
def constantSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok value := json.getObjValAs? Json "value" | throwError
      s!"Constant node does not have a 'value' field or it is not a JSON value: {json}"
    let isPythonFloat :=
      json.getObjValAs? String "python_literal_kind" == .ok "float"
    let isScientific :=
      json.getObjValAs? String "float_notation" == .ok "scientific"
    match value with
    | .num (JsonNumber.mk mantissa exponent) =>
        if isPythonFloat then
          floatNumToStx mantissa exponent isScientific
        else if exponent == 0 && stampedFloat json then
          intAsFloatStx mantissa
        else
          numToStx mantissa exponent
    | .str s => return Syntax.mkStrLit s
    | .bool b => do
        let trueStx := mkIdent ``true
        let falseStx := mkIdent ``false
        if b then `($trueStx) else `($falseStx)
    | .null =>
        -- In a boxed (`PyAny`) function, `None` is the dynamic `PyAny.none`, not `Option.none` — so a
        -- `return None` branch unifies with the other `PyAny` returns (`ite cond none <pyany>` would
        -- otherwise be `Option ?m` vs `PyAny`). Node/`Optional[C]` functions aren't boxed, so unaffected.
        if ← getBoxReturnContext then `($(mkIdent ``PastaLean.PyAny.none))
        else `($(mkIdent ``none))
    | _ => throwError s!"Unsupported constant value: {value}"
  | _, _ => throwError s!"Unsupported syntax category for Constant node"

def jsonLibraryMappedName? (json : Json) : PygenM (Option Lean.Name) := do
  match json.getObjValAs? String "library_module", json.getObjValAs? String "library_member" with
  | .ok moduleName, .ok memberName =>
      -- Proof mode (`PyProofM`) needs the pure, state-threaded twin of an IO-effectful library member
      -- (`random.*`): the `IO` version cannot be `←`-bound in the pure proof monad. Consulted first so
      -- it wins over the regular map; a miss (every non-IO member) falls through unchanged.
      if (← getNumericMode) == .exact then
        if let some proofName := Libraries.pythonLibraryMapProof? moduleName memberName then
          return some proofName
      -- Exact mode prefers provable `ℝ`/`noncomputable` mappings for transcendentals; otherwise
      -- use the regular mapping (`--mode run` always does). Example: `math.pow` → rational in the
      -- exact map, else the regular (often `Float`) mapping.
      let realName? ← if (← getNumericMode) == .exact
        then pure (Libraries.pythonLibraryMapReal? moduleName memberName
                    <|> Libraries.pythonLibraryMapExact? moduleName memberName)
        else pure none
      match realName? <|> Libraries.pythonLibraryMap? moduleName memberName with
      | some leanName => pure (some leanName)
      | none => throwError s!"Unsupported imported library member '{moduleName}.{memberName}'."
  | _, _ => pure none

/-- The in-place mutation spec (from `Libraries`) for a call's callee, if it is a library member that
mutates its first argument (e.g. `heapq.heappush`). Lets codegen lower mutators without naming any
specific library. -/
def libraryMutatorOf? (funcJson : Json) : Option Libraries.LibraryMutator :=
  match funcJson.getObjValAs? String "library_module", funcJson.getObjValAs? String "library_member" with
  | .ok m, .ok mem => Libraries.libraryMutator? m mem
  | _, _ => none

/-- Resolve a Python builtin name to its Lean runtime name, honouring the numeric mode: in exact
mode the `pythonBuiltinMapExact?` overrides (e.g. `float` → `pyRat`) win over the regular table. -/
def builtinMappedName? (name : String) : PygenM (Option Lean.Name) := do
  -- User conversions registered via `@[py_convert "name"]` are a fallback: the built-in tables win,
  -- so a user entry never silently shadows `int`/`str`/`list`.
  let registered ← pyConvertRegistered? name
  if (← getNumericMode) == .exact then
    return pythonBuiltinMapExact? name <|> pythonBuiltinMap? name <|> registered
  else
    return pythonBuiltinMap? name <|> registered

/-- The literal of a non-finite `float('inf')` / `float('-inf')` / `float('nan')` call. -/
def nonFiniteFloatLiteral? (funcJson : Json) (argsArray : Array Json) : Option String := do
  guard (funcJson.getObjValAs? String "node_type" == .ok "Name")
  guard (funcJson.getObjValAs? String "id" == .ok "float")
  let argJson ← argsArray[0]?
  guard (argJson.getObjValAs? String "node_type" == .ok "Constant")
  let .ok (Json.str raw) := argJson.getObjValAs? Json "value" | none
  let normalized := raw.toLower.trimAscii
  let body := if normalized.startsWith "-" || normalized.startsWith "+"
    then normalized.drop 1 else normalized
  guard (body == "inf" || body == "infinity" || body == "nan")
  return raw

/-- Lower a literal `float('inf')`/`float('nan')` to `pyNonFinite`, which takes its numeric type
from the slot it lands in: `ℤ` inside an integer DP, `Float` in a run-twin float slot, `ℚ` (the
default instance) otherwise. Plain `pyRat`/`pyFloat` cannot serve all three — `pyRat` degrades
these to `0`, and a `Float` infinity does not fit an `ℤ` result. -/
def nonFiniteFloatTerm? (funcJson : Json) (argsArray : Array Json) :
    PygenM (Option (TSyntax `term)) := do
  let some raw := nonFiniteFloatLiteral? funcJson argsArray | return none
  let nonFiniteIdent := mkIdent ``PastaLean.pyNonFinite
  return some (← `($nonFiniteIdent $(Syntax.mkStrLit raw)))

/-- `math.inf`/`math.nan`/`math.infinity` as a VALUE lowers to the polymorphic `pyNonFinite` (the same
sentinel `float('inf')` uses), so it takes the numeric type of its context (`ℚ`/`ℤ`/`Float`) instead of
a concrete `Float` that clashes with an `Int`/`ℚ` DP accumulator. -/
def libraryNonFiniteTerm? (json : Json) : PygenM (Option (TSyntax `term)) := do
  match json.getObjValAs? String "library_module", json.getObjValAs? String "library_member" with
  | .ok "math", .ok mem =>
      if mem == "inf" || mem == "infinity" then
        return some (← `($(mkIdent ``PastaLean.pyNonFinite) "inf"))
      else if mem == "nan" then
        return some (← `($(mkIdent ``PastaLean.pyNonFinite) "nan"))
      else return none
  | _, _ => return none

@[pygen "Name"]
def nameSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    if let some t ← libraryNonFiniteTerm? json then return t
    match ← jsonLibraryMappedName? json with
    | some leanName => pure (mkIdent leanName)
    | none =>
        let .ok id0 := json.getObjValAs? String "id" | throwError
          s!"Name node does not have an 'id' field or it is not a string: {json}"
        -- Resolve SSA renames first (a type-changing rebind `s = list(s)` renamed later `s` refs).
        let id := (← applyRename id0.toName).toString
        -- A closure-promoted variable CELL (`--heap`): raw ref when passed to its capturing sibling
        -- (`_heap_cell_arg`), else its value/object-ref via one deref in every ordinary position.
        if (← getHeapMode) && (← isHeapCellVar id.toName) then
          if (json.getObjValAs? Bool "_heap_cell_arg").toOption.getD false then
            return mkIdent id.toName
          else
            return (← `((← PastaLean.readRefM $(mkIdent id.toName))))
        -- In a run-twin, a reference to a user function/class is suffixed (`bar` → `bar'rn`,
        -- `CNN` → `CNN'rn`); locals and library names are left as-is.
        let suffixed ← suffixIfUserName id
        -- User definitions live in a dedicated `namespace PastaLean.User.<path>` (opened by the module
        -- wrapper), so a bare reference resolves to the user's own `compare`/`gcd`/`dist` by namespace
        -- precedence, not a Mathlib/Lean global of the same name. The old `_root_`-qualification is gone:
        -- it misfired for globals that live under a namespace (`Ord.compare`), since `_root_.compare`
        -- then names nothing.
        return mkIdent suffixed.toName
  | `ident, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName => pure (mkIdent leanName)
    | none =>
        let .ok id0 := json.getObjValAs? String "id" | throwError
          s!"Name node does not have an 'id' field or it is not a string: {json}"
        let id := (← applyRename id0.toName).toString
        -- In a run-twin, a reference to a user function/class is suffixed (`bar` → `bar'rn`,
        -- `CNN` → `CNN'rn`); locals and library names are left as-is.
        return mkIdent (← suffixIfUserName id).toName
  | _, _ => throwError s!"Unsupported syntax category for Name node"

/-- Under `--heap` a fresh container literal is a heap cell: wrap it in `(← alloc …)` so it yields a
`Ref …`. In value mode the literal is returned unchanged. -/
def allocIfHeap (t : TSyntax `term) : PygenM (TSyntax `term) := do
  if ← getHeapMode then `((← PastaLean.allocM $t)) else pure t

/-- The `None` literal: a `Constant` carrying JSON null. `...` is also a null-valued `Constant`,
so it is excluded by its literal kind. -/
private def isNoneConst (j : Json) : Bool :=
  j.getObjValAs? String "node_type" == .ok "Constant"
    && (match j.getObjVal? "value" with | .ok .null => true | _ => false)
    && j.getObjValAs? String "python_literal_kind" != .ok "ellipsis"

/-- The literal kind of a non-`None` `Constant`, read off the shape of its JSON value. -/
private def constKind (j : Json) : Option String :=
  if j.getObjValAs? String "node_type" != .ok "Constant" then none
  else match j.getObjVal? "value" with
    | .ok (.bool _) => some "bool"
    | .ok (.num n)  => some (if n.exponent == 0 then "int" else "float")
    | .ok (.str _)  => some "str"
    | _ => none

/-- A literal other than `None`. Being a literal is what makes wrapping it in `Option.some` safe:
unlike a name or a call, it cannot already have an `Option` type. -/
private def isPlainConst (j : Json) : Bool := (constKind j).isSome

/-- `[None, True]` needs `[none, some true]`: Lean inserts the `Option` coercion only when the
element type is already concrete, which it is not while the literal is still elaborating against a
metavariable. Wrapping the literals ourselves settles it at codegen time.

Only when every other element is a literal of one kind, so the element type really is `Option` of
that kind. A mixed `[None, "x", 3.5]` is heterogeneous and belongs in `PyAny`, and a non-literal
element may already be `Option`-typed, where wrapping would double it. -/
private def optionWrapped (elts : Array Json) : Bool :=
  elts.any isNoneConst
    && (match (elts.filterMap constKind).toList with
        | [] => false
        | k :: rest => rest.all (· == k))
    && elts.all (fun j => isNoneConst j || isPlainConst j)

@[pygen "List"]
def listSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
      s!"List node does not have an 'elts' field or it is not a JSON value: {json}"
    let elts ← match eltsJson with
      | .arr arr => pure arr
      | _ => throwError s!"List node 'elts' field is not an array: {eltsJson}"
    let wrap := optionWrapped elts
    let eltCodes ← elts.mapM fun eltJson => do
      let code ← getCode eltJson `term
      if wrap && isPlainConst eltJson then
        `($(mkIdent ``Option.some) $code)
      else
        pure code
    -- An `array_ok`-marked literal in the runnable twin is an `Array` (`#[…]`); else a `List` (`[…]`).
    let arrayBacked := (json.getObjValAs? String "_seq" == .ok "array")
      && (← getNumericMode) == .approx
    if arrayBacked then `(#[$eltCodes,*])
    else allocIfHeap (← `([$eltCodes,*]))
  | _, _ => throwError s!"Unsupported syntax category for List node"

/-- `{a, b, c}` set literals lower to a deduplicated list via `pySetFromList`; sets are
modeled as lists so list-backed protocols (`in`, `len`, iteration) apply. -/
@[pygen "Set"]
def setSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
      s!"Set node does not have an 'elts' field or it is not a JSON value: {json}"
    let eltCodes ← match eltsJson with
      | .arr arr => arr.mapM (fun eltJson => getCode eltJson `term)
      | _ => throwError s!"Set node 'elts' field is not an array: {eltsJson}"
    let fromListIdent := mkIdent ``PastaLean.pySetFromList
    let setTerm ← `($fromListIdent [$eltCodes,*])
    allocIfHeap setTerm
  | _, _ => throwError s!"Unsupported syntax category for Set node"

@[pygen "Tuple"]
def tupleSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
      s!"Tuple node does not have an 'elts' field or it is not a JSON value: {json}"
    let eltCodes ← match eltsJson with
      | .arr arr => arr.mapM (fun eltJson => getCode eltJson `term)
      | _ => throwError s!"Tuple node 'elts' field is not an array: {eltsJson}"
    let rec buildTuple (elts : List (TSyntax `term)) : PygenM (TSyntax `term) := do
      match elts with
      | [] => `(())
      | [single] => pure single
      | first :: rest => do
          let restTuple ← buildTuple rest
          `(($first, $restTuple))
    buildTuple eltCodes.toList
  | _, _ => throwError s!"Unsupported syntax category for Tuple node"

/-- `Starred` (`*iterable`) in a call lowers, in term position, to the iterable itself.
The only place that interprets the spread is the `print(...)` lowering, which detects a
`Starred` argument by node type and maps over this value. -/
@[pygen "Starred"]
def starredSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"Starred node does not have a 'value' field or it is not a JSON value: {json}"
    getCode valueJson `term
  | _, _ => throwError s!"Unsupported syntax category for Starred node"

@[pygen "Dict"]
def dictSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok entries := json.getObjValAs? (Array Json) "entries" | throwError
      s!"Dict node does not have an 'entries' field or it is not a JSON array: {json}"
    let ofListIdent := mkIdent ``Std.HashMap.ofList
    -- `{**d1, 'k': v, **d2}`: each entry contributes a `List (κ × ν)` chunk — a singleton for a
    -- `key: value` pair, the merged dict's `.toList` for a `**spread`. Concatenating in source
    -- order and feeding `ofList` gives Python's "later wins" (ofList keeps the last dup key).
    if entries.any (·.getObjVal? "spread" |>.toOption.isSome) then
      let chunks ← entries.mapM fun entryJson => do
        match entryJson.getObjVal? "spread" with
        | .ok spreadJson => `($(mkIdent ``Std.HashMap.toList) $(← getCode spreadJson `term))
        | _ =>
          let .ok keyJson := entryJson.getObjValAs? Json "key" | throwError
            s!"Dict entry is missing a 'key' field: {entryJson}"
          let .ok valueJson := entryJson.getObjValAs? Json "value" | throwError
            s!"Dict entry is missing a 'value' field: {entryJson}"
          `([($(← getCode keyJson `term), $(← getCode valueJson `term))])
      let mut joined := chunks[0]!
      for chunk in chunks.toList.drop 1 do
        joined ← `($joined ++ $chunk)
      let dictTerm ← `($ofListIdent $joined)
      allocIfHeap dictTerm
    else
      let entryCodes ← entries.mapM fun entryJson => do
        let .ok keyJson := entryJson.getObjValAs? Json "key" | throwError
          s!"Dict entry is missing a 'key' field: {entryJson}"
        let .ok valueJson := entryJson.getObjValAs? Json "value" | throwError
          s!"Dict entry is missing a 'value' field: {entryJson}"
        `(($(← getCode keyJson `term), $(← getCode valueJson `term)))
      let dictTerm ← `($ofListIdent [$entryCodes,*])
      allocIfHeap dictTerm
  | _, _ => throwError s!"Unsupported syntax category for Dict node"


def js₀ := json% {
  "node_type": "Constant",
  "value": 1
}

/- map to noop-/
@[pygen "Delete"]
def deleteSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok targetsJson := json.getObjValAs? Json "targets" | throwError
      s!"Delete node does not have a 'targets' field or it is not a JSON value: {json}"
    let _ ← match targetsJson with
      | .arr arr => arr.mapM (fun targetJson => getCode targetJson `term)
      | _ => throwError s!"Delete node 'targets' field is not an array: {targetsJson}"
    -- We currently do not support deletion semantics, so we simply return `()`.
    `(())
  | `doElem, json => do
    let .ok targetsJson := json.getObjValAs? Json "targets" | throwError
      s!"Delete node does not have a 'targets' field or it is not a JSON value: {json}"
    let .ok targets := targetsJson.getArr? | throwError
      s!"Delete node 'targets' field is not an array: {targetsJson}"
    -- `del container[i]` removes an element: rebuild and reassign the (mut) container variable.
    -- `del x` on a plain name is a binding removal with no runtime effect here. Other targets
    -- (slices, attributes) are not supported and stay no-ops.
    let mut elems : Array (TSyntax `doElem) := #[]
    for target in targets do
      if target.getObjValAs? String "node_type" == .ok "Subscript" then
        let .ok containerJson := target.getObjValAs? Json "value" | throwError
          s!"del target Subscript is missing a 'value' field: {target}"
        let .ok sliceJson := target.getObjValAs? Json "slice" | throwError
          s!"del target Subscript is missing a 'slice' field: {target}"
        if containerJson.getObjValAs? String "node_type" == .ok "Name"
            && sliceJson.getObjValAs? String "node_type" != .ok "Slice" then
          let containerIdent ← getCode containerJson `ident
          let indexCode ← getCode sliceJson `term
          let delIdent := mkIdent ``PastaLean.pyDelItem
          elems := elems.push (← `(doElem| $containerIdent:ident := $delIdent $containerIdent $indexCode))
        else
          elems := elems.push (← `(doElem| let _ := ()))
      else
        elems := elems.push (← `(doElem| let _ := ()))
    pure ⟨mkNullNode (elems.map TSyntax.raw)⟩
  | `command, json => do
    let .ok targetsJson := json.getObjValAs? Json "targets" | throwError
      s!"Delete node does not have a 'targets' field or it is not a JSON value: {json}"
    let _ ← match targetsJson with
      | .arr arr => arr.mapM (fun targetJson => getCode targetJson `term)
      | _ => throwError s!"Delete node 'targets' field is not an array: {targetsJson}"
    -- We currently do not support deletion semantics, so we simply return `()`.
    `(command| def del := ())
  | _, _ => throwError s!"Unsupported syntax category for Delete node"
/-- Detect the JSON encoding of Python's `None`. -/
def isNoneConstantJson (json : Json) : Bool :=
  match json.getObjValAs? String "node_type", json.getObjValAs? Json "value" with
  | .ok "Constant", .ok .null => true
  | _, _ => false

/-- Apply a Python binary operator to already-lowered operand terms. Shared by `binOpSyntax`
and `inlineEffectfulTerm` so IO-bearing operands can be hoisted without duplicating the op table. -/
def binOpApplyTerm (op : String) (leftCode rightCode : TSyntax `term) :
    PygenM (TSyntax `term) := do
  match op with
  | "add" => `($leftCode +ₚ $rightCode)
  | "sub" => `($leftCode -ₚ $rightCode)
  | "mul" => `($leftCode *ₚ $rightCode)
  | "div" =>
      match ← getNumericMode with
      | .approx => `(PastaLean.pyFloat $leftCode /ₚ $rightCode)
      | .exact => `($leftCode /ₚ $rightCode)
  | "floordiv" =>
      let floorDivIdent := mkIdent ``PastaLean.pyFloorDiv
      `($floorDivIdent $leftCode $rightCode)
  | "pow" => `($leftCode ^ₚ $rightCode)
  | "mod" => `($leftCode %ₚ $rightCode)
  | "bitand" => `($(mkIdent ``PastaLean.pyBitAnd) $leftCode $rightCode)
  | "bitor" => `($(mkIdent ``PastaLean.pyBitOr) $leftCode $rightCode)
  | "bitxor" => `($(mkIdent ``PastaLean.pyBitXor) $leftCode $rightCode)
  | "lshift" => `($(mkIdent ``PastaLean.pyShiftLeft) $leftCode $rightCode)
  | "rshift" => `($(mkIdent ``PastaLean.pyShiftRight) $leftCode $rightCode)
  | _ => throwError s!"Unsupported binary operator: {op}"

/-- Apply a Python unary operator to an already-lowered operand term. -/
def unaryOpApplyTerm (op : String) (operandCode : TSyntax `term) :
    PygenM (TSyntax `term) := do
  match op with
  | "not" => `(! $operandCode)
  | "neg" => `(- $operandCode)
  | "pos" => `($operandCode)
  -- `~x` is Python's bitwise complement: `-x - 1` on `Int`.
  | "invert" => `(- $operandCode - 1)
  | _ => throwError s!"Unsupported unary operator: {op}"

/-- Whether a condition's IR already lowers to a `Bool` (a comparison, boolean operator,
`not`, or a boolean literal). Such tests need no truthiness conversion; everything else (a
bare `int`/`list`/`str`/`Option` used as `if x:` / `while x:`) is wrapped in `pyTruthy`. -/
def conditionIsBoolean (json : Json) : Bool :=
  match json.getObjValAs? String "node_type" with
  | .ok "Compare" => true
  | .ok "BoolOp" => true
  | .ok "UnaryOp" => json.getObjValAs? String "op" == .ok "not"
  | .ok "Constant" =>
      match json.getObjValAs? Json "value" with
      | .ok (.bool _) => true
      | _ => false
  | _ => false

/-- `all`/`any` over a single-generator, `Name`-target comprehension, which `quantifiedAllAnyProp?`
lowers to a `∀`/`∃` in a Prop context. Lives here so the truthiness-coercion sites can consult the
same predicate — coercing an already-`Prop` operand with `pyTruthy` is a type error. -/
def isQuantifiedAllAnyJson (json : Json) : Bool :=
  json.getObjValAs? String "node_type" == .ok "Call" &&
    (match (json.getObjVal? "func").toOption with
     | some func =>
         func.getObjValAs? String "node_type" == .ok "Name" &&
           (match func.getObjValAs? String "id" with
            | .ok name => name == "all" || name == "any"
            | _ => false)
     | none => false) &&
    (match json.getObjValAs? (Array Json) "args" with
     | .ok args =>
         args.size == 1 &&
           (match args[0]!.getObjValAs? String "node_type" with
            | .ok argType =>
                (argType == "GeneratorExp" || argType == "ListComp") &&
                  (match args[0]!.getObjValAs? (Array Json) "generators" with
                   | .ok gens =>
                       gens.size == 1 &&
                         (match (gens[0]!.getObjVal? "target").toOption with
                          | some target => target.getObjValAs? String "node_type" == .ok "Name"
                          | none => false)
                   | _ => false)
            | _ => false)
     | _ => false)

/-- Lower a condition expression, applying Python truthiness (`pyTruthy`) unless it already
produces a `Bool`. Used by `if`/`while`/`if`-expression lowering. -/
def truthyConditionTerm (json : Json) (code : TSyntax `term) : PygenM (TSyntax `term) := do
  -- A quantified `all`/`any` already lowered to a decidable `∀`/`∃` Prop — usable directly as an `if`
  -- condition; wrapping it in `pyTruthy` (which wants a `Bool`) is a type error.
  if conditionIsBoolean json || isQuantifiedAllAnyJson json then pure code
  else `($(mkIdent ``PastaLean.pyTruthy) $code)

/-- A JSON node that lowers to a Lean `String` value: a string literal or an f-string. Used to
route `x in s` to substring containment when the left operand is statically a string. -/
def isStringyJson (json : Json) : Bool :=
  match json.getObjValAs? String "node_type" with
  | .ok "JoinedStr" => true
  | .ok "Constant" =>
      match json.getObjValAs? Json "value" with
      | .ok (.str _) => true
      | _ => false
  | _ => false

/-- Whether the container operand of `in`/`not in` is statically a set. A `str` literal on the LEFT
routes to substring containment, but only when the container is NOT a set: `'0' in set(s)` is set
membership (over `str` elements), not a substring test. -/
private def rightIsSetExpr (rightJson : Option Json) : PygenM Bool :=
  (rightJson.mapM jsonIsSetExpr).map (·.getD false)

/-- If `j` is a bare reference to an `Option T` slot local (`ans`, from `ans = None; …; ans = t`),
unwrap it (`ans.get!`) so an ordered `<`/`>`/`≤`/`≥` against a bare `T` type-checks — Lean's
`instLTOption` gives no `Decidable`, and the comparison is reached only when the guard proved the
value non-`None`. Non-`Option` operands are returned unchanged. -/
private def unwrapOptionOperand (j : Json) (code : TSyntax `term) : PygenM (TSyntax `term) := do
  if j.getObjValAs? String "node_type" == .ok "Name" then
    if let .ok id := j.getObjValAs? String "id" then
      if ← isOptionVar id.toName then
        return ← `(($code).get!)
  return code

/-- Apply a Python comparison operator to already-lowered terms. `leftJson` only affects
membership lowering: a string literal on the left of `in`/`not in` means substring containment
(`pyStrContainsSubstr`) — unless the container is a set — otherwise membership uses `pyContains`,
whose `outParam` element type pins the element from the container. -/
def compareApplyTerm (op : String) (leftJson : Json) (leftCode rightCode : TSyntax `term)
    (rightJson : Option Json := none) (classCmp : Bool := false) : PygenM (TSyntax `term) := do
  -- Set comparisons are order-independent (subset / set-equality), unlike the list-backed `==`/`≤`
  -- the same `List` value would otherwise select. Fires when either operand is statically a set.
  if (← jsonIsSetExpr leftJson) || (← (rightJson.mapM jsonIsSetExpr).map (·.getD false)) then
    let prop ← getPropCondition
    let call (fn : Name) (a b : TSyntax `term) : PygenM (TSyntax `term) := do
      let t ← `($(mkIdent fn) $a $b)
      if prop then `($t = true) else pure t
    match op with
    | "eq" => return ← call ``PastaLean.pySetEq leftCode rightCode
    | "ne" => let t ← `($(mkIdent ``PastaLean.pySetEq) $leftCode $rightCode)
              return ← (if prop then `($t = false) else `(! $t))
    | "le" => return ← call ``PastaLean.pySetSubset leftCode rightCode
    | "lt" => return ← call ``PastaLean.pySetProperSubset leftCode rightCode
    | "ge" => return ← call ``PastaLean.pySetSubset rightCode leftCode
    | "gt" => return ← call ``PastaLean.pySetProperSubset rightCode leftCode
    | _ => pure ()   -- `in`/`is`/`notin` fall through to the normal membership handling
  -- `x is None` / `x == None` (and their negations) dispatch through `pyIsNone`, which is total over
  -- every type: an `Option` answers by its tag, the `None` value (`Unit`) is `true`, and any other
  -- type (`Int`, `String`, …) is `false` — so `y is not None` on a known `int` no longer type-errors
  -- against `Option.isSome`. When BOTH sides are the literal `None`, the result is a compile-time
  -- constant (`None is None` → `true`). `is`/`eq` test equality-to-`None`; `isnot`/`ne` negate it.
  let noneTest := op == "is" || op == "isnot" || op == "eq" || op == "ne"
  let leftIsNone := isNoneConstantJson leftJson
  let rightIsNone := rightJson.any isNoneConstantJson
  if noneTest && (leftIsNone || rightIsNone) then
    let equalsNone := op == "is" || op == "eq"
    if leftIsNone && rightIsNone then
      -- `None is None` / `None == None` are `true`; `None is not None` / `None != None` are `false`.
      return ← if equalsNone then `(true) else `(false)
    let operand := if leftIsNone then rightCode else leftCode
    let test ← `($(mkIdent ``PastaLean.pyIsNone) $operand)
    return ← if equalsNone then pure test else `(! $test)
  -- *Condition position* (`prop`): comparison yields `Prop` (e.g., `a < b`, `a = b` in exact mode).
  -- *Value position* (`!prop`): comparison yields `Bool` (e.g., `decide (a < b)`, `a == b`).
  let prop ← getPropCondition
  let exact ← numericModeIsExact
  match op with
  -- User-class (node) operands compare through `BEq` (`==`): they derive `BEq` but not `DecidableEq`,
  -- so the propositional `=`/`≠` the exact twin would otherwise emit has no `Decidable` instance.
  | "eq" | "is" =>
      if prop && exact && !classCmp then `($leftCode = $rightCode) else `($leftCode == $rightCode)
  | "ne" | "isnot" =>
      if prop && exact && !classCmp then `($leftCode ≠ $rightCode) else `($leftCode != $rightCode)
  | "lt" | "gt" | "le" | "ge" =>
      let l ← unwrapOptionOperand leftJson leftCode
      let r ← match rightJson with | some rj => unwrapOptionOperand rj rightCode | none => pure rightCode
      match op with
      | "lt" => if prop then `($l < $r) else `(decide ($l < $r))
      | "gt" => if prop then `($l > $r) else `(decide ($l > $r))
      | "le" => if prop then `($l <= $r) else `(decide ($l <= $r))
      | _    => if prop then `($l >= $r) else `(decide ($l >= $r))
  -- `x in c` is `pyContains c x` for EVERY container: the `PyContains` instance resolves by the
  -- container's type — `String` does substring (`"AB" in s`, `c in "AEIOU"`), `List`/`PySet`/`HashMap`
  -- do membership. This is type-driven, so it needs no fragile "is the container a set?" guess (which
  -- mis-fired for `"0" in set(s)` when the set-var registry didn't reach across statements).
  | "in" => `($(mkIdent ``pyContains) $rightCode $leftCode)
  | "notin" => `(! ($(mkIdent ``pyContains) $rightCode $leftCode))
  | _ => throwError s!"Unsupported comparison operator: {op}"

@[pygen "BinOp"]
def binOpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    Term.synthesizeSyntheticMVarsNoPostponing
    let .ok op := json.getObjValAs? String "op" | throwError
      s!"BinOp node does not have an 'op' field or it is not a string: {json}"
    let .ok leftJson := json.getObjValAs? Json "left" | throwError
      s!"BinOp node does not have a 'left' field or it is not a JSON value: {json}"
    let .ok rightJson := json.getObjValAs? Json "right" | throwError
      s!"BinOp node does not have a 'right' field or it is not a JSON value: {json}"
    -- Arithmetic operates on VALUES: a comparison operand (`cnt + (a == b)`, Python's bool-as-int) is a
    -- `Bool`, never a `Prop`, even when the whole BinOp sits inside an `if`/`while` test (which set the
    -- prop context). Lower operands in value context so the comparison becomes `Bool`, not `a = b`.
    let leftCode ←  withPropCondition false (getCode leftJson `term)
    let rightCode ← withPropCondition false (getCode rightJson `term)
    -- `[x] * n`: `pyListRepeat` (or `pyArrayRepeat` when the slot is array-backed, so a sieve/DP-table
    -- `[0]*n` gets O(1) `a[i]=v`) fixes the result type immediately. The `[x]` operand is emitted as an
    -- `Array` (`#[x]`) via its own `_seq` stamp, so `pyArrayRepeat` receives an `Array`.
    if op == "mul" then
      let arrayBacked := (json.getObjValAs? String "_seq" == .ok "array") && (← getNumericMode) == .approx
      let repeatIdent := mkIdent (if arrayBacked then ``PastaLean.pyArrayRepeat else ``PastaLean.pyListRepeat)
      -- The `[x]` operand is consumed by `pyListRepeat`, which wants a bare list — NOT a heap cell. Under
      -- `--heap` the ordinary List generator wraps a literal in `(← allocM …)`, which would hand
      -- `pyListRepeat` a `Ref`; regenerate the operand raw here (any heap-ness of the RESULT is applied at
      -- the assignment, not to this transient operand).
      let rawListOperand (listJson : Json) : PygenM (TSyntax `term) := do
        let elts ← ((listJson.getObjValAs? (Array Json) "elts").toOption.getD #[]).mapM (getCode · `term)
        if arrayBacked then `(#[$elts,*]) else `([$elts,*])
      if leftJson.getObjValAs? String "node_type" == .ok "List" then
        return ← `($repeatIdent $(← rawListOperand leftJson) $rightCode)
      else if rightJson.getObjValAs? String "node_type" == .ok "List" then
        return ← `($repeatIdent $(← rawListOperand rightJson) $leftCode)
    binOpApplyTerm op leftCode rightCode
  | _, _ => throwError s!"Unsupported syntax category for BinOp node"

@[pygen "UnaryOp"]
def unaryOpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok op := json.getObjValAs? String "op" | throwError
      s!"UnaryOp node does not have an 'op' field or it is not a string: {json}"
    let .ok operandJson := json.getObjValAs? Json "operand" | throwError
      s!"UnaryOp node does not have an 'operand' field or it is not a JSON value: {json}"
    -- In a `Prop` position in exact mode (`assert`/theorem, or an `if` test), `not p` is `¬ p` with
    -- `p` itself a `Prop`. Otherwise `not` is the `Bool` `!`, so its operand must be `Bool`.
    let propNot := op == "not" && (← getPropCondition) && (← numericModeIsExact)
    let operandCode ← withPropCondition propNot (getCode operandJson `term)
    if op == "not" then
      -- `not x` is a truthiness context too: a bare non-boolean operand needs `pyTruthy`
      -- (same missing coercion as `if x:` / bool operands), else `¬`/`!` gets a raw value.
      let b ← if conditionIsBoolean operandJson then pure operandCode
              else if propNot && isQuantifiedAllAnyJson operandJson then pure operandCode
              else if propNot then `($(mkIdent ``PastaLean.pyTruthy) $operandCode = true)
                   else `($(mkIdent ``PastaLean.pyTruthy) $operandCode)
      if propNot then `(¬ $b) else `(! $b)
    else unaryOpApplyTerm op operandCode
  | _, _ => throwError s!"Unsupported syntax category for UnaryOp node"

/-- Does `stx` contain a `(← e)` await anywhere? A value-position `and`/`or` whose operands carry
one (heap derefs, IO) cannot lower to a pure `if`-term — its branches would host `←`, which is only
legal inside a `do`. -/
partial def syntaxHasLift : Syntax → Bool
  | .node _ ``Lean.Parser.Term.liftMethod _ => true
  | .node _ _ args => args.any syntaxHasLift
  | _ => false

/-- Python `and`/`or` as a VALUE (not a truthiness test): they return the deciding *operand*, not a
`Bool` — `x or '0'` yields the string. `a or b … = <first truthy, else last>`, `a and b … = <first
falsy, else last>`, lowered to nested `if pyTruthy … then … else …`. Only valid when the operands
share a Lean type (the common `<expr> or <default>` idiom); used by `return`/assignment where the
result is consumed as a value, not by condition positions (which keep the `Bool` form). -/
def boolOpValueTerm (json : Json) : PygenM (TSyntax `term) := do
  let .ok op := json.getObjValAs? String "op" | throwError s!"BoolOp is missing 'op': {json}"
  let .ok valuesJson := json.getObjValAs? (Array Json) "values" | throwError
    s!"BoolOp is missing 'values': {json}"
  let codes ← valuesJson.mapM (getCode · `term)
  let some last := codes.back? | throwError s!"BoolOp has no operands: {json}"
  let t := mkIdent ``PastaLean.pyTruthy
  -- When an operand carries a `←` (heap deref, IO) we are necessarily inside a `do`, and the
  -- `if pyTruthy … then … else …` must be a `do`-if so each await lifts into its own branch; a pure
  -- `if`-term forbids `←` in its branches. Binding the guard once (hygienic `bopGuard`) keeps
  -- Python's short-circuit: evaluate the guard, then only the chosen operand. Pure operands keep the
  -- plain `if`-term, which is also valid in non-`do` positions (top-level `def`s).
  let monadic := codes.any (fun c => syntaxHasLift c.raw)
  -- Fold the operands before the last from right to left.
  (codes.pop.reverse).foldlM (init := last) fun acc c =>
    if monadic then
      if op == "and" then
        `((← do let bopGuard := $c; if $t bopGuard then pure $acc else pure bopGuard))
      else
        `((← do let bopGuard := $c; if $t bopGuard then pure bopGuard else pure $acc))
    else if op == "and" then `(if $t $c then $acc else $c) else `(if $t $c then $c else $acc)

@[pygen "BoolOp"]
def boolOpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok op := json.getObjValAs? String "op" | throwError
      s!"BoolOp node does not have an 'op' field or it is not a string: {json}"
    let .ok valuesJson := json.getObjValAs? Json "values" | throwError
      s!"BoolOp node does not have a 'values' field or it is not a JSON value: {json}"
    -- A test position (`while`/`if`/assert) or a truthiness context (`any(…)`/`all(…)`) sets this;
    -- there `and`/`or` must stay a `Bool` connective, never the value form (a `while` cond needs
    -- `Bool`, and `any(list and bool for …)` would otherwise have mismatched value-form branches).
    let inCondition := (← getPropCondition) || (← getTruthinessContext)
    -- In exact `Prop` positions, `and`/`or` become `∧`/`∨`; otherwise lower to `Bool`. A truthiness
    -- context stays `Bool` (it does NOT force `Prop`) — so `any(a == b for …)` is `List Bool`.
    let opProp := (← getPropCondition) && (← numericModeIsExact)
    -- `a or b` / `a and b` on NON-boolean operands returns the deciding *operand*, not a `Bool`
    -- (`[…] or [0]` yields the list, `x or 0` the number) — but only in a VALUE position; a
    -- condition keeps the `Bool` connective. Only all-boolean operands are a real connective.
    let allBool := match valuesJson with
      | .arr arr => arr.all conditionIsBoolean
      | _ => false
    if !inCondition && !allBool then
      return ← boolOpValueTerm json
    -- Each `and`/`or` operand is a truthiness context, so non-booleans must be coerced with `pyTruthy`.
    -- Mark it as such while lowering so a NESTED BoolOp operand (`a or (b and c)`) also stays in the
    -- Bool/Prop connective form instead of falling to the value form — the value form would leave a
    -- non-`Bool` inner operand (`… and y%100`) to be mis-coerced by the enclosing connective.
    let lowerOperand (valueJson : Json) : PygenM (TSyntax `term) := do
      let code ← withTruthinessContext true (withPropCondition opProp (getCode valueJson `term))
      if conditionIsBoolean valueJson then pure code
      -- An `all`/`any` operand of a contract's `and`/`or` is already a `Prop` (a quantifier), so
      -- coercing it would be a type error.
      else if opProp && isQuantifiedAllAnyJson valueJson then pure code
      else if opProp then `($(mkIdent ``PastaLean.pyTruthy) $code = true)
      else `($(mkIdent ``PastaLean.pyTruthy) $code)
    let valuesCodes ← match valuesJson with
      | .arr arr => arr.mapM lowerOperand
      | _ => throwError s!"BoolOp node 'values' field is not an array: {valuesJson}"
    let l := valuesCodes.toList.length
    if l = 0 then throwError s!"BoolOp node 'values' array is empty: {valuesJson}"
    match op with
    | "and" =>
        if opProp then valuesCodes.foldlM (fun a b => `($a ∧ $b)) (valuesCodes[0]!) (start := 1)
        else valuesCodes.foldlM (fun a b => `($a && $b)) (valuesCodes[0]!) (start := 1)
    | "or" =>
        if opProp then valuesCodes.foldlM (fun a b => `($a ∨ $b)) (valuesCodes[0]!) (start := 1)
        else valuesCodes.foldlM (fun a b => `($a || $b)) (valuesCodes[0]!) (start := 1)
    | _ => throwError s!"Unsupported boolean operator: {op}"
  -- A BoolOp as a STATEMENT is a short-circuit side effect: `g and effect` runs `effect` (a mutating
  -- call like `u != v and uf.union(u, v)`) when the guards hold; `g or effect` runs it when they do
  -- not. The last operand is the effect (lowered as a statement); the earlier ones are the guard.
  | `doElem, json => do
    let .ok op := json.getObjValAs? String "op" | throwError s!"BoolOp node missing 'op': {json}"
    let values := (json.getObjValAs? (Array Json) "values").toOption.getD #[]
    if values.size < 2 then
      throwError s!"BoolOp statement needs at least two operands: {json}"
    let effectJson := values[values.size - 1]!
    let guards := values.extract 0 (values.size - 1)
    let guardTerms ← guards.mapM (fun v => do
      let c ← getCode v `term
      let t : TSyntax `term ← if conditionIsBoolean v then pure c else `($(mkIdent ``PastaLean.pyTruthy) $c)
      match op with
      | "or" => `(! $t)
      | _ => pure t)
    let guard ← guardTerms.foldlM (fun a b => `($a && $b)) guardTerms[0]! (start := 1)
    let effects : Array (TSyntax `doElem) := #[← getCode effectJson `doElem]
    `(doElem| if $guard then $[$effects:doElem]*)
  | _, _ => throwError s!"Unsupported syntax category for BoolOp node"

/-- A bare Python type-name `Name` node → its `TypeInfer.PyType` tag syntax, for `type(x) == int` and
`isinstance(x, int)`. Builtin types map to element-less `PyType` heads (Python's `list`/`dict`/… type
objects carry no element); a registered user class `Trie` maps to `PyType.cls "Trie"`. `none` for
anything that is not a type name. -/
def pyTypeNameTag? (json : Json) : PygenM (Option (TSyntax `term)) := do
  if json.getObjValAs? String "node_type" != .ok "Name" then return none
  match json.getObjValAs? String "id" with
  | .ok "int"   => return some (← `(TypeInfer.PyType.int))
  | .ok "float" => return some (← `(TypeInfer.PyType.float))
  | .ok "str"   => return some (← `(TypeInfer.PyType.str))
  | .ok "bool"  => return some (← `(TypeInfer.PyType.bool))
  | .ok "list"  => return some (← `(TypeInfer.PyType.list TypeInfer.PyType.unknown))
  | .ok "dict"  => return some (← `(TypeInfer.PyType.dict TypeInfer.PyType.unknown TypeInfer.PyType.unknown))
  | .ok "tuple" => return some (← `(TypeInfer.PyType.tuple []))
  | .ok "set"   => return some (← `(TypeInfer.PyType.set TypeInfer.PyType.unknown))
  | .ok other   =>
      -- A user class used as a type (`type(x) == Trie`, `isinstance(x, Trie)`) → its `.cls` tag.
      if ← isRegisteredClass other then
        return some (← `(TypeInfer.PyType.cls $(Syntax.mkStrLit other)))
      return none
  | _ => return none

/-- Is `json` a call to the builtin `type(...)`? -/
def isTypeCall (json : Json) : Bool :=
  json.getObjValAs? String "node_type" == .ok "Call" &&
    ((json.getObjVal? "func").toOption.bind (·.getObjValAs? String "id" |>.toOption)) == some "type"

@[pygen "Compare"]
def compareSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok op := json.getObjValAs? String "op" | throwError
      s!"Compare node does not have an 'op' field or it is not a string: {json}"
    let .ok leftJson := json.getObjValAs? Json "left" | throwError
      s!"Compare node does not have a 'left' field or it is not a JSON value: {json}"
    let .ok rightJson := json.getObjValAs? Json "right" | throwError
      s!"Compare node does not have a 'right' field or it is not a JSON value: {json}"
    -- `type(x) == int` / `type(x) != int`: when one operand is a `type(...)` call, the bare type-name
    -- on the other side lowers to its `PyTypeName` tag (so `pyType x == PyTypeName.int` compares).
    let typeCmp := isTypeCall leftJson || isTypeCall rightJson
    let sideCode (j : Json) : PygenM (TSyntax `term) := do
      if typeCmp then
        match ← pyTypeNameTag? j with | some t => pure t | none => getCode j `term
      else getCode j `term
    let leftCode ← sideCode leftJson
    let rightCode ← sideCode rightJson
    -- A `type(x) == T` check is a runtime `Bool` (never a proof goal), and `PyType` has `BEq` but no
    -- `DecidableEq`, so force the Bool `==`/`!=` form rather than the prop `=`/`≠` exact mode would emit.
    if typeCmp then
      return ← withPropCondition false (compareApplyTerm op leftJson leftCode rightCode
        (rightJson := some rightJson))
    let classCmp := json.getObjValAs? Bool "_class_cmp" == .ok true
    compareApplyTerm op leftJson leftCode rightCode (rightJson := some rightJson) (classCmp := classCmp)
  | _, _ => throwError s!"Unsupported syntax category for Compare node"

/-- Does a `Name`-call to `name` appear anywhere in `json`? (Local mirror of `containsCallTo`, kept
here to avoid importing the closure-conversion pass into the leaf-node generators.) -/
partial def jsonCallsName (name : String) (json : Json) : Bool :=
  let hereCall :=
    json.getObjValAs? String "node_type" == .ok "Call" &&
      (json.getObjVal? "func" |>.toOption.any (fun f =>
        f.getObjValAs? String "node_type" == .ok "Name" && f.getObjValAs? String "id" == .ok name))
  hereCall || (match json with
    | .arr xs => xs.any (jsonCallsName name)
    | .obj fs => fs.toList.any (fun (_, v) => jsonCallsName name v)
    | _ => false)

/-- The variable name and polarity of a `<name> is None` / `<name> is not None` (or `== None` /
`!= None`) test: `(name, true)` for an *is-None* test, `(name, false)` for *is-not-None*. `none`
if the test is not that shape. -/
private def noneTestVar? (testJson : Json) : Option (String × Bool) := do
  if testJson.getObjValAs? String "node_type" != .ok "Compare" then none else
  let op ← (testJson.getObjValAs? String "op").toOption
  if !(op == "is" || op == "eq" || op == "isnot" || op == "ne") then none else
  let left ← (testJson.getObjVal? "left").toOption
  let right ← (testJson.getObjVal? "right").toOption
  let nameSide ← if isNoneConstantJson left then some right
                 else if isNoneConstantJson right then some left else none
  if nameSide.getObjValAs? String "node_type" != .ok "Name" then none else
  let id ← (nameSide.getObjValAs? String "id").toOption
  some (id, op == "is" || op == "eq")

private def nameId? (j : Json) : Option String :=
  if j.getObjValAs? String "node_type" == .ok "Name" then (j.getObjValAs? String "id").toOption else none

@[pygen "IfExp"]
def ifExpSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok testJson := json.getObjValAs? Json "test" | throwError
      s!"IfExp node does not have a 'test' field or it is not a JSON value: {json}"
    let .ok bodyJson := json.getObjValAs? Json "body" | throwError
      s!"IfExp node does not have a 'body' field or it is not a JSON value: {json}"
    let .ok orelseJson := json.getObjValAs? Json "orelse" | throwError
      s!"IfExp node does not have an 'orelse' field or it is not a JSON value: {json}"
    -- The ternary test is a boolean context (like `if`/`while`): a `BoolOp` here must lower to the
    -- `Bool` connective, not the value-form (`x or y` where the operands have different types).
    let testCode ← truthyConditionTerm testJson (← withPropCondition true (getCode testJson `term))
    let bodyIsNone := isNoneConstantJson bodyJson
    let orelseIsNone := isNoneConstantJson orelseJson
    -- The value branch is already `Option`-typed (TypeInfer's `_branch_opt`, e.g. `l1.next` an
    -- `Option` field), so wrapping it in `some` would nest to `Option (Option _)` — emit it bare.
    let branchOpt := json.getObjValAs? Bool "_branch_opt" == .ok true
    let lift (code : TSyntax `term) : PygenM (TSyntax `term) :=
      if branchOpt then pure code else `(some $code)
    -- None-coalescing return `X if v is None else v` (or `v if v is not None else X`) on an `Option T`
    -- slot: emit `v.getD X`, unwrapping the `Option` to the bare `T` both arms share (the raw
    -- `if … then X else v` would mismatch `String` against `Option String`).
    let coalesce? ← (do
      match noneTestVar? testJson with
      | some (v, isNone) =>
        if (← isOptionVar v.toName)
            && ((isNone && nameId? orelseJson == some v) || (!isNone && nameId? bodyJson == some v)) then
          let (vNode, dfltNode) := if isNone then (orelseJson, bodyJson) else (bodyJson, orelseJson)
          let vCode ← getCode vNode `term
          let dfltCode ← getCode dfltNode `term
          pure (some (← `(($vCode).getD $dfltCode)))
        else pure none
      | none => pure none : PygenM (Option (TSyntax `term)))
    if bodyIsNone && orelseIsNone then
      `(none)
    else if bodyIsNone then
      let orelseCode ← lift (← getCode orelseJson `term)
      `(if $testCode then none else $orelseCode)
    else if orelseIsNone then
      let bodyCode ← lift (← getCode bodyJson `term)
      `(if $testCode then $bodyCode else none)
    else if let some c := coalesce? then
      pure c
    else
      let bodyCode ← getCode bodyJson `term
      let orelseCode ← getCode orelseJson `term
      -- Memoized `@cache` body: a self-call in a ternary branch lowered to `(← worker …)`; wrap each
      -- branch in its own `do return …` so the `←` stays scoped there and the branch stays lazy
      -- (hoisting it out of the `if` would run the recursion unconditionally, breaking the base case).
      if let some (memoName, _) ← getMemoizeSelf then
        if jsonCallsName memoName bodyJson || jsonCallsName memoName orelseJson then
          return ← `((← if $testCode then (do return $bodyCode) else (do return $orelseCode)))
      -- A branch carrying an `(← …)` await (a heap read `d[i]` in `d[i] if c else x`) can't sit in an
      -- `if`-TERM — wrap each branch in `do return …` so its await stays scoped, and await the whole
      -- `if` (same shape as the memoized case, and lazy so only the taken branch's effect runs).
      if syntaxHasLift bodyCode || syntaxHasLift orelseCode then
        return ← `((← if $testCode then (do return $bodyCode) else (do return $orelseCode)))
      `(if $testCode then $bodyCode else $orelseCode)
  | _, _ => throwError s!"Unsupported syntax category for IfExp node"

-- Example
def onePlusTwoNode := json% {
    "node_type": "BinOp",
    "op": "add",
    "left": {
      "node_type": "Constant",
      "value": 1
    },
    "right": {
      "node_type": "Constant",
      "value": 2
    }
  }

-- @[pygen "Call"]
-- def callSyntax : (kind : SyntaxNodeKind) → Json →
--     PygenM (TSyntax kind)
--   | `term, json => do
--     let .ok funcJson := json.getObjValAs? Json "func" | throwError
--       s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
--     let .ok argsJson := json.getObjValAs? Json "args" | throwError
--       s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
--     let funcCode : TSyntax `term ← match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
--       | .ok "Name", .ok funcName =>
--           let mappedName ← leanName funcName.toName
--           pure <| (mkIdent mappedName : TSyntax `term)
--       | _, _ =>
--           getCode funcJson `term
--     let mut t ← `($funcCode)
--     let argsCodes ← match argsJson with
--       | .arr arr => arr.mapM (fun argJson => getCode argJson `term)
--       | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
--     for argCode in argsCodes do
--       t ←  `($t $argCode)
--     let .ok keyWordsJson := json.getObjVal?  "keywords" | throwError
--       s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
--     let .ok keyWordsMap := keyWordsJson.getObj? | throwError
--       s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
--     for (kwName, kwValueJson) in keyWordsMap.toList do
--       let kwValueCode ← getCode kwValueJson `term
--       let kwId := mkIdent kwName.toName
--       t ← `($t ($kwId:ident := $kwValueCode))
--     return t
--   | `doElem, json => do
--     let .ok funcJson := json.getObjValAs? Json "func" | throwError
--       s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
--     let .ok argsJson := json.getObjValAs? Json "args" | throwError
--       s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
--     let funcCode : TSyntax `term ← match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
--       | .ok "Name", .ok funcName =>
--           let mappedName ← leanName funcName.toName
--           pure <| (mkIdent mappedName : TSyntax `term)
--       | _, _ =>
--           getCode funcJson `term
--     let mut t ← `($funcCode)
--     let argsCodes ← match argsJson with
--       | .arr arr => arr.mapM (fun argJson => getCode argJson `term)
--       | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
--     for argCode in argsCodes do
--       t ← `($t $argCode)
--     let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
--       s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
--     let .ok keyWordsMap := keyWordsJson.getObj? | throwError
--       s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
--     for (kwName, kwValueJson) in keyWordsMap.toList do
--       let kwValueCode ← getCode kwValueJson `term
--       let kwId := mkIdent kwName.toName
--       t ← `($t ($kwId:ident := $kwValueCode))
--     let callCode := t
--     `(doElem| let _ := $callCode)
--   | _, _ => throwError s!"Unsupported syntax category for Call node"

def fn := fun n => show IO _ from  do
  let m := n + 1
  return m

def fnId := Id.run do
  let n := 3
  let m := n + 1
  return m

def n₀ : Id Nat := 3

@[pygen_transform term]
def elabCheckTerm : (stx : TSyntax `term) → PygenM (TSyntax `term)
  | codeStx => do
    unless ← isCheckEnabled do
      return codeStx
    try
      let cmd ← `(command| example := $codeStx)
      liftCommandElabM <| Command.elabCommand cmd
      -- IO.eprintln s!"Successfully elaborated term: {codeStx}"  -- Debugging output
      return codeStx
    catch e =>
      throwError s!"Error elaborating code: {← e.toMessageData.toString} for {← PrettyPrinter.ppTerm codeStx}"

@[pygen_transform term]
def addArrow : (stx : TSyntax `term) → PygenM (TSyntax `term)
  | codeStx => do
    unless ← isUseArrowEnabled do
      return codeStx
    try
      let e ← elabTerm codeStx none
      let eType ← inferType e
      if eType.isAppOf ``Id then
        `(← $codeStx)
      else
        return codeStx
    catch e =>
      trace[PastaLean.pygen.info] m!"addArrow transform failed for {codeStx} with error: {← e.toMessageData.toString}"
      return codeStx

@[pygen_transform command]
def elabCheckCmd : (stx : TSyntax `command) → PygenM (TSyntax `command)
  | cmd => do
    unless ← isCheckEnabled do
      return cmd
    try
      if cmd.raw.isOfKind nullKind then
        return cmd
      else
        liftCommandElabM <| Command.elabCommand cmd
      -- IO.eprintln s!"Successfully elaborated command: {← PrettyPrinter.ppCommand cmd}"  -- Debugging output
      return cmd
    catch e =>
      throwError s!"Error elaborating code: {← e.toMessageData.toString} for {← PrettyPrinter.ppCommand cmd}"

-- #eval pygen

end PastaLean
