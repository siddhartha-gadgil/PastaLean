import Mathlib
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
        let noneIdent := mkIdent ``none
        `($noneIdent)
    | _ => throwError s!"Unsupported constant value: {value}"
  | _, _ => throwError s!"Unsupported syntax category for Constant node"

def jsonLibraryMappedName? (json : Json) : PygenM (Option Lean.Name) := do
  match json.getObjValAs? String "library_module", json.getObjValAs? String "library_member" with
  | .ok moduleName, .ok memberName =>
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
  if (← getNumericMode) == .exact then
    return pythonBuiltinMapExact? name <|> pythonBuiltinMap? name
  else
    return pythonBuiltinMap? name

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

@[pygen "Name"]
def nameSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName => pure (mkIdent leanName)
    | none =>
        let .ok id := json.getObjValAs? String "id" | throwError
          s!"Name node does not have an 'id' field or it is not a string: {json}"
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
        -- A reference to a user-defined top-level function/class is `_root_`-qualified ONLY when the
        -- name actually collides with an existing global (`dist`, `gcd`, …), so it resolves to the
        -- user's own definition rather than a Mathlib export — the endless-clash fix, no namespace.
        -- A local shadows the global, and a non-clashing name (e.g. a recursive self-reference not
        -- yet in the environment) is left bare so its reference still resolves.
        if (← userNamesRef.get).contains id && !(← hasVar id.toName)
            && !(← resolveGlobalName id.toName).isEmpty then
          return mkIdent (`_root_ ++ suffixed.toName)
        else
          return mkIdent suffixed.toName
  | `ident, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName => pure (mkIdent leanName)
    | none =>
        let .ok id := json.getObjValAs? String "id" | throwError
          s!"Name node does not have an 'id' field or it is not a string: {json}"
        -- In a run-twin, a reference to a user function/class is suffixed (`bar` → `bar'rn`,
        -- `CNN` → `CNN'rn`); locals and library names are left as-is.
        return mkIdent (← suffixIfUserName id).toName
  | _, _ => throwError s!"Unsupported syntax category for Name node"

/-- Under `--heap` a fresh container literal is a heap cell: wrap it in `(← alloc …)` so it yields a
`Ref …`. In value mode the literal is returned unchanged. -/
def allocIfHeap (t : TSyntax `term) : PygenM (TSyntax `term) := do
  if ← getHeapMode then `((← PastaLean.allocM $t)) else pure t

@[pygen "List"]
def listSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
      s!"List node does not have an 'elts' field or it is not a JSON value: {json}"
    let eltCodes ← match eltsJson with
      | .arr arr => arr.mapM (fun eltJson => getCode eltJson `term)
      | _ => throwError s!"List node 'elts' field is not an array: {eltsJson}"
    let listTerm ← `([$eltCodes,*])
    allocIfHeap listTerm
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
and `inlineIOTerm` so IO-bearing operands can be hoisted without duplicating the op table. -/
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

/-- Lower a condition expression, applying Python truthiness (`pyTruthy`) unless it already
produces a `Bool`. Used by `if`/`while`/`if`-expression lowering. -/
def truthyConditionTerm (json : Json) (code : TSyntax `term) : PygenM (TSyntax `term) := do
  if conditionIsBoolean json then pure code
  else `($(mkIdent ``PastaLean.pyTruthy) $code)

/-- A `passta` predicate marker (`Assert`/`Invariant`/…) takes a `Prop`, so a marker argument that
is a bare *value* (`assert q` on a deque, `Assume(flag)`) has to go through Python truthiness first
or it lands in the `Prop` slot as a `List`/`Int`. Comparisons, boolean operators and calls already
lower to `Bool`, which coerces. -/
def passtaMarkerNeedsTruthy (json : Json) : Bool :=
  match json.getObjValAs? String "node_type" with
  | .ok "Name" | .ok "Subscript" | .ok "Attribute"
  | .ok "List" | .ok "Tuple" | .ok "Dict" | .ok "Set" => true
  | _ => false

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

/-- Route the value-shaped arguments of a `passta` predicate marker through Python truthiness; a
no-op for every other call. Both `Call` lowerings (term and `doElem`) go through this — `Assert(q)`
is a statement, `Assert(q) if …` an expression, and either way `q` lands in a `Prop` slot. -/
def passtaMarkerArgCodes (funcJson : Json) (argsArray : Array Json)
    (argsCodes : Array (TSyntax `term)) : PygenM (Array (TSyntax `term)) := do
  unless funcJson.getObjValAs? String "library_module" == .ok "passta" &&
      funcJson.getObjValAs? String "library_member" != .ok "Decreases" &&
      argsCodes.size == argsArray.size do
    return argsCodes
  argsArray.zipIdx.mapM fun (argJson, i) =>
    if passtaMarkerNeedsTruthy argJson then truthyConditionTerm argJson argsCodes[i]!
    else pure argsCodes[i]!

/-- A JSON node whose Python value is a `float`. Python's `/` is always true division, so a `float`
can reach a slot Lean has already fixed as `Int`. Recurses through arithmetic because `x / 2 + 1` is
float-valued too; `//` and the bitwise ops are not, so they stop the recursion. -/
partial def isFloatyJson (json : Json) : Bool :=
  stampedFloat json ||
  match json.getObjValAs? String "node_type" with
  | .ok "BinOp" =>
      let arm (key : String) : Bool := (json.getObjVal? key).toOption.any isFloatyJson
      match json.getObjValAs? String "op" with
      | .ok "div" => true
      | .ok "add" | .ok "sub" | .ok "mul" | .ok "pow" | .ok "mod" => arm "left" || arm "right"
      | _ => false
  | .ok "UnaryOp" => (json.getObjVal? "operand").toOption.any isFloatyJson
  | .ok "IfExp" =>
      (json.getObjVal? "body").toOption.any isFloatyJson ||
        (json.getObjVal? "orelse").toOption.any isFloatyJson
  | .ok "Constant" => json.getObjValAs? String "python_literal_kind" == .ok "float"
  | .ok "Call" => (json.getObjVal? "func").toOption.any (·.getObjValAs? String "id" == .ok "float")
  | _ => false

/-- Widen an integer-valued term to the mode's float type — the same coercion `float(x)` lowers to:
`pyRat` (exact ℚ) or `pyFloat` (the run twin's `Float`). -/
def widenToFloat (code : TSyntax `term) : PygenM (TSyntax `term) := do
  match ← getNumericMode with
  | .approx => `(PastaLean.pyFloat $code)
  | .exact => `(PastaLean.pyRat $code)

/-- A tuple *literal* on the right of `in`/`not in` (`c in ('D', 'I')`) is a plain membership test in
Python, but lowers to a Lean `×` product, which no `PyContains` instance covers — re-lower it as a
list, which is the same test on the same elements. `none` when the right side is not such a tuple. -/
def membershipTupleAsList? (rightJson : Option Json) : PygenM (Option (TSyntax `term)) := do
  let some rj := rightJson | return none
  unless rj.getObjValAs? String "node_type" == .ok "Tuple" do return none
  let .ok (.arr elts) := rj.getObjValAs? Json "elts" | return none
  if elts.isEmpty then return none
  let eltCodes ← elts.mapM (getCode · `term)
  some <$> `([$eltCodes,*])

/-- Apply a Python comparison operator to already-lowered terms. `leftJson` only affects
membership lowering: a string literal on the left of `in`/`not in` means substring containment
(`pyStrContainsSubstr`); otherwise membership uses `pyContains`, whose `outParam` element type
pins the element from the container. -/
def compareApplyTerm (op : String) (leftJson : Json) (leftCode rightCode : TSyntax `term)
    (rightJson : Option Json := none) : PygenM (TSyntax `term) := do
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
  | "eq" | "is" =>
      if prop && exact then `($leftCode = $rightCode) else `($leftCode == $rightCode)
  | "ne" | "isnot" =>
      if prop && exact then `($leftCode ≠ $rightCode) else `($leftCode != $rightCode)
  | "lt" => if prop then `($leftCode < $rightCode) else `(decide ($leftCode < $rightCode))
  | "gt" => if prop then `($leftCode > $rightCode) else `(decide ($leftCode > $rightCode))
  | "le" => if prop then `($leftCode <= $rightCode) else `(decide ($leftCode <= $rightCode))
  | "ge" => if prop then `($leftCode >= $rightCode) else `(decide ($leftCode >= $rightCode))
  | "in" | "notin" =>
      -- Substring containment only when the container really is a string: a tuple literal on the
      -- right is an element test even for a string on the left (`"ab" in ("ab", "cd")`).
      let tuple? ← membershipTupleAsList? rightJson
      let test ← match tuple? with
        | some listCode => `($(mkIdent ``pyContains) $listCode $leftCode)
        | none =>
            if isStringyJson leftJson then
              `($(mkIdent ``PastaLean.pyStrContainsSubstr) $rightCode $leftCode)
            else `($(mkIdent ``pyContains) $rightCode $leftCode)
      if op == "in" then pure test else `(! $test)
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
    let leftCode ←  getCode leftJson `term
    let rightCode ← getCode rightJson `term
    -- Use `pyListRepeat` for list literals so the result type is fixed immediately.
    if op == "mul" then
      let repeatIdent := mkIdent ``PastaLean.pyListRepeat
      if leftJson.getObjValAs? String "node_type" == .ok "List" then
        return ← `($repeatIdent $leftCode $rightCode)
      else if rightJson.getObjValAs? String "node_type" == .ok "List" then
        return ← `($repeatIdent $rightCode $leftCode)
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
              else if propNot then `($(mkIdent ``PastaLean.pyTruthy) $operandCode = true)
                   else `($(mkIdent ``PastaLean.pyTruthy) $operandCode)
      if propNot then `(¬ $b) else `(! $b)
    else unaryOpApplyTerm op operandCode
  | _, _ => throwError s!"Unsupported syntax category for UnaryOp node"

/-- Does `stx` contain a `(← e)` await anywhere? A value-position `and`/`or` whose operands carry
one (heap derefs, IO) cannot lower to a pure `if`-term — its branches would host `←`, which is only
legal inside a `do`. -/
partial def syntaxHasLift : Syntax → Bool
  | .node _ ``Lean.Parser.Term.nestedAction _ => true
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
    -- A test position (`while`/`if`/assert) sets this; there `and`/`or` must stay a `Bool`
    -- connective in every twin, never the value form (a `while` cond needs `Bool`, not `Int`).
    let inCondition ← getPropCondition
    -- In exact `Prop` positions, `and`/`or` become `∧`/`∨`; otherwise lower to `Bool`.
    let opProp := inCondition && (← numericModeIsExact)
    -- `a or b` / `a and b` on NON-boolean operands returns the deciding *operand*, not a `Bool`
    -- (`[…] or [0]` yields the list, `x or 0` the number) — but only in a VALUE position; a
    -- condition keeps the `Bool` connective. Only all-boolean operands are a real connective.
    let allBool := match valuesJson with
      | .arr arr => arr.all conditionIsBoolean
      | _ => false
    if !inCondition && !allBool then
      return ← boolOpValueTerm json
    -- Each `and`/`or` operand is a truthiness context, so non-booleans must be coerced with `pyTruthy`.
    let lowerOperand (valueJson : Json) : PygenM (TSyntax `term) := do
      let code ← withPropCondition opProp (getCode valueJson `term)
      if conditionIsBoolean valueJson then pure code
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
  | _, _ => throwError s!"Unsupported syntax category for BoolOp node"

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
    let leftCode ← getCode leftJson `term
    let rightCode ← getCode rightJson `term
    compareApplyTerm op leftJson leftCode rightCode (rightJson := some rightJson)
  | _, _ => throwError s!"Unsupported syntax category for Compare node"

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
    if bodyIsNone && orelseIsNone then
      `(none)
    else if bodyIsNone then
      let orelseCode ← getCode orelseJson `term
      `(if $testCode then none else some $orelseCode)
    else if orelseIsNone then
      let bodyCode ← getCode bodyJson `term
      `(if $testCode then some $bodyCode else none)
    else
      let mut bodyCode ← getCode bodyJson `term
      let mut orelseCode ← getCode orelseJson `term
      -- Python is free to return an `int` from one arm and a `float` from the other; Lean unifies the
      -- two arms, so the integer one is widened to match.
      match isFloatyJson bodyJson, isFloatyJson orelseJson with
      | true, false => orelseCode ← widenToFloat orelseCode
      | false, true => bodyCode ← widenToFloat bodyCode
      | _, _ => pure ()
      -- In a contract one predicate arm forces both arms to `Prop`; Python reads the other arm as a
      -- truthiness test (`Ensures(r * 2 == s if len(d) % 2 == 0 else sorted(d)[k])`).
      if (← getPropCondition) && (← numericModeIsExact) then
        let t := mkIdent ``PastaLean.pyTruthy
        match conditionIsBoolean bodyJson, conditionIsBoolean orelseJson with
        | true, false => orelseCode ← `($t $orelseCode = true)
        | false, true => bodyCode ← `($t $bodyCode = true)
        | _, _ => pure ()
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
        `(← $codeStx:term)
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
