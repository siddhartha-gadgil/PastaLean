import PastaLean.Imports
import PastaLean.Codegen
import PastaLean.PyGens.Basic
import PastaLean.PyGens.Core.Utils
import PastaLean.PyGens.Core.Assign
import PastaLean.PyGens.UseCases.ControlFlow
import PastaLean.PyGens.UseCases.ListComp
import PastaLean.PyGens.UseCases.Match
import PastaLean.PyGens.UseCases.Exceptions
import PastaLean.PyVerify.AssertTactic
import PastaLean.PyVerify.Contracts
import PastaLean.PyGens.Transform.ClosureConvert
import PastaLean.PyGens.Transform.Desugar
import PastaLean.PyGens.Transform.GeneratorLower
import PastaLean.PyGens.Transform.Decorators

open Lean Meta Elab Term Qq Std

namespace PastaLean

open Lean.Parser.Term
open Std.Do  -- the `⦃⌜…⌝⦄ … ⦃⇓ … => …⦄` Hoare-triple notation used by the `while` (`pyWhile`) spec

/-!
  Translates Python function definitions and the remaining module-level glue.
  Feature-specific statement lowering lives in the smaller files under `PyGens/`.
-/

/-- Map a simple Python annotation JSON node to a Lean type term when we know a direct runtime type. -/
partial def functionArgTypeSyntax? (annotationJson : Json) : PygenM (Option (TSyntax `term)) := do
  let .ok nodeType := annotationJson.getObjValAs? String "node_type" | throwError
    s!"Function argument annotation is missing a 'node_type' field: {annotationJson}"
  match nodeType with
  | "Name" =>
      let .ok id := annotationJson.getObjValAs? String "id" | throwError
        s!"Function argument annotation is missing an 'id' field: {annotationJson}"
      match id with
      | "int" | "Int" => return some (mkIdent ``Int)
      | "bool" | "Bool" => return some (mkIdent ``Bool)
      | "str" | "String" => return some (mkIdent ``String)
      -- `float` → exact `ℚ` (default), `ℝ` under real-context (a real-marked param, set in
      -- `functionArgInfos`), or `Float` (`--mode run`). Real-context preserves container shape:
      -- `list[list[float]]` → `List (List ℝ)`, a scalar `float` → `ℝ`.
      | "float" | "Float" =>
          match ← getNumericMode with
          | .exact => return some (mkIdent (if (← getRealContext) then ``Real else ``Rat))
          | .approx => return some (mkIdent ``Float)
      | "Any" => return none -- let Lean handle the type inference for now
      -- A user class (`TreeNode`) or anything else this manual reader misses: fall back to the
      -- `TypeInfer` lowering, which handles class names (`.cls`) and `Optional`. A bare class name is
      -- run-suffixed here (`ListNode` → `ListNode'rn`) — `TypeInfer` is context-free and can't know.
      | _ =>
          match TypeInfer.ofAnnotation annotationJson with
          | .cls c => return some (mkIdent (← suffixIfUserName c).toName)
          | other => pyTypeSyntax? other
  | "Subscript" =>
      let .ok valueJson := annotationJson.getObjValAs? Json "value" | throwError
        s!"Function argument subscript annotation is missing a 'value' field: {annotationJson}"
      let .ok sliceJson := annotationJson.getObjValAs? Json "slice" | throwError
        s!"Function argument subscript annotation is missing a 'slice' field: {annotationJson}"
      -- Normalise `typing` container spellings to the builtin generic, so `Sequence[float]`,
      -- `Mapping[str,int]`, `FrozenSet[int]` all lower like `list`/`dict`/`set`.
      let container := match valueJson.getObjValAs? String "node_type", valueJson.getObjValAs? String "id" with
        | .ok "Name", .ok id =>
            match id with
            | "list" | "List" | "Sequence" | "MutableSequence" | "Iterable" | "Collection" => "list"
            | "dict" | "Dict" | "Mapping" | "MutableMapping" => "dict"
            | "set" | "Set" | "frozenset" | "FrozenSet" => "set"
            | other => other
        | _, _ => ""
      match container with
      -- Sets are an insertion-ordered array + hash index (`PyAPI/Sets.lean`): `set[T]` → `PySet T`.
      | "list" | "set" =>
          -- An explicit `List[Any]`/`Set[Any]` element has no runtime type of its own → `PyAny` (a
          -- boxed `List PyAny`), matching the bare-`list` param. Without this the whole ascription is
          -- dropped and the param stays a stuck metavariable.
          let elemTy? : Option (TSyntax `term) ← match ← functionArgTypeSyntax? sliceJson with
            | some e => pure (some e)
            | none =>
                if [some "Any", some "object"].contains (sliceJson.getObjValAs? String "id").toOption
                then pure (some (← `($(mkIdent ``PastaLean.PyAny)))) else pure none
          match elemTy? with
          -- The runnable (`approx`) twin backs an `array_ok`-marked `list` with `Array` for O(1)
          -- append/index (Perceus in-place reuse); the provable twin, sets, and un-marked lists stay
          -- `List`. Marked by the TypeInfer eligibility pass as `_seq: "array"` on this annotation node.
          | some elemTy =>
              if container == "set" then return some (← `(PastaLean.PySet $elemTy))
              let arrayBacked := container == "list"
                && (annotationJson.getObjValAs? String "_seq" == .ok "array")
                && (← getNumericMode) == .approx
              if arrayBacked then return some (← `(Array $elemTy))
              else return some (← `(List $elemTy))
          | none => return none
      -- `defaultdict`/`Counter` are backed by `PyDefaultDict`, not `Std.HashMap`.
      | "dict" | "defaultdict" =>
          match sliceJson.getObjValAs? String "node_type" with
          | .ok "Tuple" =>
              let .ok elts := sliceJson.getObjValAs? (Array Json) "elts" | throwError
                s!"Dictionary annotation tuple is missing an 'elts' field: {sliceJson}"
              match elts[0]?, elts[1]? with
              | some keyJson, some valJson =>
                  match ← functionArgTypeSyntax? keyJson, ← functionArgTypeSyntax? valJson with
                  | some keyTy, some valTy =>
                      if container == "defaultdict" then
                        return some (← `(Libraries.collections.PyDefaultDict $keyTy $valTy))
                      else return some (← `(Std.HashMap $keyTy $valTy))
                  | _, _ => return none
              | _, _ => return none
          | _ => return none
      -- `Callable[[A, B], R]` → the Lean arrow `A → B → R`. A function-typed parameter (a decorator's
      -- wrapped function, a `key=`/comparator arg) needs this so its applications elaborate.
      | "Callable" =>
          match sliceJson.getObjValAs? String "node_type", sliceJson.getObjValAs? (Array Json) "elts" with
          | .ok "Tuple", .ok elts =>
              match elts[0]?, elts[1]? with
              | some argsJson, some retJson =>
                  let some retTy ← functionArgTypeSyntax? retJson | return none
                  let argAnns := (argsJson.getObjValAs? (Array Json) "elts").toOption.getD #[]
                  let mut ty := retTy
                  for a in argAnns.reverse do
                    let some aTy ← functionArgTypeSyntax? a | return none
                    ty ← `($aTy → $ty)
                  return some ty
              | _, _ => return none
          | _, _ => return none
      -- `Optional[T]` and other containers this reader misses fall back to `TypeInfer` — via
      -- `seqAwareTypeSyntax?` so a class inside `Option`/a container is still run-suffixed
      -- (`Optional[ListNode]` → `Option ListNode'rn` in the run twin), not left bare.
      | _ => seqAwareTypeSyntax? annotationJson
  -- `X | None` (`Optional`) and forward-ref strings: `TypeInfer` handles them (run-suffixed).
  | _ => seqAwareTypeSyntax? annotationJson

/-- Read Python function parameters as Lean idents plus any simple type annotations we can preserve.
`heapRefTypes` (free-function paths under `--heap`): a container/object parameter is typed its HEAP
type (`Ref (List Int)` / `Ref C`) since callers pass it by reference; class-method/lambda callers
leave it `false` (they build their own arg types). -/
def functionArgInfos (json : Json) (heapRefTypes : Bool := false) :
    PygenM (Array (TSyntax `ident × Option (TSyntax `term))) := do
  let .ok args := json.getObjVal? "args" | throwError
    s!"FuncDef node does not have an 'args' field or it is not a JSON value: {json}"
  let .ok argsArray := args.getObjValAs? (Array Json) "args" | throwError
    s!"FuncDef args does not have an 'args' field or it is not a JSON value: {args}"
  let mut argInfos := #[]
  for arg in argsArray do
    let .ok argName := arg.getObjValAs? String "arg" | throwError
      s!"FuncDef argument does not have an 'arg' field or it is not a string: {arg}"
    -- A closure-promoted variable CELL param (`--heap`): its Lean type is `Ref (heapTypeSyntax ann)`
    -- — `Ref Int` for a scalar cell, `Ref (Ref (List Int))` for a container/object cell (one extra
    -- `Ref` over the ordinary heap type). The annotation rides on the arg (`annotation` or `_ty`).
    if (← getHeapMode) && arg.getObjValAs? Bool "_heap_cell_param" == .ok true then
      let annJson? : Option Json :=
        match jsonFieldOption arg "annotation" with
        | some a => if a.isNull then jsonFieldOption arg "_ty" else some a
        | none => jsonFieldOption arg "_ty"
      let pty := match annJson? with
        | some ann => TypeInfer.ofAnnotation ann
        | none => .int
      let cellTy ← `(PastaLean.Ref $(← heapTypeSyntax pty))
      argInfos := argInfos.push (mkIdent argName.toName, some cellTy)
      continue
    -- A container/object parameter (`--heap`, free-function path): passed by reference, so its type is
    -- its HEAP type (`Ref (List Int)` / `Ref C`). `.unknown` (object/Any) stays untyped (Lean infers);
    -- scalars fall through to the value logic below.
    if heapRefTypes && (← getHeapMode) then
      let annJson? : Option Json :=
        match jsonFieldOption arg "annotation" with
        | some a => if a.isNull then jsonFieldOption arg "_ty" else some a
        | none => jsonFieldOption arg "_ty"
      match annJson?.map TypeInfer.ofAnnotation with
      | some pty =>
          match pty with
          | .list _ | .set _ | .dict _ _ | .cls _ =>
              argInfos := argInfos.push (mkIdent argName.toName, some (← heapTypeSyntax pty))
              continue
          | _ => pure ()
      | none => pure ()
    -- A parameter the per-variable real-flow pass stamped `_real` receives an `ℝ` value at some
    -- call site → ascribe `ℝ` (exact mode), overriding the annotation. Everything else stays `ℚ`.
    let isRealParam := (← getNumericMode) == .exact && arg.getObjValAs? Bool "_real" == .ok true
    let ty? ← withRealContext isRealParam do
      -- An inference `_ty` override (a nullable node param widened `TreeNode` → `Optional[TreeNode]`)
      -- wins over the bare annotation — otherwise the emitted param would clash with the Option args
      -- the body recurses with. Only such widened params carry `_ty` alongside an annotation.
      match ← stampedTypeSyntax? arg with
      | some t => pure (some t)
      | none =>
        match jsonFieldOption arg "annotation" with
        -- Real-marked params lower their annotation under real-context so `float` → `ℝ` while the
        -- container shape is preserved (`list[list[float]]` → `List (List ℝ)`, scalar → `ℝ`).
        | some annotationJson =>
            -- An explicit `Any`/`object` that inference did not refine (no `_ty`) is dynamic: `PyAny`.
            if [some "Any", some "object"].contains (annotationJson.getObjValAs? String "id").toOption then
              pure (some (mkIdent ``PastaLean.PyAny))
            else functionArgTypeSyntax? annotationJson
        -- No annotation and no `_ty`: a bare `ℝ` if real, else untyped.
        | none => if isRealParam then pure (some (← `(Real))) else pure none
    argInfos := argInfos.push (mkIdent argName.toName, ty?)
  return argInfos

def functionBodyElems (json : Json) : PygenM (Array Json) := do
  let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
    s!"FuncDef node does not have a 'body' field or it is not a JSON value: {json}"
  return bodyElems

/-- The closure-promoted cell parameters of a function (`--heap`): each `_heap_cell_param` arg with
whether it is a container/object cell (`Ref (Ref T)`, registered so `heapContainerRef?` fires) vs a
scalar cell (`Ref τ`). Empty for ordinary functions, so callers pass it unconditionally. -/
def functionHeapCellParams (json : Json) : PygenM (Array (Name × Bool)) := do
  unless ← getHeapMode do return #[]
  let .ok args := json.getObjVal? "args" | return #[]
  let .ok argsArray := args.getObjValAs? (Array Json) "args" | return #[]
  let mut cells := #[]
  for arg in argsArray do
    if arg.getObjValAs? Bool "_heap_cell_param" == .ok true then
      if let .ok argName := arg.getObjValAs? String "arg" then
        let annJson? : Option Json :=
          match jsonFieldOption arg "annotation" with
          | some a => if a.isNull then jsonFieldOption arg "_ty" else some a
          | none => jsonFieldOption arg "_ty"
        let isContainer := match annJson?.map TypeInfer.ofAnnotation with
          | some (.list _) | some (.set _) | some (.dict _ _) | some (.cls _) => true
          | _ => false
        cells := cells.push (argName.toName, isContainer)
  return cells

/-- The container/object REFERENCE parameters of a function (`--heap`): each ordinary (non-cell) param
whose type is a mutable container (→ `none`, registered as a container-ref so `heapContainerRef?`
fires) or a user object of class `c` (→ `some c`, registered so `p.x` reads dereference). Empty for
ordinary functions and in value mode, so callers pass it unconditionally. -/
def functionHeapRefParams (json : Json) : PygenM (Array (Name × Option String)) := do
  unless ← getHeapMode do return #[]
  let .ok args := json.getObjVal? "args" | return #[]
  let .ok argsArray := args.getObjValAs? (Array Json) "args" | return #[]
  let mut refs := #[]
  for arg in argsArray do
    if arg.getObjValAs? Bool "_heap_cell_param" == .ok true then continue
    if let .ok argName := arg.getObjValAs? String "arg" then
      let annJson? : Option Json :=
        match jsonFieldOption arg "annotation" with
        | some a => if a.isNull then jsonFieldOption arg "_ty" else some a
        | none => jsonFieldOption arg "_ty"
      match annJson?.map TypeInfer.ofAnnotation with
      | some (.list _) | some (.set _) | some (.dict _ _) => refs := refs.push (argName.toName, none)
      | some (.cls c) => refs := refs.push (argName.toName, some c)
      | _ => pure ()
  return refs

/-- Whether the JSON references a library member that lowers to a `noncomputable` `ℝ`
transcendental (`math.exp`, `math.sqrt`, …). Used to mark a generated `def` as `noncomputable`
in exact mode — Lean rejects an unmarked `def` whose body transitively uses `Real.*`. -/
partial def jsonUsesRealTranscendental (json : Json) : Bool :=
  let directMatch :=
    match json.getObjValAs? String "library_module", json.getObjValAs? String "library_member" with
    | .ok m, .ok mem => (Libraries.pythonLibraryMapReal? m mem).isSome
    | _, _ => false
  -- `a ** <float-literal>` (e.g. `x ** 0.5` for a square root) resolves to `PyHPow Int Rat Real`
  -- (`rpow`), which is `noncomputable` in exact mode. An integer exponent (`x ** 2`) stays computable,
  -- so only a Constant with a non-zero decimal exponent (0.5, 2.0, …) fires this.
  let powReal :=
    json.getObjValAs? String "node_type" == .ok "BinOp"
    && json.getObjValAs? String "op" == .ok "pow"
    && (match (json.getObjVal? "right").toOption with
        | some r =>
            r.getObjValAs? String "node_type" == .ok "Constant"
            && (match (r.getObjVal? "value").toOption with
                | some (.num n) => n.exponent != 0
                | _ => false)
        | none => false)
  if directMatch || powReal then true
  else
    match json with
    | .arr elems => elems.toList.any jsonUsesRealTranscendental
    | .obj fields => fields.toList.any (fun (_, value) => jsonUsesRealTranscendental value)
    | _ => false

/-- Whether any body statement uses an `ℝ` transcendental, but only in exact numeric mode
(in `--mode run` the transcendentals stay computable `Float`, so no `noncomputable` is needed). -/
def bodyNeedsNoncomputable (bodyElems : Array Json) : PygenM Bool := do
  if (← getNumericMode) == .exact then
    return bodyElems.any jsonUsesRealTranscendental
  else
    return false

/-- Does `j` reference (as a `Name`) any id in `reg`? -/
partial def jsonRefsRegistered (reg : Std.HashSet String) (j : Json) : Bool :=
  (jsonNodeType? j == some "Name" &&
    (match j.getObjValAs? String "id" with | .ok s => reg.contains s | _ => false))
  || (match j with
      | .arr a => a.any (jsonRefsRegistered reg)
      | .obj kvs => kvs.toList.any (fun (_, v) => jsonRefsRegistered reg v)
      | _ => false)

/-- Whether the body calls a def already emitted `noncomputable` (a closure-converted helper reaching
`ℝ`, e.g. `is_prime` computing `int(a ** 0.5)`). Such a caller must itself be `noncomputable`. Only in
exact mode — the `'rn` run-twins are approx (`Float`, computable) and must never be marked. -/
def bodyCallsNoncomputable (bodyElems : Array Json) : PygenM Bool := do
  if (← getNumericMode) != .exact then return false
  let reg ← noncomputableDefRegistry.get
  if reg.isEmpty then return false
  return bodyElems.any (jsonRefsRegistered reg)

/-- Whether a type annotation mentions `float` anywhere (`float`, `list[float]`, `dict[_,float]`). -/
partial def annotationMentionsFloat (json : Json) : Bool :=
  if json.getObjValAs? String "node_type" == .ok "Name" then
    json.getObjValAs? String "id" == .ok "float" || json.getObjValAs? String "id" == .ok "Float"
  else
    (match (json.getObjVal? "slice").toOption with | some s => annotationMentionsFloat s | none => false)
    || (match (json.getObjValAs? (Array Json) "elts").toOption with
        | some es => es.any annotationMentionsFloat | none => false)

/-- Whether a return annotation is a SCALAR `float`/`Float` (a bare `Name`). Used for `retFloat`,
whose mixed int/float→ℚ coercion applies to a scalar float return ONLY — a `list[float]` return has
its elements coerce individually and its codomain must stay a list, never be ascribed scalar `ℚ`. -/
def annotationIsScalarFloat (json : Json) : Bool :=
  json.getObjValAs? String "node_type" == .ok "Name"
    && (json.getObjValAs? String "id" == .ok "float" || json.getObjValAs? String "id" == .ok "Float")

/-- A function's return annotation: the explicit `returns`, else the type `TypeInfer` inferred (`_ret_ty`). -/
def returnAnnotation? (json : Json) : Option Json :=
  (jsonFieldOption json "returns").orElse (fun _ => jsonFieldOption json "_ret_ty")

/-- Read a Python function return annotation when it maps cleanly to a Lean runtime type. -/
def functionReturnTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  -- A boxed function (returns disagree in type) returns `PyAny` regardless of any union annotation.
  if json.getObjValAs? Bool "_box_return" == .ok true then
    return some (mkIdent ``PastaLean.PyAny)
  -- A `_ret_float` body mixes `int` and `float` returns (`return 0` / `return ans` where `ans` is
  -- `float` from a `-inf` seed): its codomain is the mode float, overriding an `int` annotation, so
  -- both branches coerce (`(0 : ℚ)` and the float `ans`).
  if json.getObjValAs? Bool "_ret_float" == .ok true then
    return some (if (← getNumericMode) == .exact then mkIdent ``Rat else mkIdent ``Float)
  -- The explicit `returns` annotation wins; else the type inferred by `TypeInfer` (`_ret_ty`).
  match returnAnnotation? json with
  | some returnJson =>
      -- A declared `tuple[Any, int]`: its `Any` parts are boxed `PyAny` (see `lowerAgainstType`).
      let dyn := TypeInfer.ofAnnotation returnJson (anyDynamic := true)
      if dyn.boxesAny && dyn.isDeclared then return ← runAwareTypeSyntax? dyn
      -- In exact mode a `float`-involving return is left UNASCRIBED so Lean infers `ℚ` (a rational
      -- function) or `ℝ` (a transcendental one); a fixed `ℚ` would clash with an `ℝ` body. (The list
      -- return-mixing case that DOES need an ascription is handled in `optionalReturnAscription?`.)
      if (← getNumericMode) == .exact && annotationMentionsFloat returnJson then
        pure none
      else
        functionArgTypeSyntax? returnJson
  | none => pure none

/-- The `Option X` codomain ascription for a function whose inferred/annotated return is `Optional[X]`
(`return None` in one branch, `return <x>` in another — e.g. `string_to_md5` returns `None` for the
empty string, else the digest `str`). Pins the monadic/`Id.run` (or pure `if`) codomain to the CONCRETE
`Option X` so the `None` branch and the bare-`x` branch (which Lean coerces to `some x`) unify, instead
of the first `return None` fixing the codomain to `Option ?α`. A `.opt .unknown` return (the value
branch's element type is not inferred) yields `none` — the coercion needs a concrete target, so an
`Option _` hole would not fire. Complements `returnClassName?` (the `Optional[C]` *class* case). -/
def optionalReturnAscription? (json : Json) : PygenM (Option (TSyntax `term)) := do
  match returnAnnotation? json with
  | some r => match TypeInfer.ofAnnotation r with
      | .opt _ => functionReturnTypeSyntax? json
      -- A `list`/`set` return whose element is `float` pins the codomain (`List ℚ`/`List Float`), so a
      -- body mixing `return [1]` (List Int) and `return ans` (List ℚ) unifies — the int list coerces
      -- (`CoeTail (List Int) (List Rat)`) instead of the first int return fixing `List ℤ` (Tri). But NOT
      -- for a transcendental (`ℝ`) body — its list is `List ℝ`, and a fixed `List ℚ` would clash (eg1).
      | .list .float | .set .float =>
          -- Ascribe the list[float] annotation DIRECTLY (`functionArgTypeSyntax?`, bypassing the
          -- exact-mode float-unascribe in `functionReturnTypeSyntax?`) → `List ℚ`/`List Float`. NOT for
          -- a transcendental (`ℝ`) body — its list is `List ℝ`, and a fixed `List ℚ` would clash.
          let body := (json.getObjValAs? (Array Json) "body").toOption.getD #[]
          if (← bodyCallsNoncomputable body) || (← bodyNeedsNoncomputable body) then pure none
          else functionArgTypeSyntax? r
      | _ => pure none
  | none => pure none

/-- Whether some `return` in the body (outside nested definitions) satisfies `p` on its value (`none`
for a bare `return`). -/
partial def bodyAnyReturn (p : Option Json → Bool) : Json → Bool
  | .arr xs => xs.any (bodyAnyReturn p)
  | j@(.obj fs) =>
      match j.getObjValAs? String "node_type" with
      | .ok "FunctionDef" | .ok "Lambda" | .ok "ClassDef" => false
      | .ok "Return" => p (j.getObjVal? "value").toOption
      | _ => fs.toList.any fun (_, v) => bodyAnyReturn p v
  | _ => false

/-- A returned value that is `None`: absent (bare `return`), `null`, or the constant `None`. -/
def isNoneReturn : Option Json → Bool
  | none | some .null => true
  | some v => v.getObjValAs? String "node_type" == .ok "Constant" && (v.getObjVal? "value").toOption == some .null

/-- Whether some `return` in the body (outside nested definitions) returns a value. -/
def bodyHasValueReturn : Json → Bool := bodyAnyReturn (!isNoneReturn ·)

/-- Can this statement tree `return None` (explicitly or bare), outside nested scopes? -/
def bodyReturnsNone : Json → Bool := bodyAnyReturn isNoneReturn

/-- The user-class name a node-returning function's annotation names (`TreeNode` or
`Optional[TreeNode]`), if any. Such a function mixes bare `return TreeNode(...)`, a nullable cursor
`return slow`, and `return None` base cases — all `Optional[C]` in Python — so its non-recursive def
must ASCRIBE the codomain as `Option C` (never bare `C`): the bare arm coerces via `Coe C (Option C)`,
the Option arms match. Ascribing bare `C` (or letting Lean pin the codomain to the first return seen)
makes the other arms clash. Gated to node returns so other non-recursive defs (whose unascribed body
type is fine, e.g. `bool`-widening-to-`int`) stay untouched. -/
def returnClassName? (json : Json) : Option String :=
  match returnAnnotation? json with
  | some r => match TypeInfer.ofAnnotation r with
    | .opt (.cls c) => some c
    -- A bare class return is `Option C` only when the body can return `None` (a node helper's base
    -- case); `d1 - d2` returning a `timedelta` stays a `timedelta`.
    | .cls c => if bodyReturnsNone ((json.getObjVal? "body").toOption.getD Json.null) then some c else none
    | _ => none
  | none => none

/-- Return-type ascription for a RECURSIVE function: the annotated/inferred type, or `Unit` for a
genuinely void body (no `return e` anywhere — only bare `return`/fall-through). A recursive
`partial def` with an unconstrained return type otherwise leaves `Inhabited ?m` stuck. Guarded by
`hasValuedReturn` so a state-threaded helper (which gains a valued `return (…threaded…)` and a
concrete tuple return type) is never mis-pinned to `Unit`. -/
def recursiveReturnTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  -- A node-returning recursive helper (`build(i,j) -> TreeNode` that also `return None`s at its base
  -- case) has codomain `Option C`, never bare `C` — same as the non-recursive path.
  if let some c := returnClassName? json then
    if let some codom ← runAwareTypeSyntax? (TypeInfer.PyType.opt (.cls c)) then
      return some codom
  match ← functionReturnTypeSyntax? json with
  | some rt => return some rt
  | none =>
    -- Check the BODY, not the def node: `hasValuedReturn` short-circuits to `false` on a
    -- `FunctionDef` (its job is to skip *nested* defs), so passing `json` here always reads void.
    let body := (json.getObjVal? "body").toOption.getD Json.null
    if hasValuedReturn body then return none else return some (← `(Unit))

/-- Check whether a JSON subtree references a given variable name. -/
partial def jsonReferencesName (json : Json) (target : String) : Bool :=
  let directMatch :=
    match json.getObjValAs? String "node_type", json.getObjValAs? String "id" with
    | .ok "Name", .ok id => id == target
    | _, _ => false
  if directMatch then
    true
  else
    match json with
    | .arr elems => elems.toList.any (fun elem => jsonReferencesName elem target)
    | .obj fields => fields.toList.any (fun (_, value) => jsonReferencesName value target)
    | _ => false

/-- Does assigning to this target node mutate the variable `name`? Covers a bare `Name`, tuple/
list unpacking, `Starred`, and a `Subscript`/`Attribute` whose base (recursively) is `name`
(`a[i] = …` reassigns the immutable-value container `a`, so it mutates `a`). -/
partial def assignTargetMutatesName (target : Json) (name : String) : Bool :=
  match target.getObjValAs? String "node_type" with
  | .ok "Name" => target.getObjValAs? String "id" == .ok name
  | .ok "Tuple" | .ok "List" =>
      match target.getObjValAs? (Array Json) "elts" with
      | .ok elts => elts.any (fun e => assignTargetMutatesName e name)
      | _ => false
  | .ok "Starred" | .ok "Subscript" | .ok "Attribute" =>
      (target.getObjVal? "value").toOption.any (fun v => assignTargetMutatesName v name)
  | _ => false

/-- Python list/set/dict methods that mutate their receiver in place. Codegen lowers each as a
reassignment of the (immutable-value) receiver, so a parameter used as the receiver of one of
these must be shadowed by `let mut`. Over-inclusion is harmless (an unused shadow). -/
def inPlaceMutatingMethods : List String :=
  [ "append", "extend", "insert", "remove", "pop", "clear", "sort", "reverse",
    "add", "discard", "update", "setdefault", "popitem",
    "intersection_update", "difference_update", "symmetric_difference_update",
    "appendleft", "popleft", "appendright" ]

/-- Is `name` mutated (an `=`, augmented `op=`, annotated assignment, or `for` target — including
unpacking and subscript-assignment) anywhere in this subtree, without descending into a nested
function/lambda/class scope (which rebinds the name in a separate scope)? Used to decide which
function parameters must be shadowed by `let mut` so the monadic body can reassign them. -/
partial def jsonMutatesName (json : Json) (name : String) : Bool :=
  match json with
  | .arr elems => elems.toList.any (fun e => jsonMutatesName e name)
  | .obj fields =>
      match json.getObjValAs? String "node_type" with
      | .ok "FunctionDef" | .ok "AsyncFunctionDef" | .ok "Lambda" | .ok "ClassDef" => false
      | nodeType =>
          let mutatedHere :=
            match nodeType with
            | .ok "For" =>
                (json.getObjVal? "target").toOption.any (fun t => assignTargetMutatesName t name)
                -- `for x in name: <mutate x in place>` writes each element back into `name`, so it
                -- mutates `name` and the container must be a `let mut` — see `forElemWriteback?`.
                || (match (json.getObjVal? "iter").toOption, (json.getObjVal? "target").toOption,
                         (json.getObjValAs? (Array Json) "body").toOption with
                    | some it, some tgt, some body =>
                        forElemWriteback? it tgt body == some name
                    | _, _, _ => false)
            | .ok "Assign" | .ok "AugAssign" | .ok "AnnAssign" =>
                (json.getObjVal? "target").toOption.any (fun t => assignTargetMutatesName t name)
            | .ok "Delete" =>
                -- `del name[i]` rebuilds and reassigns the container, so it mutates `name`.
                match (json.getObjVal? "targets").toOption.bind (·.getArr?.toOption) with
                | some targets => targets.any (fun t => assignTargetMutatesName t name)
                | none => false
            | .ok "Call" =>
                -- An in-place mutating method (`name.append(x)`, `name.add(x)`, …) is lowered as a
                -- reassignment of the receiver, so it mutates `name`. Likewise a heapq mutating
                -- *module function* (`heapq.heappush(name, x)`, `heapify(name)`, `heappop(name)`)
                -- reassigns its FIRST ARGUMENT.
                match (json.getObjVal? "func").toOption with
                | some funcJson =>
                    (funcJson.getObjValAs? String "node_type" == .ok "Attribute"
                      && (match funcJson.getObjValAs? String "attr" with
                          | .ok m => inPlaceMutatingMethods.contains m
                          | _ => false)
                      && (funcJson.getObjVal? "value").toOption.any
                          (fun recv => assignTargetMutatesName recv name))
                    || ((libraryMutatorOf? funcJson).isSome
                      && (match (json.getObjValAs? (Array Json) "args").toOption with
                          | some args => args[0]?.any (fun a => assignTargetMutatesName a name)
                          | none => false))
                | none => false
            | _ => false
          mutatedHere || fields.toList.any (fun (_, v) => jsonMutatesName v name)
  | _ => false

/-- `(param-name, class-name)` for each node param TypeInfer marked `_mut_opt` (annotated `c` but
reassigned from `.next`/`.left`, so nullable) — codegen seeds its mut shadow as `Option c`. -/
def optMutParamsOf (json : Json) : Array (String × String) :=
  (((json.getObjVal? "args").toOption.bind
      (·.getObjValAs? (Array Json) "args" |>.toOption)).getD #[]).filterMap fun a =>
    match a.getObjValAs? String "arg", a.getObjValAs? String "_mut_opt" with
    | .ok n, .ok c => some (n, c)
    | _, _ => none

/-- Emit a `let mut p := p` shadow for each parameter the body reassigns (a Lean binder is
immutable, but Python freely mutates params — `i -= 1`, `n >>= 1`, `a.append(x)`). Registers each as
a mutable var so later reassignments resolve against the shadow. Shared by the plain monadic emission
(`functionValueSyntax`) and the contracted Track M/`Id _` emission, so both handle param mutation. -/
def mutatedParamPrelude (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (bodyElems : Array Json) (optMutParams : Array (String × String) := #[]) :
    PygenM (Array (TSyntax `doElem)) := do
  let mut paramPrelude : Array (TSyntax `doElem) := #[]
  for (argIdent, _) in argInfos do
    if bodyElems.any (fun b => jsonMutatesName b argIdent.getId.toString) then
      addVar argIdent.getId
      -- The shadow below is a real `let mut`, so record it as mutable: a later type-changing rebind
      -- (`s = list(s)`) must SSA-rename rather than illegally re-`let mut` the same name.
      setMutVar argIdent.getId
      -- A node param the body treats as nullable (`while head; head = head.next`, marked `_mut_opt` by
      -- TypeInfer) seeds its mut shadow as `Option c` (`some p`), so `Option`-unwrap field access and
      -- truthiness line up while the param itself stays a plain `c` (callers unaffected).
      match optMutParams.find? (·.1 == argIdent.getId.toString) with
      | some (_, cls) =>
          let clsId := mkIdent (← suffixIfUserName cls).toName
          paramPrelude := paramPrelude.push
            (← `(doElem| let mut $argIdent:ident : Option $clsId := some $argIdent))
      | none =>
          paramPrelude := paramPrelude.push (← `(doElem| let mut $argIdent:ident := $argIdent))
  return paramPrelude

/-- Wrap a function body as `((do <prelude> <body>) : <monad> <codomain>)`, lambda-abstracting the
params unless the function is nullary. Shared by every effectful monad (`PyProofM`/`PyExcept`/`IO`/
heap) — they differ only in the monad term. -/
def emitMonadicFunctionDef (monad effCodomain : TSyntax `term) (paramPrelude : Array (TSyntax `doElem))
    (bodyElems : Array Json) (argInfos : Array (TSyntax `ident × Option (TSyntax `term))) :
    PygenM (TSyntax `term) := do
  let bodyStxArray ← monadicFunctionBodySyntax bodyElems
  let mut body ← `(((do
        $[$paramPrelude:doElem]*
        $[$bodyStxArray:doElem]*) : $monad $effCodomain))
  for (argIdent, ty?) in argInfos.toList.reverse do
    body ← match ty? with
      | some ty => `(fun ($argIdent : $ty) ↦ $body)
      | none => `(fun $argIdent ↦ $body)
  pure body

/-- Build the Lean value for a Python function body, using a pure term when possible and
falling back to `do` notation for effectful bodies. This helper is reused for top-level
definitions, nested local functions, and `Head_FunctionDef` threading.

The body is lowered against a fresh variable set (`withFreshVariables`) so locals declared
inside a nested function do not leak into the enclosing scope's `let`/`let mut` tracking — a
leak would otherwise cause a later same-named outer assignment to be emitted as a reassignment
of a variable that was never declared `let mut`. -/
def functionValueSyntax (argInfos : Array (TSyntax `ident × Option (TSyntax `term))) (bodyElems : Array Json)
    (boxReturn : Bool := false) (retFloat : Bool := false) (optMutParams : Array (String × String) := #[])
    (heapCellParams : Array (Name × Bool) := #[])
    (heapRefParams : Array (Name × Option String) := #[])
    (retAscription : Option (TSyntax `term) := none)
    (binderArgInfos : Array (TSyntax `ident × Option (TSyntax `term)) := #[]) :
    PygenM (TSyntax `term) := withFreshVariables do
  -- Postcondition markers (`Ensures`, `Result()`-bearing `Assert`) are verification-only and have no
  -- runtime lowering, so they must never reach the emitted body — the spec theorem is built
  -- separately from the unstripped source. Strip here so EVERY monad path (pure or effectful) is
  -- covered uniformly; without it an effectful body leaks `Result()` as an unsupported member.
  let bodyElems := stripResultMarkers bodyElems
  -- Closure-promoted cell params (`--heap`): register so body reads/mutations deref them (one
  -- `readRefM`) and container cells feed `heapContainerRef?`. Function-scoped via `withFreshVariables`.
  for (nm, isContainer) in heapCellParams do
    if isContainer then registerHeapContainerCell nm else registerHeapScalarCell nm
  -- Container/object reference params (`--heap`): a container is a `Ref (List …)` (register so
  -- `.append`/`len`/`[]`/iteration dereference), an object is a `Ref C` (register its class so `p.x`
  -- reads dereference). Function-scoped via `withFreshVariables`.
  for (nm, cls?) in heapRefParams do
    match cls? with
    | some cls => registerHeapVarClass nm cls
    | none => registerHeapVarContainer nm
  let usesExceptions := bodyNeedsExceptionMonad bodyElems
  let usesRealIO := bodyNeedsIOMonad bodyElems
  let useProofMonad ← shouldUseProofMonad
  -- In proof mode (exact + wanting provable IO), use PyProofM for both exceptions and IO
  let usesProofExceptions := useProofMonad && usesExceptions
  let usesProofIO := useProofMonad && usesRealIO
  -- In exact mode without proof monad, exceptions without real IO can use the pure PyExceptId monad
  let usesPureExceptions := !useProofMonad && (← getNumericMode) == .exact && usesExceptions && !usesRealIO
  let mkLambda (body : TSyntax `term) : PygenM (TSyntax `term) := do
    let mut result := body
    for (argIdent, ty?) in argInfos.toList.reverse do
      result ← match ty? with
        | some ty => `(fun ($argIdent : $ty) ↦ $result)
        | none => `(fun $argIdent ↦ $result)
    pure result
  -- A Lean function parameter is an immutable binder, but Python lets a body reassign or
  -- augment its parameters (`i -= 1`, `a[k] = v`). Each mutated parameter gets a `let mut p := p`
  -- shadow at the top of the (monadic) body, then reassignments resolve against the mutable shadow.
  -- Pure bodies never mutate, so this prelude is empty for them. A `--heap` cell/ref param is already
  -- a `Ref` (mutated through `writeRefM`/`modifyRefM`), so exclude it — a value shadow would rebind
  -- the name to a plain value.
  -- `binderArgInfos`: params bound by `def` binders (not lambdas) still need their mutation shadows.
  let valueArgInfos := (argInfos ++ binderArgInfos).filter fun (argIdent, _) =>
    !(heapCellParams.any (·.1 == argIdent.getId)) && !(heapRefParams.any (·.1 == argIdent.getId))
  let paramPrelude ← mutatedParamPrelude valueArgInfos bodyElems optMutParams
  -- The monad codomain: `PyAny` when the returns disagree (`_box_return`), else a hole for Lean to
  -- infer. Without this an effectful boxed function would keep `_`, and Lean would fix the monad's
  -- type from the first `return` — forcing e.g. `Float`, so a later `return 0` (`ℤ`) fails to match.
  -- `retAscription` pins the codomain when the returns need a common type Lean can't infer from the
  -- first `return` — notably an `Optional[X]` return (`return None` in one branch, `return x` in
  -- another): ascribe `Option X` so the `None` branch and the bare-`x` branch (via `Coe X (Option X)`)
  -- unify instead of the first `return None` fixing the monad to `Option ?α`.
  let effCodomain : TSyntax `term ← if boxReturn then `(PastaLean.PyAny)
    else match retAscription with | some t => pure t | none => `(_)
  -- Heap tier (`--heap`): a body that touches the heap runs in `HeapM Val` (or, with IO, the
  -- `PyHeapIO`/`PyHeapProofM` stack). Takes precedence — `HeapM`'s error dimension is `PyException`,
  -- so it already subsumes exceptions. Codomain is ascribed to the body so a `_` return can infer.
  -- A body that only mutates a captured cell ref or a container/object ref param carries no heap
  -- marker, so `needsHeapMonad` alone misses it — force the heap tier when this function takes cell
  -- or reference params.
  if (← needsHeapMonad bodyElems) ||
      ((← getHeapMode) && (heapCellParams.size > 0 || heapRefParams.size > 0)) then
    let heapVal := mkIdent `Val
    let monad ← if usesRealIO then
        if useProofMonad then `($(mkIdent ``PastaLean.PyHeapProofM) $heapVal)
        else `($(mkIdent ``PastaLean.PyHeapIO) $heapVal)
      else `($(mkIdent ``PastaLean.HeapM) $heapVal)
    return ← emitMonadicFunctionDef monad effCodomain paramPrelude bodyElems argInfos
  -- Proof mode → `PyProofM`; exact-mode pure exceptions → `PyExceptId`; exceptions (+IO) → `PyExcept`;
  -- plain IO → `IO`. All four wrap the body identically save the monad, so share `emitMonadicFunctionDef`.
  if usesProofExceptions || usesProofIO then
    emitMonadicFunctionDef (mkIdent ``PastaLean.ProofMode.PyProofM) effCodomain paramPrelude bodyElems argInfos
  else if usesPureExceptions then
    emitMonadicFunctionDef (mkIdent ``PastaLean.PyExceptId) effCodomain paramPrelude bodyElems argInfos
  else if usesExceptions then
    emitMonadicFunctionDef (mkIdent ``PastaLean.PyExcept) effCodomain paramPrelude bodyElems argInfos
  else if usesRealIO then
    emitMonadicFunctionDef (mkIdent ``IO) effCodomain paramPrelude bodyElems argInfos
  else
    -- A boxed function's returns disagree in type, so ascribe the result to `PyAny`; each branch
    -- then coerces (`return 1` / `return "neg"` both become `PyAny`). A `retFloat` (float-returning,
    -- non-`ℝ`) function instead pins the result to `ℚ`/`Float`, so a `return <int>` mixed with a
    -- `return <float>` all coerce rather than the first int return fixing the type to `ℤ`.
    let boxTy := mkIdent ``PastaLean.PyAny
    let floatTy? : Option (TSyntax `term) ←
      if retFloat then
        if (← getNumericMode) == .exact then
          -- A real-valued body (`round(x ** 0.5, 2)` — an irrational root) is `ℝ` in the exact twin,
          -- not `ℚ`; ascribing `ℚ` over an `ℝ` result would clash.
          pure (some (if (← bodyNeedsNoncomputable bodyElems) then mkIdent ``Real else mkIdent ``Rat))
        else pure (some (mkIdent ``Float))
      else pure none
    -- `show T from body`, not `(body : T)`: a pure body that begins with a comment/statement `let`
    -- (`let __PastaLean_comment := (); …`) re-parses wrong under a trailing `: T` ascription
    -- ("expected ';' or line break"); `show … from` takes the whole `let`-expression as its argument.
    let ascribeResult (body : TSyntax `term) : PygenM (TSyntax `term) :=
      if boxReturn then `((show $boxTy from $body))
      else match floatTy? with
        | some t => `((show $t from $body))
        | none => match retAscription with
          | some t => `((show $t from $body))
          -- no `return` with a value: the function returns `None` (an `Id.run do` loop body would
          -- otherwise leave a universe-polymorphic `PUnit` for every caller to pin)
          | none => if bodyHasValueReturn (Json.arr bodyElems) then pure body else `((show Unit from $body))
    try
      let bodyStx ← ascribeResult (← pureFunctionBodySyntax bodyElems)
      if argInfos.isEmpty then
        pure bodyStx
      else
        mkLambda bodyStx
    catch e =>
      IO.eprintln s!"Could not generate pure function term: {← e.toMessageData.toString}"
      let bodyStxArray ← monadicFunctionBodySyntax bodyElems
      let idRunIdent := mkIdent ``Id.run
      let runBody ← ascribeResult (← `($idRunIdent do
            $[$paramPrelude:doElem]*
            $[$bodyStxArray:doElem]*))
      if argInfos.isEmpty then
        pure runBody
      else
        mkLambda runBody

/-- Build a lambda-wrapped monadic body term without adding an inner effect cast. -/
def functionMonadicValueNoCast (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (bodyElems : Array Json) : PygenM (TSyntax `term) := do
  let prelude ← mutatedParamPrelude argInfos bodyElems
  let bodyStxArray ← monadicFunctionBodySyntax bodyElems
  let elems := prelude ++ bodyStxArray
  let mut result ← `(do
    $[$elems:doElem]*)
  for (argIdent, ty?) in argInfos.toList.reverse do
    result ← match ty? with
      | some ty => `(fun ($argIdent : $ty) ↦ $result)
      | none => `(fun $argIdent ↦ $result)
  pure result

/-- Python parameter defaults (`args.defaults`, aligned to the TRAILING params). -/
def functionParamDefaults (json : Json) : Array Json :=
  ((json.getObjVal? "args").toOption.bind
    (fun a => (a.getObjValAs? (Array Json) "defaults").toOption)).getD #[]

/-- Bracketed `def` binders for the params, with `optParam` defaults where Python provides one
(`def f(a, b=10)` → `(a : _) (b : _ := 10)`), so a call with fewer args (`f(5)`) applies the default
instead of being a partial application. `none` when there are no defaults (callers keep the plain
lambda form). Pair with a body built from EMPTY `argInfos` (un-wrapped, referencing the params). -/
def functionParamBinders? (json : Json) (argInfos : Array (TSyntax `ident × Option (TSyntax `term))) :
    PygenM (Option (Array (TSyntax ``Lean.Parser.Term.bracketedBinder))) := do
  let defaults := functionParamDefaults json
  if defaults.isEmpty then return none
  let offset := argInfos.size - defaults.size
  let binders ← (Array.range argInfos.size).mapM fun i => do
    let (argIdent, ty?) := argInfos[i]!
    let tyStx ← match ty? with | some t => pure t | none => `(_)
    if i ≥ offset then
      let dCode ← getCode defaults[i - offset]! `term
      `(Lean.Parser.Term.bracketedBinderF| ($argIdent : $tyStx := $dCode))
    else
      `(Lean.Parser.Term.bracketedBinderF| ($argIdent : $tyStx))
  return some binders

/-- Build a function type like `A → B → IO _` when every argument type is known. -/
def functionArrowTypeSyntax? (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (codomain : TSyntax `term) : PygenM (Option (TSyntax `term)) := do
  let mut result := codomain
  for (_, ty?) in argInfos.toList.reverse do
    match ty? with
    | some ty =>
        result ← `($ty → $result)
    | none =>
        return none
  return some result

/-- The effect monad of a non-heap function body, or `none` when it is pure. Exceptions take precedence
over `IO`; proof mode uses `PyProofM`, exact mode without proof `PyExceptId`, run mode `PyExcept`. -/
def effectMonad? (bodyElems : Array Json) : PygenM (Option (TSyntax `term)) := do
  let usesRealIO := bodyNeedsIOMonad bodyElems
  let usesExceptions := bodyNeedsExceptionMonad bodyElems
  let useProofMonad ← shouldUseProofMonad
  if useProofMonad && (usesExceptions || usesRealIO) then
    return some (mkIdent ``PastaLean.ProofMode.PyProofM)
  else if (← getNumericMode) == .exact && usesExceptions && !usesRealIO then
    return some (mkIdent ``PastaLean.PyExceptId)
  else if usesExceptions then
    return some (mkIdent ``PastaLean.PyExcept)
  else if usesRealIO then
    return some (mkIdent ``IO)
  else
    return none

/--
For top-level effectful defs, prefer putting the effect in the signature instead of on
the body cast when the argument types are known.
-/
def functionCommandWithEffectSignature? (nameIdent : TSyntax `ident)
    (argInfos : Array (TSyntax `ident × Option (TSyntax `term))) (json : Json)
    (noncomp : Bool := false) :
    PygenM (Option (TSyntax `command)) := do
  -- Strip verification-only postcondition markers: `Result()` has no runtime lowering, so an
  -- effectful body (this path handles the IO/exception twins) would otherwise leak it as an
  -- unsupported member. The spec theorem is built from the unstripped source elsewhere.
  let bodyElems := stripResultMarkers (← functionBodyElems json)
  -- Heap functions run in `HeapM Val` with the codomain ascribed to the body (a `_` return type in
  -- an explicit `def` header can't be inferred); let `functionValueSyntax`'s heap tier build them.
  -- A function heap-tier ONLY via a container/object ref param carries no body heap marker, so also
  -- defer when it takes reference params.
  if (← needsHeapMonad bodyElems) || (← functionHeapRefParams json).size > 0 then return none
  let returnTy? ← functionReturnTypeSyntax? json
  -- Params with Python defaults go on the signature as `optParam` binders; otherwise the whole
  -- effect type is an arrow (`A → B → M R`) and the body is lambda-wrapped as before.
  let binders? ← functionParamBinders? json argInfos
  -- Recursion through an effect is not structural in general (`_encode` recursing over a list's
  -- items), so a self-recursive effectful def is `partial`, like the pure path.
  let isRec := match json.getObjValAs? String "name" with
    | .ok n => bodyElems.any (jsonReferencesName · n)
    | .error _ => false
  let mkDefFor : TSyntax `term → PygenM (Option (TSyntax `command)) := fun codomain => do
    match binders? with
    | some binders =>
        let prelude ← mutatedParamPrelude argInfos bodyElems
        let bodyStxArray ← monadicFunctionBodySyntax bodyElems
        let elems := prelude ++ bodyStxArray
        let body ← `(do
          $[$elems:doElem]*)
        match noncomp, isRec with
        | true, true => return some (← `(command| noncomputable partial def $nameIdent $binders* : $codomain := $body))
        | true, false => return some (← `(command| noncomputable def $nameIdent $binders* : $codomain := $body))
        | false, true => return some (← `(command| partial def $nameIdent $binders* : $codomain := $body))
        | false, false => return some (← `(command| def $nameIdent $binders* : $codomain := $body))
    | none =>
        match ← functionArrowTypeSyntax? argInfos codomain with
        | some fullTy =>
            let valueStx ← functionMonadicValueNoCast argInfos bodyElems
            match noncomp, isRec with
            | true, true => return some (← `(command| noncomputable partial def $nameIdent : $fullTy := $valueStx))
            | true, false => return some (← `(command| noncomputable def $nameIdent : $fullTy := $valueStx))
            | false, true => return some (← `(command| partial def $nameIdent : $fullTy := $valueStx))
            | false, false => return some (← `(command| def $nameIdent : $fullTy := $valueStx))
        | none => return none
  let withRet (mkCodomain : TSyntax `term → PygenM (TSyntax `term)) : PygenM (Option (TSyntax `command)) := do
    match returnTy? with
    | none => return none
    | some retTy => mkDefFor (← mkCodomain retTy)
  match ← effectMonad? bodyElems with
  | some m => withRet (fun retTy => `($m $retTy))
  | none => return none

/-- A comment, a leading `DocString`, or a bare string-literal `Expr` (a docstring in NON-leading
position, e.g. after a `Requires`). All are no-ops that must be filtered before contract-shape
analysis, or they wrongly knock a pure function out of the straight-line Track-P shape. -/
def isDocstringLike (s : Json) : Bool :=
  jsonNodeType? s == some "Comment" || jsonNodeType? s == some "DocString"
    || (jsonNodeType? s == some "Expr"
        && ((s.getObjVal? "value").toOption.any (fun v =>
              v.getObjValAs? String "node_type" == .ok "Constant"
              && (v.getObjVal? "value" |>.toOption.bind (·.getStr?.toOption)).isSome)))

/-- A single theorem-shaped obligation → `(hypotheses, conclusion-test)`. A bare `assert C` gives
`(#[], C)`; `if H: assert C` (no `else`, body a lone assert) gives the guard's conjuncts and `C` (a
conjunction `H1 and H2` splits into separate hypotheses, so the prover gets named hyps). `none`
otherwise. This is the per-statement half of `theoremShape?`; add new obligation forms here. -/
def obligationShape? (stmt : Json) : Option (Array Json × Json) :=
  match jsonNodeType? stmt with
  | some "Assert" => (stmt.getObjValAs? Json "test").toOption.map (fun t => (#[], t))
  | some "If" =>
      let isSubst := fun (s : Json) => !isDocstringLike s
      let body := ((stmt.getObjValAs? (Array Json) "body").toOption.getD #[]).filter isSubst
      let orelse := (stmt.getObjValAs? (Array Json) "orelse").toOption.getD #[]
      if orelse.isEmpty && body.size == 1 && jsonNodeType? body[0]! == some "Assert" then
        match stmt.getObjValAs? Json "test", body[0]!.getObjValAs? Json "test" with
        | .ok hyp, .ok concl =>
            let hyps :=
              if jsonNodeType? hyp == some "BoolOp" && hyp.getObjValAs? String "op" == .ok "and" then
                (hyp.getObjValAs? (Array Json) "values").toOption.getD #[hyp]
              else #[hyp]
            some (hyps, concl)
        | _, _ => none
      else none
  | _ => none

/-- The promotable theorem shape of a *pure* function body: zero or more pure `let`-bindings (fresh
distinct simple names — no reassignment or parameter mutation) followed by exactly ONE obligation
(`obligationShape?`). Returns `(lets, hypotheses, conclusion)`, or `none` when the body is monadic
(IO / `raise` / `try`), has a loop / mutation / early return, or isn't `let`s-then-one-obligation.
Single source of truth for assert→theorem promotion: monadic bodies can never match, since they
carry an IO/except effect or a non-`Assign` statement before the obligation. -/
def theoremShape? (paramNames : Array String) (body : Array Json) (substantive : Array Json) :
    Option (Array Json × Array Json × Json) := Id.run do
  if substantive.isEmpty then return none
  if bodyNeedsIOMonad body || bodyNeedsExceptionMonad body then return none
  let lets := substantive.pop
  let last := substantive[substantive.size - 1]!
  let mut seen : Array String := #[]
  for s in lets do
    if jsonNodeType? s != some "Assign" then return none
    let .ok target := s.getObjVal? "target" | return none
    if jsonNodeType? target != some "Name" then return none
    let .ok tname := target.getObjValAs? String "id" | return none
    if paramNames.contains tname || seen.contains tname then return none
    seen := seen.push tname
  match obligationShape? last with
  | some (hyps, concl) => return some (lets, hyps, concl)
  | none => return none

/-! ### `while`-loop verification via `pyWhile` -/

/-- Projection of the `idx`-th component (0-based) of an `n`-tuple `base`: `base.1`, `base.2.1`, …, with
the last component being the full `.2`-chain (Lean tuples are right-nested). `n ≤ 1` → `base` itself. -/
partial def whileTupleProj (base : TSyntax `term) (idx n : Nat) : PygenM (TSyntax `term) := do
  if n ≤ 1 then return base
  let mut t := base
  for _ in [0:idx] do t ← `($t.2)
  if idx == n - 1 then return t else `($t.1)

/-- Right-nested tuple `(e₀, e₁, …, e_{k-1})` from `elems` (matching `whileTupleProj`). -/
def whileNestedTuple (elems : Array (TSyntax `term)) : PygenM (TSyntax `term) := do
  if elems.isEmpty then return (← `(()))
  let mut acc := elems[elems.size - 1]!
  for i in [0:elems.size - 1] do
    let e := elems[elems.size - 2 - i]!
    acc ← `(($e, $acc))
  return acc

/-- `fun s => let v₁ := s.1; let v₂ := s.2.1; … ; <inner>` — a lambda over the loop state tuple that
binds each state variable to its projection, so `inner` (built by `getCode` over the original JSON)
refers to them by name. The `let`-projection form (not a `match` pattern) is deliberate: the verified
`while` proofs `show` the generated def is defeq to their projection-based body lambdas, and `let v :=
s.1` reduces there where a `match` matcher would not. `inner` runs with the names registered. -/
def whileStateLambda (stateVars : Array String) (inner : PygenM (TSyntax `term)) :
    PygenM (TSyntax `term) := withFreshVariables do
  for v in stateVars do addVar v.toName
  let innerStx ← inner
  let s := mkIdent `s
  let n := stateVars.size
  let mut body := innerStx
  for i in [0:n] do
    let idx := n - 1 - i
    let proj ← whileTupleProj s idx n
    body ← `(let $(mkIdent stateVars[idx]!.toName):ident := $proj; $body)
  `(fun $s => $body)

/-- Emit a `while`-shaped contracted function as a `pyWhile` verification def plus its `@[spec]`
Hoare-triple theorem, discharged by `pyWhile_correct` (init/step/exit left to `taste?`). Returns the
two commands. Exact mode only; the runnable `'rn` twin takes the ordinary `while` path. -/
def buildWhileFunction (name : String) (json : Json) (sh : WhileShape) :
    PygenM (Array (TSyntax `command)) := do
  let nameIdent := mkIdent name.toName
  let argInfos ← functionArgInfos json
  let stateVars := sh.stateVars
  let n := stateVars.size
  -- The three combinator lambdas (each captures the function parameters freely).
  let cLam ← whileStateLambda stateVars
    (do truthyConditionTerm sh.test (← withPropCondition true (getCode sh.test `term)))
  let muLam ← whileStateLambda stateVars
    (do let d ← getCode sh.decreases `term; `(($d : Int).toNat))
  let bodyLam ← whileStateLambda stateVars (do
    let elems : Array (TSyntax `term) := stateVars.map (fun v => ⟨(mkIdent v.toName).raw⟩)
    let mut b ← whileNestedTuple elems
    for assign in sh.bodyAssigns.reverse do
      let .ok target := assign.getObjVal? "target" | throwError "pyWhile: body assign without target"
      let .ok tname := target.getObjValAs? String "id" | throwError "pyWhile: body assign target not a Name"
      let .ok valJson := assign.getObjVal? "value" | throwError "pyWhile: body assign without value"
      -- `AugAssign` `v op= e` is `v = v op e`: synthesize the `BinOp` so all operator lowering applies.
      let valJson := if jsonNodeType? assign == some "AugAssign" then
          match assign.getObjValAs? String "op" with
          | .ok op => Json.mkObj [("node_type", Json.str "BinOp"), ("op", Json.str op),
                                  ("left", nameJson tname), ("right", valJson)]
          | .error _ => valJson
        else valJson
      let valStx ← getCode valJson `term
      b ← `(let $(mkIdent tname.toName):ident := $valStx; $b)
    pure b)
  -- Initial state tuple s₀.
  let s0Elems ← sh.inits.mapM (fun e => getCode e `term)
  let s0 ← whileNestedTuple s0Elems
  let pyWhileCall ← `(PastaLean.pyWhile $muLam $cLam $bodyLam $s0)
  -- The def: `fun params ↦ let sf := pyWhile …; let vᵢ := sf.<pᵢ>; <retExpr>`.
  let defValue ← withFreshVariables do
    for v in stateVars do addVar v.toName
    let retStx ← getCode sh.retExpr `term
    let sf := mkIdent `__py_sf
    let mut b := retStx
    for i in [0:n] do
      let idx := n - 1 - i
      let proj ← whileTupleProj sf idx n
      b ← `(let $(mkIdent stateVars[idx]!.toName):ident := $proj; $b)
    b ← `(let $sf := $pyWhileCall; $b)
    -- The spec is a Hoare triple `⦃P⦄ fn args ⦃⇓ r => Q⦄`, so `fn args` must be a *monadic* value.
    -- Wrap the pure result in `Id` (mirrors the `for`-loop path's `(do … : Id _)`); the `'rn` twin
    -- keeps the ordinary runnable form.
    b ← `((pure $b : Id _))
    let mut v := b
    for (argIdent, ty?) in argInfos.reverse do
      v ← match ty? with
        | some ty => `(fun ($argIdent : $ty) ↦ $v)
        | none => `(fun $argIdent ↦ $v)
    pure v
  let finalDef ← applyPrivacy name (← `(command| def $nameIdent := $defValue))
  -- The spec theorem.
  let preProps ← sh.requires.mapM (fun r => withPropCondition true (getCode r `term))
  let pre ← conjoin preProps
  let rId := mkIdent `p'_r
  let postProps ← sh.ensures.mapM
    (fun e => withPropCondition true (getCode (substResultWith (nameJson "p'_r") e) `term))
  let post ← conjoin postProps
  -- `I` and `Q` lambdas over the state tuple (`Q` uses `Result() := retExpr`).
  let iLam ← whileStateLambda stateVars
    (do conjoin (← sh.invariants.mapM (fun inv => withPropCondition true (getCode inv `term))))
  let qLam ← whileStateLambda stateVars
    (do conjoin (← sh.ensures.mapM
      (fun e => withPropCondition true (getCode (substResultWith sh.retExpr e) `term))))
  let paramIdents := argInfos.map (·.1)
  let nameLemma ← `(Lean.Parser.Tactic.simpLemma| $nameIdent:term)
  -- Each `pyWhile_correct` side goal (init `I s₀`, step `I(body) ∧ μ' < μ`, exit `Q`) is left to
  -- `taste?`, so — like the `for`/pure tracks — the prove-and-replace pipeline runs it in the backend
  -- and splices the single winning tactic back over each `taste?`, giving a clean one-line proof per
  -- obligation instead of an inlined closer portfolio.
  let thmCmd ← `(command| @[spec] theorem $(mkIdent (name ++ "_spec").toName) :
      ⦃⌜$pre⌝⦄ $nameIdent $paramIdents* ⦃⇓ $rId => ⌜$post⌝⦄ := by
        mvcgen [$nameLemma]
        · exact PastaLean.pyWhile_correct (I := $iLam) (Q := $qLam) $muLam $cLam $bodyLam $s0
            (by taste?) (by taste?) (by taste?))
  return #[finalDef, thmCmd]

/-- Build `partial def name : <arg tys → ret> := value` for a member of a mutual group. The
explicit signature is required for `mutual` and also keeps operators from defaulting (see the
self-recursive case in `funcDefSyntax`). -/
def mutualMemberDef (json : Json) : PygenM (TSyntax `command) := do
  let .ok name := json.getObjValAs? String "name" | throwError
    s!"FuncDef node does not have a 'name' field: {json}"
  let nameIdent := mkIdent (← withRunSuffix name).toName
  let heapRefParams ← functionHeapRefParams json
  let argInfos ← functionArgInfos json (heapRefTypes := true)
  let bodyElems ← functionBodyElems json
  let retAnn := returnAnnotation? json
  let valueStx ← withReturnAnnotation retAnn <| functionValueSyntax argInfos bodyElems
    (heapCellParams := ← functionHeapCellParams json) (heapRefParams := heapRefParams)
  -- A heap-tier member (touches the heap or takes a ref param) runs in `HeapM Val`; wrap the arrow's
  -- codomain so the explicit `mutual` signature matches the body's monad.
  let isHeap := !heapRefParams.isEmpty || (← needsHeapMonad bodyElems)
  let wrapCod (retTy : TSyntax `term) : PygenM (TSyntax `term) := do
    if isHeap then `(PastaLean.HeapM $(mkIdent `Val) $retTy)
    else match ← effectMonad? (stripResultMarkers bodyElems) with
      | some m => `($m $retTy)
      | none => pure retTy
  match ← functionReturnTypeSyntax? json with
  | some retTy =>
      match ← functionArrowTypeSyntax? argInfos (← wrapCod retTy) with
      | some fullTy => `(command| partial def $nameIdent : $fullTy := $valueStx)
      | none => `(command| partial def $nameIdent := $valueStx)
  | none => `(command| partial def $nameIdent := $valueStx)

/-- Emit one closure-conversion helper group: a lone helper as a plain command, a mutually-recursive
cluster (≥ 2 members that reference each other) as one `mutual … end` block of `partial def`s. -/
def emitHelperGroup (group : Array Json) : PygenM (TSyntax `command) := do
  if group.size ≥ 2 then
    -- A `mutual` block needs an explicit signature on each member; untyped params give none, and
    -- the block then fails to elaborate. Throw so best-effort degrades the function instead.
    for j in group do
      let some retTy ← functionReturnTypeSyntax? j
        | throwError "mutually-recursive nested functions need type annotations for a `mutual` block"
      let some _ ← functionArrowTypeSyntax? (← functionArgInfos j) retTy
        | throwError "mutually-recursive nested functions need type annotations for a `mutual` block"
    let defs ← group.mapM fun j => withFreshVariables do mutualMemberDef j
    `(command| mutual $defs:command* end)
  else if let some j := group[0]? then
    getCode j `command
  else throwError "closure conversion produced an empty helper group"

/-- Does a recursive call to `name` appear inside a lazily/conditionally-evaluated expression — a
ternary `IfExp`, a short-circuit `BoolOp`, a `Lambda`, or a comprehension? There a memoized self-call
`(← foo'memo'rn …)` is illegal (do-notation only hoists `(←…)` from statement position, and hoisting
out of a conditional would change *when* it runs), so such a function can't be memoized as-is. -/
partial def selfCallUnderExpr (name : String) (json : Json) : Bool :=
  match jsonNodeType? json with
  -- `IfExp` and single-generator `ListComp`/`GeneratorExp` are memoizable: the codegen lowers their
  -- self-calls to awaited monadic forms (`(← if …)`, `(← xs.mapM …)`), keeping evaluation lazy/scoped.
  -- `Lambda`/`SetComp`/`DictComp` have no such lowering yet, so a self-call under them still forces
  -- the unmemoized fallback.
  | some "Lambda"
  | some "SetComp" | some "DictComp" =>
      containsCallTo name json
  -- `a or b`/`a and b`: the FIRST operand is always evaluated, so a self-call there is memoizable
  -- (boolOpValueTerm's monadic `do let bopGuard := …` form binds it); a LATER, short-circuited operand
  -- is conditional, so a self-call there still forces the fallback. (`max([… dfs …] or [0])`.)
  | some "BoolOp" =>
      match (json.getObjValAs? (Array Json) "values").toOption.getD #[] |>.toList with
      | first :: rest => selfCallUnderExpr name first || rest.any (containsCallTo name)
      | [] => false
  -- Only `[… self-call … for x in iter]` — one generator, the recursion in the element, a clean
  -- iterable/filter — lowers via `mapM`. Anything else (multi-generator `flatMap`, a self-call in the
  -- `iter`/`ifs`) has no monadic lowering, so it must force the unmemoized fallback.
  | some "ListComp" | some "GeneratorExp" =>
      let gens := (json.getObjValAs? (Array Json) "generators").toOption.getD #[]
      let elt := (json.getObjVal? "elt").toOption.getD Json.null
      if gens.size == 1 && !(gens.any (containsCallTo name)) then
        selfCallUnderExpr name elt
      else containsCallTo name json
  | _ => match json with
    | .arr xs => xs.any (selfCallUnderExpr name)
    | .obj fs => fs.toList.any (fun (_, v) => selfCallUnderExpr name v)
    | _ => false

/-- The memoized run-twin of a `@cache`/`@lru_cache` function: a `StateM`-threaded worker `foo'memo'rn`
that shares one `HashMap` cache across the whole recursion, plus the pure wrapper `foo'rn` that seeds a
fresh cache per top-level call. Recursive self-calls in the body lower to `(← foo'memo'rn args)` (via
`withMemoizeSelf`), so the recursion is memoized — turning exponential `@cache` DP into polynomial.
Returns `none` (fall back to a plain, unmemoized def) unless the function has a known return type and
all-`int` params (a `Hashable`/`BEq` cache key). -/
def memoizedRunCommand? (json : Json) (nameIdent : TSyntax `ident) (baseName : String) :
    PygenM (Option (TSyntax `command)) := do
  let some retTy ← functionReturnTypeSyntax? json | return none
  -- Params live in the nested `arguments` node (`json.args.args`). The cache is keyed on the ORIGINAL
  -- params only; a closure-`_capture` (added when lifting a nested `@cache dfs`) is constant across
  -- the recursion and may be a non-hashable container, so it is threaded through but NOT keyed. Every
  -- ORIGINAL param must be `int`/`bool`/`str` — a `Hashable`/`BEq` type the key (a tuple of them) uses.
  let argNodes := ((json.getObjVal? "args").toOption.bind
    (·.getObjValAs? (Array Json) "args" |>.toOption)).getD #[]
  let isCapture (a : Json) : Bool := a.getObjValAs? Bool "_capture" == .ok true
  let keyTyFor (a : Json) : Option (TSyntax `term) :=
    match (a.getObjVal? "annotation").toOption.bind (·.getObjValAs? String "id" |>.toOption) with
    | some "int" => some (mkIdent ``Int)
    | some "bool" => some (mkIdent ``Bool)
    | some "str" => some (mkIdent ``String)
    | _ => none
  let argInfos ← functionArgInfos json
  unless argInfos.size == argNodes.size do return none
  -- (ident, key-type) for each ORIGINAL param; `none` if an original isn't a scalar key type.
  let keyPartsOpt : Array (Option (TSyntax `term × TSyntax `term)) :=
    (argNodes.zip argInfos).filterMap fun (a, (id, _)) =>
      if isCapture a then none else some ((keyTyFor a).map (fun kt => (⟨id.raw⟩, kt)))
  -- every original must be keyable (else the key is incomplete → wrong cache), and there must be ≥1.
  unless !keyPartsOpt.isEmpty && keyPartsOpt.all (·.isSome) do return none
  let keyParts := keyPartsOpt.filterMap id
  let keyTerms := keyParts.map (·.1)
  let keyTys := keyParts.map (·.2)
  let argTerms : Array (TSyntax `term) := argInfos.map (fun (i, _) => ⟨i.raw⟩)
  -- key: one original → the param; many → the right-nested tuple `(a, b, …)`; type = the `×` product.
  let mut keyExpr : TSyntax `term := keyTerms.back!
  for a in keyTerms.pop.reverse do keyExpr ← `(($a, $keyExpr))
  let mut keyTy : TSyntax `term := keyTys.back!
  for t in keyTys.pop.reverse do keyTy ← `($t × $keyTy)
  let worker : TSyntax `ident := mkIdent (baseName ++ "'memo'rn").toName
  let bodyElems := stripResultMarkers (← functionBodyElems json)
  -- A self-call in a ternary/`and`/`or`/lambda/comprehension can't be a monadic `(←…)`; fall back.
  if bodyElems.any (selfCallUnderExpr baseName) then return none
  -- Params are immutable binders; a body that reassigns/augments a param (`k += …`) needs a
  -- `let mut p := p` shadow, exactly as the non-memoized path does — else "`p` cannot be mutated".
  -- Register each as a mutable var BEFORE building the body, so a later plain assign (`x = 3*x+1`)
  -- lowers to a reassignment (`x := …`) rather than a fresh `let mut x` that shadows the shadow.
  let mut paramPrelude : Array (TSyntax `doElem) := #[]
  for (argIdent, _) in argInfos do
    if bodyElems.any (fun b => jsonMutatesName b argIdent.getId.toString) then
      addVar argIdent.getId
      setMutVar argIdent.getId
      paramPrelude := paramPrelude.push (← `(doElem| let mut $argIdent:ident := $argIdent))
  let bodyDoElems ← withMemoizeSelf (some (baseName, worker.getId)) (monadicFunctionBodySyntax bodyElems)
  -- Ascribe the inner do to `StateM … retTy` so mixed int/float returns coerce up (else the first
  -- `return` pins the block's type). `int(i<=n)` [ℤ] with `…/maxPts` [float] in a float DP.
  let stateTy ← `(StateM (Std.HashMap $keyTy $retTy) $retTy)
  let cacheDo ← `(do
    match (← get)[$keyExpr]? with
    | some v => return v
    | none =>
        let v ← ((do
          $[$paramPrelude:doElem]*
          $[$bodyDoElems:doElem]*) : $stateTy)
        modify (·.insert $keyExpr v)
        return v)
  let mut workerVal : TSyntax `term := cacheDo
  for (argIdent, ty?) in argInfos.reverse do
    workerVal ← match ty? with
      | some t => `(fun ($argIdent : $t) ↦ $workerVal)
      | none => `(fun $argIdent ↦ $workerVal)
  let stateRetTy ← `(StateM (Std.HashMap $keyTy $retTy) $retTy)
  let some workerTy ← functionArrowTypeSyntax? argInfos stateRetTy | return none
  let workerDef ← `(command| partial def $worker : $workerTy := $workerVal)
  -- wrapper: `fun (params) ↦ (worker args).run' ∅`
  let mut wrapCall : TSyntax `term ← `($worker)
  for i in argTerms do wrapCall ← `($wrapCall $i)
  let mut wrapperVal : TSyntax `term ← `(($wrapCall).run' ∅)
  for (argIdent, ty?) in argInfos.reverse do
    wrapperVal ← match ty? with
      | some t => `(fun ($argIdent : $t) ↦ $wrapperVal)
      | none => `(fun $argIdent ↦ $wrapperVal)
  let some wrapperTy ← functionArrowTypeSyntax? argInfos retTy | return none
  let wrapperDef ← `(command| def $nameIdent : $wrapperTy := $wrapperVal)
  return some ⟨mkNullNode #[workerDef.raw, wrapperDef.raw]⟩

@[pygen "FunctionDef"]
def funcDefSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        -- A genuine (non-transparent) decorator `@d` means `f = d(f)`. Emit the raw function under a
        -- private name and bind the decorated name to the application `d1 (d2 raw)` (bottom-up: the
        -- decorator nearest the `def` applies first). Both twins line up: the raw def and its
        -- reference share this pass's run-suffix, and decorator names get the user-name suffix.
        -- Transparent decorators (`@cache`, `@staticmethod`, …) are left for the normal path below.
        let applied := Decorators.appliedDecorators json
        if !applied.isEmpty then
          let .ok decoName := json.getObjValAs? String "name" | throwError
            s!"decorated FuncDef has no 'name': {json}"
          let rawBase := decoName ++ "'undecorated"
          let rawJson := (json.setObjVal! "name" (Json.str rawBase)).setObjVal!
            "decorator_list" (Json.arr #[])
          let rawCmd ← getCode rawJson `command
          let bindName ← withRunSuffix decoName
          let rawRef ← withRunSuffix rawBase
          let mut acc : TSyntax `term ← `($(mkIdent rawRef.toName))
          for d in applied.reverse do
            let dRef ← suffixIfUserName d
            acc ← `($(mkIdent dRef.toName) $acc)
          let bindCmd ← `(command| def $(mkIdent bindName.toName) := $acc)
          -- Flatten: the raw def's own emission is a null-node (`def` + `attribute`), so append
          -- through `appendCommandSyntax` rather than nesting null-nodes (which won't elaborate).
          let mut cmds := appendCommandSyntax #[] rawCmd
          cmds := appendCommandSyntax cmds bindCmd
          return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        -- A nested `def` becomes a sibling `partial def` emitted just before this one, with its
        -- captured variables as extra parameters (`Transform/ClosureConvert.lean`). Mutually-recursive
        -- siblings are emitted together in one `mutual` block. The rewritten function has no nested
        -- defs left, so re-entering here terminates.
        let (helperGroups, converted) ← closureConvertFunction json
        if !helperGroups.isEmpty then
          let mut cmds : Array (TSyntax `command) := #[]
          for group in helperGroups do
            cmds := appendCommandSyntax cmds (← emitHelperGroup group)
          cmds := appendCommandSyntax cmds (← getCode converted `command)
          return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        let .ok rawName := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        -- Lean reserves the top-level name `main` for the program entry point and requires it to
        -- have type `IO (UInt32 | Unit | PUnit)`. A Python function literally named `main` that is
        -- NOT the `__main__` entry point would emit `def main := …` and be rejected. The Python
        -- pre-pass already renames `main` → `main'` whenever a `__main__` guard exists (so the guard
        -- owns the entry point); therefore any `FunctionDef` that still reaches here named `main`
        -- is a plain helper with no guard, and must yield the reserved name to stay compilable.
        let baseName := if rawName == "main" then "main'" else rawName
        -- In a run-twin (`--mode both`) the emitted name gets the `'rn` suffix (`foo` → `foo'rn`);
        -- `baseName` (unsuffixed) is still used to scan the JSON body for self-reference (recursion).
        let name ← withRunSuffix baseName
        let nameIdent := mkIdent name.toName
        -- A *pure* body that is some `let`-bindings followed by ONE obligation (`assert C`, or
        -- `if H: assert C`) becomes a named, reusable `@[taste_ingr] theorem`. `theoremShape?` is the
        -- single source of truth — it returns `(lets, hyps, conclusion)` and matches only pure bodies,
        -- so monadic/loop/mutation bodies never reach here. The statement is built outside-in:
        -- `∀ params, let x := …; H1 → … → C`, lowered as a `Prop` (so `==`→`=`, `<`/`≤`→real order).
        -- The run twin (`approx`) drops the obligation. Anything else (≥2 asserts, non-`let` statements)
        -- stays a `def` with anonymous `have`s (see `Head_Assert`).
        let bodyArr := (json.getObjValAs? (Array Json) "body").toOption.getD #[]
        let substantive := bodyArr.filter fun (s : Json) => !isDocstringLike s
        -- Postconditions (`Ensures`/`Assert`) must bookend the function, not sit mid-computation.
        if hasMidFunctionPostcondition substantive then
          throwError "Ensures/Assert must appear at the start or end of the function body, not \
            interleaved with the computation — a mid-function Assert is a program-point checkpoint, \
            not a postcondition. Move it to the end (or use Invariant inside the loop)."
        let paramNames := (← functionArgInfos json).map (fun (id, _) => id.getId.toString)
        -- a function the module calls (`_called`) stays a `def`: callers need its value in both twins
        let called := (json.getObjValAs? Bool "_called").toOption.getD false
        if let some (letJsons, hypJsons, conclJson) := (if called then none else theoremShape? paramNames bodyArr substantive) then
          if (← getNumericMode) == .approx then return ⟨mkNullNode #[]⟩
          let thmCmd ← buildSpecTheorem nameIdent (← functionArgInfos json) letJsons hypJsons #[conclJson]
          return ⟨mkNullNode #[thmCmd.raw]⟩
        -- Track P: a pure, straight-line contracted function (`Requires`/`Ensures` + `let`s +
        -- `return`) emits its ordinary runnable `def` (contracts stripped) plus a `<fn>_correct` theorem.
        -- No Hoare triple here (it's pure), so the single readable theorem is named `_correct`, not `_spec`.
        -- Reference the function by name in its `_spec`/`_correct` UNLESS the name is a Python builtin
        -- (`sum`, `max`, …), where a `Call` would dispatch to the builtin, not the user def — inline there.
        let refFn := (← builtinMappedName? name).isNone
        if let some (cleanBody, letJsons, hypJsons, conclJsons) := contractShape? name refFn paramNames bodyArr substantive then
          let argInfos ← functionArgInfos json
          -- A `float`-annotated contracted body whose `return` mixes `int` and true-division
          -- (`median`) needs its result ascribed to `ℚ`/`Float` so the `int` branch coerces — same
          -- `retFloat` reconcile the generic path uses below (Track P doesn't reach it).
          let annFloat := match returnAnnotation? json with
            | some r => annotationIsScalarFloat r
            | none => false
          let retFloatP := ((json.getObjValAs? Bool "_ret_float" == .ok true) || annFloat) &&
            ((← getNumericMode) != .exact || json.getObjValAs? Bool "_real_fn" != .ok true)
          let valueStx ← withRetFloatContext retFloatP <| functionValueSyntax argInfos cleanBody false retFloatP
          -- A Track-P body that reaches `ℝ` (a transcendental, or `x ** 0.5` via `rpow`) is
          -- noncomputable in exact mode — same rule as the monadic path below, which this pure path
          -- also needs (e.g. an unannotated `is_prime` helper that computes `int(a ** 0.5)`).
          let ncP ← (pure (json.getObjValAs? Bool "_real_fn" == .ok true)) <||>
            bodyNeedsNoncomputable cleanBody <||> bodyCallsNoncomputable cleanBody
          if ncP then registerNoncomputableDef name
          -- A self-recursive contracted helper (`query_gcd(a,b) = … query_gcd(b, a%b)`) is not
          -- structurally decreasing, so it must be `partial` (Lean can't infer termination here).
          let isRecP := cleanBody.any (jsonReferencesName · baseName)
          let defCmdP ← match ncP, isRecP with
            | true,  true  => `(command| noncomputable partial def $nameIdent := $valueStx)
            | true,  false => `(command| noncomputable def $nameIdent := $valueStx)
            | false, true  => `(command| partial def $nameIdent := $valueStx)
            | false, false => `(command| def $nameIdent := $valueStx)
          let finalDef ← applyPrivacy name defCmdP
          if (← getNumericMode) == .approx then
            return ⟨mkNullNode #[finalDef.raw]⟩
          -- The one top-level readable correctness theorem is `_correct`; a helper (`_`-prefixed,
          -- e.g. a closure-converted nested def) is a supporting `_spec`.
          let suffix := if pythonNameIsPrivate name then "_spec" else "_correct"
          let thmName := mkIdent (name ++ suffix).toName
          let thmCmd ← buildSpecTheorem thmName argInfos letJsons hypJsons conclJsons
          -- A `partial def` has no equation lemmas, so it can't carry `@[simp]`.
          if isRecP then return ⟨mkNullNode #[finalDef.raw, thmCmd.raw]⟩
          let attrCmd ← `(command| attribute [simp] $nameIdent)
          return ⟨mkNullNode #[finalDef.raw, attrCmd.raw, thmCmd.raw]⟩
        -- Track W: a `while`-loop contracted function (single straight-line `while` with `Invariant`
        -- + `Decreases`). Lowered through `pyWhile` + `pyWhile_correct` (the `while` rule), since core
        -- `while` is the opaque `whileM` mvcgen can't reason about. Exact mode only; the `'rn` twin
        -- keeps a real `while`.
        -- (The legacy `pyWhile` combinator track is retired: `mvcgen` now reasons about a native
        -- `while` loop directly — `Spec.whileM`/`Spec.forIn` over `Lean.Loop` are `@[spec]` — so a
        -- `while`-contracted function falls through to Track M below and emits a real `while`.)
        -- Track M: a monadic contracted function (a `for` OR `while` loop with `Invariant(...)`). Emit
        -- function `Id`-typed (so `mvcgen` sees the `do`) with `Requires`/`Assume` stripped to the
        -- precondition, plus a `<fn>_spec` Hoare-triple theorem driven by `mvcgen … with taste?`.
        -- Exact mode only; the runnable `'rn` twin (approx) falls through to normal emission.
        -- An IO-effectful body (e.g. one drawing from `random`) runs in the state+exception proof
        -- monad, which this `Id`-typed mvcgen track cannot host — its awaited sub-actions would not
        -- sequence. Skip the strict spec for it and fall through to the generic emitter, which emits a
        -- compiling monadic `def` (contracts kept as runtime checkpoints) for hand-written proofs.
        if (← getNumericMode) == .exact && !(bodyNeedsIOMonad substantive) then
          if let some info := monadicContractInfo? substantive then
            let argInfos ← functionArgInfos json
            -- Pick the monad mvcgen sees. A `try`/`raise` body needs a *pure* exception monad with
            -- mvcgen `throw`/`try` specs: `ExceptT PyException Id`. `Id` has no `MonadExcept`, so
            -- `throw`/`caught.OfKind` won't elaborate; bare `Except PyException` leaves universe
            -- metavariables in `Spec.throw_Except` for an *uncaught* `throw`; `PyExcept` drags in `IO`
            -- (no mvcgen specs). `ExceptT … Id` avoids all three. A pure body stays `Id _`.
            let usesExc := bodyNeedsExceptionMonad info.cleanBody
            -- A `float`-annotated body whose `return` is a mixed `int`/true-division ternary needs the
            -- `retFloat` context so the `IfExp`'s `int` branch coerces to `ℚ` (see `Assign.lean`).
            let annFloatM := match returnAnnotation? json with
              | some r => annotationIsScalarFloat r
              | none => false
            let retFloatM := ((json.getObjValAs? Bool "_ret_float" == .ok true) || annFloatM) &&
              json.getObjValAs? Bool "_real_fn" != .ok true
            -- returns that disagree in type (`return None` / `return a` with `a : PyAny`) box to `PyAny`
            let boxReturnM := json.getObjValAs? Bool "_box_return" == .ok true
            let valueStx ← withBoxReturnContext boxReturnM <| withRetFloatContext retFloatM <| withFreshVariables do
              -- Shadow any mutated parameter with `let mut p := p` (as the runnable twin does via
              -- `functionValueSyntax`); without it a contracted `while n: … n >>= 1` reassigns the
              -- immutable binder `n` and fails to elaborate.
              let prelude ← mutatedParamPrelude argInfos info.cleanBody (optMutParamsOf json)
              let bodyStxArray ← monadicFunctionBodySyntax info.cleanBody
              let doStx ← `(do $[$prelude:doElem]* $[$bodyStxArray:doElem]*)
              -- A nullable return (`return None` / `return v`) pins the codomain to `Id (Option τ)` so
              -- the `none`/`some v` branches share a type Lean can't infer from a bare `Id _`.
              let optRet? ← optionalReturnAscription? json
              let monadTy ← if usesExc then `(ExceptT PastaLean.PyException Id _)
                else if boxReturnM then `(Id PastaLean.PyAny)
                else match optRet? with | some t => `(Id $t) | none => `(Id _)
              let mut v ← `(($doStx : $monadTy))
              for (argIdent, ty?) in argInfos.reverse do
                v ← match ty? with
                  | some ty => `(fun ($argIdent : $ty) ↦ $v)
                  | none => `(fun $argIdent ↦ $v)
              pure v
            -- A body that touches `ℝ` is noncomputable in exact mode; the verification def only needs
            -- to *elaborate* for `mvcgen`, so mark it as such. `bodyNeedsNoncomputable` catches a direct
            -- transcendental (`math.sqrt`); the `_real_fn` stamp (set by the Python per-variable pass)
            -- additionally catches *transitive* ℝ — e.g. a function whose value comes from calling
            -- another ℝ-returning function (`euclidean_distance`), which the body scan can't see.
            let nc ← (pure (json.getObjValAs? Bool "_real_fn" == .ok true)) <||>
              bodyNeedsNoncomputable info.cleanBody <||> bodyCallsNoncomputable info.cleanBody
            if nc then registerNoncomputableDef name
            if !usesExc then registerIdDef name
            let defCmd ← if nc then `(command| noncomputable def $nameIdent := $valueStx)
              else `(command| def $nameIdent := $valueStx)
            let finalDef ← applyPrivacy name defCmd
            let thmCmd ← buildMonadicSpec (mkIdent (name ++ "_spec").toName)
              (mkIdent (name ++ "_correct").toName) nameIdent (!pythonNameIsPrivate name) argInfos info
            -- `thmCmd` is a null node of one-or-two commands (spec + optional readable corollary);
            -- splice its children flat so each elaborates as a command.
            return ⟨mkNullNode (#[finalDef.raw] ++ thmCmd.raw.getArgs)⟩
        -- `_real_fn` (set by the Python per-variable pass) means the function produces or handles an
        -- `ℝ` value → it must be `noncomputable` in exact mode. This is now DECOUPLED from which
        -- floats are `ℝ`: real params carry a per-`arg` `_real` stamp (read in `functionArgInfos`)
        -- and real local literals are lowered under a per-assignment `withRealContext`; the function
        -- is NOT blanket-lifted, so its `ℚ` locals stay `ℚ`.
        let isReal := (← getNumericMode) == .exact && json.getObjValAs? Bool "_real_fn" == .ok true
        -- The inference pass marks a function whose returns disagree in type; its result is boxed as
        -- `PyAny`, which is not provable — so it never gets the `[simp, taste_ingr]` tag below.
        let boxReturn := json.getObjValAs? Bool "_box_return" == .ok true
        -- A float-returning body gets its result pinned to `ℚ`/`Float`, EXCEPT for an `ℝ`-valued
        -- function (`_real_fn`, incl. transitively via a callee) in exact mode — its float is `ℝ`,
        -- which a `ℚ` ascription would clash with, so it is left for Lean to infer. This fires on the
        -- inferred `_ret_float` stamp AND on an explicit `-> float` annotation: a `float`-annotated body
        -- whose branches mix `int` and true-division (`median`'s `s[k] if odd else (a+b)/2`) needs the
        -- `ℚ` ascription so the `int` branch coerces — without it the `if` branches disagree in type.
        let annFloat := match returnAnnotation? json with
          | some r => annotationIsScalarFloat r
          | none => false
        let retFloat := ((json.getObjValAs? Bool "_ret_float" == .ok true) || annFloat) &&
          ((← getNumericMode) != .exact || json.getObjValAs? Bool "_real_fn" != .ok true)
        let heapRefParams ← functionHeapRefParams json
        let argInfos ← functionArgInfos json (heapRefTypes := true)
        let retAnn := returnAnnotation? json
        let effectCmd? ← withReturnAnnotation retAnn <| withBoxReturnContext boxReturn <| withRetFloatContext retFloat
          (functionCommandWithEffectSignature? nameIdent argInfos json isReal)
        -- Drop any `Ensures(Result() …)`/`Assert(Result() …)` markers: they are verification-only
        -- (lifted to the spec postcondition) and `Result()` has no runtime lowering, so they must not
        -- leak into a runnable body — notably the `'rn` twin, which reaches this generic path.
        let bodyElems := stripResultMarkers (← functionBodyElems json)
        -- A `@cache`/`@lru_cache` function: the runnable twin memoizes (StateM-threaded cache) so
        -- exponential recursion runs in polynomial time. The provable twin (exact) stays the plain
        -- recursive def below. Falls back to the plain def for shapes memoization doesn't cover.
        if Decorators.hasMemoizingDecorator json && (← getNumericMode) == .approx then
          if let some memoCmd ← memoizedRunCommand? json nameIdent baseName then
            return memoCmd
        let isRecursive := bodyElems.any (jsonReferencesName · baseName)
        -- A real-valued body (transcendental, directly or via a callee) forces `noncomputable`.
        let nc := isReal || (← bodyNeedsNoncomputable bodyElems) || (← bodyCallsNoncomputable bodyElems)
        if nc then registerNoncomputableDef name
        let cmd ← withReturnAnnotation retAnn <| withBoxReturnContext boxReturn <| withRetFloatContext retFloat do match effectCmd? with
          | some cmd => pure cmd
          | none =>
              -- Params with Python defaults become `optParam` binders on the def (`def f (b := 10)`),
              -- with the body built un-wrapped so it reads the binders directly.
              match ← functionParamBinders? json argInfos with
              | some binders =>
                  let body ← functionValueSyntax #[] bodyElems boxReturn retFloat
                    (heapRefParams := heapRefParams)
                    (retAscription := ← optionalReturnAscription? json) (binderArgInfos := argInfos)
                  let rt? ← if isRecursive then recursiveReturnTypeSyntax? json else pure none
                  match isRecursive, nc, rt? with
                  | true, true, some rt => `(noncomputable partial def $nameIdent $binders* : $rt := $body)
                  | true, false, some rt => `(partial def $nameIdent $binders* : $rt := $body)
                  | true, true, none => `(noncomputable partial def $nameIdent $binders* := $body)
                  | true, false, none => `(partial def $nameIdent $binders* := $body)
                  | false, true, _ => `(noncomputable def $nameIdent $binders* := $body)
                  | false, false, _ => `(def $nameIdent $binders* := $body)
              | none =>
              let valueStx ← functionValueSyntax argInfos bodyElems boxReturn retFloat
                (optMutParams := optMutParamsOf json)
                (heapCellParams := ← functionHeapCellParams json) (heapRefParams := heapRefParams)
                (retAscription := ← optionalReturnAscription? json)
              -- take care of recursion function Type
              if isRecursive then
                -- A recursive heap-tier function (touches the heap or takes a ref param) runs in
                -- `HeapM Val`; wrap the arrow's codomain so the explicit signature matches the body.
                let isHeap := !heapRefParams.isEmpty || (← needsHeapMonad bodyElems)
                let fullTy? ← match ← recursiveReturnTypeSyntax? json with
                  | some retTy =>
                      let cod ← if isHeap then `(PastaLean.HeapM $(mkIdent `Val) $retTy) else pure retTy
                      functionArrowTypeSyntax? argInfos cod
                  | none => pure none
                match fullTy?, nc with
                | some fullTy, true => `(noncomputable partial def $nameIdent : $fullTy := $valueStx)
                | some fullTy, false => `(partial def $nameIdent : $fullTy := $valueStx)
                | none, true => `(noncomputable partial def $nameIdent := $valueStx)
                | none, false => `(partial def $nameIdent := $valueStx)
              else
                -- A node-returning function mixes bare `TreeNode(...)`, nullable cursors and `None`
                -- base cases: ascribe the full arrow type with codomain `Option C` so every arm
                -- coerces (`Coe C (Option C)`) instead of pinning the codomain to the first return.
                let fullTy? ← match returnClassName? json with
                  | some c =>
                      match ← runAwareTypeSyntax? (TypeInfer.PyType.opt (.cls c)) with
                      | some codom => functionArrowTypeSyntax? argInfos codom
                      | none => pure none
                  | none => pure none
                match fullTy?, nc with
                | some fullTy, true => `(noncomputable def $nameIdent : $fullTy := $valueStx)
                | some fullTy, false => `(def $nameIdent : $fullTy := $valueStx)
                | none, true => `(noncomputable def $nameIdent := $valueStx)
                | none, false => `(def $nameIdent := $valueStx)
        -- Python's leading-underscore convention (`def _foo`) maps to a Lean `private def`.
        let finalCmd ← applyPrivacy name cmd
        -- Tag prove-version (exact) functions for proof search. Skip RECURSIVE/`partial` defs: Lean
        -- rejects `@[simp]` on them (no unfolding equation). `taste_ingr` is narrower still — only a
        -- *simple arithmetic* function (pure: no IO/raise, no `assert` in its body, computable) — so
        -- `taste?`'s `simp only [taste_ingr]` stays a small fast set (never `main'`, a proof
        -- obligation, or a noncomputable `norm` whose `whnf` would stall simp).
        if (← getNumericMode) == .exact && !isRecursive then
          let isEffectful := bodyNeedsExceptionMonad bodyElems || bodyNeedsIOMonad bodyElems
          let hasAssert := bodyArr.any (jsonNodeType? · == some "Assert")
          let attrCmd ← if !isEffectful && !hasAssert && !nc && !boxReturn
            then `(command| attribute [simp, taste_ingr] $nameIdent)
            else `(command| attribute [simp] $nameIdent)
          return ⟨mkNullNode #[finalCmd.raw, attrCmd.raw]⟩
        else
          return finalCmd
    | `term, json => do
        let argInfos ← functionArgInfos json (heapRefTypes := true)
        let bodyElems ← functionBodyElems json
        functionValueSyntax argInfos bodyElems
          (heapCellParams := ← functionHeapCellParams json)
          (heapRefParams := ← functionHeapRefParams json)
          (retAscription := ← optionalReturnAscription? json)
    | `doElem, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let argInfos ← functionArgInfos json (heapRefTypes := true)
        let bodyElems ← functionBodyElems json
        let valueStx ← functionValueSyntax argInfos bodyElems
          (heapCellParams := ← functionHeapCellParams json)
          (heapRefParams := ← functionHeapRefParams json)
          (retAscription := ← optionalReturnAscription? json)
        `(doElem| let $nameIdent := $valueStx)
    | kind, _ => throwError s!"Unsupported syntax category `{kind}` for FuncDef node"

@[pygen "Head_Assign"]
def assignHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Assign node does not have a 'rest' field or it is not a JSON value: {json}"
        let splitRest ← splitList rest
        let tailCode ← withoutCheck do
          getCode splitRest `term
        match ← tupleTargetElts? target with
        | some elts => do
            let n := elts.size
            let valueStx ← getCode value `term
            let unpackTmpIdent := mkIdent (← freshName `__unpack_pair)
            -- Inference-first (see `Core/Assign.lean`): `_list_unpack` (RHS a `list`, `a,b = map(…)`) →
            -- index; `_tuple_unpack` → `Prod`; else the syntactic `Tuple`/`Call` fallback.
            let isTuple :=
              if target.getObjValAs? Bool "_list_unpack" == .ok true then false
              else if target.getObjValAs? Bool "_tuple_unpack" == .ok true then true
              else jsonNodeType? value == some "Tuple" || jsonNodeType? value == some "Call"
            let nestedIsTuple := target.getObjValAs? Bool "_thread_unpack" == .ok true
            let mut result := tailCode
            for i in (List.range n).reverse do
              result ← pureUnpackBinding nestedIsTuple elts[i]! (← unpackAccessTerm isTuple unpackTmpIdent i n) result
            `(let $unpackTmpIdent := $valueStx
              $result)
        | none => do
            let nameIdent ← getCode target `ident
            let valueStx ← getCode value `term
            -- Ascribe the inferred type when TypeInfer stamped one — the pure `let` mirror of the
            -- `let mut x : T` the monadic path emits. This is what lets a heterogeneous literal
            -- (`[1, "hi", [2]]` → `List PyAny`) box its elements instead of Lean pinning `List Int`
            -- from the first element. A bare numeric literal is re-emitted in the target type
            -- (`(0 : Float)`), since `((0 : Int) : Float)` has no coercion. A *bare* `PyAny` stamp is
            -- skipped: it marks a reassignment-conflict slot, which the pure path already handles by
            -- let-shadowing (each `let` re-infers), so forcing `PyAny` would break its per-binding
            -- monomorphic arithmetic — exactly the shadow guard the monadic path uses.
            let tyStx? ←
              match jsonFieldOption target "_ty" with
              | some ann =>
                  if ann.getObjValAs? String "id" == .ok "PyAny" then pure none
                  else stampedTypeSyntax? target
              | none => pure none
            let rhs ← match tyStx? with
              | some tyStx =>
                  match jsonNodeType? value, value.getObjValAs? Int "value" with
                  | some "Constant", .ok i =>
                      let n := Syntax.mkNumLit (toString i.natAbs)
                      let lit : TSyntax `term ← if i < 0 then `(- $n:num) else pure ⟨n⟩
                      `(($lit : $tyStx))
                  | _, _ => `(($valueStx : $tyStx))
              | none => pure valueStx
            `(let $nameIdent := $rhs
              $tailCode)
    | _, _ => throwError s!"Unsupported syntax category for Head_Assign node"

@[pygen "Head_AnnAssign"]
def annAssignHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
              s!"AnnAssign node does not have a 'rest' field or it is not a JSON value: {json}"
            let splitRest ← splitList rest
            withoutCheck do
              getCode splitRest `term
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Head_Assign")]
            let json := targetJson.mergeObj json
            assignHeadSyntax `term json
    | _, _ => throwError s!"Unsupported syntax category for Head_AnnAssign node"

@[pygen "Head_AugAssign"]
def augAssignHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok target := json.getObjVal? "target" | throwError s!"Head_AugAssign missing 'target': {json}"
        let .ok op := json.getObjValAs? String "op" | throwError s!"Head_AugAssign missing 'op': {json}"
        let .ok value := json.getObjVal? "value" | throwError s!"Head_AugAssign missing 'value': {json}"
        let binOp := match op with | "and" => "bitand" | "or" => "bitor" | "xor" => "bitxor" | o => o
        let binValue := Json.mkObj [("node_type", .str "BinOp"), ("op", .str binOp),
          ("left", target), ("right", value)]
        let asAssign := (json.setObjVal! "node_type" (.str "Head_Assign")).setObjVal! "value" binValue
        assignHeadSyntax `term asAssign
    | _, _ => throwError s!"Unsupported syntax category for Head_AugAssign node"

@[pygen "Head_Pass"]
def passHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Pass node does not have a 'rest' field or it is not a JSON value: {json}"
        let splitRest ← splitList rest
        withoutCheck do
          getCode splitRest `term
    | _, _ => throwError s!"Unsupported syntax category for Head_Pass node"

@[pygen "Head_FunctionDef"]
def functionDefHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok name := json.getObjValAs? String "name" | throwError
          s!"FuncDef node does not have a 'name' field or it is not a string: {json}"
        let nameIdent := mkIdent name.toName
        let argInfos ← functionArgInfos json (heapRefTypes := true)
        let bodyElems ← functionBodyElems json
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"FuncDef node does not have a 'rest' field or it is not a JSON value: {json}"
        let valueStx ← functionValueSyntax argInfos bodyElems
          (heapRefParams := ← functionHeapRefParams json)
          (retAscription := ← optionalReturnAscription? json)
        let splitRest ← splitList rest
        let tailCode ← withoutCheck do
          getCode splitRest `term
        `(let $nameIdent := $valueStx
          $tailCode)
    | _, _ => throwError s!"Unsupported syntax category for Head_FunctionDef node"

@[pygen "Head_If"]
def ifHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        -- `Optional` narrowing (`if let some x := x`) is a `do` form: take the monadic lowering.
        if (json.getObjValAs? String "_unwrap_some").isOk then
          throwError "narrowing `if x is not None` is lowered in `do` notation"
        let .ok testJson := json.getObjValAs? Json "test" | throwError
          s!"If node does not have a 'test' field or it is not a JSON value: {json}"
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"If node does not have an 'orelse' field or it is not a JSON array: {json}"
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"If node does not have a 'rest' field or it is not a JSON value: {json}"
        -- Pure lowering is safe as long as the `if` *body* definitely returns: the then-branch is
        -- then self-contained and `rest` is reached only through the else path (`if c then body else
        -- rest`), so no binding leaks across branches. This is the common `if c: return x⏎ return y`
        -- shape. If the body falls through, `rest` would be duplicated into both branches while the
        -- body's own bindings live only in the then-branch — keep that on the monadic path.
        if !rest.isEmpty && !statementListDefinitelyReturns bodyElems.toList then
          throwError
            "If body falls through into later statements; requires monadic lowering."
        -- A boolean context like every other `if`: `pyTruthy`-wrap a bare non-Bool test (`if s & 1:`)
        -- and force a `BoolOp` to the `Bool` connective, not the value-form.
        let testStx ← truthyConditionTerm testJson (← withPropCondition true (getCode testJson `term))
        let thenBranch ← withoutCheck do
          let splitThen ← splitList (bodyElems.toList ++ rest)
          getCode splitThen `term
        let elseTail := if orelseElems.isEmpty then rest else orelseElems.toList ++ rest
        let elseBranch ← withoutCheck do
          let splitElse ← splitList elseTail
          getCode splitElse `term
        `(if $testStx then $thenBranch else $elseBranch)
    | _, _ => throwError s!"Unsupported syntax category for Head_If node"

@[pygen "Head_Match"]
def matchHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok subjectJson := json.getObjValAs? Json "subject" | throwError
          s!"Match node does not have a 'subject' field or it is not a JSON value: {json}"
        let .ok casesJson := json.getObjValAs? (Array Json) "cases" | throwError
          s!"Match node does not have a 'cases' field or it is not a JSON array: {json}"
        let .ok rest := json.getObjValAs? (List Json) "rest" | throwError
          s!"Match node does not have a 'rest' field or it is not a JSON value: {json}"
        let subjectTerm ← getCode subjectJson `term
        matchCaseTermSyntax subjectTerm casesJson.toList rest
    | _, _ => throwError s!"Unsupported syntax category for Head_Match node"

@[pygen "Head_Return"]
def returnHeadSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        -- `return a or b` returns the deciding *value* (`x or '0'` → the string), not a `Bool`.
        if jsonNodeType? value == some "BoolOp" then
          return ← withoutCheck do boolOpValueTerm value
        let valueStx ← withoutCheck do
          getCode value `term
        return valueStx
    | _, _ => throwError s!"Unsupported syntax category for Head_Return node"

/-- All top-level `FunctionDef` nodes in a module body, paired with their names, in module order. -/
def topLevelFuncDefs (bodyElems : Array Json) : Array (String × Json) :=
  bodyElems.filterMap fun e =>
    match e.getObjValAs? String "node_type", e.getObjValAs? String "name" with
    | .ok "FunctionDef", .ok name => some (name, e)
    | _, _ => none

/-- For each top-level function, the set of top-level functions reachable from its body
(transitive closure of "references"). Used to find mutually-recursive groups. -/
def transitiveFuncRefs (funcs : Array (String × Json)) : Array (String × Array String) := Id.run do
  let names := funcs.map (·.1)
  let mut reach : Array (String × Array String) := funcs.map fun (nm, body) =>
    (nm, names.filter fun m => jsonReferencesName body m)
  -- Relax to a fixed point (longest reference chain is at most `names.size` long).
  for _ in [0:names.size] do
    reach := reach.map fun (nm, rs) => Id.run do
      let mut acc := rs
      for r in rs do
        match reach.find? (·.1 == r) with
        | some (_, rs2) =>
            for x in rs2 do
              unless acc.contains x do acc := acc.push x
        | none => pure ()
      return (nm, acc)
  return reach

/-- The mutual-recursion group (strongly-connected component) containing `nm`: every function `m`
such that `nm` reaches `m` and `m` reaches `nm`. A non-mutual function yields a singleton. -/
def mutualGroupOf (reach : Array (String × Array String)) (nm : String) : Array String :=
  let reachOf := fun x => ((reach.find? (·.1 == x)).map (·.2)).getD #[]
  (#[nm] ++ (reachOf nm).filter fun m => m != nm && (reachOf m).contains nm)

@[pygen "Module"]
def moduleSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"Module node does not have a 'body' field or it is not a JSON array: {json}"
        let some first := bodyElems[0]? | throwError "Cannot translate an empty module to a term."
        unless bodyElems.size == 1 do
          throwError "Module-to-term translation requires exactly one top-level statement."
        withFreshVariables do
          getCode first `term
    | `command, json => do
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"Module node does not have a 'body' field or it is not a JSON array: {json}"
        let funcs := topLevelFuncDefs bodyElems
        let reach := transitiveFuncRefs funcs
        let mut cmds : Array (TSyntax `command) := #[]
        let mut emitted : Array String := #[]
        for elem in bodyElems do
          match elem.getObjValAs? String "node_type", elem.getObjValAs? String "name" with
          | .ok "FunctionDef", .ok name =>
              unless emitted.contains name do
                let group := mutualGroupOf reach name
                if group.size ≥ 2 then
                  -- A mutually-recursive group can't be a sequence of plain `def`s (each would
                  -- forward-reference an undeclared name), so emit it as one `mutual … end` block
                  -- of `partial def`s, in module order.
                  let members := funcs.filterMap fun (m, j) =>
                    if group.contains m then some j else none
                  let defs ← members.mapM fun j => withFreshVariables do mutualMemberDef j
                  cmds := appendCommandSyntax cmds (← `(command| mutual $defs:command* end))
                  emitted := emitted ++ group
                else
                  cmds := appendCommandSyntax cmds (← withFreshVariables do getCode elem `command)
          | _, _ =>
              cmds := appendCommandSyntax cmds (← withFreshVariables do getCode elem `command)
        return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
    | _, _ => throwError s!"Unsupported syntax category for Module node"

end PastaLean
