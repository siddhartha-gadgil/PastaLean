import PastaLean.Imports
import PastaLean.Codegen
import PastaLean.PyGens.Basic
import PastaLean.PyGens.Core.Utils
import PastaLean.PyGens.UseCases.FuncDef

open Lean Meta Elab Term Qq Std

namespace PastaLean

open Lean.Parser.Term
open Lean.Parser.Command

/-!
  Translates Python `class` definitions to a Lean `structure` plus namespaced method `def`s.

  * Fields (`self.x = …`, class-level `x = …`) become structure fields, types from
    `annotate_python`/parameter annotations (defaulting to `Int`).
  * `__init__` becomes the smart constructor `C.new`, built by the same `self`-threading machinery
    as a mutator (start from `default`, apply each `self.x = …`, return `self`), so partial and
    locally-computed `__init__`s both work.
  * A non-mutating method is a pure `def C.method (self : C) … `; a mutator returns the rebuilt
    `self` (value semantics — see the module plan for the aliasing caveat).
  * Methods are emitted with fully-qualified names (`def C.method`), so `obj.method` dot-notation
    resolves without a `namespace` wrapper.
-/

/-- Names of `__init__` parameters that default to `None`; the fields they initialise are typed
`Option ClassName` (the recursive node pattern, `TreeNode.left`/`ListNode.next`). -/
def noneDefaultParamNames (initJson : Json) : List String := Id.run do
  let args := ((initJson.getObjVal? "args").toOption.bind
    (fun a => (a.getObjValAs? (Array Json) "args").toOption)).getD #[]
  let defaults := functionParamDefaults initJson
  let offset := args.size - defaults.size
  let mut names := []
  for i in [0:args.size] do
    if i ≥ offset then
      let d := defaults[i - offset]!
      if d.getObjValAs? String "node_type" == .ok "Constant" && (d.getObjVal? "value").toOption == some Json.null then
        if let .ok nm := args[i]!.getObjValAs? String "arg" then names := nm :: names
  return names

/-- A `None` literal (`Constant` whose value is JSON null). -/
private def isNoneConstJson (j : Json) : Bool :=
  j.getObjValAs? String "node_type" == .ok "Constant" && (j.getObjVal? "value").toOption == some Json.null

/-- A list whose elements are all `None` — `[None, None]` or `[None] * k` (`[None for _ in …]`) — the
initial value of a recursive node's children array (a Trie's `children`, a segment tree's kids). -/
private partial def isListOfNoneJson (j : Json) : Bool :=
  match j.getObjValAs? String "node_type" with
  | .ok "List" =>
      let elts := (j.getObjValAs? (Array Json) "elts").toOption.getD #[]
      !elts.isEmpty && elts.all isNoneConstJson
  | .ok "BinOp" =>
      j.getObjValAs? String "op" == .ok "mul"
        && ((j.getObjVal? "left").toOption.any isListOfNoneJson
            || (j.getObjVal? "right").toOption.any isListOfNoneJson)
  | .ok "ListComp" => (j.getObjVal? "elt").toOption.any isNoneConstJson
  | _ => false

/-- The `PyType` of a class field from its `{annotation?, init?}` entry (a `None`-default param field
is `Option className`). Used by both the plain and heap field-type renderers. -/
def classFieldPyType (className : String) (noneParams : List String) (fieldJson : Json) :
    TypeInfer.PyType :=
  let initFromNoneParam : Bool := match (fieldJson.getObjVal? "init").toOption with
    | some initJson =>
        (initJson.getObjValAs? String "node_type" == .ok "Name")
        && (match initJson.getObjValAs? String "id" with | .ok nm => noneParams.contains nm | _ => false)
    | none => false
  match (fieldJson.getObjVal? "annotation").toOption with
  | some (.null) | none =>
      if initFromNoneParam then .opt (.cls className)
      else match (fieldJson.getObjVal? "init").toOption with
        -- A DIRECT `self.x = None` is `Option ClassName`, and `self.children = [None]*k` / `[None,None]`
        -- is `List (Option ClassName)` — the recursive-node pattern with NO annotation (a `__slots__`
        -- trie). A bare `None` would otherwise mis-infer to `Unit` / `List Unit` from the literal.
        | some initJson =>
            if isNoneConstJson initJson then .opt (.cls className)
            else if isListOfNoneJson initJson then .list (.opt (.cls className))
            else TypeInfer.ofValue initJson
        | none => .int
  | some annJson =>
      -- An explicit container-of-`object`/`Any` (`list[object]`, `set[Any]`, `dict[str, object]`)
      -- whose element reads as ⊥ signals a deliberately heterogeneous container: promote the element
      -- to ⊤ (`.any`) so heap codegen boxes it to `PyAny`. A bare `= []` (no annotation, handled
      -- above) stays ⊥ and defaults to a concrete element, so `IntList` keeps `Ref (List Int)`.
      match TypeInfer.ofAnnotation annJson with
      | .list .unknown  => .list .any
      | .set .unknown   => .set .any
      | .dict k .unknown => .dict k .any
      | other           => other

/-- The name identifier and Lean type of one class field. Shared by the `structure` field emitter and
(under `--heap`) the generated `Val` constructor, so both agree. Under `--heap`, object/container
fields are `Ref`-wrapped (`Node.next : Option (Ref Node)`); otherwise the plain (value) type. -/
def classFieldNameType (className : String) (noneParams : List String) (fieldJson : Json) :
    PygenM (TSyntax `ident × TSyntax `term) := do
  let .ok fname := fieldJson.getObjValAs? String "name" | throwError
    s!"Class field is missing a 'name': {fieldJson}"
  let fid := mkIdent fname.toName
  let intTy : TSyntax `term := mkIdent ``Int
  let isRealField := (← getNumericMode) == .exact && fieldJson.getObjValAs? Bool "_real" == .ok true
  if ← getHeapMode then
    let ty ← withRealContext isRealField do heapTypeSyntax (classFieldPyType className noneParams fieldJson)
    return (fid, ty)
  let initFromNoneParam : Bool := match (fieldJson.getObjVal? "init").toOption with
    | some initJson =>
        (initJson.getObjValAs? String "node_type" == .ok "Name")
        && (match initJson.getObjValAs? String "id" with | .ok nm => noneParams.contains nm | _ => false)
    | none => false
  -- No annotation: a `None`-default param → `Option ClassName`; else read the type off what
  -- `__init__` assigns (`self.c = [0] * n` → `List Int`); only then fall back to `Int`.
  let ty : TSyntax `term ← withRealContext isRealField do
    match (fieldJson.getObjVal? "annotation").toOption with
    | some (.null) | none =>
        if initFromNoneParam then `(Option $(mkIdent className.toName))
        else match (fieldJson.getObjVal? "init").toOption with
          -- A DIRECT `self.x = None` (not via a None-default param) is `Option ClassName`, and
          -- `self.children = [None]*k` is `List (Option ClassName)` — the recursive-node pattern. Both
          -- otherwise mis-infer to `Unit` / `List Unit` from the bare `None` literal.
          | some initJson =>
              if isNoneConstJson initJson then `(Option $(mkIdent className.toName))
              else if isListOfNoneJson initJson then `(List (Option $(mkIdent className.toName)))
              else pure ((← pyTypeSyntax? (TypeInfer.ofValue initJson)).getD intTy)
          | none => pure intTy
    | some annJson => pure ((← functionArgTypeSyntax? annJson).getD intTy)
  return (fid, ty)

/-- One structure field `name : Type [:= default]` from a `{name, annotation?, default?}` entry. -/
def classStructFieldSyntax (className : String) (noneParams : List String) (fieldJson : Json) :
    PygenM (TSyntax ``Lean.Parser.Command.structSimpleBinder) := do
  let (fid, ty) ← classFieldNameType className noneParams fieldJson
  match (fieldJson.getObjVal? "default").toOption with
  | some (.null) | none => `(structSimpleBinder| $fid:ident : $ty)
  | some defJson =>
      let defCode ← getCode defJson `term
      `(structSimpleBinder| $fid:ident : $ty := $defCode)

/-- Build the `Id.run do` body of a `self`-threading routine (`__init__` or a mutator method):
declare a mutable `self` (the parameter for a mutator, or `default` for a constructor), lower the
body (where `self.x = …` becomes `self := { self with x := … }` — see `Core/Assign.lean`), then
`return self`. Wrapped in a lambda over `argInfos`. -/
def classSelfThreadingValue (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (classTyTerm : TSyntax `term) (bodyElems : Array Json) (selfIsParam : Bool)
    (monad? : Option (TSyntax `term) := none) (lambdas : Bool := true) :
    PygenM (TSyntax `term) := withFreshVariables do
  let selfId := mkIdent `self
  addVar `self
  let selfDecl ← if selfIsParam then `(doElem| let mut $selfId:ident := $selfId:ident)
                 else `(doElem| let mut $selfId:ident : $classTyTerm := default)
  -- A mutator method may also reassign/augment its OWN parameters (`x += x & -x` in a Fenwick
  -- `update`), so each mutated param needs a `let mut` shadow — exactly as free functions do. Without
  -- it the immutable binder throws "`x` cannot be mutated" and the whole method fails to elaborate.
  let mut paramPrelude : Array (TSyntax `doElem) := #[]
  for (argIdent, _) in argInfos do
    if argIdent.getId != `self && bodyElems.any (fun b => jsonMutatesName b argIdent.getId.toString) then
      addVar argIdent.getId
      paramPrelude := paramPrelude.push (← `(doElem| let mut $argIdent:ident := $argIdent))
  let bodyStxArray ← monadicFunctionBodySyntax bodyElems
  let idRun := mkIdent ``Id.run
  -- A routine that raises (a validating `__init__`) runs in its effect monad instead of `Id`.
  let core ← match monad? with
    | some m => `(((do
          $selfDecl:doElem
          $[$paramPrelude:doElem]*
          $[$bodyStxArray:doElem]*
          return $selfId:term) : $m $classTyTerm))
    | none => `($idRun do
          $selfDecl:doElem
          $[$paramPrelude:doElem]*
          $[$bodyStxArray:doElem]*
          return $selfId:term)
  if !lambdas then return core
  let mut result := core
  for (argIdent, ty?) in argInfos.toList.reverse do
    result ← match ty? with
      | some ty => `(fun ($argIdent : $ty) ↦ $result)
      | none => `(fun $argIdent ↦ $result)
  pure result

/-- Body of a VALUE+MUTATE method — mutates `self` AND returns a value (union-find `union`). Like
`classSelfThreadingValue` but each `return v` is emitted as `return (v, self)` (via `valueMutatorRef`),
so the method returns `(result × Self)`; the caller binds both, reassigns the receiver, and uses the
result. A fall-through returns `(default, self)`. -/
def classValueMutatorValue (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (bodyElems : Array Json) : PygenM (TSyntax `term) := withFreshVariables do
  let selfId := mkIdent `self
  addVar `self
  let selfDecl ← `(doElem| let mut $selfId:ident := $selfId:ident)
  let mut paramPrelude : Array (TSyntax `doElem) := #[]
  for (argIdent, _) in argInfos do
    if argIdent.getId != `self && bodyElems.any (fun b => jsonMutatesName b argIdent.getId.toString) then
      addVar argIdent.getId
      paramPrelude := paramPrelude.push (← `(doElem| let mut $argIdent:ident := $argIdent))
  let old ← valueMutatorRef.get
  valueMutatorRef.set true
  let bodyStxArray ← monadicFunctionBodySyntax bodyElems
  valueMutatorRef.set old
  let idRun := mkIdent ``Id.run
  -- A trailing `return v` already emits `return (v, self)`; only supply the fall-through terminal
  -- when the body doesn't itself end in a `return` (else the two returns collide in the do-sequence).
  let endsInReturn := bodyElems.back?.any (jsonNodeType? · == some "Return")
  let core ← if endsInReturn then
      `($idRun do
        $selfDecl:doElem
        $[$paramPrelude:doElem]*
        $[$bodyStxArray:doElem]*)
    else
      `($idRun do
        $selfDecl:doElem
        $[$paramPrelude:doElem]*
        $[$bodyStxArray:doElem]*
        return (default, $selfId:term))
  let mut result := core
  for (argIdent, ty?) in argInfos.toList.reverse do
    result ← match ty? with
      | some ty => `(fun ($argIdent : $ty) ↦ $result)
      | none => `(fun $argIdent ↦ $result)
  pure result

/-- If `__init__`'s body is purely straight-line `self.X = expr` (no control flow, no locals, and
no value reading `self`), return the `(field, valueJson)` pairs in order — the case that lowers to
a plain record literal (which honors structure field defaults for unassigned fields). `none`
otherwise (then the constructor threads a mutable `self` from `default`). -/
def initFieldAssignments? (bodyElems : Array Json) : Option (Array (String × Json × Bool)) := Id.run do
  let mut out := #[]
  for s in bodyElems do
    if jsonNodeType? s != some "Assign" then return none
    let some target := (s.getObjVal? "target").toOption | return none
    let some attr := selfAttrTarget? target | return none
    let some value := (s.getObjVal? "value").toOption | return none
    if jsonReferencesName value "self" then return none
    -- carry the per-field `_real` stamp so a real field's initial value is lowered in real-context
    out := out.push (attr, value, s.getObjValAs? Bool "_real" == .ok true)
  return some out

/-- The smart constructor `C.new` from `__init__`. A straight-line `__init__` becomes a record
literal `{ field := … }` (so unassigned fields take their structure defaults); anything else threads
a mutable `self` from `default`. Named `new` (not `mk`) to avoid clashing with the structure's
auto-generated `C.mk` field constructor. -/
def classInitConstructor (className : String) (initJson : Json) (hasRealField : Bool) :
    PygenM (TSyntax `command) := do
  let mkIdentC := mkIdent (Name.mkStr className.toName "new")
  let classTy : TSyntax `term := mkIdent className.toName
  let argInfos := (← functionArgInfos initJson).drop 1   -- drop the leading `self`
  let bodyElems ← functionBodyElems initJson
  let defaults := functionParamDefaults initJson
  match initFieldAssignments? bodyElems with
  | some pairs =>
      -- Straight-line `__init__` → a record literal. `__init__` defaults become `optParam` binders on
      -- `C.new`, so `TreeNode(x)` fills `left`/`right` instead of being a partial application.
      withFreshVariables do
        let fields ← pairs.mapM fun (attr, valJson, isReal) => do
          let v ← if isReal then withRealContext true (getCode valJson `term) else getCode valJson `term
          `(Lean.Parser.Term.structInstField| $(mkIdent attr.toName):ident := $v)
        let recordBody : TSyntax `term ← `(({ $fields:structInstField,* } : $classTy))
        if defaults.isEmpty then
          let mut result := recordBody
          for (argIdent, ty?) in argInfos.toList.reverse do
            result ← match ty? with
              | some ty => `(fun ($argIdent : $ty) ↦ $result)
              | none => `(fun $argIdent ↦ $result)
          -- `result` is `fun (n : Int) ↦ …` once there are params, so the ascription must be the
          -- arrow type `Int → C`, not `C`. No params → the record itself, ascribed `C`; an
          -- unannotated param → no full arrow, so emit without ascription and let Lean infer.
          let fullTy? ← if argInfos.isEmpty then pure (some classTy)
                        else functionArrowTypeSyntax? argInfos classTy
          match fullTy? with
          | some ty => if hasRealField then `(command| noncomputable def $mkIdentC : $ty := $result)
                       else `(command| def $mkIdentC : $ty := $result)
          | none => if hasRealField then `(command| noncomputable def $mkIdentC := $result)
                    else `(command| def $mkIdentC := $result)
        else
          let offset := argInfos.size - defaults.size
          let binders ← (Array.range argInfos.size).mapM fun i => do
            let (argIdent, ty?) := argInfos[i]!
            let d? := if i ≥ offset then some defaults[i - offset]! else none
            -- Unannotated `None`-default param is `Option ClassName` (matches the field type).
            let tyStx ← match ty? with
              | some t => pure t
              | none =>
                  if d?.any (fun d => d.getObjValAs? String "node_type" == .ok "Constant"
                                      && (d.getObjVal? "value").toOption == some Json.null)
                  then `(Option $classTy) else `(_)
            match d? with
            | some d => let dCode ← getCode d `term
                        `(Lean.Parser.Term.bracketedBinderF| ($argIdent : $tyStx := $dCode))
            | none => `(Lean.Parser.Term.bracketedBinderF| ($argIdent : $tyStx))
          if hasRealField then `(command| noncomputable def $mkIdentC $binders* : $classTy := $recordBody)
          else `(command| def $mkIdentC $binders* : $classTy := $recordBody)
  | none =>
      let monad? ← effectMonad? bodyElems
      let codomain ← match monad? with | some m => `($m $classTy) | none => pure classTy
      -- `__init__` defaults become `optParam` binders, so `C(x)` / `C(x, y=1)` fill the rest.
      if let some binders ← functionParamBinders? initJson argInfos then
        let valueStx ← withFreshVariables do
          withCurrentClass className [] do
            classSelfThreadingValue argInfos classTy bodyElems (selfIsParam := false) monad? (lambdas := false)
        return ← if hasRealField then `(command| noncomputable def $mkIdentC $binders* : $codomain := $valueStx)
          else `(command| def $mkIdentC $binders* : $codomain := $valueStx)
      let valueStx ← withFreshVariables do
        withCurrentClass className [] do
          classSelfThreadingValue argInfos classTy bodyElems (selfIsParam := false) monad?
      let mkDef : TSyntax `term → PygenM (TSyntax `command) := fun ty =>
        if hasRealField then `(command| noncomputable def $mkIdentC : $ty := $valueStx)
        else `(command| def $mkIdentC : $ty := $valueStx)
      match ← functionArrowTypeSyntax? argInfos codomain with
      | some fullTy => mkDef fullTy
      | none => if hasRealField then `(command| noncomputable def $mkIdentC := $valueStx)
                else `(command| def $mkIdentC := $valueStx)

/-- True when the method's body calls itself (`self.find(…)`). Lean cannot show termination for
path-compression / DFS recursion, so such a method is emitted `partial` — and without `@[simp]`,
which on a recursive def is an unfolding hazard. -/
partial def methodIsSelfRecursive (mName : String) (json : Json) : Bool :=
  let selfCall :=
    jsonNodeType? json == some "Attribute"
    && json.getObjValAs? String "attr" == .ok mName
    && (match (json.getObjVal? "value").toOption with
        | some v => jsonNodeType? v == some "Name" && v.getObjValAs? String "id" == .ok "self"
        | none => false)
  selfCall || (match json with
    | .arr xs => xs.any (methodIsSelfRecursive mName)
    | .obj fs => fs.toList.any (fun (_, v) => methodIsSelfRecursive mName v)
    | _ => false)

/-- One method `def C.method …`. A getter is a pure `functionValueSyntax`; a mutator returns the
rebuilt `self`. Static/class methods drop the leading `self`/`cls`. -/
def classMethodDef (className : String) (info : ClassInfo) (m : Json) : PygenM (Array (TSyntax `command)) := do
  let .ok mName := m.getObjValAs? String "name" | throwError
    s!"Class method is missing a 'name': {m}"
  let defIdent := mkIdent (Name.mkStr className.toName mName)
  let classTy : TSyntax `term := mkIdent className.toName
  let allArgInfos ← functionArgInfos m
  let bodyElems ← functionBodyElems m
  let isStatic := info.staticmethods.contains mName
  let isClassM := info.classmethods.contains mName
  let isMutator := info.mutators.contains mName && !isStatic && !isClassM
  let isValueMutator := info.valueMutators.contains mName && !isStatic && !isClassM
  let argInfos : Array (TSyntax `ident × Option (TSyntax `term)) :=
    if isStatic then allArgInfos
    else if isClassM then allArgInfos.drop 1
    else #[(mkIdent `self, some classTy)] ++ allArgInfos.drop 1
  -- Params with Python defaults become `optParam` binders; then the body is built un-wrapped
  -- (empty argInfos), reading `self`/params from the binders.
  let binders? ← functionParamBinders? m argInfos
  let bodyArgInfos := if binders?.isSome then #[] else argInfos
  let valueStx ← withCurrentClass className info.mutators do
    if isMutator then
      classSelfThreadingValue bodyArgInfos classTy bodyElems (selfIsParam := true)
    else if isValueMutator then
      classValueMutatorValue bodyArgInfos bodyElems
    else
      -- An `Optional[T]` method (`utcoffset`) pins its codomain so `return None` and `return t` unify.
      let optRet := match (jsonFieldOption m "returns").orElse (fun _ => jsonFieldOption m "_ret_ty") with
        | some r => match TypeInfer.ofAnnotation r with | .opt _ => true | _ => false
        | none => false
      functionValueSyntax bodyArgInfos bodyElems
        (retAscription := ← if optRet then optionalReturnAscription? m else pure none)
  -- A method the per-variable pass stamped `_real_fn` (produces/handles an `ℝ` transcendental)
  -- must be `noncomputable` in exact mode, exactly like a free function.
  let nc := (← getNumericMode) == .exact && m.getObjValAs? Bool "_real_fn" == .ok true
  let isRecursive := bodyElems.any (methodIsSelfRecursive mName)
  let cmd ← match binders? with
    | some binders =>
        if isRecursive then `(command| partial def $defIdent $binders* := $valueStx)
        else if nc then `(command| noncomputable def $defIdent $binders* := $valueStx)
        else `(command| def $defIdent $binders* := $valueStx)
    | none =>
        if isRecursive then `(command| partial def $defIdent := $valueStx)
        else if nc then `(command| noncomputable def $defIdent := $valueStx)
        else `(command| def $defIdent := $valueStx)
  let finalCmd ← applyPrivacy mName cmd
  -- Prove-version (exact) methods get `@[simp]` (and `taste_ingr` when a pure, computable, non-
  -- `assert` value method), so `taste?` can unfold them — mirroring free functions in `FuncDef`.
  -- Never the `'rn` twin (approx mode is skipped). Methods are emitted as plain `def`s, not
  -- `partial`, so there's no recursive-`@[simp]` hazard.
  -- An `IO` method (the clock) is not unfolded: its `if let` over the state monad makes the equation
  -- lemma blow `maxRecDepth`, and its result is unspecified anyway.
  if (← getNumericMode) == .exact && !isRecursive && !bodyNeedsIOMonad bodyElems then
    let isEffectful := bodyNeedsExceptionMonad bodyElems || bodyNeedsIOMonad bodyElems
    let hasAssert := bodyElems.any (jsonNodeType? · == some "Assert")
    let attrCmd ← if !isEffectful && !hasAssert && !nc
      then `(command| attribute [simp, taste_ingr] $defIdent)
      else `(command| attribute [simp] $defIdent)
    return #[finalCmd, attrCmd]
  else
    return #[finalCmd]

/-- A `__repr__`/`__str__` method becomes a `PyPrintable` instance, so `print(obj)` / `str(obj)`
use it (overriding the `deriving Repr` fallback). -/
def classPrintableInstance (className : String) (m : Json) (repr? : Option Json := none) :
    PygenM (TSyntax `command) := do
  let classTy : TSyntax `term := mkIdent className.toName
  let lamOf (m : Json) : PygenM (TSyntax `term) := do
    let bodyElems ← functionBodyElems m
    withCurrentClass className [] do functionValueSyntax #[(mkIdent `self, some classTy)] bodyElems
  let lam ← lamOf m
  let printableC ← `($(mkIdent ``PastaLean.PyPrintable) $classTy)
  -- With both, `str()`/`print` use `__str__` and a container's rendering uses `__repr__`.
  match repr? with
  | some r => `(command| instance : $printableC where
      pyStringify := $lam
      pyReprify := $(← lamOf r))
  | none => `(command| instance : $printableC where pyStringify := $lam)

/-- The operator typeclass and method a binary dunder implements (`a + b` → `PyHAdd.hAdd`). -/
def binaryDunderClass? : String → Option (Name × Name)
  | "__add__" => some (``PastaLean.PyHAdd, `hAdd)
  | "__sub__" => some (``PastaLean.PyHSub, `hSub)
  | "__mul__" => some (``PastaLean.PyHMul, `hMul)
  | "__truediv__" => some (``PastaLean.PyHDiv, `hDiv)
  | "__floordiv__" => some (``PastaLean.PyFloorDiv, `floorDiv)
  | "__mod__" => some (``PastaLean.PyModulo, `hMod)
  | _ => none

/-- The Python dunder a method implements: its name, or for one `@overload` of it (`__sub__'date`)
the name it specialises (`_dunder`). -/
def methodDunder (m : Json) : String :=
  (m.getObjValAs? String "_dunder").toOption.getD ((m.getObjValAs? String "name").toOption.getD "")

/-- Is this method a dunder that becomes a typeclass instance (beyond `__init__`/`__str__`/`__repr__`)? -/
def isInstanceDunder (m : Json) : Bool :=
  let d := methodDunder m
  (binaryDunderClass? d).isSome
    || ["__eq__", "__lt__", "__le__", "__neg__", "__abs__", "__hash__", "__bool__"].contains d

/-- Typeclass instances for a dunder method, which is also emitted as the plain method `C.<name>` they
call. A binary operator's operand and result types come from its annotations (default: the class), so
`date.__add__(self, other: timedelta) -> date` is `PyHAdd date timedelta date`; a dunder that raises
returns its effect monad (`PyHAdd date timedelta (PyExcept date)`), and the expression is awaited (its
`BinOp` is stamped by TypeInfer). `__lt__` also gives `Ord` (sorting, `min`), deciding ties by `__lt__`
both ways, as Python's sort does. -/
def classDunderInstances (className : String) (m : Json) : PygenM (Array (TSyntax `command)) := do
  let .ok mName := m.getObjValAs? String "name" | return #[]
  let dunder := methodDunder m
  let classTy : TSyntax `term := mkIdent className.toName
  let fn : TSyntax `term := mkIdent (Name.mkStr className.toName mName)
  let argInfos ← functionArgInfos m
  let bodyElems ← functionBodyElems m
  let monad? ← effectMonad? (stripResultMarkers bodyElems)
  let ret ← match ← functionReturnTypeSyntax? m with | some t => pure t | none => pure classTy
  let resTy ← match monad? with | some mo => `($mo $ret) | none => pure ret
  let otherTy := ((argInfos[1]?).bind (·.2)).getD classTy
  let a := mkIdent `a
  let b := mkIdent `b
  if let some (cls, field) := binaryDunderClass? dunder then
    return #[← `(command| instance : $(mkIdent cls) $classTy $otherTy $resTy where
        $(mkIdent field):ident := $fn)]
  match dunder with
  | "__eq__" => return #[← `(command| instance : BEq $classTy where beq := $fn)]
  -- A comparison that can raise (TypeInfer stamps its uses to call the method) still orders values
  -- for `sorted`/`min`: run purely, an exception surfacing as a recorded runtime error.
  | "__lt__" => do
      let lt ← if monad?.isSome then `(fun $a $b => PastaLean.runPure ($fn $a $b)) else pure fn
      return #[
      ← `(command| instance : LT $classTy := ⟨fun $a $b => $lt $a $b = true⟩),
      ← `(command| instance : DecidableRel (α := $classTy) (· < ·) := fun $a $b =>
            inferInstanceAs (Decidable ($lt $a $b = true))),
      ← `(command| instance : Ord $classTy :=
            ⟨fun $a $b => if $lt $a $b then .lt else if $lt $b $a then .gt else .eq⟩)]
  | "__le__" => do
      let le ← if monad?.isSome then `(fun $a $b => PastaLean.runPure ($fn $a $b)) else pure fn
      return #[
      ← `(command| instance : LE $classTy := ⟨fun $a $b => $le $a $b = true⟩),
      ← `(command| instance : DecidableRel (α := $classTy) (· ≤ ·) := fun $a $b =>
            inferInstanceAs (Decidable ($le $a $b = true)))]
  -- A raising `__neg__`/`__abs__` gets no instance: TypeInfer stamps the expression and codegen calls
  -- the method, awaited (`(← C.__neg__ x)`).
  | "__neg__" => do
      if monad?.isSome then return #[]
      return #[← `(command| instance : Neg $classTy := ⟨$fn⟩)]
  | "__abs__" => do
      if monad?.isSome then return #[]
      return #[← `(command| instance : $(mkIdent ``PastaLean.PyAbs) $classTy := ⟨$fn⟩)]
  | "__hash__" => return #[← `(command| instance : Hashable $classTy := ⟨fun $a => hash ($fn $a)⟩)]
  | "__bool__" => return #[← `(command| instance : $(mkIdent ``PastaLean.PyTruthy) $classTy := ⟨$fn⟩),
      ← `(command| instance : $(mkIdent ``PastaLean.PyBool) $classTy := ⟨$fn⟩)]
  | _ => return #[]

/-- Heap-typed parameter infos: each param's type is its HEAP type (objects/containers → `Ref`), so
constructor/method binders line up with the ref-typed fields. -/
def heapArgInfos (json : Json) : PygenM (Array (TSyntax `ident × Option (TSyntax `term))) := do
  let .ok args := json.getObjVal? "args" | throwError
    s!"FuncDef node does not have an 'args' field: {json}"
  let .ok argsArray := args.getObjValAs? (Array Json) "args" | throwError
    s!"FuncDef args does not have an 'args' field: {args}"
  let mut argInfos := #[]
  for arg in argsArray do
    let .ok argName := arg.getObjValAs? String "arg" | throwError
      s!"FuncDef argument does not have an 'arg' field: {arg}"
    let pty? : Option TypeInfer.PyType :=
      match jsonFieldOption arg "annotation" with
      | some annJson => some (TypeInfer.ofAnnotation annJson)
      | none => (jsonFieldOption arg "_ty").map TypeInfer.ofAnnotation
    let ty? ← match pty? with
      -- An un-pinnable param (`object`/`Any` → `.unknown`) is left untyped so Lean infers it from the
      -- body: `PyAny` when it feeds a `List PyAny` (a generic-container method), `Int`/etc. when used
      -- concretely. Ascribing `Int` here would reject `push("s")` onto a `PyAny` stack.
      | some .unknown => pure none
      | some pty => some <$> heapTypeSyntax pty
      | none => pure none
    argInfos := argInfos.push (mkIdent argName.toName, ty?)
  return argInfos

/-- Heap-typed return type (objects/containers → `Ref`); `none` when unknown. -/
def heapReturnTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  if json.getObjValAs? Bool "_box_return" == .ok true then return some (mkIdent ``PastaLean.PyAny)
  match returnAnnotation? json with
  | some ann => some <$> heapTypeSyntax (TypeInfer.ofAnnotation ann)
  | none => pure none

/-- `C.new` under `--heap`: build the object value (a record for a straight-line `__init__`, else a
threaded value) and `alloc` it, so the constructor returns `HeapM Val (Ref C)`. -/
def classInitConstructorHeap (className : String) (initJson : Json)
    (classFields : Array Json) (noneParams : List String) : PygenM (TSyntax `command) := do
  let mkIdentC := mkIdent (Name.mkStr className.toName "new")
  let classTy : TSyntax `term := mkIdent className.toName
  let heapVal := mkIdent `Val
  let refCod ← `(PastaLean.HeapM $heapVal (PastaLean.Ref $classTy))
  let argInfos := (← heapArgInfos initJson).drop 1
  let bodyElems ← functionBodyElems initJson
  let defaults := functionParamDefaults initJson
  let mkLambda (body : TSyntax `term) : PygenM (TSyntax `term) := do
    let mut result := body
    for (argIdent, ty?) in argInfos.toList.reverse do
      result ← match ty? with
        | some ty => `(fun ($argIdent : $ty) ↦ $result)
        | none => `(fun $argIdent ↦ $result)
    pure result
  let mkArrowDef (body : TSyntax `term) : PygenM (TSyntax `command) := do
    if argInfos.isEmpty then `(command| def $mkIdentC : $refCod := $body)
    else
      let result ← mkLambda body
      match ← functionArrowTypeSyntax? argInfos refCod with
      | some fullTy => `(command| def $mkIdentC : $fullTy := $result)
      | none => `(command| def $mkIdentC := $result)
  match initFieldAssignments? bodyElems with
  | some pairs =>
      withFreshVariables do
        let fields2 ← pairs.mapM fun (attr, valJson, isReal) => do
          let v ← if isReal then withRealContext true (getCode valJson `term) else getCode valJson `term
          -- A CONTAINER field's heap type is `Ref (container)`, so its `__init__` value must become a
          -- `Ref` with its element type pinned (so a `[None]*k`/`[None,None]` init's bare `none`
          -- resolves to `Option (Ref Node)` rather than a stuck metavariable). A LITERAL (`[None,None]`)
          -- was already `(← allocM …)`-wrapped by `allocIfHeap`, so only ASCRIBE the full `Ref` type;
          -- a raw container (`[x]*n`, a comprehension) is wrapped once. Object/scalar/`Option` fields
          -- keep their init (a `C()` call already yields a `Ref`).
          let v ← match classFields.find? (·.getObjValAs? String "name" == .ok attr) with
            | some fj =>
                let fieldTy := classFieldPyType className noneParams fj
                let inner? ← match fieldTy with
                  | .list e | .set e => pure (some (← `(List $(← heapElemTypeSyntax e))))
                  | .dict k vv => pure (some (← `(Std.HashMap $(← heapTypeSyntax k) $(← heapElemTypeSyntax vv))))
                  | _ => pure none
                match inner? with
                | some inner =>
                    if jsonNodeType? valJson == some "List" || jsonNodeType? valJson == some "Dict"
                        || jsonNodeType? valJson == some "Set" then
                      `(($v : PastaLean.Ref $inner))
                    else `((← PastaLean.allocM ($v : $inner)))
                | none => pure v
            | none => pure v
          `(Lean.Parser.Term.structInstField| $(mkIdent attr.toName):ident := $v)
        let recordBody : TSyntax `term ← `(({ $fields2:structInstField,* } : $classTy))
        -- A `do` block (even a one-statement one) lets container-field initializers `(← alloc …)`
        -- lift out of the record; the ascription pins `alloc`'s universe `V` to `Val` even when the
        -- `def` has no explicit arrow type (untyped constructor args).
        let allocBody ← `(((do PastaLean.alloc $recordBody) : $refCod))
        if defaults.isEmpty then mkArrowDef allocBody
        else
          let offset := argInfos.size - defaults.size
          let binders ← (Array.range argInfos.size).mapM fun i => do
            let (argIdent, ty?) := argInfos[i]!
            let d? := if i ≥ offset then some defaults[i - offset]! else none
            let tyStx ← match ty? with
              | some t => pure t
              | none => if d?.any (fun d => d.getObjValAs? String "node_type" == .ok "Constant"
                                            && (d.getObjVal? "value").toOption == some Json.null)
                        then `(Option (PastaLean.Ref $classTy)) else `(_)
            match d? with
            | some d => let dCode ← getCode d `term
                        `(Lean.Parser.Term.bracketedBinderF| ($argIdent : $tyStx := $dCode))
            | none => `(Lean.Parser.Term.bracketedBinderF| ($argIdent : $tyStx))
          `(command| def $mkIdentC $binders* : $refCod := $allocBody)
  | none =>
      let coreVal ← withFreshVariables do
        withCurrentClass className [] do
          classSelfThreadingValue #[] classTy bodyElems (selfIsParam := false)
      mkArrowDef (← `(((PastaLean.alloc $coreVal) : $refCod)))

/-- Whether a statement contains a value-yielding `return e` (a bare `return` yields `Unit`), scanning
the owned control-flow branches (`if`/`for`/`while`/`try`) but NOT nested `FunctionDef`/`Lambda`
bodies (whose returns belong to the inner scope). -/
partial def stmtReturnsValue (stmt : Json) : Bool :=
  match jsonNodeType? stmt with
  | some "Return" =>
      match jsonFieldOption stmt "value" with
      | some (.null) => false
      | some _ => true
      | none => false
  | some "FunctionDef" | some "Lambda" => false
  | _ =>
      match stmt with
      | .obj fields => fields.toList.any (fun (k, v) =>
          (k == "body" || k == "orelse" || k == "finalbody" || k == "handlers")
          && (match v with | .arr es => es.any stmtReturnsValue | _ => stmtReturnsValue v))
      | _ => false

/-- Whether any statement in a method body returns a value — used to decide a heap mutator's codomain
(a mutator that also `return`s a value must keep its real codomain, not be forced to `Unit`). -/
def bodyReturnsValue (bodyElems : Array Json) : Bool :=
  bodyElems.any stmtReturnsValue

/-- One method under `--heap`: `self : Ref C`, runs in `HeapM Val`; `self.x` reads/writes go through
`readRef`/`writeRef` (see `withHeapSelfRef`). Static/class methods keep the value-mode lowering. -/
def classMethodDefHeap (className : String) (info : ClassInfo) (m : Json) :
    PygenM (Array (TSyntax `command)) := do
  let .ok mName := m.getObjValAs? String "name" | throwError s!"Class method is missing a 'name': {m}"
  if info.staticmethods.contains mName || info.classmethods.contains mName then
    return ← classMethodDef className info m
  let defIdent := mkIdent (Name.mkStr className.toName mName)
  let classTy : TSyntax `term := mkIdent className.toName
  let heapVal := mkIdent `Val
  let isMutator := info.mutators.contains mName
  let bodyElems ← functionBodyElems m
  let dunderOps := ["__add__", "__sub__", "__mul__", "__eq__", "__lt__", "__le__", "__gt__", "__ge__"]
  let extraArgs := (← heapArgInfos m).drop 1
  let selfBinder ← `(Lean.Parser.Term.bracketedBinderF| (self : PastaLean.Ref $classTy))
  let mut extraBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinderF) := #[]
  for i in [0:extraArgs.size] do
    let (id, ty?) := extraArgs[i]!
    -- An operator dunder's first extra param (`other`) is conventionally the same class; type it a
    -- `Ref C` (usually unannotated) so `readRef other` / `other.x` resolve.
    let ty?' ← if ty?.isNone && dunderOps.contains mName && i == 0
               then pure (some (← `(PastaLean.Ref $classTy))) else pure ty?
    let b ← match ty?' with
      | some ty => `(Lean.Parser.Term.bracketedBinderF| ($id : $ty))
      | none => `(Lean.Parser.Term.bracketedBinderF| ($id))
    extraBinders := extraBinders.push b
  let binders := #[selfBinder] ++ extraBinders
  -- Register `self` and any class-typed params as heap-object variables so `self.x`/`p.x` reads in
  -- the body dereference. Operator dunders' second param (`other`) is conventionally the same class.
  let rawArgs := (((m.getObjVal? "args").toOption.bind
      (fun a => (a.getObjValAs? (Array Json) "args").toOption)).getD #[]).drop 1
  let mut bodyStx ← withFreshVariables do withCurrentClass className info.mutators do withHeapSelfRef do
    registerHeapVarClass `self className
    for arg in rawArgs do
      if let .ok argName := arg.getObjValAs? String "arg" then
        match (arg.getObjVal? "annotation").toOption with
        | some ann => match TypeInfer.ofAnnotation ann with
                      | .cls c => registerHeapVarClass argName.toName c
                      | _ => pure ()
        | none => pure ()
    if dunderOps.contains mName then
      if let some firstArg := rawArgs[0]? then
        if let .ok argName := firstArg.getObjValAs? String "arg" then
          registerHeapVarClass argName.toName className
    monadicFunctionBodySyntax bodyElems
  if bodyStx.isEmpty then bodyStx := #[← `(doElem| pure ())]
  -- The effect codomain is ASCRIBED to the body (`(do … : HeapM Val _)`), not put on the `def`
  -- header: a `_` in an explicit header type can't be inferred, but a hole in a body ascription can
  -- (the getter's return type is filled from the body's `return`).
  -- A pure mutator (assigns `self`, no value-returning `return`) is `HeapM Val Unit`. A mutator that
  -- ALSO returns a value keeps its real codomain (annotated `_ret_ty`, else an inferred `_`), like a
  -- getter — otherwise the `return` is silently coerced to `Unit` and the value is lost.
  let effCod ← if isMutator && !bodyReturnsValue bodyElems then `(PastaLean.HeapM $heapVal Unit)
               else match ← heapReturnTypeSyntax? m with
                 | some rt => `(PastaLean.HeapM $heapVal $rt)
                 | none => `(PastaLean.HeapM $heapVal _)
  return #[← `(command| def $defIdent $binders* := ((do
      $[$bodyStx:doElem]*) : $effCod))]

/-- Build the `structure C …` command for a class node (fields + `deriving` + docstring + `extends`).
Under `--heap` this is emitted by the `HeapPrelude` generator, so that all structs precede the
generated `Val` universe; otherwise `classDefSyntax` emits it inline. -/
def classStructCommand (json : Json) : PygenM (TSyntax `command) := do
  let .ok rawName := json.getObjValAs? String "name" | throwError
    s!"ClassDef node is missing a 'name': {json}"
  let name ← withRunSuffix rawName
  let nameId := mkIdent name.toName
  let .ok fields := json.getObjValAs? (Array Json) "fields" | throwError
    s!"ClassDef node is missing a 'fields' array: {json}"
  let .ok methods := json.getObjValAs? (Array Json) "methods" | throwError
    s!"ClassDef node is missing a 'methods' array: {json}"
  let bases := (json.getObjValAs? (Array Json) "bases").toOption.getD #[]
  let methodNames := methods.filterMap (·.getObjValAs? String "name" |>.toOption)
  let hasEq := methodNames.contains "__eq__"
  let hasRealField := (← getNumericMode) == .exact
    && fields.any (fun f => f.getObjValAs? Bool "_real" == .ok true)
  let mkDeriv (n : Name) : TSyntax ``Lean.Parser.Command.derivingClass :=
    ⟨mkNode ``Lean.Parser.Command.derivingClass #[mkNullNode, (mkIdent n).raw]⟩
  let derivs : Array (TSyntax ``Lean.Parser.Command.derivingClass) :=
    #[mkDeriv ``Inhabited]
      ++ (if hasRealField then #[] else #[mkDeriv ``Repr])
      ++ (if hasEq || hasRealField then #[] else #[mkDeriv ``BEq])
  let noneParams :=
    (methods.find? (·.getObjValAs? String "name" == .ok "__init__")).elim [] noneDefaultParamNames
  let fieldBinders ← fields.mapM (classStructFieldSyntax name noneParams)
  -- All bases (multiple inheritance → `structure C extends B1, B2`). Lean resolves an inherited
  -- method / conflicting field by MRO order (first base wins), matching Python. Each base is suffixed
  -- like the class's own name, so a `'rn` twin extends `Base'rn`, not `Base`.
  let baseIds : Array (TSyntax ``Lean.Parser.Command.structParent) ← bases.mapM (fun baseJson => do
    match baseJson.getObjValAs? String "id" with
    | .ok bid => do
        let bname ← withRunSuffix bid
        let t : TSyntax `term ← `($(mkIdent bname.toName))
        pure ⟨mkNode ``Lean.Parser.Command.structParent #[mkNullNode, t.raw]⟩
    | _ => throwError s!"Class base is not a simple Name: {baseJson}")
  let docStx? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    match (json.getObjValAs? String "docstring").toOption with
    | some text =>
        let body := (text.trimAscii).toString.replace "-/" "- /"
        some ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (body ++ " -/")]⟩
    | none => none
  match docStx?, baseIds.isEmpty with
  | some doc, false =>
      `(command| $doc:docComment structure $nameId:ident extends $baseIds,* where
          $[$fieldBinders]* deriving $derivs,*)
  | some doc, true =>
      `(command| $doc:docComment structure $nameId:ident where
          $[$fieldBinders]* deriving $derivs,*)
  | none, false =>
      `(command| structure $nameId:ident extends $baseIds,* where
          $[$fieldBinders]* deriving $derivs,*)
  | none, true =>
      `(command| structure $nameId:ident where
          $[$fieldBinders]* deriving $derivs,*)

@[pygen "ClassDef"]
def classDefSyntax : (kind : SyntaxNodeKind) → Json → PygenM (TSyntax kind)
  | `command, json => do
      let .ok rawName := json.getObjValAs? String "name" | throwError
        s!"ClassDef node is missing a 'name': {json}"
      -- Run-twin: the class is emitted as `CNN'rn`; its methods/constructor follow (`CNN'rn.new`,
      -- `CNN'rn.forward`) since they are built from this name, and references to `CNN` are suffixed
      -- by the Name pygen + the constructor/method call sites.
      let name ← withRunSuffix rawName
      let nameId := mkIdent name.toName
      let .ok fields := json.getObjValAs? (Array Json) "fields" | throwError
        s!"ClassDef node is missing a 'fields' array: {json}"
      let .ok methods := json.getObjValAs? (Array Json) "methods" | throwError
        s!"ClassDef node is missing a 'methods' array: {json}"
      let mutators := (json.getObjValAs? (Array String) "mutators").toOption.getD #[]
      let valueMutators := (json.getObjValAs? (Array String) "value_mutators").toOption.getD #[]
      let staticmethods := (json.getObjValAs? (Array String) "staticmethods").toOption.getD #[]
      let classmethods := (json.getObjValAs? (Array String) "classmethods").toOption.getD #[]

      -- Record class metadata so later top-level statements can dispatch instantiation/methods.
      let methodNames := methods.filterMap (·.getObjValAs? String "name" |>.toOption)
      let info : ClassInfo := {
        methods := methodNames.toList
        mutators := mutators.toList
        valueMutators := valueMutators.toList
        staticmethods := staticmethods.toList
        classmethods := classmethods.toList }
      registerClass name info

      -- A class with an `ℝ` field (exact mode) can't derive a COMPUTABLE `BEq`/`Repr`, and its
      -- constructor builds an `ℝ` struct → `noncomputable` (consulted by `classInitConstructor`).
      let hasRealField := (← getNumericMode) == .exact
        && fields.any (fun f => f.getObjValAs? Bool "_real" == .ok true)
      -- The `structure` itself: under `--heap` the `HeapPrelude` generator emits every struct (so
      -- they all precede the generated `Val` universe), so skip it here; otherwise emit it inline
      -- together with the value-semantics instances.
      let mut members : Array (TSyntax `command) := #[]
      unless (← getHeapMode) do
        members := #[← classStructCommand json]
        -- A class instance is a non-`None` object, so Python truthiness on it is always `true`
        -- (`if node:` / `while node:`); a nullable cursor is `Option C`, whose own `PyTruthy` handles
        -- the `none` case. Without this, `if node:` on a bare-typed `ListNode`/`TreeNode` has no instance.
        members := members.push
          (← `(command| instance : PastaLean.PyTruthy $nameId where truthy _ := true))
        members := members.push
          (← `(command| instance : PastaLean.PyBool $nameId where pyBool _ := true))
        -- `type(instance)` / `isinstance(instance, C)` report the class: `PyType.cls "C"`.
        members := members.push
          (← `(command| instance : PastaLean.PyTyped $nameId where
                 pyTypeOf _ := TypeInfer.PyType.cls $(Syntax.mkStrLit rawName)))
        -- Lift a bare node into `Option C` so a nullable cursor (`curr = head`, later `curr = curr.next`)
        -- ascribed `Option C` takes its bare initial value, and `curr = ListNode(...)` reassignments fit.
        members := members.push
          (← `(command| instance : Coe $nameId (Option $nameId) := ⟨some⟩))
        -- An instance of a subclass is an instance of each base (`f(xs)` with `xs : list[Sub]` where
        -- `f` takes `Iterable[Base]`): coerce through the `extends` parent projection.
        if let .ok bases := json.getObjValAs? (Array Json) "bases" then
          for b in bases do
            if let .ok bid := b.getObjValAs? String "id" then
              let bname ← withRunSuffix bid
              if (← isRegisteredClass bid) then
                members := members.push (← `(command| instance : Coe $nameId $(mkIdent bname.toName) :=
                  ⟨fun x => x.$(mkIdent ("to" ++ bname).toName)⟩))

      -- Constructor (from `__init__`), operator/printable dunders, and the remaining methods.
      let heap ← getHeapMode
      let mut hasInit := false
      for m in methods do
        let .ok mName := m.getObjValAs? String "name" | throwError
          s!"Class method is missing a 'name': {m}"
        if mName == "__init__" then
          hasInit := true
          members := members.push (← if heap then classInitConstructorHeap name m fields (noneDefaultParamNames m)
                                     else classInitConstructor name m hasRealField)
        else if heap then
          -- Under `--heap`, every method (including dunders/`__str__`) is a plain heap method over
          -- `Ref C`; operator/print dispatch through typeclasses on refs is future work.
          members := members ++ (← classMethodDefHeap name info m)
        else if mName == "__str__" || (mName == "__repr__" && !methodNames.contains "__str__") then
          -- Prefer `__str__` for `pyStringify` when both are defined (Python `str()`/`print`).
          let repr? := if mName == "__str__" then
            methods.find? (·.getObjValAs? String "name" == .ok "__repr__") else none
          members := members.push (← classPrintableInstance name m repr?)
        else if mName == "__repr__" then
          pure ()  -- folded into the `__str__` instance
        else if isInstanceDunder m then
          members := members ++ (← classMethodDef name info m) ++ (← classDunderInstances name m)
        else
          members := members ++ (← classMethodDef name info m)
      -- No `__init__`: `C()` builds an all-defaults instance (fields use their declared defaults).
      unless hasInit do
        if heap then
          let heapVal := mkIdent `Val
          members := members.push (← `(command| def $(mkIdent (Name.mkStr name.toName "new")) :
            PastaLean.HeapM $heapVal (PastaLean.Ref $nameId) :=
              ((PastaLean.alloc (default : $nameId)) : PastaLean.HeapM $heapVal (PastaLean.Ref $nameId))))
        else
          members := members.push (← `(command| def $(mkIdent (Name.mkStr name.toName "new")) : $nameId := default))
      return ⟨mkNullNode (members.map (·.raw))⟩
  | kind, _ => throwError
      s!"ClassDef is only supported at command (top-level) position, not '{kind}'."

end PastaLean
