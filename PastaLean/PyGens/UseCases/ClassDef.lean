import Mathlib
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
        | some initJson => TypeInfer.ofValue initJson
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
          | some initJson => pure ((← pyTypeSyntax? (TypeInfer.ofValue initJson)).getD intTy)
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
    (classTyTerm : TSyntax `term) (bodyElems : Array Json) (selfIsParam : Bool) :
    PygenM (TSyntax `term) := withFreshVariables do
  let selfId := mkIdent `self
  addVar `self
  let selfDecl ← if selfIsParam then `(doElem| let mut $selfId:ident := $selfId:ident)
                 else `(doElem| let mut $selfId:ident : $classTyTerm := default)
  -- `self` is declared above; the body may also reassign an ordinary parameter (`while x <= self.n: … x += …`).
  let paramPrelude ← mutatedParamPrelude (argInfos.filter (·.1.getId != `self)) bodyElems
  let bodyStxArray ← monadicFunctionBodySyntax bodyElems
  let idRun := mkIdent ``Id.run
  let core ← `($idRun do
      $selfDecl:doElem
      $[$paramPrelude:doElem]*
      $[$bodyStxArray:doElem]*
      return $selfId:term)
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
      let valueStx ← withFreshVariables do
        withCurrentClass className [] do
          classSelfThreadingValue argInfos classTy bodyElems (selfIsParam := false)
      let mkDef : TSyntax `term → PygenM (TSyntax `command) := fun ty =>
        if hasRealField then `(command| noncomputable def $mkIdentC : $ty := $valueStx)
        else `(command| def $mkIdentC : $ty := $valueStx)
      match ← functionArrowTypeSyntax? argInfos classTy with
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
    else
      functionValueSyntax bodyArgInfos bodyElems
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
  if (← getNumericMode) == .exact && !isRecursive then
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
def classPrintableInstance (className : String) (m : Json) : PygenM (TSyntax `command) := do
  let classTy : TSyntax `term := mkIdent className.toName
  let bodyElems ← functionBodyElems m
  let lam ← withCurrentClass className [] do
    functionValueSyntax #[(mkIdent `self, some classTy)] bodyElems
  let printableC ← `($(mkIdent ``PastaLean.PyPrintable) $classTy)
  `(command| instance : $printableC where pyStringify := $lam)

/-- Operator dunders become the runtime operator typeclass instances the generated code dispatches
through: `__add__`→`PyHAdd` (used by `+ₚ`), `__sub__`→`PyHSub`, `__mul__`→`PyHMul`, `__eq__`→`BEq`
(used by `==`). Returns `none` for a non-operator method name. -/
def classDunderInstance? (className : String) (m : Json) : PygenM (Option (TSyntax `command)) := do
  let .ok mName := m.getObjValAs? String "name" | return none
  let classTy : TSyntax `term := mkIdent className.toName
  let bodyElems ← functionBodyElems m
  let argInfos := #[(mkIdent `self, some classTy)] ++ (← functionArgInfos m).drop 1
  let lam ← withCurrentClass className [] do functionValueSyntax argInfos bodyElems
  match mName with
  | "__add__" => some <$> `(command| instance : $(mkIdent ``PastaLean.PyHAdd) $classTy $classTy $classTy where hAdd := $lam)
  | "__sub__" => some <$> `(command| instance : $(mkIdent ``PastaLean.PyHSub) $classTy $classTy $classTy where hSub := $lam)
  | "__mul__" => some <$> `(command| instance : $(mkIdent ``PastaLean.PyHMul) $classTy $classTy $classTy where hMul := $lam)
  | "__eq__"  => some <$> `(command| instance : BEq $classTy where beq := $lam)
  | _ => return none

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
  match (jsonFieldOption json "returns").orElse (fun _ => jsonFieldOption json "_ret_ty") with
  | some ann => some <$> heapTypeSyntax (TypeInfer.ofAnnotation ann)
  | none => pure none

/-- `C.new` under `--heap`: build the object value (a record for a straight-line `__init__`, else a
threaded value) and `alloc` it, so the constructor returns `HeapM Val (Ref C)`. -/
def classInitConstructorHeap (className : String) (initJson : Json) : PygenM (TSyntax `command) := do
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
        let fields ← pairs.mapM fun (attr, valJson, isReal) => do
          let v ← if isReal then withRealContext true (getCode valJson `term) else getCode valJson `term
          `(Lean.Parser.Term.structInstField| $(mkIdent attr.toName):ident := $v)
        let recordBody : TSyntax `term ← `(({ $fields:structInstField,* } : $classTy))
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
  let baseId? : Option (TSyntax `ident) ←
    match bases[0]? with
    | some baseJson =>
        match baseJson.getObjValAs? String "id" with
        -- Suffix the base like the class's own name, so a `'rn` twin extends `Base'rn`, not `Base`.
        | .ok bid => do
            let bname ← withRunSuffix bid
            pure (some (mkIdent bname.toName))
        | _ => throwError s!"Class base is not a simple Name: {baseJson}"
    | none => pure none
  let docStx? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    match (json.getObjValAs? String "docstring").toOption with
    | some text =>
        let body := (text.trimAscii).toString.replace "-/" "- /"
        some ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (body ++ " -/")]⟩
    | none => none
  match docStx?, baseId? with
  | some doc, some baseId =>
      `(command| $doc:docComment structure $nameId:ident extends $baseId:ident where
          $[$fieldBinders]* deriving $derivs,*)
  | some doc, none =>
      `(command| $doc:docComment structure $nameId:ident where
          $[$fieldBinders]* deriving $derivs,*)
  | none, some baseId =>
      `(command| structure $nameId:ident extends $baseId:ident where
          $[$fieldBinders]* deriving $derivs,*)
  | none, none =>
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
      let staticmethods := (json.getObjValAs? (Array String) "staticmethods").toOption.getD #[]
      let classmethods := (json.getObjValAs? (Array String) "classmethods").toOption.getD #[]

      -- Record class metadata so later top-level statements can dispatch instantiation/methods.
      let methodNames := methods.filterMap (·.getObjValAs? String "name" |>.toOption)
      let info : ClassInfo := {
        methods := methodNames.toList
        mutators := mutators.toList
        staticmethods := staticmethods.toList
        classmethods := classmethods.toList }
      registerClass name info

      -- A class with an `ℝ` field (exact mode) can't derive a COMPUTABLE `BEq`/`Repr`, and its
      -- constructor builds an `ℝ` struct → `noncomputable` (consulted by `classInitConstructor`).
      let hasRealField := (← getNumericMode) == .exact
        && fields.any (fun f => f.getObjValAs? Bool "_real" == .ok true)
      -- The `structure` itself: under `--heap` the `HeapPrelude` generator emits every struct (so
      -- they all precede the generated `Val` universe), so skip it here; otherwise emit it inline.
      let mut members : Array (TSyntax `command) := #[]
      unless (← getHeapMode) do
        members := #[← classStructCommand json]

      -- Constructor (from `__init__`), operator/printable dunders, and the remaining methods.
      let heap ← getHeapMode
      let mut hasInit := false
      for m in methods do
        let .ok mName := m.getObjValAs? String "name" | throwError
          s!"Class method is missing a 'name': {m}"
        if mName == "__init__" then
          hasInit := true
          members := members.push (← if heap then classInitConstructorHeap name m
                                     else classInitConstructor name m hasRealField)
        else if heap then
          -- Under `--heap`, every method (including dunders/`__str__`) is a plain heap method over
          -- `Ref C`; operator/print dispatch through typeclasses on refs is future work.
          members := members ++ (← classMethodDefHeap name info m)
        else if mName == "__str__" || (mName == "__repr__" && !methodNames.contains "__str__") then
          -- Prefer `__str__` for `pyStringify` when both are defined (Python `str()`/`print`).
          members := members.push (← classPrintableInstance name m)
        else if mName == "__repr__" then
          pure ()  -- shadowed by `__str__`

        else if let some inst ← classDunderInstance? name m then
          members := members.push inst
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
