import Lean
import Qq
import PastaLean.Basic

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-!
## Numeric lowering mode

Controls how a Python `float` is lowered: `exact` → Lean `ℚ` (an exact, *computable* and
*provable* ordered field — the default, so generated functions can be reasoned about with
`ring`/`nlinarith`); `approx` → `Float` (IEEE; fast and computable but not a ring, so unprovable).
The mode is set per backend request (see `py2lean.lean`) into a global ref the codegen reads.
-/

inductive NumericMode where
  | exact
  | approx
  deriving Repr, BEq, Inhabited

initialize numericModeRef : IO.Ref NumericMode ← IO.mkRef .exact

/-- Read the current numeric lowering mode (set per backend request). -/
def getNumericMode : IO NumericMode := numericModeRef.get

/-- Opt-in reference semantics (`--heap`): when `true`, generators emit heap-monad ops (`alloc`/
`readRef`/`modifyRef`) so class instances and mutable containers alias like real Python objects,
instead of the default value-semantics rebuild-and-reassign. Set per backend request. -/
initialize heapModeRef : IO.Ref Bool ← IO.mkRef false

/-- Read whether opt-in heap/reference semantics is active (set per backend request). -/
def getHeapMode : IO Bool := heapModeRef.get

/-- True when `float` should lower to `ℚ` (the default exact mode). -/
def numericModeIsExact : IO Bool := return (← getNumericMode) == .exact

/-- Whether the function currently being lowered is "real-valued" — it (transitively) produces an
`ℝ` transcendental (the Python pass stamps such defs `_real_fn`). While set, exact-mode `float`
literals/params lower to `ℝ` instead of `ℚ`, so the whole function is uniformly `ℝ` (noncomputable)
rather than a `ℚ`/`ℝ` mix that won't type-check. Only consulted in exact mode. -/
initialize realContextRef : IO.Ref Bool ← IO.mkRef false

/-- Read whether we're lowering inside a real-valued (`ℝ`) function body. -/
def getRealContext : IO Bool := realContextRef.get

/-- True while lowering the body of a function whose return is boxed to `PyAny` (its branches
return disagreeing types). Each `return e` then ascribes `(e : PyAny)`, so `try/catch` branches
coerce individually instead of Lean unifying their types from the first return. -/
initialize boxReturnRef : IO.Ref Bool ← IO.mkRef false

/-- Read whether we're lowering inside a `PyAny`-boxed-return function body. -/
def getBoxReturnContext : IO Bool := boxReturnRef.get

/-- The return annotation (`returns`/`_ret_ty` JSON) of the function whose body is being lowered. -/
initialize retAnnotationRef : IO.Ref (Option Lean.Json) ← IO.mkRef none

def getReturnAnnotation : IO (Option Lean.Json) := retAnnotationRef.get

/-- Set while lowering a function whose returns mix `int` and `float` (`_ret_float`): each return
value is ascribed to the mode float (`ℚ`/`Float`) so a mixed ternary `return -1 if … else v`
coerces the `int` branch up instead of pinning the type to `ℤ` from the first branch. -/
initialize retFloatRef : IO.Ref Bool ← IO.mkRef false

/-- Read whether we're lowering inside a float-return-reconciled function body. -/
def getRetFloatContext : IO Bool := retFloatRef.get

/-- True while lowering a *condition position* — the direct test of an `if`/`while` — where a
comparison may be a `Prop` (`a < b`, and `a = b`/`a ≠ b` in exact mode) so it is provable, paired
with the `if h : …` hypothesis. False everywhere else (the default): a comparison used as a *value*
— a comprehension element, an `and`/`or` operand, an `any`/`all` generator — must stay `Bool`
(`decide (a < b)`, `==`), since a `Prop` has no value there. `Float` equality stays `==` regardless
(no `DecidableEq`). See `compareApplyTerm`. -/
initialize propConditionRef : IO.Ref Bool ← IO.mkRef false

/-- Read whether comparisons may currently lower to a provable `Prop` (condition position). -/
def getPropCondition : IO Bool := propConditionRef.get

/-- Set while lowering an expression whose *truthiness* is what matters — e.g. an element of
`any(...)`/`all(...)`. There a `BoolOp` (`a and b`) must stay a `Bool` connective (`pyTruthy a && b`)
rather than the value form `if pyTruthy a then b else a`, whose branches would be different types
(`a : List`, `b : Bool`). Unlike `propCondition` it does NOT force comparisons to `Prop` (so an
`any(a == b for …)` stays `List Bool`), and comprehensions do NOT reset it. -/
initialize truthinessContextRef : IO.Ref Bool ← IO.mkRef false

/-- Read whether the current expression is evaluated only for its truthiness. -/
def getTruthinessContext : IO Bool := truthinessContextRef.get

/-- Inside a memoized function's body (a `@cache`/`@lru_cache` run-twin), the base name of the
function being memoized paired with its `StateM` worker `fooMemo'rn`, so a recursive self-call lowers
to a monadic `(← fooMemo'rn args)` threading the shared cache instead of an unmemoized plain call. -/
initialize memoizeSelfRef : IO.Ref (Option (String × Lean.Name)) ← IO.mkRef none

/-- Read the currently-memoized function's (base name, `StateM` worker name), if any. -/
def getMemoizeSelf : IO (Option (String × Lean.Name)) := memoizeSelfRef.get

/-- When emitting the runnable "twin" of a declaration in `--mode both`, this is the suffix (`'rn`)
appended to every top-level definition name AND to references to other user-defined functions/classes
(listed in `userNamesRef`). Empty for the single-version `prove`/`run` modes. Lets one file carry the
provable `foo` and the runnable `foo'rn` side by side. -/
initialize runSuffixRef : IO.Ref String ← IO.mkRef ""

/-- The names of the user's top-level functions/classes — references to these get `runSuffix` appended
in a run-twin so `foo'rn` calls `bar'rn` / builds `CNN'rn`, not the `prove` `bar`/`CNN`. -/
initialize userNamesRef : IO.Ref (List String) ← IO.mkRef []

/-- Best-effort mode (set from the translate task's `best_effort`): a single statement whose codegen
throws is degraded to a `pyUnsupported` placeholder — keeping the REST of the function — instead of the
whole `FunctionDef` collapsing. Off by default (strict). -/
initialize bestEffortRef : IO.Ref Bool ← IO.mkRef false

/-- Set while lowering the body of a VALUE+MUTATE class method — one that mutates `self` AND returns a
value (union-find `union`). Each `return v` is emitted as `return (v, self)` so the caller receives
BOTH the result and the mutated receiver (which it reassigns). Empty outside such a method. -/
initialize valueMutatorRef : IO.Ref Bool ← IO.mkRef false

/-- Read whether we're lowering a value+mutate method body (so `return v` → `return (v, self)`). -/
def getValueMutatorContext : IO Bool := valueMutatorRef.get

/-- The suffix to append to a top-level def name being emitted (empty unless in a run-twin). -/
def getRunSuffix : IO String := runSuffixRef.get

/-- Append the run-twin suffix to a name unconditionally (for the def being emitted). -/
def withRunSuffix (name : String) : IO String := return name ++ (← getRunSuffix)

/-- Append the run-twin suffix to a *reference* only when it names a user function/class (so locals
and library names are untouched). -/
def suffixIfUserName (name : String) : IO String := do
  let names ← userNamesRef.get
  -- A class-library name (`date!lib`) is compiled with both twins, so the run twin is `date'rn`
  -- in every runnable translation, `--mode run` included.
  if names.contains (name ++ "!lib") then
    return if (← numericModeRef.get) == .approx then name ++ "'rn" else name
  if names.contains name then return name ++ (← getRunSuffix) else return name

/-!
## Code generation from JSON data

This module provides a way to generate Lean code from JSON data in an extensible way. The main function is `getCode`, which takes a `pygenerator` a Json object and a syntax category, and returns the corresponding syntax (in the monad `PygenM`) or throws an error.
-/

namespace PyGen

structure State where
  varNames : HashSet Name := HashSet.emptyWithCapacity 100
  /-- Variables known to hold a Python `set` (assigned from `set(...)`, a `{…}` literal, or a set
  operation). Set comparisons (`==`, `<=`, …) are order-independent, unlike the list-backed `==`/`≤`
  the same `List` value would otherwise use — see the `Compare` lowering. -/
  setVars : HashSet Name := HashSet.emptyWithCapacity 16
  /-- Variables holding a `sortedcontainers.SortedList` (assigned from `SortedList(...)`). Their
  `add`/`remove`/`discard` maintain sort order instead of set semantics; the value is a plain sorted
  `List`, so subscript/`len`/`in`/iteration use the ordinary list protocols. -/
  sortedVars : HashSet Name := HashSet.emptyWithCapacity 8
  /-- Variables holding a library-owned object, mapped to the owning module (`m = hashlib.md5()`
  ↦ `m ↦ "hashlib"`), so `m.update(...)` dispatches through `Libraries.libraryMethod?` rather than
  the builtin method map. Generalises `sortedVars` to any library that declares `constructsObject`. -/
  libObjVars : Std.HashMap Name String := ∅
  /-- Variables known to hold a dict (assigned from `{…}`, a dict comprehension, or `dict(…)`/
  `defaultdict(…)`/`Counter(…)`). `d.pop(k)` on a dict is the DICT pop (remove key, return value),
  which shares the method name with a 1-arg `list.pop(i)`; the receiver's dict-ness disambiguates. -/
  dictVars : HashSet Name := HashSet.emptyWithCapacity 16
  /-- Variables whose slot type is `Option T` (a `None`-initialised sentinel local, `ans = None`, later
  reassigned a `T`). Ordered comparisons (`t < ans`) and the `X if ans is None else ans` coalescing
  return must UNWRAP the `Option` — there is no `String < Option String` / `Option String → String`.
  `pyLen`/`is None`/reassignment already handle the `Option` directly, so those are left untouched. -/
  optionVars : HashSet Name := HashSet.emptyWithCapacity 16
  /-- Variables bound with `let mut` (reassignable in place). An immutable `let` loop var that a body
  reassigns to a different type is shadowed instead; a `let mut` (incl. a `PyAny` slot) is not. -/
  mutVars : HashSet Name := HashSet.emptyWithCapacity 32
  /-- Mut vars whose slot type is `PyAny`. A `PyAny` slot absorbs any later value by coercion, so a
  cross-type reassignment to it is a plain reassign — NOT a type-changing `'rbN` rebind. -/
  pyAnySlotVars : HashSet Name := HashSet.emptyWithCapacity 16
  /-- SSA renames for type-changing rebinds. When `s = list(s)` reassigns an existing `let mut s`
  (a `str`) to a `List`, we can neither re-`let mut s` (Lean forbids shadowing a mut var) nor
  reassign (types differ), so we bind a fresh `let mut s'rbN` and map `s ↦ s'rbN` here; every later
  reference to `s` resolves through this map. Scoped per top-level statement (fresh state) and
  saved/restored around each block (a branch-local rebind stays branch-local). -/
  renames : Std.HashMap Name Name := {}
  renameCounter : Nat := 0
  checkExr : Bool := true
  useArrow : Bool := false
  /-- When the innermost enclosing loop has a Python `else` clause, this holds the name of the
  `let mut` flag that records whether a `break` fired (so the `else` runs only on natural
  completion). `none` means the innermost loop has no `else`, so `break` lowers plainly. -/
  breakFlag : Option Name := none
  /-- While lowering the methods of a `class C`, the class name `C` (so `self.method(..)` calls
  inside the body dispatch to `C.method`). `none` outside any class body. -/
  currentClass : Option String := none
  /-- The mutator-method names of the class currently being lowered (a `self.m(..)` call to one of
  these reassigns `self`). Empty outside a class body. -/
  currentClassMutators : List String := []
  /-- Under `--heap`, true while lowering a method body where `self` is a `Ref C` (so `self.x` reads
  become `(← readRef self).x` and `self.x = v` becomes a `writeRef`). False in `__init__` bodies,
  where `self` is still a plain value being built before `alloc`. -/
  heapSelfRef : Bool := false
  /-- Under `--heap`, the class of each local/parameter that holds a heap object (`p = Point(..)` →
  `p ↦ "Point"`, a param `q : Point`). Lets a non-`self` attribute read `p.x` dereference the ref:
  `(← readRef p).x`. Function-scoped (reset by `withFreshVariables`). -/
  heapVarClasses : List (Name × String) := []
  /-- Under `--heap`, the local/parameter names that hold a mutable container by reference (`xs = []`,
  or `ys = xs`) — i.e. are a `Ref (List …)`/`Ref (HashMap …)`. Lets container reads (`xs[i]`, `len xs`,
  `for x in xs`) dereference and mutations (`xs.append`) `modifyRef`. Function-scoped. -/
  heapVarContainers : List Name := []
  /-- Under `--heap`, local/parameter names promoted to a shared **variable cell** because a nested
  closure captures and mutates them. A cell presents as `(← readRefM id)` in ordinary value positions
  and as the raw ref in a `_heap_cell_arg` call arg. Holds both scalar cells (`Ref τ`) and
  container/object cells (`Ref (Ref T)`). Function-scoped. -/
  heapCellVars : List Name := []
  /-- The container/object subset of `heapCellVars` (`Ref (Ref T)`) — these also drive
  `heapContainerRef?` so `.append`/`len`/`[]` dereference to the inner object. Function-scoped. -/
  heapCellContainers : List Name := []
  deriving Inhabited, Repr

end PyGen

abbrev PygenM := StateT PyGen.State TermElabM

def withPygenState {α : Type} (modifyState : PyGen.State → PyGen.State) (x : PygenM α) :
    PygenM α := do
  let saved ← get
  set (modifyState saved)
  try
    let result ← x
    set saved
    return result
  catch e =>
    set saved
    throw e

def withPygenStateField {α β : Type} (getField : PyGen.State → β)
    (setField : PyGen.State → β → PyGen.State) (value : β) (x : PygenM α) :
    PygenM α := do
  let saved := getField (← get)
  modify fun st => setField st value
  try
    let result ← x
    modify fun st => setField st saved
    return result
  catch e =>
    modify fun st => setField st saved
    throw e

def withoutCheck {α : Type} (x : PygenM α) : PygenM α :=
  withPygenStateField (·.checkExr) (fun st checkExr => { st with checkExr := checkExr }) false x

def withUseArrow {α : Type} (x : PygenM α) : PygenM α :=
  withPygenStateField (·.useArrow) (fun st useArrow => { st with useArrow := useArrow }) true x

/-- Run `x` with `r` set to `v`, restoring its value afterwards (also when `x` throws). -/
def withRefSet {α β : Type} (r : IO.Ref β) (v : β) (x : PygenM α) : PygenM α := do
  let saved ← r.get
  r.set v
  try x finally r.set saved

/-- Run `x` with the real-context flag set to `b` (restoring it afterwards). Used to lower a
real-marked assignment's RHS so its float literals (and list literals) become `ℝ`. -/
def withRealContext {α : Type} (b : Bool) (x : PygenM α) : PygenM α :=
  withRefSet realContextRef b x

/-- Run `x` with the boxed-return flag set to `b` (restoring it afterwards). -/
def withBoxReturnContext {α : Type} (b : Bool) (x : PygenM α) : PygenM α :=
  withRefSet boxReturnRef b x

/-- Run `x` with the current function's return annotation set to `ann?` (restoring it afterwards). -/
def withReturnAnnotation {α : Type} (ann? : Option Lean.Json) (x : PygenM α) : PygenM α :=
  withRefSet retAnnotationRef ann? x

/-- Run `x` with the float-return-reconcile flag set to `b` (restoring it afterwards). -/
def withRetFloatContext {α : Type} (b : Bool) (x : PygenM α) : PygenM α :=
  withRefSet retFloatRef b x

/-- Run `x` with the memoize-self context set (a recursive self-call to `name` lowers to
`(← $worker args)`), restoring it afterwards. -/
def withMemoizeSelf {α : Type} (ctx : Option (String × Lean.Name)) (x : PygenM α) : PygenM α :=
  withRefSet memoizeSelfRef ctx x

/-- Run `x` with the truthiness flag set to `b` (restoring it afterwards). Set by `any`/`all` around
their element so a `BoolOp` there stays a `Bool` connective, not the mixed-type value form. -/
def withTruthinessContext {α : Type} (b : Bool) (x : PygenM α) : PygenM α :=
  withRefSet truthinessContextRef b x

/-- Run `x` with the prop-condition flag set to `b` (restoring it afterwards). `if`/`while` set it
`true` around lowering their test; `and`/`or`/`not` operands set it back `false` (they need `Bool`). -/
def withPropCondition {α : Type} (b : Bool) (x : PygenM α) : PygenM α :=
  withRefSet propConditionRef b x

/-- Lower `x` in real-context when `json` carries the per-variable `_real` stamp (exact mode) — set
by the Python pass on every assignment whose root variable holds an `ℝ` value, so the RHS literals
are born `ℝ` (scalars would coerce, but `List ℚ ↛ List ℝ`, so list literals must be `ℝ` directly). -/
def withRealIfMarked {α : Type} (json : Lean.Json) (x : PygenM α) : PygenM α := do
  if (← getNumericMode) == .exact && json.getObjValAs? Bool "_real" == .ok true then
    withRealContext true x
  else
    x

def withFixedVariables {α : Type} (x : PygenM α) : PygenM α := do
  withPygenStateField (·.varNames) (fun st varNames => { st with varNames := varNames }) (← get).varNames <|
    withPygenStateField (·.setVars) (fun st setVars => { st with setVars := setVars }) (← get).setVars <|
     withPygenStateField (·.sortedVars) (fun st sortedVars => { st with sortedVars := sortedVars }) (← get).sortedVars <|
      withPygenStateField (·.libObjVars) (fun st libObjVars => { st with libObjVars := libObjVars }) (← get).libObjVars <|
      withPygenStateField (·.dictVars) (fun st dictVars => { st with dictVars := dictVars }) (← get).dictVars <|
       withPygenStateField (·.optionVars) (fun st optionVars => { st with optionVars := optionVars }) (← get).optionVars <|
       withPygenStateField (·.renames) (fun st renames => { st with renames := renames }) (← get).renames <|
        withPygenStateField (·.mutVars) (fun st mutVars => { st with mutVars := mutVars }) (← get).mutVars <|
         withPygenStateField (·.pyAnySlotVars) (fun st v => { st with pyAnySlotVars := v }) (← get).pyAnySlotVars x

/-- Run `x` with the current loop's break-flag set to `flag?`. A loop body always overrides the
flag (to its own `else` flag, or `none`) so a `break` binds to the innermost loop only. -/
def withBreakFlag {α : Type} (flag? : Option Name) (x : PygenM α) : PygenM α :=
  withPygenStateField (·.breakFlag) (fun st breakFlag => { st with breakFlag := breakFlag }) flag? x

def getBreakFlag : PygenM (Option Name) := do
  return (← get).breakFlag

def isCheckEnabled : PygenM Bool := do
  return (← get).checkExr

def isUseArrowEnabled : PygenM Bool := do
  return (← get).useArrow

def hasVar (usedName : Name) : PygenM Bool := do
  return (← get).varNames.contains usedName

def addVar (usedName : Name) : PygenM Unit := do
  modify fun st => { st with varNames := st.varNames.insert usedName }

/-- Whether `self` is currently a `Ref C` (a `--heap` method body) rather than a plain value. -/
def getHeapSelfRef : PygenM Bool := do
  return (← get).heapSelfRef

/-- Record that local/parameter `n` holds a heap object of class `cls` (so `n.x` dereferences). -/
def registerHeapVarClass (n : Name) (cls : String) : PygenM Unit := do
  modify fun st => { st with heapVarClasses := (n, cls) :: st.heapVarClasses }

/-- The class of a heap-object local/parameter `n`, if known. -/
def heapVarClassOf? (n : Name) : PygenM (Option String) := do
  return ((← get).heapVarClasses.find? (·.1 == n)).map (·.2)

/-- Record that local/parameter `n` holds a mutable container by reference. -/
def registerHeapVarContainer (n : Name) : PygenM Unit := do
  modify fun st => { st with heapVarContainers := n :: st.heapVarContainers }

/-- Whether `n` is a container-ref local/parameter. -/
def isHeapVarContainer (n : Name) : PygenM Bool := do
  return (← get).heapVarContainers.contains n

/-- Record that local/parameter `n` is a scalar variable cell (`Ref τ`) — captured and mutated by a
nested closure. -/
def registerHeapScalarCell (n : Name) : PygenM Unit := do
  modify fun st => { st with heapCellVars := n :: st.heapCellVars }

/-- Record that local/parameter `n` is a container/object variable cell (`Ref (Ref T)`). -/
def registerHeapContainerCell (n : Name) : PygenM Unit := do
  modify fun st => { st with heapCellVars := n :: st.heapCellVars,
                             heapCellContainers := n :: st.heapCellContainers }

/-- Whether `n` is a variable cell (scalar or container). -/
def isHeapCellVar (n : Name) : PygenM Bool := do
  return (← get).heapCellVars.contains n

/-- Whether `n` is a container/object variable cell (`Ref (Ref T)`). -/
def isHeapCellContainer (n : Name) : PygenM Bool := do
  return (← get).heapCellContainers.contains n

/-- Run `x` with `self` treated as a `Ref C` (heap method body). Restored on exit. -/
def withHeapSelfRef {α : Type} (x : PygenM α) : PygenM α := do
  let saved := (← get).heapSelfRef
  modify fun st => { st with heapSelfRef := true }
  let r ← x
  modify fun st => { st with heapSelfRef := saved }
  pure r
/-- Whether `name` was bound with `let mut` (so it can be reassigned rather than shadowed). -/
def isMutVar (name : Name) : PygenM Bool := do
  return (← get).mutVars.contains name

def setMutVar (name : Name) : PygenM Unit := do
  modify fun st => { st with mutVars := st.mutVars.insert name }

/-- Whether `name`'s `let mut` slot has type `PyAny` (so a reassign coerces, never rebinds). -/
def isPyAnySlot (name : Name) : PygenM Bool := do
  return (← get).pyAnySlotVars.contains name

def setPyAnySlot (name : Name) (isPyAny : Bool) : PygenM Unit := do
  modify fun st => { st with
    pyAnySlotVars := if isPyAny then st.pyAnySlotVars.insert name else st.pyAnySlotVars.erase name }

/-- Resolve a local name through the SSA rename map (identity if unrenamed). -/
def applyRename (name : Name) : PygenM Name := do
  return (← get).renames.getD name name

/-- Register `name ↦ fresh`: every later reference to `name` resolves to `fresh`. Keyed by the
original name, so a second type-change on the same variable overwrites cleanly. -/
def addRename (name fresh : Name) : PygenM Unit := do
  modify fun st => { st with renames := st.renames.insert name fresh }

/-- A fresh rename target for `name`, containing `'` so it can never collide with a Python name. -/
def freshRenameName (name : Name) : PygenM Name := do
  let n := (← get).renameCounter
  modify fun st => { st with renameCounter := n + 1 }
  return (name.toString ++ "'rb" ++ toString n).toName

def isSetVar (name : Name) : PygenM Bool := do
  return (← get).setVars.contains name

/-- Mark (`isSet := true`) or unmark a variable as holding a Python `set`. -/
def setSetVar (name : Name) (isSet : Bool) : PygenM Unit := do
  modify fun st => { st with setVars := if isSet then st.setVars.insert name else st.setVars.erase name }

def isOptionVar (name : Name) : PygenM Bool := do
  return (← get).optionVars.contains name

/-- Mark a variable as holding an `Option T` slot (never unmarked: a plain reassignment `ans = t`
keeps the `Option` slot, coercing `t` to `some t`). -/
def setOptionVar (name : Name) : PygenM Unit := do
  modify fun st => { st with optionVars := st.optionVars.insert name }

def isDictVar (name : Name) : PygenM Bool := do
  return (← get).dictVars.contains name

/-- Mark (`isDict := true`) or unmark a variable as holding a dict. -/
def setDictVar (name : Name) (isDict : Bool) : PygenM Unit := do
  modify fun st => { st with dictVars := if isDict then st.dictVars.insert name else st.dictVars.erase name }

def isSortedVar (name : Name) : PygenM Bool := do
  return (← get).sortedVars.contains name

/-- Mark (`isSorted := true`) or unmark a variable as holding a `sortedcontainers.SortedList`, so its
`add`/`remove`/`discard` dispatch to the order-maintaining runtime rather than the set versions. -/
def setSortedVar (name : Name) (isSorted : Bool) : PygenM Unit := do
  modify fun st => { st with sortedVars := if isSorted then st.sortedVars.insert name else st.sortedVars.erase name }

/-- The library module whose object `name` holds, if any. -/
def libObjVarModule? (name : Name) : PygenM (Option String) := do
  return (← get).libObjVars[name]?

/-- Record (or clear) that `name` holds an object owned by `module?`. -/
def setLibObjVar (name : Name) (module? : Option String) : PygenM Unit := do
  modify fun st => { st with libObjVars :=
    match module? with | some m => st.libObjVars.insert name m | none => st.libObjVars.erase name }

/-- Whether `json` is a `SortedList(...)` construction (a call whose callee is the `sortedcontainers`
member `SortedList`), OR a `Name` already known to hold one. Marks the target so its `add`/`remove`/
`discard` maintain sort order. -/
partial def jsonIsSortedListExpr (json : Lean.Json) : PygenM Bool := do
  match (json.getObjValAs? String "node_type").toOption with
  | some "Name" => match json.getObjValAs? String "id" with
                   | .ok id => isSortedVar id.toName
                   | _ => pure false
  | some "Call" => match json.getObjVal? "func" with
                   | .ok f => pure (f.getObjValAs? String "library_member" == .ok "SortedList")
                   | _ => pure false
  | _ => pure false

/-- Whether `json` denotes a Python `set`: a `set(...)` call, a `{…}` literal / set comprehension, a
set operation (`&`/`|`/`^`/`-` on a set operand), or a `Name` already known to hold a set. Routes set
comparisons (`==`, `<=`, …) to their order-independent runtime rather than the list-backed ones. -/
partial def jsonIsSetExpr (json : Lean.Json) : PygenM Bool := do
  match (json.getObjValAs? String "node_type").toOption with
  | some "Name" => match json.getObjValAs? String "id" with
                   | .ok id => isSetVar id.toName
                   | _ => pure false
  | some "Set" | some "SetComp" => pure true
  | some "Call" => match json.getObjVal? "func" with
                   | .ok f => pure ((f.getObjValAs? String "node_type") == .ok "Name"
                                    && f.getObjValAs? String "id" == .ok "set")
                   | _ => pure false
  | some "BinOp" =>
      let op := (json.getObjValAs? String "op").toOption.getD ""
      if op == "bitand" || op == "bitor" || op == "bitxor" || op == "sub" then do
        let l ← match json.getObjVal? "left" with | .ok l => jsonIsSetExpr l | _ => pure false
        if l then pure true
        else match json.getObjVal? "right" with | .ok r => jsonIsSetExpr r | _ => pure false
      else pure false
  | _ => pure false

/-- Does `json` evaluate to a dict? A `{k:v}` literal / dict comprehension, a `dict()`/`defaultdict()`/
`Counter()` constructor, or a known dict variable. Used to route `d.pop(k)` to the DICT pop. -/
def jsonIsDictExpr (json : Lean.Json) : PygenM Bool := do
  match (json.getObjValAs? String "node_type").toOption with
  | some "Name" => match json.getObjValAs? String "id" with
                   | .ok id => isDictVar id.toName
                   | _ => pure false
  | some "Dict" | some "DictComp" => pure true
  | some "Call" => match json.getObjVal? "func" with
                   | .ok f => pure ((f.getObjValAs? String "node_type") == .ok "Name"
                                    && (#["dict", "defaultdict", "Counter"].contains
                                        ((f.getObjValAs? String "id").toOption.getD "")))
                   | _ => pure false
  | _ => pure false

/-- Run `x` while lowering the body of `class name` (with mutator set `mutators`), so `self.m(..)`
calls inside dispatch to `name.m` and reassign `self` when `m` mutates. Restored on exit. -/
def withCurrentClass {α : Type} (name : String) (mutators : List String) (x : PygenM α) : PygenM α :=
  withPygenStateField (·.currentClass) (fun st v => { st with currentClass := v }) (some name) <|
    withPygenStateField (·.currentClassMutators)
      (fun st v => { st with currentClassMutators := v }) mutators x

/-- Metadata about a generated Python class, recorded when its `ClassDef` is lowered so later
top-level statements can dispatch instantiation (`C(..)` → `C.mk`) and method calls
(`obj.m(..)` → `C.m obj ..`, with mutators reassigning the receiver). -/
structure ClassInfo where
  methods : List String := []
  mutators : List String := []
  valueMutators : List String := []
  staticmethods : List String := []
  classmethods : List String := []
  deriving Inhabited, Repr

/-- Process-global registry of generated classes. The Lean backend is a persistent server that
streams one statement at a time with a fresh `PygenM` state per statement, so cross-statement
class metadata cannot live in `PyGen.State`; it lives here and persists for the process. A class's
`ClassDef` is always lowered before any statement that instantiates it (module order), so the
registry is populated in time. -/
initialize classRegistry : IO.Ref (Std.HashMap String ClassInfo) ←
  IO.mkRef (Std.HashMap.emptyWithCapacity 16)

def registerClass (name : String) (info : ClassInfo) : PygenM Unit := do
  classRegistry.modify (·.insert name info)

/-- Process-global registry (like `classRegistry`) of which class fields hold a mutable container
(and are therefore a `Ref (List …)`/`Ref (HashMap …)`), keyed `className → [fieldName]`. Populated by
the `HeapPrelude` generator (which sees every class's field types); read by codegen to decide when a
`self.f`/`obj.f` container access must dereference. -/
initialize heapContainerFieldsRegistry : IO.Ref (Std.HashMap String (List String)) ←
  IO.mkRef (Std.HashMap.emptyWithCapacity 16)

/-- Record that `className.field` holds a heap-allocated container (a `Ref` to a List/dict/set). -/
def registerContainerField (className field : String) : PygenM Unit := do
  heapContainerFieldsRegistry.modify fun m =>
    m.insert className (field :: (m.getD className []))

/-- Whether `className.field` is a container-ref field (registered by `HeapPrelude`). -/
def isContainerField (className field : String) : PygenM Bool := do
  return ((← heapContainerFieldsRegistry.get).getD className []).contains field

/-- Process-global registry of def names emitted `noncomputable` (they reach `ℝ`, e.g. `x ** 0.5`).
A computable `def` cannot depend on a noncomputable one, so a function that CALLS a registered name
must itself be `noncomputable`. Closure-converted helpers are emitted before their parent (module
order), so this is populated in time. Names are the emitted (mangled) ids, so clashes are unlikely. -/
initialize noncomputableDefRegistry : IO.Ref (Std.HashSet String) ←
  IO.mkRef (Std.HashSet.emptyWithCapacity 16)

def registerNoncomputableDef (name : String) : PygenM Unit := do
  noncomputableDefRegistry.modify (·.insert name)

/-- Exact-mode defs emitted `Id`-typed (Track M contracts); a pure caller reads them through `runPure`,
whose identity fallback keeps a stale entry from another file harmless. -/
initialize idDefRegistry : IO.Ref (Std.HashSet String) ←
  IO.mkRef (Std.HashSet.emptyWithCapacity 16)

def registerIdDef (name : String) : PygenM Unit := do
  idDefRegistry.modify (·.insert name)

/-- The class whose body is currently being lowered (`self`'s class), if any. -/
def getCurrentClass : PygenM (Option String) := do
  return (← get).currentClass

def isRegisteredClass (name : String) : PygenM Bool := do
  return (← classRegistry.get).contains name

def classInfo? (name : String) : PygenM (Option ClassInfo) := do
  return (← classRegistry.get).get? name

def methodIsMutator (className method : String) : PygenM Bool := do
  match (← classRegistry.get).get? className with
  | some info => return info.mutators.contains method
  | none => return false

def methodIsValueMutator (className method : String) : PygenM Bool := do
  match (← classRegistry.get).get? className with
  | some info => return info.valueMutators.contains method
  | none => return false

/-- The unique class declaring method `m`, if exactly one does (else `none`: ambiguous or unknown).
Fallback for resolving a method-call receiver's class when the receiver isn't `self`. -/
def classOfMethod? (m : String) : PygenM (Option String) := do
  let reg ← classRegistry.get
  let owners := reg.toList.filterMap fun (c, info) =>
    if info.methods.contains m then some c else none
  match owners with
  | [c] => return some c
  | _ => return none

instance : MonadEvalT PygenM TermElabM where
    monadEval := fun x => x.run' {}


initialize
  registerTraceClass `PastaLean.pygen.info
  registerTraceClass `PastaLean.pygen.debug


instance : Repr SyntaxNodeKind where
  reprPrec kind n :=
    let name : Name := kind
    Repr.reprPrec name n

instance : ToString SyntaxNodeKind where
  toString kind :=
    let name : Name := kind
    ToString.toString name

/-- Environment extension storing code generation lemmas -/
initialize pygenExt :
    SimpleScopedEnvExtension (Name × String) (Std.HashMap String (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, key) =>
        m.insert key <| (m.getD key #[] ).push n
    initial := {}
  }

/-- Environment extension storing syntax transformation functions. -/
initialize pygenTransformExt :
    SimpleScopedEnvExtension (SyntaxNodeKind × Name) (Std.HashMap SyntaxNodeKind (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (kind, f) =>
        m.insert kind <| (m.getD kind #[]).push f
    initial := {}
  }

/--
Attribute for generating Lean code, more precisely Syntax of a given category, from JSON data. More precisely, we generate `PygenM <| TSyntax kind` from a JSON object, with the matching key as part of the attribute.

As the same statement can generate different syntax categories (e.g. `def` and `let`) this is not specified in the attribute. Instead the target category is part of the signature of the function.
-/
syntax (name := pygen) "pygen" (str,*) : attr

/--
Attribute for Lean syntax transformers that can rewrite syntax in a given category.
-/
syntax (name := pygenTransform) "pygen_transform" ident : attr

/--
Extract the keys from the `pygen` attribute syntax. Returns an array of strings.
-/
def pygenKeyM (stx : Syntax) : CoreM <| Array String := do
  match stx with
  | `(attr|pygen $x) => do
    return #[x.getString]
  | `(attr|pygen $xs,*) => do
    let keys := xs.getElems
    return keys.map (·.getString)
  | _ => throwUnsupportedSyntax

/--
Extract the syntax kind from the `pygen_transform` attribute syntax.
-/
def pygenTransformKindM (stx : Syntax) : CoreM SyntaxNodeKind := do
  match stx with
  | `(attr|pygen_transform $kind:ident) =>
    return kind.getId
  | _ => throwUnsupportedSyntax

/--
An environment extension for code generation functions. It stores the functions that can be used to generate code from JSON data. The key is a string that identifies the function, and the value is an array of names of the functions that can be used to generate code for that key.
-/
initialize registerBuiltinAttribute {
  name := `pygen
  descr := "Lean code generator"
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    -- Obtained from Qq.
    let expectedType : Q(Type) := q((kind : SyntaxNodeKind) →  (json : Json) → PygenM (TSyntax kind))
    unless ← isDefEq declTy expectedType do
      throwError -- replace with error
        s!"pygen: {decl} has type {declTy}, but expected {expectedType}"
    let keys ← pygenKeyM stx
    trace[PastaLean.pygen.debug] m!"pygen: {decl}; keys: {keys}"
    for key in keys do
      pygenExt.add (decl, key) kind
}

/--
An environment extension for syntax transformation functions. It stores functions that can
transform generated syntax after the initial JSON-to-syntax pass.
-/
initialize registerBuiltinAttribute {
  name := `pygenTransform
  descr := "Lean syntax transformer for generated code"
  add := fun decl stx attrKind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let kind ← pygenTransformKindM stx
    let kindExpr : Q(SyntaxNodeKind) := toExpr kind
    let expectedType : Q(Type) := q((stx : TSyntax $kindExpr) → PygenM (TSyntax $kindExpr))
    unless ← isDefEq declTy expectedType do
      throwError
        s!"pygen_transform: {decl} has type {declTy}, but expected {expectedType}"
    trace[PastaLean.pygen.debug] m!"pygen_transform: {decl}; kind: {kind}"
    pygenTransformExt.add (kind, decl) attrKind
}

/-- Environment extension storing code generation lemmas -/
initialize funcMapExt :
    SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (py, lean) =>
        m.insert py lean
    initial := {}
  }

syntax nameMapEntry := ident " → " ident

elab "#map_names" "[" nms:nameMapEntry,* "]" : command => do
  for nm in nms.getElems do
    match nm with
    | `(nameMapEntry| $py → $lean) =>
      let pyName := py.getId
      let leanName := lean.getId
      funcMapExt.add (pyName, leanName)
    | _ => throwUnsupportedSyntax

def leanName (pyName: Name) : CoreM Name := do
  let leanName := (funcMapExt.getState (← getEnv)).getD pyName pyName
  return leanName

/-- Registry mapping a Python *conversion / callable name* to the Lean function it lowers to,
populated by the `@[py_convert "name"]` attribute. Lets a user support a new conversion
`a = myconv(s)` by tagging ONE Lean function — no edit to `pythonBuiltinMap?`. The Python name pins
the target type (Lean can't infer it backwards at an untyped `let mut`); the tagged function stays
open on its *source* via its own typeclass (`def pyMyConv {α} [MyConvCast α] (x : α) : T`), so adding
a new source type is just another instance. Consulted as a fallback after the built-in tables, so a
user entry cannot silently shadow `int`/`str`/`list`. Composes with the SSA-rename of a
type-changing rebind, so the retyped assignment stitches automatically. -/
initialize pyConvertExt :
    SimpleScopedEnvExtension (String × Name) (Std.HashMap String Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (key, n) => m.insert key n
    initial := {}
  }

syntax (name := pyConvert) "py_convert" str : attr

initialize registerBuiltinAttribute {
  name := `pyConvert
  descr := "Register a Lean function as the lowering of a Python conversion/callable name"
  add := fun decl stx _ => MetaM.run' do
    match stx with
    | `(attr| py_convert $s:str) => pyConvertExt.add (s.getString, decl)
    | _ => throwUnsupportedSyntax
}

/-- Resolve a `@[py_convert]`-registered conversion name to its Lean function. -/
def pyConvertRegistered? (name : String) : CoreM (Option Name) := do
  return (pyConvertExt.getState (← getEnv)).get? name

/--
Get the code generation functions for a given key. The key is a string that identifies the function. If no function is found for the key, an error is thrown.
-/
def pygenMatches (key: String) : CoreM <| Array Name := do
  let allKeys := (pygenExt.getState (← getEnv)).toArray.map (fun (k, _) => k)
  let some fs :=
    (pygenExt.getState (← getEnv)).get? key | throwError
      s!"pygen: no function found for key '{key}' available keys are {allKeys.toList}"
  trace[PastaLean.pygen.info] m!"found {fs.size} functions for key {key}"
  if fs.isEmpty then
    trace[PastaLean.pygen.debug] m!"no function found for key {key} in {allKeys.toList}"
  return fs

/--
Get the syntax transformation functions registered for a syntax category.
-/
def pygenTransformers (kind : SyntaxNodeKind) : CoreM <| Array Name := do
  return (pygenTransformExt.getState (← getEnv)).getD kind #[]

def codeFromFunc (f: Name) (json: Json) (kind: SyntaxNodeKind)  : PygenM <| TSyntax kind := do
  let fInfo ← getConstInfo f
  let expectedType : Q(Type) := q((kind : SyntaxNodeKind) →  (json : Json) → PygenM (TSyntax kind))
  unless ← isDefEq fInfo.type expectedType do
    throwError -- replace with error
      s!"pygen: {f} has type {fInfo.type}, but expected {expectedType}"
  let fn ← unsafe evalConst ((kind : SyntaxNodeKind) →  (json : Json) → PygenM (TSyntax kind)) f
  fn kind json
/--
  Get the code generation function for a given key and syntax category. The key is a string that identifies the function, and the syntax category is used to disambiguate between functions that can generate different syntax categories. If no function is found for the key and syntax category, an error is thrown.
-/
def getCode (json: Json) (kind: SyntaxNodeKind) : PygenM <| TSyntax kind := do
  let .ok key := json.getObjValAs? String "node_type" | throwError
    s!"pygen: JSON object does not have a 'node_type' field or it is not a string: {json}"
  -- a field read the receiver's type cannot have (TypeInfer's `markAttrErrors`): Python's AttributeError
  if kind == `term then
    if let .ok ty := json.getObjValAs? String "_attr_error" then
      let attr := (json.getObjValAs? String "attr").toOption.getD ""
      let msg := Syntax.mkStrLit s!"AttributeError: '{ty}' object has no attribute '{attr}'"
      return ⟨(← `(term| PastaLean.pyPanic $msg)).raw⟩
  let fs ← pygenMatches key
  -- IO.eprintln s!"getting code for json: \n{json.pretty}"
  -- IO.eprintln s!"getCode: found functions '{fs}' for key '{key}' and syntax category '{kind}'" -- Debugging output
  let code? ← fs.findSomeM? (fun f => do try
    let mut code ← codeFromFunc f json kind
    let transformers ← pygenTransformers kind
    for t in transformers do
      let transformFn ← unsafe evalConst (TSyntax kind → PygenM (TSyntax kind)) t
      code ← transformFn code
    pure (some code)
  catch e =>
    let inner ← e.toMessageData.toString
    -- Only the INNERMOST failure is wrapped. `getCode` nests (a `Return` lowers a `Call` lowers a
    -- `Call` …), and re-wrapping at every level prepends ~100 chars of boilerplate each time, which
    -- pushes the actual cause out of the degraded-placeholder message entirely.
    if inner.startsWith "Error in code generation function" then throw e
    else throwError s!"Error in code generation function {f} for key '{key}' and syntax category '{kind}': {inner}")
  match code? with
  | some code =>
      -- an `Optional` value read only where the program has tested it is not `None` (`_or_default`,
      -- see TypeInfer's `markNarrowed`): its payload; the default is never observed
      if kind == `term && json.getObjValAs? Bool "_or_default" == .ok true then
        return ⟨(← `(term| (($(⟨code.raw⟩) : Option _).getD default))).raw⟩
      return code
  | none => throwError s!"pygen: no function found for key '{key}' and syntax category '{kind}'"

def getCodeCore (json: Json) (kind: SyntaxNodeKind) (checkCode : Bool := true) : CoreM <| Except String Format := do
  try
    let code := if checkCode then getCode json kind else withoutCheck <| getCode json kind
    let codeElab := code.run' {}
    let codeMeta := codeElab.run' {} {}
    let codeCore ← codeMeta.run' {} {}
    -- A pygen may return several commands wrapped in a null node (e.g. tuple-assign
    -- re-exports or top-level state-threading folds). Pretty-print each child and
    -- join them, since `ppCategory` cannot render a raw null node.
    if kind == `command && codeCore.raw.isOfKind nullKind then
      let mut fmts : Array Format := #[]
      for arg in codeCore.raw.getArgs do
        let child : TSyntax `command := ⟨arg⟩
        let childFmt ← PrettyPrinter.ppCategory `command child
        fmts := fmts.push childFmt
      return .ok (Format.joinSep fmts.toList "\n\n")
    let fmt ← PrettyPrinter.ppCategory kind codeCore
    return .ok fmt
  catch e =>
    return .error s!"Error generating code: {← e.toMessageData.toString}"

def getCodeIO (json: Json) (kind: SyntaxNodeKind) (ctx : Core.Context) (env: Environment)
    (checkCode : Bool := true) :
  IO <| Except String Format := do
  let code := getCodeCore json kind checkCode
  -- Codegen runs unbounded (`maxHeartbeats := 0`): the budget exists to stop runaway *proof search*,
  -- and there is no proof search here — just elaboration of the emitted syntax, which must scale to
  -- arbitrarily long programs. It also has to be disabled rather than merely raised: `IO.getNumHeartbeats`
  -- counts from thread start and `CoreM.run'` keeps the caller's `initHeartbeats`, so the persistent
  -- backend server (`py2lean --server`) shares one budget across every request it ever serves. Once the
  -- process crosses the ceiling, each further translation fails at `isDefEq` however small its program is.
  let ctx := { ctx with maxHeartbeats := 0, options := ctx.options.insert `maxHeartbeats (.ofNat 0) }
  let eio := code.run' ctx {env := env}
  match ← eio.toIO' with
  | .ok code =>
    return code
  | .error err =>
    return .error s!"Error generating code: {← err.toMessageData.toString}"

open Tactic
syntax (name:= pyTerm) "py_term%" term : term
@[term_elab pyTerm] def elabPyTerm : TermElab := fun stx expectedType => do
  match stx with
  | `(py_term% $json) => do
    let jsonExpr ← elabTerm json (mkConst ``Json)
    Term.synthesizeSyntheticMVarsNoPostponing
    let js ← unsafe evalExpr Json (mkConst ``Json) jsonExpr
    let termCodeM := getCode js `term
    let termCode ← termCodeM.run' {}
    TryThis.addSuggestion stx termCode
    elabTerm termCode expectedType
  | _ => throwUnsupportedSyntax

macro "py_term%" js:json : term =>
  `(py_term% json% $js)

-- #eval pygen

end PastaLean
