import PastaLean.PyAPI

/-!
# The substitution table: every way the runnable twin differs from the provable twin

The code generator emits each Python function twice from one walk of the same AST. Wherever the two
emissions differ, the difference is a row of this table, and code generation reads its primitive
substitutions from here (`runPrim?`), so the table and the generated code cannot disagree.

* `prim`: a runtime function replaced by another (an `Array` operation for its `List` one). Each row
  is a proved refinement, `run (up a) = up (prov a)`, checked by `#twin_table` (`Twin/Tactic.lean`).
* `type`: a type replaced by another, related by `TwinRel` (`Twin/Relation.lean`), or by an IEEE
  enclosure for floats (`PastaLean/PyAPI/FloatInterval.lean`), which is not an equation.
* `erase`: proof-only content absent from the runnable twin (no runtime content).
* `effect`: an effect the provable twin models and the runnable twin performs (trusted model).
* `transform`: the runnable twin computes the same function by a different algorithm.
-/

namespace PastaLean.Twin

inductive SubstKind where
  | prim | type | erase | effect | transform
  deriving Repr, BEq, Inhabited

structure Subst where
  kind : SubstKind
  /-- What the provable twin emits (`.anonymous` when it is not a single constant). -/
  prov : Lean.Name
  /-- What the runnable twin emits in its place (`.anonymous` for an erasure). -/
  run : Lean.Name
  /-- The Python construct, and when the substitution applies. -/
  python : String
  deriving Inhabited

/-- Every difference between the twins. Rows of kind `prim` are applied by code generation through
`runPrim?`; the others document the remaining switch points (`getNumericMode` call sites). -/
def substTable : Array Subst := #[
  -- an array-backed list (`_seq = "array"`, runnable twin only): the `Array` operation
  ⟨.prim, ``PastaLean.pyAppend, ``PastaLean.pyArrayAppend, "xs.append(v)"⟩,
  ⟨.prim, ``PastaLean.pyExtend, ``PastaLean.pyArrayExtend, "xs.extend(ys)"⟩,
  ⟨.prim, ``PastaLean.pyReverse, ``PastaLean.pyArrayReverse, "xs.reverse()"⟩,
  ⟨.prim, ``PastaLean.pyInsert, ``PastaLean.pyArrayInsert, "xs.insert(i, v)"⟩,
  ⟨.prim, ``PastaLean.pyPopValue, ``PastaLean.pyArrayPopValue, "v = xs.pop(i)"⟩,
  ⟨.prim, ``PastaLean.pyPopRest, ``PastaLean.pyArrayPopRest, "xs.pop(i) (the list after)"⟩,
  ⟨.prim, ``PastaLean.pyPopLeftValue, ``PastaLean.pyArrayPopLeftValue, "v = q.popleft()"⟩,
  ⟨.prim, ``PastaLean.pyPopLeftRest, ``PastaLean.pyArrayPopLeftRest, "q.popleft() (the deque after)"⟩,
  ⟨.prim, ``PastaLean.pyListRepeat, ``PastaLean.pyArrayRepeat, "[x] * n"⟩,
  -- types
  ⟨.type, ``List, ``Array, "an array-backed list (literals `#[…]`, comprehensions `.toArray`)"⟩,
  ⟨.type, ``Rat, ``Float, "float (an enclosure, not an equation)"⟩,
  ⟨.type, ``Real, ``Float, "float in a function reaching sqrt/exp/… (an enclosure)"⟩,
  ⟨.type, ``PastaLean.pyRat, ``PastaLean.pyFloat, "float(x)"⟩,
  ⟨.type, ``PastaLean.PyHDiv.hDiv, ``PastaLean.pyTrueDiv, "a / b (exact division vs IEEE, raising on 0)"⟩,
  ⟨.type, ``PastaLean.PyExceptId, ``PastaLean.PyExcept, "a function that raises"⟩,
  ⟨.type, ``PastaLean.ProofMode.PyProofM, ``IO, "a function that raises and does IO"⟩,
  -- proof-only content
  ⟨.erase, .anonymous, .anonymous, "assert c (`have : c := by taste?`)"⟩,
  ⟨.erase, .anonymous, .anonymous, "a property function or contract (`_correct` / `_spec` theorems)"⟩,
  ⟨.erase, .anonymous, .anonymous, "`@[simp, taste_ingr]` and `noncomputable` markers"⟩,
  -- effects
  ⟨.effect, ``PastaLean.ProofMode.pyPrintProof, ``PastaLean.pyPrintIO, "print(…) (stream model vs real IO)"⟩,
  -- transforms
  ⟨.transform, .anonymous, .anonymous, "@cache / @lru_cache (memoised only in the runnable twin)"⟩
]

/-- The runnable twin's primitive for the provable twin's `prov`, if the table substitutes it. -/
def runPrim? (prov : Lean.Name) : Option Lean.Name :=
  (substTable.find? fun s => s.kind == .prim && s.prov == prov).map (·.run)

/-- `runPrim?`, keeping `prov` when the table has no row for it. -/
def runPrim (prov : Lean.Name) : Lean.Name := (runPrim? prov).getD prov

end PastaLean.Twin
