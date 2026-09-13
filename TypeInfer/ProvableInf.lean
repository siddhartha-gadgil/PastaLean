import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations

/-! # A PROVABLE infinity — `pyInf`/`pyNegInf` from the extended reals

The exact-mode runtime represents `float('inf')` as a finite `ℚ` sentinel (`pyRatNonFinite`): fine for
*executing* the `best = inf; best = min(best, …)` idiom, but a finite value can NEVER satisfy
`∀ x, x ≤ inf` (false for `x > 10³⁰`), so it has no order-theoretic proof support. When a specification
needs a genuine greatest/least value, use these instead: `EReal = WithBot (WithTop ℝ)` — the extended
reals — gives a real top and bottom **constructed from ℝ, with NO axiom**, and the greatest/least
theorems below hold by construction. (These are `noncomputable` — they live in specs/proofs; the
runtime keeps the computable Float/`ℚ` representations.)

This lives in its own file (not the `TypeInfer/Theorem/` proofs) so that the lattice-correctness
theorems, which need only Lean core, are not slowed by compiling Mathlib's `EReal`. Like the `Theorem/`
files it is off the default build path — check it with `lake build TypeInfer.ProvableInf`. -/

namespace PastaLean

/-- Python `inf`, as the genuine TOP of the extended reals (ℝ ∪ {±∞}). Axiom-free (built from ℝ). -/
noncomputable def pyInf : EReal := ⊤

/-- Python `-inf`, as the genuine BOTTOM of the extended reals. -/
noncomputable def pyNegInf : EReal := ⊥

/-- **`pyInf` is the greatest value:** every extended real is `≤ pyInf`. (What the finite sentinel
cannot give.) -/
theorem le_pyInf (x : EReal) : x ≤ pyInf := le_top

/-- **`pyNegInf` is the least value:** every extended real is `≥ pyNegInf`. -/
theorem pyNegInf_le (x : EReal) : pyNegInf ≤ x := bot_le

/-- Every real is strictly below `pyInf`. -/
theorem real_lt_pyInf (r : ℝ) : (r : EReal) < pyInf := EReal.coe_lt_top r

/-- Every real is strictly above `pyNegInf`. -/
theorem pyNegInf_lt_real (r : ℝ) : pyNegInf < (r : EReal) := EReal.bot_lt_coe r

/-- Infinity absorbs addition (`inf + x = inf` for `x ≠ -inf`), matching Python's `inf` arithmetic. -/
theorem pyInf_add (x : EReal) (hx : x ≠ ⊥) : pyInf + x = pyInf := EReal.top_add_of_ne_bot hx

/-- `pyInf` is THE greatest element — any value dominating everything equals it (antisymmetry). -/
theorem pyInf_unique (t : EReal) (h : ∀ x, x ≤ t) : t = pyInf := le_antisymm (le_pyInf t) (h pyInf)

end PastaLean

/-! ### Float companion — the COMPUTABLE runtime infinity (approx mode)

`pyInf` above is `noncomputable` (a spec/proof object). At runtime in `--approx` mode, `float('inf')`
is the native IEEE Float infinity: computable, and — unlike the finite `ℚ` sentinel — it carries
genuine infinity semantics (absorbs arithmetic, compares correctly against finite floats). We give it a
name but state NO order theorem for it, because IEEE `nan` makes Float's `≤` non-total (`nan ≤ x` and
`x ≤ nan` are both false) — which is exactly why exact-mode `nan` now *panics* rather than lying. -/

namespace PastaLean

/-- Approx-mode `float('inf')` at runtime: native IEEE `+∞`. -/
def pyFloatInf : Float := 1.0 / 0.0
/-- Approx-mode `float('-inf')` at runtime: native IEEE `-∞`. -/
def pyFloatNegInf : Float := -1.0 / 0.0

end PastaLean
