import PastaLean

/-!
# PastaBench proof support

Shared lemmas for the hand-written proofs in `leetcode/*/Proofs.lean`. Nothing generated lives
here and nothing here is generated — it is the benchmark's own small library.

Its main job is bridging PastaLean's Python operators (`+ₚ`, `*ₚ`, `%ₚ`, …) to Lean's native
ones. Each is `rfl` at `Int`, but stating it as `@[simp]` is what lets `omega` / `ring` /
`linarith` see through a generated definition without every proof re-unfolding instances by hand.

Scoped to this library on purpose: unfolding `%ₚ` globally would change how PastaLean's own
`taste?` portfolio normalises goals.
-/

namespace PastaBench

open PastaLean

@[simp] theorem int_pyAdd (a b : Int) : a +ₚ b = a + b := rfl
@[simp] theorem int_pySub (a b : Int) : a -ₚ b = a - b := rfl
@[simp] theorem int_pyMul (a b : Int) : a *ₚ b = a * b := rfl
@[simp] theorem int_pyMod (a b : Int) : a %ₚ b = pyMod a b := rfl

/-- Python's `/` on two ints is true division, so `/ₚ` leaves `Int` for `Rat`. -/
@[simp] theorem int_pyDiv (a b : Int) : a /ₚ b = (a : Rat) / (b : Rat) := rfl

/-- The mixed multiplication a true division feeds into. -/
@[simp] theorem rat_int_pyMul (a : Rat) (b : Int) : a *ₚ b = a * (b : Rat) := rfl

/-- `len` counts elements, so it is never negative. -/
@[simp] theorem pyLen_nonneg {α : Type} (xs : List α) : 0 ≤ pyLen xs :=
  Int.natCast_nonneg _

/-- Python's floored `%` agrees with Lean's `%` on a positive divisor when the dividend's
remainder is already non-negative — the only case the benchmark's parity proofs need. -/
theorem pyMod_eq_emod_of_nonneg {a b : Int} (hb : 0 < b) (h : 0 ≤ a % b) :
    pyMod a b = a % b := by
  unfold pyMod; simp; omega

/-- The binary-search midpoint lies in `[lo, hi)`. This is what makes `bisect`'s loop both
preserve its bounds invariant and strictly shrink `hi - lo`. -/
theorem pyFloorDiv_two_mem {lo hi : Int} (h : lo < hi) :
    lo ≤ pyFloorDiv (lo + hi) (2 : Int) ∧ pyFloorDiv (lo + hi) (2 : Int) < hi := by
  have hfd : pyFloorDiv (lo + hi) (2 : Int) = Int.fdiv (lo + hi) 2 := rfl
  rw [hfd, Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 2)]
  constructor <;> omega


end PastaBench
