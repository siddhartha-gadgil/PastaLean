import PastaBench.stdlib.CPython.Generated
import PastaBench.Support

/-!
# CPython standard-library algorithms — hand-written proofs

HUMAN-WRITTEN. Regeneration only rewrites `Generated.lean`.

What PastaLean produced on its own, and what is proved here, per function:

| function | PastaLean | here |
|---|---|---|
| `gcd` | `gcd_spec` (`Result() ≥ 0`), loop init + exit closed, **step left `sorry`** | computes exactly `Int.gcd`; divides both; is greatest |
| `bisect_left` | `bisect_left_spec` (`Result() ≥ 0`), same shape | result lies in `[0, len a]` |
| `bisect_right` | `bisect_right_spec` (`Result() ≥ 0`), same shape | result lies in `[0, len a]` |
| `mean` | statement of `mean_spec`, body `sorry` | the same statement, proved |
| `median` | `median_spec` with postcondition `True` | value on a singleton |

The pattern throughout: PastaLean states the obligation and discharges the parts its tactic
portfolio can reach; what needs the *meaning* of the loop is proved by hand against
`pyWhileFuel`, by induction on the fuel.
-/

namespace PastaBench.stdlib.CPython

open PastaLean PastaBench

/-! ## `gcd` — Lib/fractions.py -/

/-- The loop guard of the generated `pyWhile`: keep going while `y ≠ 0`. -/
private abbrev GC : Int × Int × Int → Bool := fun s => decide (s.2.1 ≠ 0)

/-- The loop body: `t = x % y; x = y; y = t`, as the generated code threads the state tuple. -/
private abbrev GB : Int × Int × Int → Int × Int × Int :=
  fun s => (s.2.1, (pyMod s.1 s.2.1, pyMod s.1 s.2.1))

/-- On non-negative arguments Python's floored `%` is Lean's `%`. -/
private theorem pyMod_nonneg_eq {x y : Int} (_hx : 0 ≤ x) (hy : 0 < y) : pyMod x y = x % y :=
  pyMod_eq_emod_of_nonneg hy (Int.emod_nonneg x (by omega))

/-- Euclid's step, as Mathlib's `Int.gcd` sees it. -/
private theorem gcd_step {x y : Int} (hx : 0 ≤ x) (hy : 0 < y) :
    Int.gcd x y = Int.gcd y (x % y) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hy.le
  have hcast : ((m : Int) % (n : Int)) = ((m % n : Nat) : Int) := by omega
  rw [hcast]
  simp only [Int.gcd, Int.natAbs_natCast]
  rw [Nat.gcd_comm m n, Nat.gcd_rec n m, Nat.gcd_comm]

/-- **The loop lemma.** With enough fuel, the fuel-bounded loop lands on `Int.gcd`. Induction on
the fuel; the measure `y` strictly decreases because `x % y < y`. -/
private theorem gcd_loop :
    ∀ (fuel : Nat) (x y t : Int), 0 ≤ x → 0 ≤ y → y.toNat ≤ fuel →
      (pyWhileFuel GC GB fuel (x, (y, t))).1 = (Int.gcd x y : Int) := by
  intro fuel
  induction fuel with
  | zero =>
    intro x y t hx hy hfuel
    have hy0 : y = 0 := by omega
    subst hy0
    simp [pyWhileFuel, Int.gcd, Int.natAbs_of_nonneg hx]
  | succ n ih =>
    intro x y t hx hy hfuel
    by_cases hy0 : y = 0
    · subst hy0
      simp [pyWhileFuel, GC, Int.gcd, Int.natAbs_of_nonneg hx]
    · have hypos : 0 < y := by omega
      have hmod : pyMod x y = x % y := pyMod_nonneg_eq hx hypos
      have hlt : x % y < y := Int.emod_lt_of_pos x hypos
      have hnn : (0 : Int) ≤ x % y := Int.emod_nonneg x (by omega)
      have hstep : pyWhileFuel GC GB (n + 1) (x, (y, t))
          = pyWhileFuel GC GB n (y, (x % y, x % y)) := by
        simp [pyWhileFuel, GC, GB, hy0, hmod]
      rw [hstep, ih y (x % y) (x % y) hypos.le hnn (by omega), gcd_step hx hypos]

/-- **The theorem.** The Lean that PastaLean generated from `solution.py` computes `Int.gcd`. -/
theorem gcd_eq_intGcd (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Id.run (gcd a b) = (Int.gcd a b : Int) := by
  show (pyWhile _ GC GB (a, (b, (0 : Int)))).1 = _
  exact gcd_loop _ a b 0 ha hb (le_refl _)

theorem gcd_dvd_left (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : Id.run (gcd a b) ∣ a := by
  rw [gcd_eq_intGcd a b ha hb]; exact Int.gcd_dvd_left a b

theorem gcd_dvd_right (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : Id.run (gcd a b) ∣ b := by
  rw [gcd_eq_intGcd a b ha hb]; exact Int.gcd_dvd_right a b

/-- It is the *greatest* common divisor — the half a test suite can never check. -/
theorem dvd_gcd_of_dvd {a b d : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ Id.run (gcd a b) := by
  rw [gcd_eq_intGcd a b ha hb, Int.coe_gcd]
  exact dvd_gcd hda hdb

/-! ## `bisect_left` / `bisect_right` — Lib/bisect.py -/

private abbrev BC : Int × Int × Int → Bool := fun s => decide (s.1 < s.2.1)

private abbrev BLB (a : List Int) (x : Int) : Int × Int × Int → Int × Int × Int :=
  fun s =>
    let mid := pyFloorDiv (s.1 + s.2.1) (2 : Int)
    (if a⦋mid⦌ < x then mid + 1 else s.1, (if a⦋mid⦌ < x then s.2.1 else mid, mid))

private abbrev BRB (a : List Int) (x : Int) : Int × Int × Int → Int × Int × Int :=
  fun s =>
    let mid := pyFloorDiv (s.1 + s.2.1) (2 : Int)
    (if x < a⦋mid⦌ then s.1 else mid + 1, (if x < a⦋mid⦌ then mid else s.2.1, mid))

/-- The bounds invariant `0 ≤ lo ≤ hi ≤ n` survives the loop, so the returned index is a legal
insertion position. Stated for either body: both move exactly one endpoint to the midpoint, and
the midpoint lies in `[lo, hi)` (`pyFloorDiv_two_mem`). -/
private theorem bisect_loop (B : Int × Int × Int → Int × Int × Int) (n : Int)
    (hB : ∀ lo hi mid, lo < hi → 0 ≤ lo → hi ≤ n →
        0 ≤ (B (lo, (hi, mid))).1 ∧ (B (lo, (hi, mid))).1 ≤ (B (lo, (hi, mid))).2.1 ∧
        (B (lo, (hi, mid))).2.1 ≤ n ∧
        ((B (lo, (hi, mid))).2.1 - (B (lo, (hi, mid))).1).toNat < (hi - lo).toNat) :
    ∀ (fuel : Nat) (lo hi mid : Int), 0 ≤ lo → lo ≤ hi → hi ≤ n → (hi - lo).toNat ≤ fuel →
      0 ≤ (pyWhileFuel BC B fuel (lo, (hi, mid))).1 ∧
        (pyWhileFuel BC B fuel (lo, (hi, mid))).1 ≤ n := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi mid h0 hle hn _
    simp only [pyWhileFuel]
    exact ⟨h0, by omega⟩
  | succ k ih =>
    intro lo hi mid h0 hle hn hfuel
    by_cases hlt : lo < hi
    · obtain ⟨p0, ple, pn, pdec⟩ := hB lo hi mid hlt h0 hn
      have hstep : pyWhileFuel BC B (k + 1) (lo, (hi, mid)) = pyWhileFuel BC B k (B (lo, (hi, mid))) := by
        simp [pyWhileFuel, BC, hlt]
      rw [hstep]
      -- `Prod` eta lets `ih` take the three components of `B (lo, (hi, mid))` directly; naming them
      -- with `obtain` first would leave `p0`/`ple`/`pn` talking about the un-destructured term.
      exact ih _ _ _ p0 ple pn (Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le pdec hfuel))
    · simp only [pyWhileFuel, BC, decide_eq_true_eq, ite_eq_right hlt]
      exact ⟨h0, by omega⟩

private theorem bisect_left_body (a : List Int) (x : Int) (lo hi mid : Int)
    (hlt : lo < hi) (h0 : 0 ≤ lo) (hn : hi ≤ pyLen a) :
    0 ≤ (BLB a x (lo, (hi, mid))).1 ∧
      (BLB a x (lo, (hi, mid))).1 ≤ (BLB a x (lo, (hi, mid))).2.1 ∧
      (BLB a x (lo, (hi, mid))).2.1 ≤ pyLen a ∧
      ((BLB a x (lo, (hi, mid))).2.1 - (BLB a x (lo, (hi, mid))).1).toNat < (hi - lo).toNat := by
  obtain ⟨hml, hmr⟩ := pyFloorDiv_two_mem hlt
  by_cases hb : a⦋pyFloorDiv (lo + hi) (2 : Int)⦌ < x <;> simp only [hb, ite_true, ite_false] <;>
    refine ⟨by omega, by omega, by omega, by omega⟩

private theorem bisect_right_body (a : List Int) (x : Int) (lo hi mid : Int)
    (hlt : lo < hi) (h0 : 0 ≤ lo) (hn : hi ≤ pyLen a) :
    0 ≤ (BRB a x (lo, (hi, mid))).1 ∧
      (BRB a x (lo, (hi, mid))).1 ≤ (BRB a x (lo, (hi, mid))).2.1 ∧
      (BRB a x (lo, (hi, mid))).2.1 ≤ pyLen a ∧
      ((BRB a x (lo, (hi, mid))).2.1 - (BRB a x (lo, (hi, mid))).1).toNat < (hi - lo).toNat := by
  obtain ⟨hml, hmr⟩ := pyFloorDiv_two_mem hlt
  by_cases hb : x < a⦋pyFloorDiv (lo + hi) (2 : Int)⦌ <;> simp only [hb, ite_true, ite_false] <;>
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- `bisect_left` returns a legal insertion index. -/
theorem bisect_left_mem_range (a : List Int) (x : Int) :
    0 ≤ Id.run (bisect_left a x) ∧ Id.run (bisect_left a x) ≤ pyLen a := by
  show 0 ≤ (pyWhile _ BC (BLB a x) _).1 ∧ (pyWhile _ BC (BLB a x) _).1 ≤ _
  exact bisect_loop (BLB a x) (pyLen a) (fun lo hi mid h1 h2 h3 =>
    bisect_left_body a x lo hi mid h1 h2 h3) _ 0 (pyLen a) 0
    (le_refl _) (pyLen_nonneg a) (le_refl _) (le_refl _)

/-- `bisect_right` returns a legal insertion index. -/
theorem bisect_right_mem_range (a : List Int) (x : Int) :
    0 ≤ Id.run (bisect_right a x) ∧ Id.run (bisect_right a x) ≤ pyLen a := by
  show 0 ≤ (pyWhile _ BC (BRB a x) _).1 ∧ (pyWhile _ BC (BRB a x) _).1 ≤ _
  exact bisect_loop (BRB a x) (pyLen a) (fun lo hi mid h1 h2 h3 =>
    bisect_right_body a x lo hi mid h1 h2 h3) _ 0 (pyLen a) 0
    (le_refl _) (pyLen_nonneg a) (le_refl _) (le_refl _)

/-! ## `mean` / `median` — Lib/statistics.py -/

/-- PastaLean stated this from the `Ensures` and left the body `sorry`; here it is proved. -/
theorem mean_spec' : ∀ (data : List Int), pyLen data > (0 : Int) →
    pySum data /ₚ pyLen data *ₚ pyLen data = pySum data := by
  intro data h
  have hne : ((pyLen data : Int) : ℚ) ≠ 0 := by
    simp only [ne_eq, Int.cast_eq_zero]; omega
  simp only [int_pyDiv, rat_int_pyMul]
  field_simp

/-- Statement fidelity: our theorem is exactly the one PastaLean generated. -/
example : mean_spec = mean_spec' := rfl

theorem median_singleton (v : Int) : Id.run (median [v]) = ((v : Int) : ℚ) := by
  -- `pySort` is `List.mergeSort`, defined by well-founded recursion: it needs its own equation
  -- lemma before the rest of the body reduces.
  have hs : pySort [v] = [v] := List.mergeSort_singleton v
  simp only [median, Id.run, hs]
  rfl

end PastaBench.stdlib.CPython
