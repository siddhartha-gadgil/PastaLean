import Mathlib
import Libraries.math.MathDef

namespace Libraries.math

/-! ### `gcd` -/

/-- `math.gcd` is commutative. -/
theorem pyMathGcd_comm (a b : Int) : pyMathGcd a b = pyMathGcd b a := by
  unfold pyMathGcd
  exact_mod_cast Int.gcd_comm a b

/-- `math.gcd` is always nonnegative (Python returns a nonnegative `int`). -/
theorem pyMathGcd_nonneg (a b : Int) : 0 ≤ pyMathGcd a b := by
  unfold pyMathGcd; positivity

/-- The gcd divides its first argument. -/
theorem pyMathGcd_dvd_left (a b : Int) : (pyMathGcd a b) ∣ a := by
  unfold pyMathGcd
  grind only [Int.gcd_dvd_left]

/-- The gcd divides its second argument. -/
theorem pyMathGcd_dvd_right (a b : Int) : (pyMathGcd a b) ∣ b := by
  unfold pyMathGcd
  grind only [Int.gcd_dvd_right]

/-! ### `lcm` -/

/-- `math.lcm` is commutative. -/
theorem pyMathLcm_comm (a b : Int) : pyMathLcm a b = pyMathLcm b a := by
  unfold pyMathLcm
  exact_mod_cast Int.lcm_comm a b

/-- `math.lcm` is always nonnegative. -/
theorem pyMathLcm_nonneg (a b : Int) : 0 ≤ pyMathLcm a b := by
  unfold pyMathLcm; positivity

/-- The product of gcd and lcm recovers the product of the magnitudes — the key identity that
makes `lcm` exact. -/
theorem pyMathGcd_mul_lcm (a b : Int) :
    pyMathGcd a b * pyMathLcm a b = a.natAbs * b.natAbs := by
  unfold pyMathGcd pyMathLcm
  exact_mod_cast Int.gcd_mul_lcm a b

/-! ### `factorial` -/

/-- `math.factorial` is strictly positive on every nonnegative input. -/
theorem pyMathFactorial_pos {n : Int} (hn : 0 ≤ n) : 0 < pyMathFactorial n := by
  unfold pyMathFactorial
  rw [ite_eq_right (by omega)]
  refine Int.sign_pos_iff.mp ?_
  simp only [Int.ofNat_eq_natCast, Int.sign_pos_iff, Int.natCast_pos]
  exact_mod_cast Nat.factorial_pos n.toNat

/-- The standard recurrence `(n+1)! = (n+1) · n!` for nonnegative `n`. -/
theorem pyMathFactorial_succ {n : Int} (hn : 0 ≤ n) :
    pyMathFactorial (n + 1) = (n + 1) * pyMathFactorial n := by
  unfold pyMathFactorial
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have h : (n + 1).toNat = n.toNat + 1 := by omega
  rw [h, Nat.factorial_succ]
  ring_nf
  grind only

/-! ### `comb` and `perm` -/

/-- Pascal's symmetry `C(n, k) = C(n, n-k)` for `0 ≤ k ≤ n`. -/
theorem pyMathComb_symm {n k : Int} (hk : 0 ≤ k) (hkn : k ≤ n) :
    pyMathComb n (n - k) = pyMathComb n k := by
  unfold pyMathComb
  simp_all
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have h : (n - k).toNat = n.toNat - k.toNat := by omega
  rw [h]
  exact_mod_cast Nat.choose_symm (by omega)

/-- `C(n, 0) = 1` for nonnegative `n`. -/
theorem pyMathComb_zero_right {n : Int} (hn : 0 ≤ n) : pyMathComb n 0 = 1 := by
  unfold pyMathComb
  rw [ite_eq_right (by grind)]
  simp

/-- `perm(n, n) = n!`: arranging all `n` items is `n` factorial. -/
theorem pyMathPerm_self {n : Int} (hn : 0 ≤ n) : pyMathPerm n n = pyMathFactorial n := by
  unfold pyMathPerm pyMathFactorial
  rw [ite_eq_right (by grind), ite_eq_right (by omega)]
  rw [Nat.descFactorial_self]

/-! ### `isqrt` -/

/-- `math.isqrt` never overshoots: `isqrt(n)² ≤ n` for nonnegative `n`. -/
theorem pyMathIsqrt_sq_le {n : Int} (hn : 0 ≤ n) :
    pyMathIsqrt n * pyMathIsqrt n ≤ n := by
  unfold pyMathIsqrt
  rw [ite_eq_right (by omega)]
  have := Int.sqrt_nonneg n
  simp_all
  refine (Int.abs_le_sqrt hn).mp ?_
  grind

/-- `math.isqrt` is nonnegative. -/
theorem pyMathIsqrt_nonneg {n : Int} (hn : 0 ≤ n) : 0 ≤ pyMathIsqrt n := by
  unfold pyMathIsqrt
  rw [ite_eq_right (by omega)]
  exact Int.sqrt_nonneg n

end Libraries.math
