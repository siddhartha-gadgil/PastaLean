import Mathlib
import Libraries.numpy.NumpyDef
import Libraries.numpy.Creation
import Libraries.numpy.Statistics

/-!
# Correctness theorems for the `numpy` runtime surface

Structural guarantees about the NumPy-style helpers: the *shapes* the constructors produce and
the *lengths* the elementwise/reduction helpers preserve. These are the invariants downstream
code silently relies on — `zeros((r, c))` really has `r` rows of `c` columns, `eye(n)` really is
square, `cumsum` keeps the vector length, `diff` drops exactly one element. They double as
machine-checked documentation: a regression that breaks one of these shapes breaks its proof.

Numeric-value identities over `Float` are deliberately omitted: Lean's `Float` is IEEE-754 and
admits no useful algebraic rewriting (no associativity, `NaN ≠ NaN`, etc.).
-/

namespace Libraries.numpy

/-! ### Shared helpers -/

/-- A nonnegative dimension passed as a `Nat` cast survives `pyNumpyNatFromInt` unchanged. -/
@[simp] theorem natFromInt_natCast (r : Nat) : pyNumpyNatFromInt (r : Int) = r := by
  unfold pyNumpyNatFromInt
  rw [ite_eq_right (by simp)]
  simp

/-- A list of lists whose rows all share a common length `k` is rectangular. This is the workhorse
behind every "constructor produces a rectangular/square matrix" theorem below. -/
theorem isRect_of_all_len {α} (m : List (List α)) (k : Nat)
    (h : ∀ row ∈ m, row.length = k) : pyNumpyIsRectangular m = true := by
  unfold pyNumpyIsRectangular
  cases m with
  | nil => rfl
  | cons row rows =>
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro x hx
    rw [h x (List.mem_cons_of_mem _ hx), h row (List.mem_cons_self ..)]

/-! ### Constructor shapes -/

/-- `zeros((r, c))` has exactly `r` rows. -/
@[simp] theorem pyNumpyRows_zeros {γ} [Zero γ] (r c : Nat) :
    pyNumpyRows (pyNumpyZeros (γ := γ) ((r : Int), (c : Int))) = r := by
  simp [pyNumpyRows, pyNumpyZeros]

/-- `ones((r, c))` has exactly `r` rows. -/
@[simp] theorem pyNumpyRows_ones {γ} [One γ] (r c : Nat) :
    pyNumpyRows (pyNumpyOnes (γ := γ) ((r : Int), (c : Int))) = r := by
  simp [pyNumpyRows, pyNumpyOnes]

/-- `full((r, c), v)` has exactly `r` rows. -/
@[simp] theorem pyNumpyRows_full {α} [PyNumpyScalar α] (r c : Nat) (v : α) :
    pyNumpyRows (pyNumpyFull ((r : Int), (c : Int)) v) = r := by
  simp [pyNumpyRows, pyNumpyFull]

/-- Every row of `zeros((r, c))` has `c` columns, so the matrix is rectangular. -/
theorem pyNumpyZeros_isRectangular {γ} [Zero γ] (r c : Nat) :
    pyNumpyIsRectangular (pyNumpyZeros (γ := γ) ((r : Int), (c : Int))) = true := by
  apply isRect_of_all_len _ c
  intro row hrow
  simp only [pyNumpyZeros, natFromInt_natCast, List.mem_replicate] at hrow
  rw [hrow.2]; simp

/-- Every row of `ones((r, c))` has `c` columns, so the matrix is rectangular. -/
theorem pyNumpyOnes_isRectangular {γ} [One γ] (r c : Nat) :
    pyNumpyIsRectangular (pyNumpyOnes (γ := γ) ((r : Int), (c : Int))) = true := by
  apply isRect_of_all_len _ c
  intro row hrow
  simp only [pyNumpyOnes, natFromInt_natCast, List.mem_replicate] at hrow
  rw [hrow.2]; simp

/-- `eye(n)` is a square matrix: `n` rows, each of length `n`. -/
theorem pyNumpyEye_isSquare {γ} [Zero γ] [One γ] (n : Nat) :
    pyNumpyIsSquare (pyNumpyEye (γ := γ) (n : Int)) = true := by
  have hlen : ∀ row ∈ pyNumpyEye (γ := γ) (n : Int), row.length = n := by
    intro row hrow
    simp only [pyNumpyEye, natFromInt_natCast, List.mem_map] at hrow
    obtain ⟨i, _, rfl⟩ := hrow
    simp
  have hrows : (pyNumpyEye (γ := γ) (n : Int)).length = n := by simp [pyNumpyEye]
  unfold pyNumpyIsSquare
  rw [isRect_of_all_len _ n hlen, Bool.true_and]
  cases hm : pyNumpyEye (γ := γ) (n : Int) with
  | nil => rfl
  | cons row rows =>
    simp only [decide_eq_true_eq]
    have h1 : (row :: rows).length = n := by rw [← hm]; exact hrows
    have h2 : row.length = n := hlen row (by rw [hm]; exact List.mem_cons_self ..)
    rw [h1, h2]

/-! ### Length-preserving vector ops -/

/-- The accumulator-threading worker of `cumsum` preserves length. -/
theorem pyNumpyCumsum_go_length (a : Float) (ys : List Float) :
    (pyNumpyCumsum.go a ys).length = ys.length := by
  induction ys generalizing a with
  | nil => rfl
  | cons z zs ih => simp only [pyNumpyCumsum.go, List.length_cons]; rw [ih]

/-- `cumsum` preserves the length of the input vector. -/
@[simp] theorem pyNumpyCumsum_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpyCumsum xs).length = xs.length := by
  unfold pyNumpyCumsum
  rw [pyNumpyToFloats, pyNumpyCumsum_go_length, List.length_map]

/-- The accumulator-threading worker of `cumprod` preserves length. -/
theorem pyNumpyCumprod_go_length (a : Float) (ys : List Float) :
    (pyNumpyCumprod.go a ys).length = ys.length := by
  induction ys generalizing a with
  | nil => rfl
  | cons z zs ih => simp only [pyNumpyCumprod.go, List.length_cons]; rw [ih]

/-- `cumprod` preserves the length of the input vector. -/
@[simp] theorem pyNumpyCumprod_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpyCumprod xs).length = xs.length := by
  unfold pyNumpyCumprod
  rw [pyNumpyToFloats, pyNumpyCumprod_go_length, List.length_map]

/-- `sign` preserves the length of the input vector. -/
@[simp] theorem pyNumpySign_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpySign xs).length = xs.length := by
  simp [pyNumpySign, pyNumpyToFloats]

/-- `abs` preserves the length of the input vector. -/
@[simp] theorem pyNumpyAbs_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpyAbs xs).length = xs.length := by
  simp [pyNumpyAbs, pyNumpyToFloats]

/-- `clip` preserves the length of the input vector. -/
@[simp] theorem pyNumpyClip_length {α} [PyNumpyScalar α] (xs : List α) (lo hi : Float) :
    (pyNumpyClip xs lo hi).length = xs.length := by
  simp [pyNumpyClip, pyNumpyToFloats]

/-- `round` preserves the length of the input vector. -/
@[simp] theorem pyNumpyRound_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpyRound xs).length = xs.length := by
  simp [pyNumpyRound, pyNumpyToFloats]

/-- `diff` removes exactly one element from a vector. -/
@[simp] theorem pyNumpyDiff_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpyDiff xs).length = xs.length - 1 := by
  simp only [pyNumpyDiff, pyNumpyToFloats, List.length_zipWith, List.length_drop,
    List.length_map]
  omega

end Libraries.numpy
