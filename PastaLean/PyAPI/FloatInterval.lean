import Mathlib.Tactic

/-!
# Enclosures of IEEE-754 double results

The provable twin computes over exact `ℚ`; the runnable twin over IEEE doubles. Lean's `Float` is opaque
to the kernel, so how far the two can drift apart is stated here over `ℚ`, against the one fact IEEE
round-to-nearest guarantees: the rounded value of a real `z` in range lies within `err z =
max (u·|z|, η)` of `z`, with `u = 2⁻⁵³` (unit roundoff) and `η = 2⁻¹⁰⁷⁵` (half the smallest subnormal).

An `FI` is a closed interval (either end may be infinite) containing the double a computation
produces. Each operation takes the exact interval of its result and widens each end by the rounding
bound (`roundEnds`). `roundEnds_sound`, `neg_sound`, `add_sound`, `sub_sound`, `mul_sound`,
`div_sound` and `fabs_sound` prove the enclosure for any rounding function obeying the bound, and
`lt_of_ends` / `not_lt_of_ends` that a comparison the enclosures decide is decided for every member. `src/refute/fi.py` runs the same arithmetic over Python
`Fraction`s to classify float counterexamples in `pastalean refute`.
-/

namespace PastaLean.FloatInterval

/-- Unit roundoff of binary64, `2⁻⁵³`. -/
def u : ℚ := 1 / 2 ^ 53

/-- Half the smallest positive subnormal, `2⁻¹⁰⁷⁵`: the absolute error bound near zero. -/
def η : ℚ := 1 / 2 ^ 1075

/-- The largest finite double; a rounded value beyond it is ±∞. -/
def maxFinite : ℚ := (2 ^ 53 - 1) * 2 ^ 971

/-- The error one rounding can introduce at `z`. -/
def err (z : ℚ) : ℚ := max (u * |z|) η

/-- What IEEE round-to-nearest guarantees of a rounding function on its finite range. -/
def RoundsNearest (rnd : ℚ → ℚ) : Prop := ∀ z, |z| ≤ maxFinite → |rnd z - z| ≤ err z

theorem u_nonneg : (0 : ℚ) ≤ u := by norm_num [u]
theorem u_le_one : u ≤ 1 := by norm_num [u]

/-- `err` is `u`-Lipschitz: it is the max of `u·|z|` and a constant. -/
theorem err_lipschitz (x y : ℚ) : |err y - err x| ≤ u * |y - x| := by
  unfold err
  calc abs (max (u * abs y) η - max (u * abs x) η) ≤ abs (u * abs y - u * abs x) :=
        abs_max_sub_max_le_abs _ _ _
    _ = u * abs (abs y - abs x) := by rw [← mul_sub, abs_mul, abs_of_nonneg u_nonneg]
    _ ≤ u * abs (y - x) := mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub y x) u_nonneg

/-- The lowest a rounding of `z` can land, `z - err z`, rises with `z`. -/
theorem sub_err_mono {x y : ℚ} (h : x ≤ y) : x - err x ≤ y - err y := by
  have := (abs_le.mp (err_lipschitz x y)).2
  have : u * |y - x| ≤ y - x := by
    rw [abs_of_nonneg (by linarith)]; nlinarith [u_le_one, u_nonneg]
  linarith

/-- The highest a rounding of `z` can land, `z + err z`, rises with `z`. -/
theorem add_err_mono {x y : ℚ} (h : x ≤ y) : x + err x ≤ y + err y := by
  have := (abs_le.mp (err_lipschitz x y)).1
  have : u * |y - x| ≤ y - x := by
    rw [abs_of_nonneg (by linarith)]; nlinarith [u_le_one, u_nonneg]
  linarith

/-- An interval of rationals; `none` is an infinite end. -/
structure FI where
  lo : Option ℚ
  hi : Option ℚ
  deriving Repr, DecidableEq, Inhabited

/-- `q` lies in the interval. -/
def FI.mem (x : FI) (q : ℚ) : Prop :=
  (∀ l, x.lo = some l → l ≤ q) ∧ (∀ h, x.hi = some h → q ≤ h)

/-- An exact input (every generated float is dyadic, hence exactly representable). -/
def FI.point (q : ℚ) : FI := ⟨some q, some q⟩

theorem FI.point_mem (q : ℚ) : (FI.point q).mem q := by
  constructor <;> intro _ h <;> simp [FI.point] at h <;> simp [h]

/-- Widen an exact lower end by the rounding bound; one past the finite range is `-∞`. -/
def lowerEnd : Option ℚ → Option ℚ
  | none => none
  | some a => if a - err a < -maxFinite then none else some (a - err a)

/-- Widen an exact upper end by the rounding bound; one past the finite range is `+∞`. -/
def upperEnd : Option ℚ → Option ℚ
  | none => none
  | some b => if b + err b > maxFinite then none else some (b + err b)

/-- The enclosure of the rounded results of an operation whose exact results lie between `lo`, `hi`. -/
def roundEnds (lo hi : Option ℚ) : FI := ⟨lowerEnd lo, upperEnd hi⟩

/-- **Rounding is enclosed**: if the exact result `z` lies between `lo` and `hi` and is in range, every
rounding of it obeying the IEEE bound lies in `roundEnds lo hi`. -/
theorem roundEnds_sound {rnd : ℚ → ℚ} (hr : RoundsNearest rnd) {lo hi : Option ℚ} {z : ℚ}
    (hlo : ∀ a, lo = some a → a ≤ z) (hhi : ∀ b, hi = some b → z ≤ b) (hz : |z| ≤ maxFinite) :
    (roundEnds lo hi).mem (rnd z) := by
  have hrz := abs_le.mp (hr z hz)
  constructor
  · intro l hl
    cases lo with
    | none => simp [roundEnds, lowerEnd] at hl
    | some a =>
      simp only [roundEnds, lowerEnd] at hl
      split_ifs at hl
      cases hl
      have := sub_err_mono (hlo a rfl)
      linarith
  · intro h hh
    cases hi with
    | none => simp [roundEnds, upperEnd] at hh
    | some b =>
      simp only [roundEnds, upperEnd] at hh
      split_ifs at hh
      cases hh
      have := add_err_mono (hhi b rfl)
      linarith

/-- Negation is exact in IEEE arithmetic. -/
def neg (x : FI) : FI := ⟨x.hi.map (- ·), x.lo.map (- ·)⟩

theorem neg_sound {x : FI} {q : ℚ} (h : x.mem q) : (neg x).mem (-q) := by
  constructor
  · intro l hl
    simp only [neg, Option.map_eq_some_iff] at hl
    obtain ⟨b, hb, rfl⟩ := hl
    linarith [h.2 b hb]
  · intro t ht
    simp only [neg, Option.map_eq_some_iff] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    linarith [h.1 a ha]

/-- Sum of two ends (an infinite end stays infinite). -/
def addEnd : Option ℚ → Option ℚ → Option ℚ
  | some a, some b => some (a + b)
  | _, _ => none

/-- IEEE `x + y`: the exact interval of sums, then one rounding. -/
def add (x y : FI) : FI := roundEnds (addEnd x.lo y.lo) (addEnd x.hi y.hi)

/-- **Addition is enclosed**: the rounded sum of two enclosed values lies in `add`. -/
theorem add_sound {rnd : ℚ → ℚ} (hr : RoundsNearest rnd) {x y : FI} {p q : ℚ}
    (hp : x.mem p) (hq : y.mem q) (hz : |p + q| ≤ maxFinite) : (add x y).mem (rnd (p + q)) := by
  apply roundEnds_sound hr _ _ hz
  · intro s hs
    match hxl : x.lo, hyl : y.lo with
    | some a, some b =>
      simp [addEnd, hxl, hyl] at hs; subst hs
      linarith [hp.1 a hxl, hq.1 b hyl]
    | none, _ => simp [addEnd, hxl] at hs
    | some _, none => simp [addEnd, hxl, hyl] at hs
  · intro s hs
    match hxh : x.hi, hyh : y.hi with
    | some a, some b =>
      simp [addEnd, hxh, hyh] at hs; subst hs
      linarith [hp.2 a hxh, hq.2 b hyh]
    | none, _ => simp [addEnd, hxh] at hs
    | some _, none => simp [addEnd, hxh, hyh] at hs

/-- IEEE `x - y` is `x + (-y)` exactly. -/
def sub (x y : FI) : FI := add x (neg y)

theorem sub_sound {rnd : ℚ → ℚ} (hr : RoundsNearest rnd) {x y : FI} {p q : ℚ}
    (hp : x.mem p) (hq : y.mem q) (hz : |p - q| ≤ maxFinite) : (sub x y).mem (rnd (p - q)) := by
  have := add_sound hr hp (neg_sound hq) (by simpa [sub_eq_add_neg] using hz)
  simpa [sub, sub_eq_add_neg] using this

/-- Between two corners of a segment: `p·k` lies between `a·k` and `b·k` when `p` lies between `a`, `b`. -/
theorem mul_between {a b p : ℚ} (k : ℚ) (h1 : a ≤ p) (h2 : p ≤ b) :
    min (a * k) (b * k) ≤ p * k ∧ p * k ≤ max (a * k) (b * k) := by
  rcases le_total 0 k with hk | hk
  · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
  · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩

/-- The least of the four corner products. -/
def min4 (a b c d : ℚ) : ℚ := min (min (a * c) (a * d)) (min (b * c) (b * d))
/-- The greatest of the four corner products. -/
def max4 (a b c d : ℚ) : ℚ := max (max (a * c) (a * d)) (max (b * c) (b * d))

/-- A product of two interval members lies between the extreme corner products. -/
theorem mul_corners {a b c d p q : ℚ} (ha : a ≤ p) (hb : p ≤ b) (hc : c ≤ q) (hd : q ≤ d) :
    min4 a b c d ≤ p * q ∧ p * q ≤ max4 a b c d := by
  obtain ⟨l1, u1⟩ := mul_between q ha hb
  obtain ⟨la, ua⟩ := mul_between a hc hd
  obtain ⟨lb, ub⟩ := mul_between b hc hd
  rw [mul_comm c a, mul_comm d a, mul_comm q a] at la ua
  rw [mul_comm c b, mul_comm d b, mul_comm q b] at lb ub
  unfold min4 max4
  constructor
  · rcases min_cases (a * q) (b * q) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at l1
    · exact le_trans (min_le_of_left_le la) l1
    · exact le_trans (min_le_of_right_le lb) l1
  · rcases max_cases (a * q) (b * q) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at u1
    · exact le_trans u1 (le_max_of_le_left ua)
    · exact le_trans u1 (le_max_of_le_right ub)

/-- Products of finite ends, as an exact interval; any infinite end gives the whole line. -/
def mulEnds (x y : FI) : Option ℚ × Option ℚ :=
  match x.lo, x.hi, y.lo, y.hi with
  | some a, some b, some c, some d => (some (min4 a b c d), some (max4 a b c d))
  | _, _, _, _ => (none, none)

/-- IEEE `x * y`: the exact interval of products, then one rounding. -/
def mul (x y : FI) : FI := roundEnds (mulEnds x y).1 (mulEnds x y).2

/-- The exact product of two members lies in `mulEnds`. -/
theorem mulEnds_mem {x y : FI} {p q : ℚ} (hp : x.mem p) (hq : y.mem q) :
    (∀ l, (mulEnds x y).1 = some l → l ≤ p * q) ∧ (∀ h, (mulEnds x y).2 = some h → p * q ≤ h) := by
  unfold mulEnds
  match hxl : x.lo, hxh : x.hi, hyl : y.lo, hyh : y.hi with
  | some a, some b, some c, some d =>
    have := mul_corners (hp.1 a hxl) (hp.2 b hxh) (hq.1 c hyl) (hq.2 d hyh)
    exact ⟨fun l hl => by simp at hl; exact hl ▸ this.1, fun h hh => by simp at hh; exact hh ▸ this.2⟩
  | none, _, _, _ => simp
  | some _, none, _, _ => simp
  | some _, some _, none, _ => simp
  | some _, some _, some _, none => simp

/-- **Multiplication is enclosed**. -/
theorem mul_sound {rnd : ℚ → ℚ} (hr : RoundsNearest rnd) {x y : FI} {p q : ℚ}
    (hp : x.mem p) (hq : y.mem q) (hz : |p * q| ≤ maxFinite) : (mul x y).mem (rnd (p * q)) :=
  roundEnds_sound hr (mulEnds_mem hp hq).1 (mulEnds_mem hp hq).2 hz

/-- The exact reciprocals of a divisor interval `[c, d]` not containing `0`. -/
def recip (c d : ℚ) : FI := ⟨some (min (1 / c) (1 / d)), some (max (1 / c) (1 / d))⟩

theorem recip_mem {c d q : ℚ} (hc : c ≤ q) (hd : q ≤ d) (h0 : 0 < c ∨ d < 0) : (recip c d).mem (1 / q) := by
  have key : 1 / d ≤ 1 / q ∧ 1 / q ≤ 1 / c := by
    rcases h0 with h | h
    · exact ⟨one_div_le_one_div_of_le (by linarith) hd, one_div_le_one_div_of_le h hc⟩
    · exact ⟨one_div_le_one_div_of_neg_of_le (by linarith) hd,
        one_div_le_one_div_of_neg_of_le (by linarith) hc⟩
  constructor
  · intro l hl; simp only [recip, Option.some.injEq] at hl; subst hl; exact min_le_of_right_le key.1
  · intro h hh; simp only [recip, Option.some.injEq] at hh; subst hh; exact le_max_of_le_left key.2

/-- IEEE `x / y`: the exact interval of quotients (as `x · 1/y`), then one rounding. A divisor interval
containing `0` gives the whole line. -/
def div (x y : FI) : FI :=
  match y.lo, y.hi with
  | some c, some d => if 0 < c ∨ d < 0 then mul x (recip c d) else ⟨none, none⟩
  | _, _ => ⟨none, none⟩

/-- **Division is enclosed** (for a nonzero divisor; IEEE `x / 0` raises in Python). -/
theorem div_sound {rnd : ℚ → ℚ} (hr : RoundsNearest rnd) {x y : FI} {p q : ℚ}
    (hp : x.mem p) (hq : y.mem q) (hz : |p / q| ≤ maxFinite) : (div x y).mem (rnd (p / q)) := by
  unfold div
  match hyl : y.lo, hyh : y.hi with
  | some c, some d =>
    simp only
    split_ifs with h0
    · rw [div_eq_mul_one_div p q] at hz ⊢
      exact mul_sound hr hp (recip_mem (hq.1 c hyl) (hq.2 d hyh) h0) hz
    · exact ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
  | none, _ => exact ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
  | some _, none => exact ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- `|x|` is exact in IEEE arithmetic. -/
def fabs (x : FI) : FI :=
  match x.lo, x.hi with
  | some a, some b => if 0 ≤ a then x else if b ≤ 0 then neg x else ⟨some 0, some (max (-a) b)⟩
  | some a, none => if 0 ≤ a then x else ⟨some 0, none⟩
  | none, some b => if b ≤ 0 then neg x else ⟨some 0, none⟩
  | none, none => ⟨some 0, none⟩

theorem fabs_sound {x : FI} {q : ℚ} (h : x.mem q) : (fabs x).mem |q| := by
  have h0 : (0 : ℚ) ≤ |q| := abs_nonneg q
  have neg_mem := neg_sound h
  unfold fabs
  match hl : x.lo, hh : x.hi with
  | some a, some b =>
    have ha := h.1 a hl; have hb := h.2 b hh
    simp only
    split_ifs with h1 h2
    · rwa [abs_of_nonneg (by linarith)]
    · rwa [abs_of_nonpos (by linarith)]
    · constructor
      · intro l hl'; simp at hl'; subst hl'; exact h0
      · intro t ht; simp at ht; subst ht
        rcases abs_cases q with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> [exact le_max_of_le_right hb;
          exact le_max_of_le_left (by linarith)]
  | some a, none =>
    have ha := h.1 a hl
    simp only
    split_ifs with h1
    · rwa [abs_of_nonneg (by linarith)]
    · exact ⟨fun l hl' => by simp at hl'; exact hl' ▸ h0, fun _ ht => by simp at ht⟩
  | none, some b =>
    have hb := h.2 b hh
    simp only
    split_ifs with h1
    · rwa [abs_of_nonpos (by linarith)]
    · exact ⟨fun l hl' => by simp at hl'; exact hl' ▸ h0, fun _ ht => by simp at ht⟩
  | none, none => exact ⟨fun l hl' => by simp at hl'; exact hl' ▸ h0, fun _ ht => by simp at ht⟩

/-- A comparison the enclosures decide is decided for every pair of members. -/
theorem lt_of_ends {x y : FI} {p q h l : ℚ} (hp : x.mem p) (hq : y.mem q) (hh : x.hi = some h)
    (hl : y.lo = some l) (hlt : h < l) : p < q :=
  lt_of_le_of_lt (hp.2 h hh) (lt_of_lt_of_le hlt (hq.1 l hl))

theorem not_lt_of_ends {x y : FI} {p q l h : ℚ} (hp : x.mem p) (hq : y.mem q) (hl : x.lo = some l)
    (hh : y.hi = some h) (hle : h ≤ l) : ¬ p < q :=
  not_lt.mpr (le_trans (hq.2 h hh) (le_trans hle (hp.1 l hl)))

end PastaLean.FloatInterval
