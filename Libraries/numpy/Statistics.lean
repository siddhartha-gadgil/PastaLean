import PastaLean.PyAPI.PyPanic
import Libraries.math.MathDef
import Libraries.numpy.NumpyDef

namespace Libraries.numpy

/-- Convert NumPy scalars to floats. -/
def pyNumpyToFloats {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  xs.map toFloat

/-- Insert a float into a sorted list. -/
def pyNumpyInsertSorted (x : Float) : List Float -> List Float
  | [] => [x]
  | y :: ys => if x <= y then x :: y :: ys else y :: pyNumpyInsertSorted x ys

/-- Sort floats using insertion sort. -/
def pyNumpySortFloats : List Float -> List Float
  | [] => []
  | x :: xs => pyNumpyInsertSorted x (pyNumpySortFloats xs)

/-- Index pairs for `argsort`. -/
def pyNumpyInsertIndexed (x : Float × Nat) : List (Float × Nat) -> List (Float × Nat)
  | [] => [x]
  | y :: ys => if x.1 <= y.1 then x :: y :: ys else y :: pyNumpyInsertIndexed x ys

/-- Sort indexed values by the numeric component. -/
def pyNumpyArgsortFloats : List Float -> List Nat :=
  fun xs =>
    let indexed := (List.range xs.length).zip xs
    let sorted :=
      indexed.foldl
        (fun acc p => pyNumpyInsertIndexed (p.2, p.1) acc)
        []
    sorted.map (fun p => p.2)

/-- Helper for reductions on nonempty float lists. -/
def pyNumpyReduceFloats (f : Float -> Float -> Float) : List Float -> Float
  | [] => PastaLean.pyPanic "ValueError: reduction on an empty list"
  | x :: xs => xs.foldl f x

/-- Helper for indexed argmin/argmax. -/
def pyNumpyArgReduceFloats (better : Float -> Float -> Bool) : List Float -> Nat
  | [] => PastaLean.pyPanic "ValueError: reduction on an empty list"
  | x :: xs =>
      let rec go (best : Float) (bestIdx curIdx : Nat) : List Float -> Nat
        | [] => bestIdx
        | y :: ys =>
            if better y best then
              go y curIdx (curIdx + 1) ys
            else
              go best bestIdx (curIdx + 1) ys
      go x 0 1 xs

/-- Helper to access the `n`th element safely. -/
def pyNumpyGetD (xs : List Float) (n : Nat) (default : Float := 0.0) : Float :=
  xs.getD n default

/-- Sum a list of NumPy scalars. -/
def pyNumpySumVec {α} [PyNumpyScalar α] (xs : List α) : Float :=
  (pyNumpyToFloats xs).foldl (· + ·) 0.0

/-- Mean of a list of NumPy scalars. -/
def pyNumpyMeanVec {α} [PyNumpyScalar α] (xs : List α) : Float :=
  let ys := pyNumpyToFloats xs
  if ys.isEmpty then
    PastaLean.pyPanic "ValueError: mean() of an empty list is undefined"
  else
    ys.foldl (· + ·) 0.0 / Rat.toFloat (ys.length : Rat)

/-- Minimum of a nonempty list. -/
def pyNumpyMin {α} [PyNumpyScalar α] (xs : List α) : Float :=
  pyNumpyReduceFloats (fun a b => if b < a then b else a) (pyNumpyToFloats xs)

/-- Maximum of a nonempty list. -/
def pyNumpyMax {α} [PyNumpyScalar α] (xs : List α) : Float :=
  pyNumpyReduceFloats (fun a b => if b > a then b else a) (pyNumpyToFloats xs)

/-- Index of the minimum element. -/
def pyNumpyArgmin {α} [PyNumpyScalar α] (xs : List α) : Nat :=
  pyNumpyArgReduceFloats (fun a b => a < b) (pyNumpyToFloats xs)

/-- Index of the maximum element. -/
def pyNumpyArgmax {α} [PyNumpyScalar α] (xs : List α) : Nat :=
  pyNumpyArgReduceFloats (fun a b => a > b) (pyNumpyToFloats xs)

/-- Median of a list. -/
def pyNumpyMedian {α} [PyNumpyScalar α] (xs : List α) : Float :=
  let ys := pyNumpySortFloats (pyNumpyToFloats xs)
  match ys.length with
  | 0 => PastaLean.pyPanic "ValueError: median() of an empty list is undefined"
  | n + 1 =>
      if (n + 1) % 2 = 1 then
        ys.getD ((n + 1) / 2) 0.0
      else
        let hi := ys.getD ((n + 1) / 2) 0.0
        let lo := ys.getD (((n + 1) / 2) - 1) 0.0
        (lo + hi) / 2.0

/-- Population variance of a list. -/
def pyNumpyVar {α} [PyNumpyScalar α] (xs : List α) : Float :=
  let ys := pyNumpyToFloats xs
  if ys.isEmpty then
    PastaLean.pyPanic "ValueError: var() of an empty list is undefined"
  else
    let μ := ys.foldl (· + ·) 0.0 / Rat.toFloat (ys.length : Rat)
    ys.foldl (fun acc x => acc + (x - μ) * (x - μ)) 0.0 / Rat.toFloat (ys.length : Rat)

/-- Population standard deviation of a list. -/
def pyNumpyStd {α} [PyNumpyScalar α] (xs : List α) : Float :=
  Float.sqrt (pyNumpyVar xs)

/-- Convert a float percentile to a fractional list rank. -/
def pyNumpyPercentileIndex (n : Nat) (p : Float) : Nat :=
  let p' := if p < 0.0 then 0.0 else if p > 100.0 then 100.0 else p
  let idx := ((p' / 100.0) * Rat.toFloat ((n - 1) : Rat))
  Int.toNat (Libraries.math.floatToInt (Float.floor idx))

/-- Percentile matching NumPy's default `method='linear'`: the percentile `p` maps to the
fractional rank `(p/100)·(n-1)` in the sorted data, and the result linearly interpolates
between the two surrounding samples. (`np.percentile([1,2,3,4], 50) = 2.5`.) -/
def pyNumpyPercentile {α} [PyNumpyScalar α] (xs : List α) (p : Float) : Float :=
  let ys := pyNumpySortFloats (pyNumpyToFloats xs)
  match ys.length with
  | 0 => PastaLean.pyPanic "ValueError: percentile() of an empty list is undefined"
  | n + 1 =>
      let p' := if p < 0.0 then 0.0 else if p > 100.0 then 100.0 else p
      let rank := (p' / 100.0) * Rat.toFloat (n : Rat)
      let lo := Int.toNat (Libraries.math.floatToInt (Float.floor rank))
      let hi := Int.toNat (Libraries.math.floatToInt (Float.ceil rank))
      let frac := rank - Float.floor rank
      let yLo := ys.getD lo 0.0
      let yHi := ys.getD hi 0.0
      yLo + frac * (yHi - yLo)

/-- Clip values to a closed interval. -/
def pyNumpyClip {α} [PyNumpyScalar α] (xs : List α) (lo hi : Float) : List Float :=
  (pyNumpyToFloats xs).map (fun x => if x < lo then lo else if x > hi then hi else x)

/-- Round values to the nearest integer-valued float. -/
def pyNumpyRound {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map (fun x =>
    if x < 0.0 then
      Float.ceil (x - 0.5)
    else
      Float.floor (x + 0.5))

/-- Exponential elementwise map. -/
def pyNumpyExp {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map Float.exp

/-- Natural log elementwise map. -/
def pyNumpyLog {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map Float.log

/-- Base-10 log elementwise map. -/
def pyNumpyLog10 {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map (fun x => Float.log x / Float.log 10.0)

/-- Base-2 log elementwise map. -/
def pyNumpyLog2 {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map (fun x => Float.log x / Float.log 2.0)

/-- Square root elementwise map. -/
def pyNumpySqrt {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map Float.sqrt

/-! ## Exact (`ℝ`) transcendental maps (default mode)

`noncomputable` `ℝ` counterparts of the elementwise transcendental maps and `std`, backed by
`Real.*`. Selected over the `Float` versions in exact mode; theorems about them are true. -/

/-- Map numpy scalars to `ℝ` (exact-mode analogue of `pyNumpyToFloats`). -/
noncomputable def pyNumpyToReals {α} [PyNumpyRealScalar α] (xs : List α) : List ℝ :=
  xs.map PyNumpyRealScalar.toReal

noncomputable def pyNumpyExpR {α} [PyNumpyRealScalar α] (xs : List α) : List ℝ :=
  (pyNumpyToReals xs).map Real.exp

noncomputable def pyNumpyLogR {α} [PyNumpyRealScalar α] (xs : List α) : List ℝ :=
  (pyNumpyToReals xs).map Real.log

noncomputable def pyNumpyLog10R {α} [PyNumpyRealScalar α] (xs : List α) : List ℝ :=
  (pyNumpyToReals xs).map (fun x => Real.log x / Real.log 10)

noncomputable def pyNumpyLog2R {α} [PyNumpyRealScalar α] (xs : List α) : List ℝ :=
  (pyNumpyToReals xs).map (fun x => Real.log x / Real.log 2)

noncomputable def pyNumpySqrtR {α} [PyNumpyRealScalar α] (xs : List α) : List ℝ :=
  (pyNumpyToReals xs).map Real.sqrt

/-- Population standard deviation over `ℝ` (`std`): `√(mean((xᵢ - mean)²))`. -/
noncomputable def pyNumpyStdR {α} [PyNumpyRealScalar α] (xs : List α) : ℝ :=
  let ys := pyNumpyToReals xs
  if ys.isEmpty then 0
  else
    let n : ℝ := (ys.length : ℝ)
    let mean := ys.foldl (· + ·) 0 / n
    let var := (ys.map (fun x => (x - mean) ^ 2)).foldl (· + ·) 0 / n
    Real.sqrt var

/-- Logical `any` over a list. -/
def pyNumpyAny {α} [PyNumpyScalar α] (xs : List α) : Bool :=
  xs.any (fun x => toFloat x != 0.0)

/-- Logical `all` over a list. -/
def pyNumpyAll {α} [PyNumpyScalar α] (xs : List α) : Bool :=
  xs.all (fun x => toFloat x != 0.0)

/-- Elementwise membership test. -/
def pyNumpyIsin {α β} [PyNumpyScalar α] [PyNumpyScalar β] (xs : List α) (ys : List β) : List Bool :=
  let choices := pyNumpyToFloats ys
  (pyNumpyToFloats xs).map (fun x => choices.any (fun y => (x == y)))

/-- Elementwise boolean and. -/
def pyNumpyLogicalAnd (xs ys : List Bool) : List Bool :=
  List.zipWith (· && ·) xs ys

/-- Elementwise boolean or. -/
def pyNumpyLogicalOr (xs ys : List Bool) : List Bool :=
  List.zipWith (· || ·) xs ys

/-- Elementwise boolean not. -/
def pyNumpyLogicalNot (xs : List Bool) : List Bool :=
  xs.map not

/-- Elementwise closeness check. -/
def pyNumpyIsclose {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (xs : List α) (ys : List β) (tol : Float := 1e-8) : List Bool :=
  let lhs := pyNumpyToFloats xs
  let rhs := pyNumpyToFloats ys
  if lhs.length = rhs.length then
    List.zipWith (fun x y => Float.abs (x - y) ≤ tol) lhs rhs
  else
    PastaLean.pyPanic "ValueError: isclose() expects equal-length lists"

/-- Sort a list of scalars. -/
def pyNumpySort {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  pyNumpySortFloats (pyNumpyToFloats xs)

/-- Indices that would sort a list. -/
def pyNumpyArgsort {α} [PyNumpyScalar α] (xs : List α) : List Nat :=
  pyNumpyArgsortFloats (pyNumpyToFloats xs)

/-- First insertion point into a sorted list. -/
def pyNumpySearchsorted (sorted : List Float) (x : Float) : Nat :=
  let rec go : List Float -> Nat -> Nat
    | [] , idx => idx
    | y :: ys, idx => if x ≤ y then idx else go ys (idx + 1)
  go sorted 0

/-- Deduplicate a sorted list. -/
def pyNumpyUniqueFloats (xs : List Float) : List Float :=
  let rec go : Option Float → List Float → List Float
    | _, [] => []
    | none, y :: ys => y :: go (some y) ys
    | some prev, y :: ys =>
        if y == prev then
          go (some prev) ys
        else
          y :: go (some y) ys
  go none xs

/-- Unique values of a list. -/
def pyNumpyUnique {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  pyNumpyUniqueFloats (pyNumpySort xs)

/-- Return values satisfying a boolean mask. -/
def pyNumpyWhere {α} [PyNumpyScalar α] (cond : List Bool) (x y : List α) : List Float :=
  let lhs := pyNumpyToFloats x
  let rhs := pyNumpyToFloats y
  if cond.length = lhs.length && lhs.length = rhs.length then
    let rec go : List Bool -> List Float -> List Float -> List Float
      | [], [], [] => []
      | c :: cs, tx :: xs, fx :: ys => (if c then tx else fx) :: go cs xs ys
      | _, _, _ => PastaLean.pyPanic "ValueError: where() expects equal-length lists"
    go cond lhs rhs
  else
    PastaLean.pyPanic "ValueError: where() expects equal-length lists"

/-- Indices of nonzero values. -/
def pyNumpyNonzero {α} [PyNumpyScalar α] (xs : List α) : List Nat :=
  let ys := pyNumpyToFloats xs
  let rec go : List Float -> Nat -> List Nat
    | [], _ => []
    | x :: rest, i => if x != 0.0 then i :: go rest (i + 1) else go rest (i + 1)
  go ys 0

/-- Coordinates of truthy values in a matrix-like boolean array. -/
def pyNumpyArgwhere (matrix : List (List Bool)) : List (Nat × Nat) :=
  let rec rowsGo : List (List Bool) -> Nat -> List (Nat × Nat)
    | [], _ => []
    | row :: rows, i =>
        let rec colsGo : List Bool -> Nat -> List (Nat × Nat)
          | [], _ => []
          | c :: cs, j => if c then (i, j) :: colsGo cs (j + 1) else colsGo cs (j + 1)
        colsGo row 0 ++ rowsGo rows (i + 1)
  rowsGo matrix 0

/-- Extract values satisfying a mask. -/
def pyNumpyExtract {α} [PyNumpyScalar α] (cond : List Bool) (xs : List α) : List Float :=
  let vals := pyNumpyToFloats xs
  if cond.length = vals.length then
    (List.zipWith (fun c x => if c then some x else none) cond vals).filterMap id
  else
    PastaLean.pyPanic "ValueError: extract() expects equal-length lists"

/-- Take elements at a list of indices. -/
def pyNumpyTake {α} [PyNumpyScalar α] (xs : List α) (indices : List Nat) : List Float :=
  let vals := pyNumpyToFloats xs
  indices.map (fun i => vals.getD i 0.0)

/-- Put values at a list of indices. -/
def pyNumpyPut {α} [PyNumpyScalar α] (xs : List α) (indices : List Nat) (values : List α) : List Float :=
  let vals := pyNumpyToFloats xs
  let reps := pyNumpyToFloats values
  if indices.length = reps.length then
    let rec go : List Float -> List Nat -> List Float -> List Float
      | [], [], _ => []
      | [], _ :: _, _ => []
      | x :: rest, idxs, repls =>
          match idxs, repls with
          | [], [] => x :: go rest [] []
          | i :: is, v :: vs =>
              if i = 0 then
                v :: go rest is vs
              else
                x :: go rest ((i - 1) :: is) (v :: vs)
          | _, _ => x :: go rest idxs repls
      go vals indices reps
  else
    PastaLean.pyPanic "ValueError: put() expects equal numbers of indices and values"

/-- Product of all elements in a vector (`np.prod`). -/
def pyNumpyProd {α} [PyNumpyScalar α] (xs : List α) : Float :=
  (pyNumpyToFloats xs).foldl (· * ·) 1.0

/-- Cumulative sum of a vector (`np.cumsum`); the `i`th entry is the sum of `xs[0..i]`. -/
def pyNumpyCumsum {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  let rec go (acc : Float) : List Float → List Float
    | [] => []
    | y :: ys => (acc + y) :: go (acc + y) ys
  go 0.0 (pyNumpyToFloats xs)

/-- Cumulative product of a vector (`np.cumprod`). -/
def pyNumpyCumprod {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  let rec go (acc : Float) : List Float → List Float
    | [] => []
    | y :: ys => (acc * y) :: go (acc * y) ys
  go 1.0 (pyNumpyToFloats xs)

/-- Consecutive differences `xs[i+1] - xs[i]` (`np.diff`). Result has one fewer element. -/
def pyNumpyDiff {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  let ys := pyNumpyToFloats xs
  List.zipWith (fun b a => b - a) (ys.drop 1) ys

/-- Peak-to-peak range `max - min` of a nonempty vector (`np.ptp`). -/
def pyNumpyPtp {α} [PyNumpyScalar α] (xs : List α) : Float :=
  pyNumpyMax xs - pyNumpyMin xs

/-- Elementwise sign `-1 / 0 / 1` (`np.sign`). -/
def pyNumpySign {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map (fun x => if x < 0.0 then -1.0 else if x > 0.0 then 1.0 else 0.0)

/-- Elementwise absolute value (`np.abs` / `np.absolute`). -/
def pyNumpyAbs {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map Float.abs

/-- Elementwise binary maximum (`np.maximum`). -/
def pyNumpyMaximum {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (xs : List α) (ys : List β) : List Float :=
  List.zipWith (fun a b => if a < b then b else a) (pyNumpyToFloats xs) (pyNumpyToFloats ys)

/-- Elementwise binary minimum (`np.minimum`). -/
def pyNumpyMinimum {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (xs : List α) (ys : List β) : List Float :=
  List.zipWith (fun a b => if b < a then b else a) (pyNumpyToFloats xs) (pyNumpyToFloats ys)

/-- Elementwise power `xs[i] ** ys[i]` (`np.power`). -/
def pyNumpyPower {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (xs : List α) (ys : List β) : List Float :=
  List.zipWith Float.pow (pyNumpyToFloats xs) (pyNumpyToFloats ys)

/-- Weighted average (`np.average`); with no weights this is the plain mean. The weights are
normalized by their own sum, matching `np.average(xs, weights=ws)`. -/
def pyNumpyAverage {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (xs : List α) (weights : List β := []) : Float :=
  let vals := pyNumpyToFloats xs
  if vals.isEmpty then
    PastaLean.pyPanic "ValueError: average() of an empty list is undefined"
  else
    let ws := pyNumpyToFloats weights
    if ws.isEmpty then
      vals.foldl (· + ·) 0.0 / Rat.toFloat (vals.length : Rat)
    else if ws.length = vals.length then
      let wsum := ws.foldl (· + ·) 0.0
      if wsum == 0.0 then
        PastaLean.pyPanic "ZeroDivisionError: weights sum to zero"
      else
        (List.zipWith (· * ·) vals ws).foldl (· + ·) 0.0 / wsum
    else
      PastaLean.pyPanic "ValueError: average() weights must match the data length"

/-- Population covariance of two equal-length vectors (`np.cov(x, y, bias=True)[0,1]`). -/
def pyNumpyCov {α β} [PyNumpyScalar α] [PyNumpyScalar β] (xs : List α) (ys : List β) : Float :=
  let a := pyNumpyToFloats xs
  let b := pyNumpyToFloats ys
  if a.isEmpty || a.length ≠ b.length then
    PastaLean.pyPanic "ValueError: cov() expects two nonempty equal-length lists"
  else
    let n := Rat.toFloat (a.length : Rat)
    let μa := a.foldl (· + ·) 0.0 / n
    let μb := b.foldl (· + ·) 0.0 / n
    (List.zipWith (fun x y => (x - μa) * (y - μb)) a b).foldl (· + ·) 0.0 / n

/-- Pearson correlation coefficient of two equal-length vectors (`np.corrcoef(x, y)[0,1]`). -/
def pyNumpyCorrcoef {α β} [PyNumpyScalar α] [PyNumpyScalar β] (xs : List α) (ys : List β) : Float :=
  let cov := pyNumpyCov xs ys
  let varx := pyNumpyVar xs
  let vary := pyNumpyVar ys
  let denom := Float.sqrt (varx * vary)
  if denom == 0.0 then
    PastaLean.pyPanic "ValueError: corrcoef() is undefined for a constant input"
  else
    cov / denom

/-- Sum all entries in a matrix. -/
def pyNumpySum {α} [PyNumpyScalar α] (matrix : List (List α)) : Float :=
  (pyNumpyArray matrix).flatten.foldl (· + ·) 0.0

/-- Mean of all entries in a matrix. -/
def pyNumpyMean {α γ} [PyNumpyCompute α γ] [PyOdeScalar γ] [Add γ] [Zero γ] [Inhabited γ]
    (matrix : List (List α)) : γ :=
  let entries := (pyNumpyArrayOver (γ := γ) matrix).flatten
  if entries.isEmpty then
    PastaLean.pyPanic "ValueError: mean() of an empty matrix is undefined"
  else
    -- `PyOdeScalar` (not `NatCast`/`Div`) because `Float` has neither in Mathlib.
    PyOdeScalar.div (entries.foldl (· + ·) 0) (PyOdeScalar.ofNat entries.length)

end Libraries.numpy
