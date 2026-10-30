import PastaLean.PyAPI.PyPanic
import Libraries.numpy.NumpyDef

namespace Libraries.numpy

/-- Lean-friendly stand-in for NumPy's `empty`; we use `NaN` placeholders. -/
def pyNumpyNaN : Float :=
  0.0 / 0.0

/-- Build an "empty" matrix with `NaN` placeholders. -/
def pyNumpyEmpty (shape : Int × Int) : List (List Float) :=
  let rows := pyNumpyNatFromInt shape.1
  let cols := pyNumpyNatFromInt shape.2
  List.replicate rows (List.replicate cols pyNumpyNaN)

/-- Build a matrix filled with a constant value. -/
def pyNumpyFull {α} [PyNumpyScalar α] (shape : Int × Int) (fillValue : α) : List (List Float) :=
  let rows := pyNumpyNatFromInt shape.1
  let cols := pyNumpyNatFromInt shape.2
  List.replicate rows (List.replicate cols (toFloat fillValue))

/-- Build a zero-filled matrix. Output-polymorphic: a constructor has no argument to take its
field from, so the surrounding code decides (`ℚ` in exact mode, `Float` under `--approx`). -/
def pyNumpyZeros {γ} [Zero γ] (shape : Int × Int) : List (List γ) :=
  let rows' := pyNumpyNatFromInt shape.1
  let cols' := pyNumpyNatFromInt shape.2
  List.replicate rows' (List.replicate cols' 0)

/-- Build a one-filled matrix. -/
def pyNumpyOnes {γ} [One γ] (shape : Int × Int) : List (List γ) :=
  let rows' := pyNumpyNatFromInt shape.1
  let cols' := pyNumpyNatFromInt shape.2
  List.replicate rows' (List.replicate cols' 1)

/-- Build an identity matrix. -/
def pyNumpyEye {γ} [Zero γ] [One γ] (n : Int) : List (List γ) :=
  let n' := pyNumpyNatFromInt n
  (List.range n').map (fun i =>
    (List.range n').map (fun j => if i = j then 1 else 0))

/-- NumPy-style `arange` with 1-, 2-, or 3-argument behavior encoded by defaults. -/
def pyNumpyArange (a : Float) (b : Float := pyNumpyNaN) (c : Float := pyNumpyNaN) : List Float :=
  let oneArg := b != b && c != c
  let twoArgs := b == b && c != c
  let start := if oneArg then 0.0 else a
  let stop := if oneArg then a else b
  let step := if c == c then c else 1.0
  if step == 0.0 then
    PastaLean.pyPanic "ValueError: arange() step must be nonzero"
  else
    if oneArg || twoArgs || c == c then
      let maxIter : Nat := 100000
      let vals := (List.range maxIter).map (fun i => start + step * Rat.toFloat (i : Rat))
      if step > 0.0 then
        vals.takeWhile (fun x => x < stop)
      else
        vals.takeWhile (fun x => x > stop)
    else
      PastaLean.pyPanic "ValueError: arange() received invalid defaults"

/-- Conversion of a `linspace`/`logspace` bound (`Int`/`Float`/`ℚ`/`ℝ`) into the chosen output
scalar `γ`. `γ` is determined by the call context (e.g. the `odeint` that consumes the grid, or a
`Float.pow` in `logspace`), so it's a regular (not `outParam`) class — `Int → ℚ` and `Int → Float`
both exist. Only the conversions that actually arise are provided (no lossy `Float → ℚ`). -/
class PyGridConv (α : Type) (γ : Type) where
  conv : α → γ

instance : PyGridConv Float Float := ⟨id⟩
instance : PyGridConv Rat Rat := ⟨id⟩
noncomputable instance : PyGridConv ℝ ℝ := ⟨id⟩
instance : PyGridConv Int Float := ⟨Float.ofInt⟩
instance : PyGridConv Int Rat := ⟨fun n => (n : ℚ)⟩
noncomputable instance : PyGridConv Int ℝ := ⟨fun n => (n : ℝ)⟩
instance : PyGridConv Nat Float := ⟨Float.ofNat⟩
instance : PyGridConv Nat Rat := ⟨fun n => (n : ℚ)⟩

open scoped Libraries.numpy.PyOdeScalar in
/-- Evenly spaced values over a closed interval, over the output scalar `γ` (`Float` to run, `ℚ`/`ℝ`
to prove — inferred from how the grid is used). `np.linspace(0, 100, n)` (integer bounds) and float
bounds both work. -/
def pyNumpyLinspace {α β γ : Type} [PyOdeScalar γ] [PyGridConv α γ] [PyGridConv β γ]
    (start : α) (stop : β) (num : Int) : List γ :=
  let s : γ := PyGridConv.conv start
  let e : γ := PyGridConv.conv stop
  let n := pyNumpyNatFromInt num
  match n with
  | 0 => []
  | 1 => [s]
  | n + 1 =>
      let step := (e -ₒ s) /ₒ PyOdeScalar.ofNat (α := γ) n
      (List.range (n + 1)).map (fun i => s +ₒ step *ₒ PyOdeScalar.ofNat (α := γ) i)

/-- Logarithmically spaced values over a closed interval. -/
def pyNumpyLogspace (start stop : Float) (num : Int) (base : Float := pyNumpyNaN) : List Float :=
  let base' := if base == base then base else 10.0
  (pyNumpyLinspace start stop num).map (fun x => Float.pow base' x)

/-- Build grid matrices from two coordinate vectors. -/
def pyNumpyMeshgrid (xs ys : List Float) : List (List Float) × List (List Float) :=
  let xgrid := ys.map (fun _ => xs)
  let ygrid := ys.map (fun y => xs.map (fun _ => y))
  (xgrid, ygrid)

/-- Reshape a matrix by flattening and re-chunking it. -/
def pyNumpyReshape {α} [PyNumpyScalar α] (matrix : List (List α)) (shape : Int × Int) : List (List Float) :=
  let rows := pyNumpyNatFromInt shape.1
  let cols := pyNumpyNatFromInt shape.2
  let entries := pyNumpyFlatten matrix
  if entries.length = rows * cols then
    if cols = 0 then
      List.replicate rows []
    else
      let rec go (xs : List Float) (remaining : Nat) : List (List Float) :=
        match remaining with
        | 0 => []
        | r + 1 => xs.take cols :: go (xs.drop cols) r
      go entries rows
  else
    PastaLean.pyPanic "ValueError: reshape() cannot change the number of elements"

/-- Insert a size-1 axis into a vector. -/
def pyNumpyExpandDims (axis : Int) (xs : List Float) : List (List Float) :=
  if axis = 0 then
    [xs]
  else
    xs.map (fun x => [x])

/-- Remove trivial dimensions from a matrix-like value. -/
def pyNumpySqueeze (matrix : List (List Float)) : List Float :=
  match matrix with
  | [row] => row
  | rows =>
      if rows.all (fun row => row.length = 1) then
        rows.map (fun row => row.getD 0 0.0)
      else
        rows.flatten

/-- Concatenate two matrices along axis 0 or 1. -/
def pyNumpyConcatenate (axis : Int := 0) (lhs rhs : List (List Float)) : List (List Float) :=
  if axis = 0 then
    lhs ++ rhs
  else if axis = 1 then
    if lhs.length = rhs.length then
      List.zipWith (· ++ ·) lhs rhs
    else
      PastaLean.pyPanic "ValueError: concatenate() along axis 1 requires equal row counts"
  else
    PastaLean.pyPanic "ValueError: concatenate() only supports axes 0 and 1"

/-- Vertical stack. -/
def pyNumpyVstack (lhs rhs : List (List Float)) : List (List Float) :=
  pyNumpyConcatenate 0 lhs rhs

/-- Horizontal stack. -/
def pyNumpyHstack (lhs rhs : List (List Float)) : List (List Float) :=
  pyNumpyConcatenate 1 lhs rhs

/-- Split a vector into equally sized chunks. -/
def pyNumpySplit (xs : List Float) (parts : Int) : List (List Float) :=
  let parts' := pyNumpyNatFromInt parts
  if parts' = 0 then
    PastaLean.pyPanic "ValueError: split() requires at least one part"
  else
    let chunk := xs.length / parts'
    if chunk * parts' ≠ xs.length then
      PastaLean.pyPanic "ValueError: split() requires equal-sized chunks"
    else
      let rec go (rest : List Float) (remaining : Nat) : List (List Float) :=
        match remaining with
        | 0 => []
        | r + 1 => rest.take chunk :: go (rest.drop chunk) r
      go xs parts'

/-- Tile a matrix by repeating rows and columns. -/
def pyNumpyTile (matrix : List (List Float)) (reps : Int × Int) : List (List Float) :=
  let rowReps := pyNumpyNatFromInt reps.1
  let colReps := pyNumpyNatFromInt reps.2
  let repeatedRows := matrix.map (fun row => (List.replicate colReps row).flatten)
  (List.replicate rowReps repeatedRows).flatten

/-! A constructor takes its field from nowhere, so an unconstrained use (`print(np.zeros((2,3)))`)
would leave a metavariable. Codegen therefore maps `np.zeros` to a CONCRETE variant per numeric
mode: `ℚ` in exact mode (provable), `Float` under `--approx` (runnable). -/

def pyNumpyZerosFloat (shape : Int × Int) : List (List Float) := pyNumpyZeros shape
def pyNumpyOnesFloat  (shape : Int × Int) : List (List Float) := pyNumpyOnes shape
def pyNumpyEyeFloat   (n : Int) : List (List Float) := pyNumpyEye n

def pyNumpyZerosRat (shape : Int × Int) : List (List Rat) := pyNumpyZeros shape
def pyNumpyOnesRat  (shape : Int × Int) : List (List Rat) := pyNumpyOnes shape
def pyNumpyEyeRat   (n : Int) : List (List Rat) := pyNumpyEye n

end Libraries.numpy
