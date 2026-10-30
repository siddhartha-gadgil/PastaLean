import PastaLean.PyAPI.PyPanic
import PastaLean.Imports

namespace Libraries.numpy

/-- The numeric scalar an RK4/odeint integration and a `linspace` grid run over — `Float` (runnable)
or `ℚ`/`ℝ` (provable). Bundles only the ops these use (NOT `Field`, which `Float` lacks). Lives here
(numpy, the base library) so both `np.linspace` and `scipy.odeint` can share it. -/
class PyOdeScalar (α : Type) where
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  ofNat : Nat → α

instance : PyOdeScalar Float := ⟨(·+·), (·-·), (·*·), (·/·), Float.ofNat⟩
instance : PyOdeScalar Rat := ⟨(·+·), (·-·), (·*·), (·/·), fun n => (n : ℚ)⟩
noncomputable instance : PyOdeScalar ℝ := ⟨(·+·), (·-·), (·*·), (·/·), fun n => (n : ℝ)⟩

namespace PyOdeScalar
scoped infixl:65 " +ₒ " => PyOdeScalar.add
scoped infixl:65 " -ₒ " => PyOdeScalar.sub
scoped infixl:70 " *ₒ " => PyOdeScalar.mul
scoped infixl:70 " /ₒ " => PyOdeScalar.div
end PyOdeScalar

/-- Types that can be treated as NumPy numeric entries by the runtime layer. -/
class PyNumpyScalar (α : Type) where
  toFloat : α → Float

export PyNumpyScalar (toFloat)

instance : PyNumpyScalar Float where
  toFloat := id

instance : PyNumpyScalar Rat where
  toFloat := Rat.toFloat

instance : PyNumpyScalar Int where
  toFloat x := Rat.toFloat (x : Rat)

instance : PyNumpyScalar Nat where
  toFloat x := Rat.toFloat (x : Rat)

instance : PyNumpyScalar Bool where
  toFloat b := if b then 1.0 else 0.0

/-- Maps a numpy scalar entry type to the numeric *field* its purely-algebraic reductions
(`dot`, `det`, `mean`, …) should compute in. `Float → Float` and `Rat → Rat` stay in their own
field (so exact-mode `ℚ` results compose with surrounding `ℚ` code, and `--approx` `Float`
results are unchanged); the integral/bool scalars promote to `Float` to match the historical
`Float`-valued behaviour. The result type is an `outParam` so callers don't have to annotate it. -/
class PyNumpyCompute (α : Type) (γ : outParam Type) where
  cast : α → γ

instance : PyNumpyCompute Float Float := ⟨id⟩
instance : PyNumpyCompute Rat Rat := ⟨id⟩
instance : PyNumpyCompute Int Float := ⟨fun x => Rat.toFloat (x : Rat)⟩
instance : PyNumpyCompute Nat Float := ⟨fun x => Rat.toFloat (x : Rat)⟩
instance : PyNumpyCompute Bool Float := ⟨fun b => if b then 1.0 else 0.0⟩
/-- `ℝ` entries (arising when a transcendental result feeds back into an algebraic numpy op,
e.g. `np.dot` over `sigmoid` outputs in exact mode) compute in `ℝ`. -/
noncomputable instance : PyNumpyCompute ℝ ℝ := ⟨id⟩

/-- Common compute type for a binary numpy op over two (possibly DIFFERENT) element types. Lets
`np.dot` mix `ℚ` data with `ℝ` weights — `(ℚ,ℝ) → ℝ` — without a `List ℚ → List ℝ` coercion (which
Lean does not provide). Same-type pairs reuse `PyNumpyCompute`; only the mixed `ℚ`/`ℝ` cases are
extra. -/
class PyNumpyJoin (α β : Type) (γ : outParam Type) where
  castL : α → γ
  castR : β → γ

instance {α γ} [PyNumpyCompute α γ] : PyNumpyJoin α α γ where
  castL := PyNumpyCompute.cast
  castR := PyNumpyCompute.cast
noncomputable instance : PyNumpyJoin Rat ℝ ℝ where castL := fun q => (q : ℝ); castR := id
noncomputable instance : PyNumpyJoin ℝ Rat ℝ where castL := id; castR := fun q => (q : ℝ)

/-- Exact (`ℝ`) counterpart of `PyNumpyScalar`, used in the default numeric mode so numpy's
transcendental maps (`exp`/`log`/`sqrt`/`std`) produce provable `ℝ` values instead of `Float`. -/
class PyNumpyRealScalar (α : Type) where
  toReal : α → ℝ

noncomputable instance : PyNumpyRealScalar ℝ := ⟨id⟩
noncomputable instance : PyNumpyRealScalar Rat := ⟨fun q => (q : ℝ)⟩
noncomputable instance : PyNumpyRealScalar Int := ⟨fun n => (n : ℝ)⟩
noncomputable instance : PyNumpyRealScalar Nat := ⟨fun n => (n : ℝ)⟩
noncomputable instance : PyNumpyRealScalar Bool := ⟨fun b => if b then 1 else 0⟩

/-- Convert a nonnegative `Int` dimension to `Nat`. -/
def pyNumpyNatFromInt (n : Int) : Nat :=
  if n < 0 then
    PastaLean.pyPanic "ValueError: numpy dimensions must be nonnegative"
  else
    n.toNat

/-- Number of rows in a matrix. -/
def pyNumpyRows {α} (matrix : List (List α)) : Nat :=
  matrix.length

/-- Number of columns in a matrix, taken from the first row. -/
def pyNumpyCols {α} (matrix : List (List α)) : Nat :=
  match matrix with
  | [] => 0
  | row :: _ => row.length

/-- Check that every row has the same length. -/
def pyNumpyIsRectangular {α} (matrix : List (List α)) : Bool :=
  match matrix with
  | [] => true
  | row :: rows => rows.all (fun r => r.length = row.length)

/-- Check that a matrix is square. -/
def pyNumpyIsSquare {α} (matrix : List (List α)) : Bool :=
  pyNumpyIsRectangular matrix &&
    match matrix with
    | [] => true
    | row :: _ => matrix.length = row.length

/-- Compare the shapes of two matrices. -/
def pyNumpySameShape? {α β} (lhs : List (List α)) (rhs : List (List β)) : Bool :=
  match lhs, rhs with
  | [], [] => true
  | l :: ls, r :: rs => l.length = r.length && pyNumpySameShape? ls rs
  | _, _ => false

/-- Normalize a matrix to `Float` entries. -/
def pyNumpyArray {α} [PyNumpyScalar α] (matrix : List (List α)) : List (List Float) :=
  matrix.map (List.map toFloat)

/-- `np.copy(x)`: a shallow copy. Our containers are immutable values, so it is the identity. -/
def pyNumpyCopy {α : Type} (x : α) : α := x

/-- Normalize a matrix into its compute field `γ` (`ℚ` stays `ℚ`, `Float` stays `Float`), so an
algebraic numpy op returns a value in the SAME field as the surrounding code instead of always
collapsing to `Float`. -/
def pyNumpyArrayOver {α γ} [PyNumpyCompute α γ] (matrix : List (List α)) : List (List γ) :=
  matrix.map (List.map PyNumpyCompute.cast)

/-- Return the matrix shape as `[rows, cols]`. A `List Int` (not a `Prod`) so that both indexing
(`np.shape(x)[0]`) and tuple-unpack assignment (`rows, cols = np.shape(x)`) — which the codegen
lowers to `⦋0⦌`/`⦋1⦌` (`pyGetItem`) — work; a `Prod` has no `PyGetItem` instance. -/
def pyNumpyShape {α} (matrix : List (List α)) : List Int :=
  if pyNumpyIsRectangular matrix then
    [Int.ofNat matrix.length, Int.ofNat (pyNumpyCols matrix)]
  else
    PastaLean.pyPanic "ValueError: shape() expects a rectangular matrix"

/-- Flatten a matrix into a vector. -/
def pyNumpyFlatten {α} [PyNumpyScalar α] (matrix : List (List α)) : List Float :=
  (pyNumpyArray matrix).flatten

end Libraries.numpy
