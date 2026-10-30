import PastaLean.PyAPI.PyPanic
import Libraries.pandas.Cell

/-!
# pandas `Series` — core

A one-dimensional labelled array: a `name`, a list of index labels, and the cell values (same length
as the index). This file holds the type, construction, positional/label access, and the
value-preserving transforms (`apply`, `abs`, `round`, `cumsum`, arithmetic, `sort_values`, `unique`).
The numeric reductions (`sum`, `mean`, `std`, `describe`, …) live in `Series` statistics
(`SeriesStats.lean`), which extends this namespace.
-/

namespace Libraries.pandas

/-- A 1-D labelled column of values. -/
structure Series where
  values : List Cell
  index  : List String := []
  name   : String := ""
  deriving Repr, Inhabited

namespace Series

/-- Default `RangeIndex`: labels `"0" … "n-1"`. -/
def rangeIndex (n : Nat) : List String := (List.range n).map toString

/-- Construct from a list of cells, defaulting the index to a `RangeIndex`. -/
def ofCells (values : List Cell) (index : Option (List String) := none) (name : String := "") : Series :=
  { values, name, index := index.getD (rangeIndex values.length) }

/-- Construct from any Lean list whose elements convert to cells (`[1,2,3]`, `["a","b"]`, …). -/
def ofList {α} [ToCell α] (xs : List α) (index : Option (List String) := none) (name : String := "") : Series :=
  ofCells (toCells xs) index name

/-- The numeric values, missing/non-numeric cells dropped (the `skipna=True` view). -/
def numeric (s : Series) : List Float :=
  s.values.filterMap Cell.toFloat?

/-- Inferred dtype of the series (`int64`/`float64`/`object`). -/
def dtype (s : Series) : DType := dtypeOf s.values

/-- `len(s)` — number of entries, including missing ones. -/
def size (s : Series) : Nat := s.values.length

/-- Position access with Python semantics (negative indices count from the end). `iloc`. -/
def iloc (s : Series) (i : Int) : Cell :=
  let n := s.values.length
  let j := if i < 0 then i + Int.ofNat n else i
  if j < 0 || j ≥ Int.ofNat n then PastaLean.pyPanic "IndexError: single positional indexer is out-of-bounds"
  else s.values[j.toNat]!

/-- Label access. `loc`. -/
def loc (s : Series) (label : String) : Cell :=
  match s.index.idxOf? label with
  | some i => s.values[i]!
  | none   => PastaLean.pyPanic "KeyError: label not found in Series index"

/-- First `n` entries (default 5). -/
def head (s : Series) (n : Nat := 5) : Series :=
  { s with values := s.values.take n, index := s.index.take n }

/-- Last `n` entries (default 5). -/
def tail (s : Series) (n : Nat := 5) : Series :=
  let k := s.values.length - n
  { s with values := s.values.drop k, index := s.index.drop k }

/-- Apply a numeric function elementwise; missing/non-numeric cells stay missing. -/
def apply (s : Series) (f : Float → Float) : Series :=
  { s with values := s.values.map fun c => match c.toFloat? with
      | some v => Cell.float (f v)
      | none   => Cell.na }

/-- `s.abs()`. -/
def abs (s : Series) : Series := s.apply Float.abs

/-- Round each value to `nd` decimal places. -/
def round (s : Series) (nd : Nat := 0) : Series :=
  let p := Float.ofNat (10 ^ nd)
  s.apply fun v => (v * p).round / p

/-- Running (cumulative) sum. Missing cells stay missing but do not reset the accumulator. Preserves
integer dtype (an int column's cumsum is integer, as in pandas). -/
def cumsum (s : Series) : Series :=
  if s.dtype == DType.int then
    let rec goI (acc : Int) : List Cell → List Cell
      | []      => []
      | c :: cs =>
        match c with
        | .int n  => Cell.int (acc + n) :: goI (acc + n) cs
        | .bool b => let v := acc + (if b then 1 else 0); Cell.int v :: goI v cs
        | _       => Cell.na :: goI acc cs
    { s with values := goI 0 s.values }
  else
    let rec goF (acc : Float) : List Cell → List Cell
      | []      => []
      | c :: cs =>
        match c.toFloat? with
        | some v => Cell.float (acc + v) :: goF (acc + v) cs
        | none   => Cell.na :: goF acc cs
    { s with values := goF 0.0 s.values }

/-- Distinct values, first occurrence kept (pandas `unique`, returned as a `Series`). -/
def unique (s : Series) : Series :=
  { s with values := s.values.foldl (fun acc c => if acc.contains c then acc else acc ++ [c]) [],
           index := [] }

/-- Values as a plain list of cells (`s.tolist()`). -/
def tolist (s : Series) : List Cell := s.values

/-- Combine two series positionally with a numeric op; either side missing ⇒ missing. -/
private def zipWithNumeric (f : Float → Float → Float) (a b : Series) : Series :=
  { a with values := (a.values.zip b.values).map fun (x, y) =>
      match x.toFloat?, y.toFloat? with
      | some u, some v => Cell.float (f u v)
      | _, _           => Cell.na }

def add (a b : Series) : Series := zipWithNumeric (· + ·) a b
def sub (a b : Series) : Series := zipWithNumeric (· - ·) a b
def mul (a b : Series) : Series := zipWithNumeric (· * ·) a b
def div (a b : Series) : Series := zipWithNumeric (· / ·) a b
def addScalar (a : Series) (k : Float) : Series := a.apply (· + k)
def mulScalar (a : Series) (k : Float) : Series := a.apply (· * k)

/-- Sort by value ascending; missing values go last (`na_position='last'`). Index is realigned. -/
def sortValues (s : Series) (ascending : Bool := true) : Series :=
  let idx := if s.index.length == s.values.length then s.index else rangeIndex s.values.length
  let paired := s.values.zip idx
  let key : (Cell × String) → Float := fun (c, _) => (c.toFloat?).getD (1.0 / 0.0)
  let sorted := paired.foldr
    (fun p acc =>
      let rec ins : List (Cell × String) → List (Cell × String)
        | [] => [p]
        | q :: qs => if key p ≤ key q then p :: q :: qs else q :: ins qs
      ins acc) []
  let ordered := if ascending then sorted else sorted.reverse
  { s with values := ordered.map (·.1), index := ordered.map (·.2) }

/-- pandas-style `str(series)`: index column, right-justified values, and a `dtype:` footer
(prefixed with `Name:` when the series is named). -/
def toStr (s : Series) : String :=
  let idx := if s.index.length == s.values.length then s.index else rangeIndex s.values.length
  let iw := (idx.map String.length).foldl Nat.max 0
  let vstrs := s.values.map Cell.toStr
  let vw := (vstrs.map String.length).foldl Nat.max 0
  let lines := (idx.zip vstrs).map fun p => padRight p.1 iw ++ "    " ++ padLeft p.2 vw
  let footer := (if s.name.isEmpty then "" else s!"Name: {s.name}, ") ++ s!"dtype: {s.dtype}"
  String.intercalate "\n" (lines ++ [footer])

instance : ToString Series := ⟨toStr⟩

/-- Print a series (`print(s)`). -/
def printSeries (s : Series) : IO Unit := IO.println s.toStr

end Series
end Libraries.pandas
