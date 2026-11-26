import PastaLean.PyAPI.PyPanic
import Libraries.pandas.Series

set_option linter.unusedVariables false

/-!
# pandas `DataFrame` — core

A 2-D labelled table. Columns are stored as an **ordered** association list `(name, cells)` — pandas
guarantees column order (`df.columns`, `df.shape`, iteration and printing all depend on it), which a
`HashMap` would not preserve. Each column has one cell per index label.

This file holds the type, construction, access (`columns`/`index`/`shape`/`at`/`iat`/column →
`Series`), row slicing (`head`/`tail`), mutation (`insert`/`drop`) and printing. Column-wise
reductions (`sum`, `mean`, `describe`, …) live in `DataFrameStats.lean`.
-/

namespace Libraries.pandas

/-- A 2-D labelled table with ordered columns. -/
structure DataFrame where
  /-- Ordered `(columnName, cells)` pairs; every column has `index.length` cells. -/
  cols  : List (String × List Cell)
  /-- Row index labels. -/
  index : List String
  deriving Repr, Inhabited

namespace DataFrame

private def rangeIndex (n : Nat) : List String := (List.range n).map toString

/-- Transpose a row-major list of rows into columns (pandas reads `[[..],[..]]` as rows). -/
private def transpose (rows : List (List Cell)) : List (List Cell) :=
  match rows with
  | []      => []
  | r :: _  => (List.range r.length).map fun j => rows.map fun row => row[j]!

/-- Build from row-major data (`pd.DataFrame([[1,2],[3,4]], columns=[...])`). Defaults to a
`RangeIndex` for both rows and columns, as pandas does. -/
def ofRows {α} [ToCell α]
    (data : List (List α))
    (index : Option (List String) := none) (columns : Option (List String) := none) : DataFrame :=
  let rows := data.map toCells
  let colData := transpose rows
  let colNames := columns.getD (rangeIndex colData.length)
  { cols := colNames.zip colData, index := index.getD (rangeIndex rows.length) }

/-- Build column-wise (`pd.DataFrame({"a":[1,2], "b":[3,4]})`), preserving the given column order. -/
def ofColumns (cols : List (String × List Cell)) (index : Option (List String) := none) : DataFrame :=
  let nrows := (cols.head?.map (·.2.length)).getD 0
  { cols, index := index.getD (rangeIndex nrows) }

/-- Codegen entry point for `pd.DataFrame(...)`: row-major data with optional index/columns. -/
def pyDataFrame {α} [ToCell α]
    (data : List (List α))
    (index : Option (List String) := none) (columns : Option (List String) := none)
    (dtype copy : Unit := ()) : DataFrame :=
  ofRows data index columns

/-- Column names, in order. -/
def getColumns (df : DataFrame) : List String := df.cols.map (·.1)

/-- Row index labels. -/
def getIndex (df : DataFrame) : List String := df.index

/-- `(nrows, ncols)`. -/
def shape (df : DataFrame) : Int × Int := (Int.ofNat df.index.length, Int.ofNat df.cols.length)

/-- `df.empty`. -/
def empty (df : DataFrame) : Bool := df.index.isEmpty || df.cols.isEmpty

/-- Raw cells of a column by name. -/
def colCells? (df : DataFrame) (name : String) : Option (List Cell) :=
  (df.cols.find? (·.1 == name)).map (·.2)

/-- Column access `df[name]` → a `Series` (indexed by the frame's row index). -/
def getColumn (df : DataFrame) (name : String) : Series :=
  match df.colCells? name with
  | some cells => { values := cells, index := df.index, name }
  | none       => panic! s!"KeyError: {name}"

/-- First `n` rows (default 5). -/
def head (df : DataFrame) (n : Nat := 5) : DataFrame :=
  { cols := df.cols.map fun (nm, c) => (nm, c.take n), index := df.index.take n }

/-- Last `n` rows (default 5). -/
def tail (df : DataFrame) (n : Nat := 5) : DataFrame :=
  let k := df.index.length - n
  { cols := df.cols.map fun (nm, c) => (nm, c.drop k), index := df.index.drop k }

/-- Scalar access by row label and column name (`df.at[row, col]`). -/
def getAt (df : DataFrame) (rowLabel : String) (colName : String) : Cell :=
  match df.index.idxOf? rowLabel, df.colCells? colName with
  | some i, some cells => cells[i]!
  | _, _ => PastaLean.pyPanic "KeyError: row label or column name not found"

/-- Scalar access by integer positions (`df.iat[i, j]`). -/
def iat (df : DataFrame) (i j : Nat) : Cell :=
  match df.cols[j]? with
  | some col => col.2[i]!
  | none => PastaLean.pyPanic "IndexError: iat position out of bounds"

/-- Insert / replace a column, preserving order (append if new). Length must match the row count. -/
def insertColumn (df : DataFrame) (name : String) (cells : List Cell) : DataFrame :=
  if cells.length != df.index.length then
    PastaLean.pyPanic "ValueError: length of values does not match length of index"
  else if df.cols.any (·.1 == name) then
    { df with cols := df.cols.map fun (nm, c) => if nm == name then (nm, cells) else (nm, c) }
  else
    { df with cols := df.cols ++ [(name, cells)] }

/-- Drop a column by name (`df.drop(columns=[name])`). No-op if absent. -/
def dropColumn (df : DataFrame) (name : String) : DataFrame :=
  { df with cols := df.cols.filter (·.1 != name) }

set_option linter.unusedVariables false in
/-- pandas-compatible `insert(loc, column, value)` (loc currently appends/replaces). -/
def insert (df : DataFrame) (loc : Nat) (colName : String) (colData : List Cell) (ad : Bool := false) : DataFrame :=
  df.insertColumn colName colData

/-- Render a frame as aligned text, pandas `__repr__`-style: an index column plus one right-justified
column per name (each column widened to fit its header and cells). -/
def toStr (df : DataFrame) : String :=
  let idxW := (df.index.map String.length).foldl Nat.max 0
  let colStrs : List (String × List String) := df.cols.map fun col =>
    let cells := col.2.map Cell.toStr
    let w := (col.1.length :: cells.map String.length).foldl Nat.max 0
    (padLeft col.1 w, cells.map (fun x => padLeft x w))
  let header := padRight "" idxW ++ String.join (colStrs.map fun hc => "  " ++ hc.1)
  let rows := (List.range df.index.length).map fun i =>
    padRight (df.index.getD i "") idxW ++ String.join (colStrs.map fun hc => "  " ++ hc.2.getD i "")
  String.intercalate "\n" (header :: rows)

instance : ToString DataFrame := ⟨toStr⟩

/-- Print a frame (`print(df)`). -/
def printDf (df : DataFrame) : IO Unit := IO.println df.toStr

instance : Coe (Array String) (Option (List String)) where
  coe a := some a.toList

instance : Coe (List String) (Option (List String)) where
  coe l := some l

end DataFrame
end Libraries.pandas
