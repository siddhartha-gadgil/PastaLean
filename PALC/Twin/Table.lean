import PastaLean.PyVerify.Twin

/-! The substitution table (`#twin_table`) and `twin_table`: a pair proved from the table's rows, and
a callee split off as its own goal. -/

open PastaLean

namespace PastaLean.TwinTest

-- The substitution table: every `prim` row is a proved refinement (a warning otherwise).
#twin_table

-- `twin_table` reduces a twin goal to the table: an `Array`-state loop closes from the `prim` rows.
def addAll (xs : List Int) (ys : List Int) : List Int := Id.run do
  let mut acc := xs
  for y in ys do acc := pyAppend acc y
  return acc
def addAll'rn (xs : Array Int) (ys : List Int) : Array Int := Id.run do
  let mut acc := xs
  for y in ys do acc := pyArrayAppend acc y
  return acc
theorem addAll_twin : twin% addAll := by twin_table

-- A callee whose twins differ is split off as a goal (`callee.g`), discharged separately.
def g (x : Int) : Int := x + 1
def g'rn (x : Int) : Int := 1 + x
def h (x : Int) : Int := g x * 2
def h'rn (x : Int) : Int := g'rn x * 2
theorem h_twin : twin% h := by
  twin_table
  case callee.g => intro x; simp only [g, g'rn]; omega

end PastaLean.TwinTest
