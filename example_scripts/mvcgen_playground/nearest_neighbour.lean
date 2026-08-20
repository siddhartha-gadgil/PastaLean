import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

noncomputable def euclidean_distance := fun (p1 : List Int) ↦ fun (p2 : List Int) ↦
  (do
    if h_1 : PastaLean.pyLen p1 ≠ PastaLean.pyLen p2 then 
      throw
          (PastaLean.PyException.Raise "ValueError"
            (ToString.toString "Points must have the same number of dimensions"))
    else
      let _ := ()
    let _ := Libraries.passta.pyPassAssert (PastaLean.pyLen p1 == PastaLean.pyLen p2)
    let mut sq_diffs :=
      (PastaLean.pyIter (PastaLean.pyZip p1 p2)).map fun _pair_1 =>
        let a := Prod.fst _pair_1;
        let b := Prod.snd _pair_1;
        Libraries.math.pyMathPowExact (a -ₚ b) (2 : Int)
    let __py_ret_1 := Libraries.math.pyMathSqrtR (PastaLean.pySum sq_diffs)
    return __py_ret_1 : ExceptT PastaLean.PyException Id _)

theorem euclidean_distance_spec :
    ⦃⌜PastaLean.pyLen p1 = PastaLean.pyLen p2⌝⦄ euclidean_distance p1 p2 ⦃⇓_ => ⌜True⌝⦄ :=
  by
  mvcgen [euclidean_distance, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start]

def euclidean_distance'rn : List Int → List Int → PastaLean.PyExcept Float := fun (p1 : List Int) ↦
  fun (p2 : List Int) ↦ do
  -- Precondition: the two points live in the same number of dimensions.
  let _ := Libraries.passta.pyPassRequires (PastaLean.pyLen p1 == PastaLean.pyLen p2)
  if h_1 : PastaLean.pyLen p1 != PastaLean.pyLen p2 then 
    throw
        (PastaLean.PyException.Raise "ValueError" (ToString.toString "Points must have the same number of dimensions"))
  else
    let _ := ()
  -- Past the guard the dimensions must match (provable from the precondition).
  let _ := Libraries.passta.pyPassAssert (PastaLean.pyLen p1 == PastaLean.pyLen p2)
  -- Using zip, a list comprehension, and math.pow
  let mut sq_diffs :=
    (PastaLean.pyIter (PastaLean.pyZip p1 p2)).map fun _pair_1 =>
      let a := Prod.fst _pair_1;
      let b := Prod.snd _pair_1;
      Libraries.math.pyMathPow (a -ₚ b) (2 : Int)
  let __py_ret_1 := Libraries.math.pyMathSqrt (PastaLean.pySum sq_diffs)
  return __py_ret_1

noncomputable def find_nearest_neighbor := fun (target : List Int) ↦ fun (dataset : List (List Int)) ↦
  (do
    try
      -- Distances to every point via a list comprehension over a raising function
      let mut distances := (← (PastaLean.pyIter dataset).mapM fun point => euclidean_distance target point)
      let mut min_dist := PastaLean.pyMin distances
      -- The minimum is one of the computed distances.
      let _ := Libraries.passta.pyPassAssert (PastaLean.pyContains distances min_dist)
      -- Find the index of the minimum distance with an explicit loop + break
      let mut min_index : Int := -(1 : Int)
      for _pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate distances)) do
        let i := Prod.fst _pair_1
        let d := Prod.snd _pair_1
        -- The index stays within bounds for the whole scan.
        let _ := Libraries.passta.pyPassInvariant (decide (min_index < PastaLean.pyLen distances))
        if h_1 : d = min_dist then 
          min_index := i
          break
        else
          let _ := ()
      let __py_ret_1 := (min_dist, dataset⦋min_index⦌)
      return __py_ret_1
    catch caught =>
      if (caught).OfKind == "ValueError" then 
        -- Fallback when a point has the wrong number of dimensions
        let __py_ret_2 := (-(1.0 : Real), [])
        return __py_ret_2
      else
        throw caught :
    ExceptT PastaLean.PyException Id _)

theorem find_nearest_neighbor_spec :
    ⦃⌜PastaLean.pyLen dataset > (0 : Int)⌝⦄ find_nearest_neighbor target dataset ⦃⇓_ => ⌜True⌝⦄ :=
  by
  mvcgen [find_nearest_neighbor, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start]
  simp_all (config := { zetaDelta := true }) [taste_ingr]; sorry

def find_nearest_neighbor'rn : List Int → List (List Int) → PastaLean.PyExcept (Float × List Int) :=
  fun (target : List Int) ↦ fun (dataset : List (List Int)) ↦ do
  -- Precondition: there is at least one candidate point to compare against.
  let _ := Libraries.passta.pyPassRequires (decide (PastaLean.pyLen dataset > (0 : Int)))
  try
    -- Distances to every point via a list comprehension over a raising function
    let mut distances := (← (PastaLean.pyIter dataset).mapM fun point => euclidean_distance'rn target point)
    let mut min_dist := PastaLean.pyMin distances
    -- The minimum is one of the computed distances.
    let _ := Libraries.passta.pyPassAssert (PastaLean.pyContains distances min_dist)
    -- Find the index of the minimum distance with an explicit loop + break
    let mut min_index : Int := -(1 : Int)
    for _pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate distances)) do
      let i := Prod.fst _pair_1
      let d := Prod.snd _pair_1
      -- The index stays within bounds for the whole scan.
      let _ := Libraries.passta.pyPassInvariant (decide (min_index < PastaLean.pyLen distances))
      if h_1 : d == min_dist then 
        min_index := i
        break
      else
        let _ := ()
    let __py_ret_1 := (min_dist, dataset⦋min_index⦌)
    return __py_ret_1
  catch caught =>
    if (caught).OfKind == "ValueError" then 
      -- Fallback when a point has the wrong number of dimensions
      let __py_ret_2 := (-(1.0 : Float), [])
      return __py_ret_2
    else
      throw caught