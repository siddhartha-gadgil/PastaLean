import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

noncomputable def euclidean_distance := fun (p1 : List Int) ↦ fun (p2 : List Int) ↦
  ((do
      if h_1 : PastaLean.pyLen p1 ≠ PastaLean.pyLen p2 then 
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString "Points must have the same number of dimensions"))
      else
        let _ := ()
      -- Using zip, list comprehension, and math.pow
      let mut sq_diffs :=
        (PastaLean.pyIter (PastaLean.pyZip p1 p2)).map fun _pair_1 =>
          let a := Prod.fst _pair_1;
          let b := Prod.snd _pair_1;
          Libraries.math.pyMathPowExact (a -ₚ b) (2 : Int)
      let __py_ret_1 := Libraries.math.pyMathSqrtR (PastaLean.pySum sq_diffs)
      return __py_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] euclidean_distance

def euclidean_distance'rn : List Int → List Int → PastaLean.PyExcept Float := fun (p1 : List Int) ↦
  fun (p2 : List Int) ↦ do
  if h_1 : PastaLean.pyLen p1 != PastaLean.pyLen p2 then 
    throw
        (PastaLean.PyException.Raise "ValueError" (ToString.toString "Points must have the same number of dimensions"))
  else
    let _ := ()
  -- Using zip, list comprehension, and math.pow
  let mut sq_diffs :=
    (PastaLean.pyIter (PastaLean.pyZip p1 p2)).map fun _pair_1 =>
      let a := Prod.fst _pair_1;
      let b := Prod.snd _pair_1;
      Libraries.math.pyMathPow (a -ₚ b) (2 : Int)
  let __py_ret_1 := Libraries.math.pyMathSqrt (PastaLean.pySum sq_diffs)
  return __py_ret_1

noncomputable def find_nearest_neighbor := fun (target : List Int) ↦ fun (dataset : List (List Int)) ↦
  ((do
      try
        -- Calculate distances using list comprehension
        let mut distances := (← (PastaLean.pyIter dataset).mapM fun point => euclidean_distance target point)
        -- Find the minimum distance
        let mut min_dist := PastaLean.pyMin distances
        -- Find the index of the minimum distance
        -- Using a loop since index() might not be supported based on tests
        let mut min_index : Int := -(1 : Int)
        for _pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate distances)) do
          let i := Prod.fst _pair_1
          let d := Prod.snd _pair_1
          if h_1 : d = min_dist then 
            min_index := i
            break
          else
            let _ := ()
        let __py_ret_1 := (min_dist, dataset⦋min_index⦌)
        return __py_ret_1
      catch caught =>
        if (caught).OfKind == "ValueError" then 
          let e := caught
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Error calculating distances: {e}"]
          let __py_ret_2 := (-(1.0 : Real), [])
          return __py_ret_2
        else
          throw caught) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] find_nearest_neighbor

def find_nearest_neighbor'rn : List Int → List (List Int) → PastaLean.PyExcept (Float × List Int) :=
  fun (target : List Int) ↦ fun (dataset : List (List Int)) ↦ do
  try
    -- Calculate distances using list comprehension
    let mut distances := (← (PastaLean.pyIter dataset).mapM fun point => euclidean_distance'rn target point)
    -- Find the minimum distance
    let mut min_dist := PastaLean.pyMin distances
    -- Find the index of the minimum distance
    -- Using a loop since index() might not be supported based on tests
    let mut min_index : Int := -(1 : Int)
    for _pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate distances)) do
      let i := Prod.fst _pair_1
      let d := Prod.snd _pair_1
      if h_1 : d == min_dist then 
        min_index := i
        break
      else
        let _ := ()
    let __py_ret_1 := (min_dist, dataset⦋min_index⦌)
    return __py_ret_1
  catch caught =>
    if (caught).OfKind == "ValueError" then 
      let e := caught
      let _ ← pyPrintIO [pyPrintArg s! "Error calculating distances: {e}"]
      let __py_ret_2 := (-(1.0 : Float), [])
      return __py_ret_2
    else
      throw caught

noncomputable def run_example :=
  ((do
      let mut dataset : List (List Int) :=
        [[(1 : Int), (2 : Int), (3 : Int)], [(4 : Int), (5 : Int), (6 : Int)], [(7 : Int), (8 : Int), (9 : Int)],
          [(2 : Int), (1 : Int), (4 : Int)]]
      let mut target_point : List Int := [(2 : Int), (3 : Int), (4 : Int)]
      let mut invalid_point : List Int := [(1 : Int), (2 : Int)]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Dataset:", pyPrintArg dataset]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Target Point:", pyPrintArg target_point]
      -- Valid Case
      let __unpack_value_1 ← find_nearest_neighbor target_point dataset
      let __unpack_pair_1 := __unpack_value_1
      let mut dist := Prod.fst __unpack_pair_1
      let mut nearest := Prod.snd __unpack_pair_1
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Nearest Neighbor to Target:"]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Point:", pyPrintArg nearest]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Distance:", pyPrintArg dist]
      -- Invalid Case
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "\nTesting Invalid Point:"]
      let __unpack_value_2 ← find_nearest_neighbor invalid_point dataset
      let __unpack_pair_2 := __unpack_value_2
      let mut dist_inv := Prod.fst __unpack_pair_2
      let mut nearest_inv := Prod.snd __unpack_pair_2
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Fallback Distance:", pyPrintArg dist_inv]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] run_example

def run_example'rn :=
  ((do
      let mut dataset : List (List Int) :=
        [[(1 : Int), (2 : Int), (3 : Int)], [(4 : Int), (5 : Int), (6 : Int)], [(7 : Int), (8 : Int), (9 : Int)],
          [(2 : Int), (1 : Int), (4 : Int)]]
      let mut target_point : List Int := [(2 : Int), (3 : Int), (4 : Int)]
      let mut invalid_point : List Int := [(1 : Int), (2 : Int)]
      let _ ← pyPrintIO [pyPrintArg "Dataset:", pyPrintArg dataset]
      let _ ← pyPrintIO [pyPrintArg "Target Point:", pyPrintArg target_point]
      -- Valid Case
      let __unpack_value_1 ← find_nearest_neighbor'rn target_point dataset
      let __unpack_pair_1 := __unpack_value_1
      let mut dist := Prod.fst __unpack_pair_1
      let mut nearest := Prod.snd __unpack_pair_1
      let _ ← pyPrintIO [pyPrintArg "Nearest Neighbor to Target:"]
      let _ ← pyPrintIO [pyPrintArg "Point:", pyPrintArg nearest]
      let _ ← pyPrintIO [pyPrintArg "Distance:", pyPrintArg dist]
      -- Invalid Case
      let _ ← pyPrintIO [pyPrintArg "\nTesting Invalid Point:"]
      let __unpack_value_2 ← find_nearest_neighbor'rn invalid_point dataset
      let __unpack_pair_2 := __unpack_value_2
      let mut dist_inv := Prod.fst __unpack_pair_2
      let mut nearest_inv := Prod.snd __unpack_pair_2
      let _ ← pyPrintIO [pyPrintArg "Fallback Distance:", pyPrintArg dist_inv]) :
    PastaLean.PyExcept _)

noncomputable def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputLines := String.splitOn inputText "\n"
  let inputStream : PastaLean.ProofMode.IOStream :=
    ⟨0, fun i => PastaLean.ProofMode.IOResult.success (List.getD inputLines i "")⟩
  let initState : PastaLean.ProofMode.IOState := ⟨inputStream, []⟩
  let (result, finalState) :=
    (((do
          let _ ← run_example
          pure ()) :
        PastaLean.ProofMode.PyProofM Unit))
      initState
  let outputLines := finalState.output
  for line in outputLines do
    IO.print line
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

def main'rn : IO Unit := do
  let result ←
    (((do
            let _ ← run_example'rn
            pure ()) :
          PastaLean.PyExcept Unit)).run
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))