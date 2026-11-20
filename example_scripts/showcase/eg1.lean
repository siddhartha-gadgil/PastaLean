import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

noncomputable def euclidean_distance := fun (p1 : List Int) ↦ fun (p2 : List Int) ↦
  ((do
      if h_1 : PastaLean.pyLen p1 ≠ PastaLean.pyLen p2 then 
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString "Points must have the same number of dimensions"))
      -- Using zip, list comprehension, and math.pow
      let mut sq_diffs :=
        (PastaLean.pyIter (PastaLean.pyZip p1 p2)).map fun (p'_pair_1 : Int × Int) =>
          let a := Prod.fst p'_pair_1;
          let b := Prod.snd p'_pair_1;
          Libraries.math.pyMathPowExact (a -ₚ b) (2 : Int)
      let p'_ret_1 := Libraries.math.pyMathSqrtR (PastaLean.pySum sq_diffs)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] euclidean_distance

def euclidean_distance'rn : List Int → List Int → PastaLean.PyExcept Float := fun (p1 : List Int) ↦
  fun (p2 : List Int) ↦ do
  if h_1 : PastaLean.pyLen p1 != PastaLean.pyLen p2 then 
    throw
        (PastaLean.PyException.Raise "ValueError" (ToString.toString "Points must have the same number of dimensions"))
  -- Using zip, list comprehension, and math.pow
  let mut sq_diffs :=
    ((PastaLean.pyIter (PastaLean.pyZip p1 p2)).map fun (p'_pair_1 : Int × Int) =>
        let a := Prod.fst p'_pair_1;
        let b := Prod.snd p'_pair_1;
        Libraries.math.pyMathPow (a -ₚ b) (2 : Int)) |>.toArray
  let p'_ret_1 := Libraries.math.pyMathSqrt (PastaLean.pySum sq_diffs)
  return p'_ret_1

noncomputable def find_nearest_neighbor := fun (target : List Int) ↦ fun (dataset : List (List Int)) ↦
  ((do
      try
        -- Calculate distances using list comprehension
        let mut distances :=
          (← (PastaLean.pyIter dataset).mapM fun (point : List Int) => euclidean_distance target point)
        -- Find the minimum distance
        let mut min_dist := PastaLean.pyMin distances
        -- Find the index of the minimum distance
        -- Using a loop since index() might not be supported based on tests
        let mut min_index : Int := -(1 : Int)
        for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate distances))do
          let i := Prod.fst p'_pair_1
          let d := Prod.snd p'_pair_1
          if h_1 : d = min_dist then 
            min_index := i
            break
        let p'_ret_1 := (min_dist, dataset⦋min_index⦌)
        return p'_ret_1
      catch caught =>
        if PastaLean.pyExcIsA caught "ValueError" then 
          let e := caught
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Error calculating distances: {e}"]
          let p'_ret_2 := (-(1.0 : Real), [])
          return p'_ret_2
        else
          throw caught) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] find_nearest_neighbor

def find_nearest_neighbor'rn : List Int → List (List Int) → PastaLean.PyExcept (Float × List Int) :=
  fun (target : List Int) ↦ fun (dataset : List (List Int)) ↦ do
  try
    -- Calculate distances using list comprehension
    let mut distances :=
      (← (PastaLean.pyIter dataset).mapM fun (point : List Int) => euclidean_distance'rn target point)
    -- Find the minimum distance
    let mut min_dist := PastaLean.pyMin distances
    -- Find the index of the minimum distance
    -- Using a loop since index() might not be supported based on tests
    let mut min_index : Int := -(1 : Int)
    for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate distances))do
      let i := Prod.fst p'_pair_1
      let d := Prod.snd p'_pair_1
      if h_1 : d == min_dist then 
        min_index := i
        break
    let p'_ret_1 := (min_dist, dataset⦋min_index⦌)
    return p'_ret_1
  catch caught =>
    if PastaLean.pyExcIsA caught "ValueError" then 
      let e := caught
      let _ ← pyPrintIO [pyPrintArg s! "Error calculating distances: {e}"]
      let p'_ret_2 := (-(1.0 : Float), [])
      return p'_ret_2
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
      let p'_unpack_value_1 ← find_nearest_neighbor target_point dataset
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut dist : Real := ↑(Prod.fst p'_unpack_pair_1)
      let mut nearest : List Int := Prod.snd p'_unpack_pair_1
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Nearest Neighbor to Target:"]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Point:", pyPrintArg nearest]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Distance:", pyPrintArg dist]
      -- Invalid Case
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "\nTesting Invalid Point:"]
      let p'_unpack_value_2 ← find_nearest_neighbor invalid_point dataset
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut dist_inv : Real := ↑(Prod.fst p'_unpack_pair_2)
      let mut nearest_inv : List Int := Prod.snd p'_unpack_pair_2
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
      let p'_unpack_value_1 ← find_nearest_neighbor'rn target_point dataset
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut dist : Float := ↑(Prod.fst p'_unpack_pair_1)
      let mut nearest : List Int := Prod.snd p'_unpack_pair_1
      let _ ← pyPrintIO [pyPrintArg "Nearest Neighbor to Target:"]
      let _ ← pyPrintIO [pyPrintArg "Point:", pyPrintArg nearest]
      let _ ← pyPrintIO [pyPrintArg "Distance:", pyPrintArg dist]
      -- Invalid Case
      let _ ← pyPrintIO [pyPrintArg "\nTesting Invalid Point:"]
      let p'_unpack_value_2 ← find_nearest_neighbor'rn invalid_point dataset
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut dist_inv : Float := ↑(Prod.fst p'_unpack_pair_2)
      let mut nearest_inv : List Int := Prod.snd p'_unpack_pair_2
      let _ ← pyPrintIO [pyPrintArg "Fallback Distance:", pyPrintArg dist_inv]) :
    PastaLean.PyExcept _)

noncomputable def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputStream : PastaLean.ProofMode.IOStream := PastaLean.ProofMode.IOStream.ofText inputText
  let initState : PastaLean.ProofMode.IOState := { input := inputStream, output := [] }
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

end PastaLean.User.Root
