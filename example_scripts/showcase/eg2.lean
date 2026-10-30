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

def process_data := fun (data : List (List Rat)) ↦ fun (weights : List (List Rat)) ↦
  ((do
      try
        -- Calculate mean of the dataset
        let mut m := Libraries.numpy.pyNumpyMean data
        let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Dataset Global Mean: {m}"]
        -- Center the data by subtracting the mean
        -- (Using a manual broadcast-like subtraction for this example)
        -- Note: np.subtract is mapped to pyNumpySubtract
        let mut centered := Libraries.numpy.pyNumpySubtract data [[m, m], [m, m]]
        -- Perform matrix multiplication
        -- Note: np.matmul is mapped to pyNumpyMatmul
        let mut result := Libraries.numpy.pyNumpyMatmul centered weights
        return result
      catch caught =>
        if (caught).OfKind == "ValueError" then 
          let e := caught
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Processing failed: {e}"]
          -- Fallback to a zero matrix if dimensions fail
          let p'_ret_1 := Libraries.numpy.pyNumpyZerosRat ((2 : Int), (2 : Int))
          return p'_ret_1
        else
          throw caught) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] process_data

def process_data'rn : List (List Float) → List (List Float) → PastaLean.PyExcept (List (List Float)) :=
  fun (data : List (List Float)) ↦ fun (weights : List (List Float)) ↦ do
  try
    -- Calculate mean of the dataset
    let mut m := Libraries.numpy.pyNumpyMean data
    let _ ← pyPrintIO [pyPrintArg s! "Dataset Global Mean: {m}"]
    -- Center the data by subtracting the mean
    -- (Using a manual broadcast-like subtraction for this example)
    -- Note: np.subtract is mapped to pyNumpySubtract
    let mut centered := Libraries.numpy.pyNumpySubtract data [[m, m], [m, m]]
    -- Perform matrix multiplication
    -- Note: np.matmul is mapped to pyNumpyMatmul
    let mut result := Libraries.numpy.pyNumpyMatmul centered weights
    return result
  catch caught =>
    if (caught).OfKind == "ValueError" then 
      let e := caught
      let _ ← pyPrintIO [pyPrintArg s! "Processing failed: {e}"]
      -- Fallback to a zero matrix if dimensions fail
      let p'_ret_1 := Libraries.numpy.pyNumpyZerosFloat ((2 : Int), (2 : Int))
      return p'_ret_1
    else
      throw caught

def run_example :=
  ((do
      -- Define a 2x2 dataset and a 2x2 weight matrix
      let mut dataset := ([[(1.0 : Rat), (2.0 : Rat)], [(3.0 : Rat), (4.0 : Rat)]] : List (List Rat))
      let mut weights := ([[(0.5 : Rat), (0.5 : Rat)], [(1.0 : Rat), (2.0 : Rat)]] : List (List Rat))
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "=== PastaLean NumPy Showcase ==="]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Input Data: {dataset}"]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Weight Matrix: {weights}"]
      -- 1. Main Processing Pipeline
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "\n[1] Running Data Pipeline:"]
      let mut output := (← process_data dataset weights)
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Final Result:\n{output}"]
      -- 2. Utility Operations
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "\n[2] Structural Operations:"]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg s! "Identity Matrix (2x2):\n{Libraries.numpy.pyNumpyEyeRat (2 : Int)}"]
      let _ ←
        PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Flattened Weights: {Libraries.numpy.pyNumpyFlatten weights}"]
      -- 3. Shape Info
      -- Note: np.shape returns (rows, cols)
      let p'_unpack_value_1 := Libraries.numpy.pyNumpyShape dataset
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut rows : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (0 : Int)
      let mut cols : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (1 : Int)
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Dataset Shape: {rows }x{cols}"]
      -- 4. Error Handling Simulation
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "\n[3] Exception Handling (Mismatched Dimensions):"]
      let mut invalid_data := ([[(1.0 : Rat), (2.0 : Rat), (3.0 : Rat)]] : List (List Rat))
      -- This should trigger the ValueError in np.matmul(1x3, 2x2)
      let _ ← process_data invalid_data weights) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] run_example

def run_example'rn :=
  ((do
      -- Define a 2x2 dataset and a 2x2 weight matrix
      let mut dataset := ([[(1.0 : Float), (2.0 : Float)], [(3.0 : Float), (4.0 : Float)]] : List (List Float))
      let mut weights := ([[(0.5 : Float), (0.5 : Float)], [(1.0 : Float), (2.0 : Float)]] : List (List Float))
      let _ ← pyPrintIO [pyPrintArg "=== PastaLean NumPy Showcase ==="]
      let _ ← pyPrintIO [pyPrintArg s! "Input Data: {dataset}"]
      let _ ← pyPrintIO [pyPrintArg s! "Weight Matrix: {weights}"]
      -- 1. Main Processing Pipeline
      let _ ← pyPrintIO [pyPrintArg "\n[1] Running Data Pipeline:"]
      let mut output := (← process_data'rn dataset weights)
      let _ ← pyPrintIO [pyPrintArg s! "Final Result:\n{output}"]
      -- 2. Utility Operations
      let _ ← pyPrintIO [pyPrintArg "\n[2] Structural Operations:"]
      let _ ← pyPrintIO [pyPrintArg s! "Identity Matrix (2x2):\n{Libraries.numpy.pyNumpyEyeFloat (2 : Int)}"]
      let _ ← pyPrintIO [pyPrintArg s! "Flattened Weights: {Libraries.numpy.pyNumpyFlatten weights}"]
      -- 3. Shape Info
      -- Note: np.shape returns (rows, cols)
      let p'_unpack_value_1 := Libraries.numpy.pyNumpyShape dataset
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut rows : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (0 : Int)
      let mut cols : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (1 : Int)
      let _ ← pyPrintIO [pyPrintArg s! "Dataset Shape: {rows }x{cols}"]
      -- 4. Error Handling Simulation
      let _ ← pyPrintIO [pyPrintArg "\n[3] Exception Handling (Mismatched Dimensions):"]
      let mut invalid_data := ([[(1.0 : Float), (2.0 : Float), (3.0 : Float)]] : List (List Float))
      -- This should trigger the ValueError in np.matmul(1x3, 2x2)
      let _ ← process_data'rn invalid_data weights) :
    PastaLean.PyExcept _)

def main : IO Unit := do
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
