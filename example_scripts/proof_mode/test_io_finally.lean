import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

-- Test: Try-finally with IO
def main' :=
  ((do
      try
        let mut x : String := (← (PastaLean.ProofMode.pyInputProof ""))
      catch caught =>
        throw caught
      finally
        do
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "cleanup"]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      try
        let mut x : String := (← PastaLean.PyExcept.captureIOErrors (PastaLean.pyInputIO ""))
      catch caught =>
        throw caught
      finally
        do
          let _ ← pyPrintIO [pyPrintArg "cleanup"]) :
    PastaLean.PyExcept _)