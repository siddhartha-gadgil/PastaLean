import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

-- Test: IO exception handling (EOFError from input)
def main' :=
  ((do
      let mut x : String := default
      try
        x := (← (PastaLean.ProofMode.pyInputProof ""))
      catch caught =>
        if (caught).OfKind == "EOFError" then 
          x := "default"
        else
          throw caught
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg x]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let mut x : String := default
      try
        x := (← PastaLean.PyExcept.captureIOErrors (PastaLean.pyInputIO ""))
      catch caught =>
        if (caught).OfKind == "EOFError" then 
          x := "default"
        else
          throw caught
      let _ ← pyPrintIO [pyPrintArg x]) :
    PastaLean.PyExcept _)