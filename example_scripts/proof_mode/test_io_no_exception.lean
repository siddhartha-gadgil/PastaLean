import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Test: IO without explicit exception handling
def main' :=
  ((do
      let mut x : String := (← PastaLean.ProofMode.pyInputProof "")
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg x]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let mut x : String := (← PastaLean.pyInputIO "")
      let _ ← pyPrintIO [pyPrintArg x]) :
    IO _)

end PastaLean.User.Root
