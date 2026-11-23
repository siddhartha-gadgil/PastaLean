import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def total_len := fun (lst : List String) ↦ PastaLean.pySum (PastaLean.pyMap PastaLean.pyLen lst)

attribute [simp, taste_ingr] total_len

def total_len'rn := fun (lst : List String) ↦ PastaLean.pySum (PastaLean.pyMap PastaLean.pyLen lst)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (total_len ["ab", "cde", "f"])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (total_len'rn ["ab", "cde", "f"])]) :
    IO _)

end PastaLean.User.Root
