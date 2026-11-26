import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def read_int_list : PastaLean.ProofMode.PyProofM (List Int) := do
  let mut xs : List Int :=
    PastaLean.pyList (PastaLean.pyMap PastaLean.pyInt (PastaLean.pyStringSplit (← PastaLean.ProofMode.pyInputProof "")))
  return xs

attribute [simp] read_int_list

def read_int_list'rn : IO (List Int) := do
  let mut xs : List Int :=
    PastaLean.pyList (PastaLean.pyMap PastaLean.pyInt (PastaLean.pyStringSplit (← PastaLean.pyInputIO "")))
  return xs

end PastaLean.User.Root
