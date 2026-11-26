import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Test: Pure exception handling (no IO)
def divide := fun a ↦ fun b ↦
  ((do
      try
        let p'_ret_1 := a /ₚ b
        return p'_ret_1
      catch caught =>
        if Bool.true then 
          return (0 : Int)
        else
          throw caught) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] divide

def divide'rn := fun a ↦ fun b ↦
  ((do
      try
        let p'_ret_1 := PastaLean.pyTrueDiv a b
        return p'_ret_1
      catch caught =>
        if Bool.true then 
          return (0 : Int)
        else
          throw caught) :
    PastaLean.PyExcept _)

end PastaLean.User.Root
