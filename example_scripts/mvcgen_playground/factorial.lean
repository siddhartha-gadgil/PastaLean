import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- While-loop product accumulator with an explicit termination measure (Decreases).
-- Maintainable invariant: the running product stays >= 1 (so it is never zero / negative).
def factorial := fun (n : Int) ↦
  Id.run
    (do
      let mut result : Int := (1 : Int)
      let mut i : Int := (1 : Int)
      while (i ≤ n) do
        result := result *ₚ i
        i := i +ₚ (1 : Int)
      return result)

attribute [simp, taste_ingr] factorial

def factorial'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut result : Int := (1 : Int)
      let mut i : Int := (1 : Int)
      while (i ≤ n) do
        result := result *ₚ i
        i := i +ₚ (1 : Int)
      return result)

end PastaLean.User.Root
