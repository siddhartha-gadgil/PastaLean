import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def count_to := fun (n : Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      while (total < n) do
        total := total +ₚ (1 : Int)
      return total)

attribute [simp, taste_ingr] count_to

def count_to'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      while (total < n) do
        total := total +ₚ (1 : Int)
      return total)

end PastaLean.User.Root
