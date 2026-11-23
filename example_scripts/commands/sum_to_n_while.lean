import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def sum_to_n := fun (n : Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      let mut i : Int := (1 : Int)
      while (i ≤ n) do
        total := total +ₚ i
        i := i +ₚ (1 : Int)
      return total)

attribute [simp, taste_ingr] sum_to_n

def sum_to_n'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      let mut i : Int := (1 : Int)
      while (i ≤ n) do
        total := total +ₚ i
        i := i +ₚ (1 : Int)
      return total)

end PastaLean.User.Root
