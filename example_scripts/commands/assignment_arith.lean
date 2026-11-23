import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def f := fun (n : Int) ↦
  let x := (n +ₚ (1 : Int) : Int)
  let y := (x *ₚ (2 : Int) : Int)
  let x := (y -ₚ (1 : Int) : Int)
  x +ₚ y

attribute [simp, taste_ingr] f

def f'rn := fun (n : Int) ↦
  let x := (n +ₚ (1 : Int) : Int)
  let y := (x *ₚ (2 : Int) : Int)
  let x := (y -ₚ (1 : Int) : Int)
  x +ₚ y

end PastaLean.User.Root
