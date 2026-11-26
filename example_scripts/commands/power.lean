import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def exp := fun n ↦ n ^ₚ (4 : Int)

attribute [simp, taste_ingr] exp

def exp'rn := fun n ↦ n ^ₚ (4 : Int)

end PastaLean.User.Root
