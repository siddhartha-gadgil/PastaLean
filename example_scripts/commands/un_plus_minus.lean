import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def f := fun (n : Int) ↦ n -ₚ -n

attribute [simp, taste_ingr] f

def f'rn := fun (n : Int) ↦ n -ₚ -n

end PastaLean.User.Root
