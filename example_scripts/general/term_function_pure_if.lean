import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def choose := fun (x : Int) ↦ if x > (0 : Int) then (1 : Int) else (2 : Int)

attribute [simp, taste_ingr] choose

def choose'rn := fun (x : Int) ↦ if x > (0 : Int) then (1 : Int) else (2 : Int)

end PastaLean.User.Root
