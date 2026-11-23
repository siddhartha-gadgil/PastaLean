import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 800000

namespace PastaLean.User.Root

partial def countdown := fun (n : Int) ↦ if n ≤ (0 : Int) then (0 : Int) else countdown (n -ₚ (1 : Int))

@[taste_ingr]
theorem countdown_correct : ∀ (n : Int), countdown n = (0 : Int) := by intros; sorry

partial def countdown'rn := fun (n : Int) ↦ if n ≤ (0 : Int) then (0 : Int) else countdown'rn (n -ₚ (1 : Int))

end PastaLean.User.Root
