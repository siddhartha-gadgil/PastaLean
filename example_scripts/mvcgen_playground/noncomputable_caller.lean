import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 800000

namespace PastaLean.User.Root

private noncomputable def _sqrt_floor_plus_one'approx_sqrt := fun (a : Int) ↦ PastaLean.pyInt (a ^ₚ (0.5 : Rat))

attribute [simp] _sqrt_floor_plus_one'approx_sqrt

noncomputable def sqrt_floor_plus_one := fun (n : Int) ↦ _sqrt_floor_plus_one'approx_sqrt n +ₚ (1 : Int)

attribute [simp] sqrt_floor_plus_one

@[taste_ingr]
theorem sqrt_floor_plus_one_correct : ∀ (n : Int), sqrt_floor_plus_one n ≥ (1 : Int) := by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; sorry

private def _sqrt_floor_plus_one'approx_sqrt'rn := fun (a : Int) ↦ PastaLean.pyInt (a ^ₚ (0.5 : Float))

def sqrt_floor_plus_one'rn := fun (n : Int) ↦ _sqrt_floor_plus_one'approx_sqrt'rn n +ₚ (1 : Int)

end PastaLean.User.Root
