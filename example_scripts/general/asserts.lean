import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 800000

namespace PastaLean.User.Root

-- Assert statements: inline (inside a function) and top-level (outside any function).
def GREETING :=
  "hi"

-- top-level assert — outside any function
@[taste_ingr]
theorem assert_stmt_1 : PastaLean.pyLen GREETING = (2 : Int) := by decide

def checked_add := fun (a : Int) ↦ fun (b : Int) ↦
  -- inline asserts inside a function body
  have ht_1 : a = a := by simp_all (config := { zetaDelta := true }) [taste_ingr]
  have ht_2 : a +ₚ b ≥ a +ₚ b := by simp_all (config := { zetaDelta := true }) [taste_ingr]
  a +ₚ b

attribute [simp] checked_add

def checked_add'rn := fun (a : Int) ↦ fun (b : Int) ↦
  -- inline asserts inside a function body
  a +ₚ b

end PastaLean.User.Root
