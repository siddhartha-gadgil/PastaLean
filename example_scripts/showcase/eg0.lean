import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

partial def fibonacci : Int → Int := fun (n : Int) ↦
  if n ≤ (0 : Int) then (0 : Int)
  else if n = (1 : Int) then (1 : Int) else fibonacci (n -ₚ (1 : Int)) +ₚ fibonacci (n -ₚ (2 : Int))

partial def fibonacci'rn : Int → Int := fun (n : Int) ↦
  if n ≤ (0 : Int) then (0 : Int)
  else if n == (1 : Int) then (1 : Int) else fibonacci'rn (n -ₚ (1 : Int)) +ₚ fibonacci'rn (n -ₚ (2 : Int))

def funnyfoo := fun (x : Int) ↦ (x *ₚ x +ₚ x) ^ₚ x

attribute [simp, taste_ingr] funnyfoo

def funnyfoo'rn := fun (x : Int) ↦ (x *ₚ x +ₚ x) ^ₚ x

end PastaLean.User.Root
