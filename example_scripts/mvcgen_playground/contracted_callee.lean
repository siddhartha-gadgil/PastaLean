import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

namespace PastaLean.User.Root

-- A pure caller of a contracted (`Id`-typed) function: the call must read its value, not the action.
def classify := fun (a : Int) ↦ fun (b : Int) ↦
  (do
    if h_1 : a > (1000 : Int) then 
      if h_2 : b = (3 : Int) then 
        let p'_ret_1 := -(1 : Int)
        return p'_ret_1
    return (1 : Int) : Id _)

@[spec]
theorem classify_spec : ⦃⌜True⌝⦄ classify a b ⦃⇓result => ⌜result ≥ (0 : Int)⌝⦄ :=
  by
  mvcgen [classify, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start]
  simp_all (config := { zetaDelta := true }) [taste_ingr]; sorry
  all_goals sorry

theorem classify_correct :
    ∀ (a : Int),
      ∀ (b : Int),
        let result := (classify a b).run;
        result ≥ (0 : Int) :=
  by
  intro a b
  exact classify_spec True.intro

def classify'rn := fun (a : Int) ↦ fun (b : Int) ↦
  Id.run
    (do
      if h_1 : a > (1000 : Int) then 
        if h_2 : b == (3 : Int) then 
          let p'_ret_1 := -(1 : Int)
          return p'_ret_1
      return (1 : Int))

def is_nonneg := fun (a : Int) ↦ fun (b : Int) ↦
  let r := (PastaLean.runPure (classify a b) : Int)
  decide (r ≥ (0 : Int))

attribute [simp, taste_ingr] is_nonneg

def is_nonneg'rn := fun (a : Int) ↦ fun (b : Int) ↦
  let r := (classify'rn a b : Int)
  decide (r ≥ (0 : Int))

def shifted := fun (a : Int) ↦ fun (b : Int) ↦ PastaLean.runPure (classify a b) +ₚ (1 : Int)

attribute [simp, taste_ingr] shifted

def shifted'rn := fun (a : Int) ↦ fun (b : Int) ↦ classify'rn a b +ₚ (1 : Int)

end PastaLean.User.Root
