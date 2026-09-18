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

-- Early-return linear search (mirrors early_return_break.lean): return the first index whose value
-- equals k, or -1. The loop invariant is "k absent from the prefix scanned so far".
def find_first := fun (xs : List Int) ↦ fun (k : Int) ↦
  (do
    for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen xs))do
      let _ := Libraries.passta.pyPassInvariant !(PastaLean.pyContains (PastaLean.pySlice xs none (some i) none) k)
      if h_1 : PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i) = k then 
        return i
    let p'_ret_1 := -(1 : Int)
    return p'_ret_1 : Id _)

theorem find_first_spec : ⦃⌜True⌝⦄ find_first xs k ⦃⇓_ => ⌜True⌝⦄ :=
  by
  try (apply Std.Do.Triple.of_entails_wp; intro _; exact True.intro)
  all_goals sorry

def find_first'rn := fun (xs : List Int) ↦ fun (k : Int) ↦
  Id.run
    (do
      for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        let _ := Libraries.passta.pyPassInvariant !(PastaLean.pyContains (PastaLean.pySlice xs none (some i) none) k)
        if h_1 : PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i) == k then 
          return i
      let p'_ret_1 := -(1 : Int)
      return p'_ret_1)

end PastaLean.User.Root
