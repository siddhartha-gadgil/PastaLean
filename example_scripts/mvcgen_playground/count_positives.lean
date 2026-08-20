import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

-- Conditional accumulator over a list: count strictly-positive entries.
-- Bounds invariant `0 <= cnt <= processed-so-far`; the count never exceeds the list length.
def count_positives := fun (xs : List Int) ↦
  (do
    let mut cnt : Int := (0 : Int)
    for x in (PastaLean.pyIter xs) do
      let _ := Libraries.passta.pyPassInvariant (decide (cnt ≥ (0 : Int)))
      if h_1 : x > (0 : Int) then 
        cnt := cnt +ₚ (1 : Int)
      else
        let _ := ()
    let _ := Libraries.passta.pyPassEnsures (decide (cnt ≥ (0 : Int)))
    let _ := Libraries.passta.pyPassEnsures (decide (cnt ≤ PastaLean.pyLen xs))
    return cnt : Id _)

theorem count_positives_spec : ⦃⌜True⌝⦄ count_positives xs ⦃⇓_ => ⌜True⌝⦄ :=
  by
  mvcgen [count_positives, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
  · ⇓⟨cur, cnt⟩ => ⌜cnt ≥ (0 : Int)⌝
  simp_all (config := { zetaDelta := true }) [taste_ingr]

def count_positives'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut cnt : Int := (0 : Int)
      for x in (PastaLean.pyIter xs) do
        let _ := Libraries.passta.pyPassInvariant (decide (cnt ≥ (0 : Int)))
        if h_1 : x > (0 : Int) then 
          cnt := cnt +ₚ (1 : Int)
        else
          let _ := ()
      let _ := Libraries.passta.pyPassEnsures (decide (cnt ≥ (0 : Int)))
      let _ := Libraries.passta.pyPassEnsures (decide (cnt ≤ PastaLean.pyLen xs))
      return cnt)