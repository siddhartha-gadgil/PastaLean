import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 800000

namespace PastaLean.User.Root

-- Running maximum over a non-empty list. Monotone invariant: the running max never drops below
-- the first element. (A full "m ≥ every seen element" invariant is the harder follow-up.)
def running_max := fun (xs : List Int) ↦
  (do
    let mut m : Int := xs⦋(0 : Int)⦌
    for x in (PastaLean.pyIter xs) do
      let _ := Libraries.passta.pyPassInvariant (decide (m ≥ xs⦋(0 : Int)⦌))
      if h_1 : x > m then 
        m := x
    return m : Id _)

@[spec]
theorem running_max_spec : ⦃⌜PastaLean.pyLen xs > (0 : Int)⌝⦄ running_max xs ⦃⇓m => ⌜m ≥ xs⦋(0 : Int)⦌⌝⦄ :=
  by
  try
    mvcgen [running_max, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
    · ⇓⟨cur, m⟩ => ⌜m ≥ xs⦋(0 : Int)⦌⌝
  simp_all (config := { zetaDelta := true }) [taste_ingr]; omega
  all_goals sorry

theorem running_max_correct :
    ∀ (xs : List Int),
      PastaLean.pyLen xs > (0 : Int) →
        let m := (running_max xs).run;
        m ≥ xs⦋(0 : Int)⦌ :=
  by
  intro xs hpre
  exact running_max_spec hpre

def running_max'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let _ := Libraries.passta.pyPassRequires (decide (PastaLean.pyLen xs > (0 : Int)))
      let mut m : Int := xs⦋(0 : Int)⦌
      for x in (PastaLean.pyIter xs) do
        let _ := Libraries.passta.pyPassInvariant (decide (m ≥ xs⦋(0 : Int)⦌))
        if h_1 : x > m then 
          m := x
      return m)

end PastaLean.User.Root
