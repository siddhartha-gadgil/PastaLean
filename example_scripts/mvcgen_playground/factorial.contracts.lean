import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 800000

namespace PastaLean.User.Root

def factorial := fun (n : Int) ↦
  (do
    let mut result : Int := (1 : Int)
    let mut i : Int := (1 : Int)
    while (i ≤ n) do
      let _ := Libraries.passta.pyPassInvariant (decide ((1 : Int) ≤ i))
      let _ := Libraries.passta.pyPassInvariant (decide (i ≤ n +ₚ (1 : Int)))
      let _ := Libraries.passta.pyPassInvariant (decide (result ≥ (1 : Int)))
      let _ := Libraries.passta.pyPassDecreases (n +ₚ (1 : Int) -ₚ i)
      result := result *ₚ i
      i := i +ₚ (1 : Int)
    return result : Id _)

@[spec]
theorem factorial_spec : ⦃⌜n ≥ (0 : Int)⌝⦄ factorial n ⦃⇓result => ⌜result ≥ (1 : Int)⌝⦄ :=
  by
  try
    mvcgen [factorial, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
    · fun s =>
      let i := s |>.snd;
      let result := s |>.fst;
      (⟨(n +ₚ (1 : Int) -ₚ i).toNat⟩ : ULift Nat)
    · ⇓s =>
      ⌜Sum.elim
          (fun st =>
            let i := st |>.snd;
            let result := st |>.fst;
            ((1 : Int) ≤ i ∧ i ≤ n +ₚ (1 : Int)) ∧ result ≥ (1 : Int))
          (fun _ => True) s⌝
  simp_all (config := { zetaDelta := true }) [taste_ingr]; sorry; simp_all (config := { zetaDelta := true }) [taste_ingr]; sorry
  all_goals sorry

theorem factorial_correct :
    ∀ (n : Int),
      n ≥ (0 : Int) →
        let result := (factorial n).run;
        result ≥ (1 : Int) :=
  by
  intro n hpre
  exact factorial_spec hpre

def factorial'rn := fun (n : Int) ↦
  Id.run
    (do
      let _ := Libraries.passta.pyPassRequires (decide (n ≥ (0 : Int)))
      let mut result : Int := (1 : Int)
      let mut i : Int := (1 : Int)
      while (i ≤ n) do
        let _ := Libraries.passta.pyPassInvariant (decide ((1 : Int) ≤ i))
        let _ := Libraries.passta.pyPassInvariant (decide (i ≤ n +ₚ (1 : Int)))
        let _ := Libraries.passta.pyPassInvariant (decide (result ≥ (1 : Int)))
        let _ := Libraries.passta.pyPassDecreases (n +ₚ (1 : Int) -ₚ i)
        result := result *ₚ i
        i := i +ₚ (1 : Int)
      return result)

end PastaLean.User.Root
