import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

-- Closed-form accumulator: total = 0+1+...+n = n(n+1)/2.
-- Index-style invariant (references the loop counter), so it exercises element=index + division.
def sum_to_n := fun (n : Int) ↦
  (do
    let mut total : Int := (0 : Int)
    for i in (PastaLean.pyRange (n +ₚ (1 : Int))) do
      let _ := Libraries.passta.pyPassInvariant ((2 : Int) *ₚ total == i *ₚ (i -ₚ (1 : Int)))
      total := total +ₚ i
    let _ := Libraries.passta.pyPassEnsures ((2 : Int) *ₚ total == n *ₚ (n +ₚ (1 : Int)))
    return total : Id _)

theorem sum_to_n_spec : ⦃⌜n ≥ (0 : Int)⌝⦄ sum_to_n n ⦃⇓_ => ⌜True⌝⦄ :=
  by
  mvcgen [sum_to_n, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
  · ⇓⟨cur, total⟩ =>
    ⌜let i := (cur.prefix.length : Int);
      (2 : Int) *ₚ total = i *ₚ (i -ₚ (1 : Int))⌝
  simp_all (config := { zetaDelta := true }) [taste_ingr]; grind +locals +suggestions

def sum_to_n'rn := fun (n : Int) ↦
  Id.run
    (do
      let _ := Libraries.passta.pyPassRequires (decide (n ≥ (0 : Int)))
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int))) do
        let _ := Libraries.passta.pyPassInvariant ((2 : Int) *ₚ total == i *ₚ (i -ₚ (1 : Int)))
        total := total +ₚ i
      let _ := Libraries.passta.pyPassEnsures ((2 : Int) *ₚ total == n *ₚ (n +ₚ (1 : Int)))
      return total)