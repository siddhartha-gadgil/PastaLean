import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

-- Multi-loop pipeline with assert checkpoints between phases (mirrors pipeline.lean).
-- Accumulator-style invariants (acc = prefix sum, cnt = prefix length) — no closed form.
def pipeline := fun (xs : List Int) ↦
  (do
    let mut acc : Int := (0 : Int)
    for x in (PastaLean.pyIter xs) do
      acc := acc +ₚ x
    let _ := Libraries.passta.pyPassAssert (acc == PastaLean.pySum xs)
    acc := acc *ₚ (2 : Int)
    let mut cnt : Int := (0 : Int)
    for x in (PastaLean.pyIter xs) do
      cnt := cnt +ₚ (1 : Int)
    let _ := Libraries.passta.pyPassAssert (cnt == PastaLean.pyLen xs)
    let mut result : Int := acc +ₚ cnt
    let _ := Libraries.passta.pyPassEnsures (result == (2 : Int) *ₚ PastaLean.pySum xs +ₚ PastaLean.pyLen xs)
    return result : Id _)

theorem pipeline_spec : ⦃⌜True⌝⦄ pipeline xs ⦃⇓_ => ⌜True⌝⦄ :=
  by
  mvcgen [pipeline, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
  · ⇓⟨cur, acc⟩ => ⌜acc = (cur.prefix.map (fun x => x)).sum⌝
  · ⇓⟨cur, cnt⟩ => ⌜cnt = (cur.prefix.map (fun x => (1 : Int))).sum⌝
  simp_all (config := { zetaDelta := true }) [taste_ingr]; simp_all (config := { zetaDelta := true }) [taste_ingr]

def pipeline'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut acc : Int := (0 : Int)
      for x in (PastaLean.pyIter xs) do
        acc := acc +ₚ x
      let _ := Libraries.passta.pyPassAssert (acc == PastaLean.pySum xs)
      acc := acc *ₚ (2 : Int)
      let mut cnt : Int := (0 : Int)
      for x in (PastaLean.pyIter xs) do
        cnt := cnt +ₚ (1 : Int)
      let _ := Libraries.passta.pyPassAssert (cnt == PastaLean.pyLen xs)
      let mut result : Int := acc +ₚ cnt
      let _ := Libraries.passta.pyPassEnsures (result == (2 : Int) *ₚ PastaLean.pySum xs +ₚ PastaLean.pyLen xs)
      return result)