import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 800000

namespace PastaLean.User.Root

-- Kitchen-sink: two loops (with invariants), if/else, exponentiation, try/except, and the math
-- library — a small "summary statistic" over a list of measurements.
noncomputable def analyze := fun (xs : List Int) ↦ fun (threshold : Int) ↦
  (do
    let mut total : Int := (0 : Int)
    let mut count : Int := (0 : Int)
    for x in (PastaLean.pyIter xs) do
      let _ := Libraries.passta.pyPassInvariant (decide (count ≥ (0 : Int)))
      total := total +ₚ x
      if h_1 : x > threshold then 
        count := count +ₚ (1 : Int)
    let mut ss : Int := (0 : Int)
    for x in (PastaLean.pyIter xs) do
      let _ := Libraries.passta.pyPassInvariant (decide (ss ≥ (0 : Int)))
      ss := ss +ₚ x ^ₚ (2 : Int)
    let mut avg := default
    let mut spread := default
    if h_1 : count > (0 : Int) then 
      try
        avg := total /ₚ count
        spread := Libraries.math.pyMathSqrtR (PastaLean.pyRat ss)
      catch caught =>
        if PastaLean.pyExcIsA caught "ZeroDivisionError" then 
          avg := (0.0 : Rat)
          spread := (0.0 : Real)
        else
          throw caught
    else
      avg := (0.0 : Rat)
      spread := (0.0 : Real)
    let mut result := avg +ₚ spread
    return result : ExceptT PastaLean.PyException Id _)

@[spec]
theorem analyze_spec : ⦃⌜PastaLean.pyLen xs > (0 : Int)⌝⦄ analyze xs threshold ⦃⇓result => ⌜result ≥ (0.0 : Rat)⌝⦄ :=
  by
  try
    mvcgen [analyze, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start] invariants
    · ⇓⟨cur, total, count⟩ => ⌜count ≥ (0 : Int)⌝
    · ⇓⟨cur, ss⟩ => ⌜ss ≥ (0 : Int)⌝
  simp_all (config := { zetaDelta := true }) [taste_ingr]; simp_all (config := { zetaDelta := true }) [taste_ingr]; positivity; sorry; sorry
  all_goals sorry

def analyze'rn : List Int → Int → PastaLean.PyExcept Float := fun (xs : List Int) ↦ fun (threshold : Int) ↦ do
  let _ := Libraries.passta.pyPassRequires (decide (PastaLean.pyLen xs > (0 : Int)))
  -- Loop 1: running total + count of entries above the threshold.
  let mut total : Int := (0 : Int)
  let mut count : Int := (0 : Int)
  for x in (PastaLean.pyIter xs) do
    let _ := Libraries.passta.pyPassInvariant (decide (count ≥ (0 : Int)))
    total := total +ₚ x
    if h_1 : x > threshold then 
      count := count +ₚ (1 : Int)
  -- Loop 2: sum of squares (uses exponentiation).
  let mut ss : Int := (0 : Int)
  for x in (PastaLean.pyIter xs) do
    let _ := Libraries.passta.pyPassInvariant (decide (ss ≥ (0 : Int)))
    ss := ss +ₚ x ^ₚ (2 : Int)
  -- if/else + math library + exception handling.
  let mut avg := default
  let mut spread := default
  if h_1 : count > (0 : Int) then 
    try
      avg := PastaLean.pyTrueDiv total count
      spread := Libraries.math.pyMathSqrt (PastaLean.pyFloat ss)
    catch caught =>
      if PastaLean.pyExcIsA caught "ZeroDivisionError" then 
        avg := (0.0 : Float)
        spread := (0.0 : Float)
      else
        throw caught
  else
    avg := (0.0 : Float)
    spread := (0.0 : Float)
  let mut result := avg +ₚ spread
  return result

end PastaLean.User.Root
