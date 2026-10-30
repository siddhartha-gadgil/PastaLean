import PastaLean.Imports
import PastaLean.PyAPI.Operators
import PastaLean.PyAPI.PyAnyProof
import PastaLean.PyVerify.Pastafolio
import PastaLean.PyVerify.HelperLemmas
import PastaLean.PyVerify.Refute

open Lean Elab Tactic Meta
open PastaLean.Pastafolio

namespace PastaLean

/-! `taste?` — PastaLean's recipe for the Pastafolio proof-search engine, TUNED to the shapes
PastaLean actually emits (operator-laden Int/ℚ arithmetic, `pyTruthy` guards, boxed `PyAny`, and
`mvcgen` Hoare goals) rather than run as a generic hammer. Retune freely. -/

-- Extra lemmas for every `simp_all [taste_ingr]`. Add more with `attribute [taste_ingr] my_lemma`.
attribute [taste_ingr] mul_nonneg add_nonneg
-- Lower the Python operators to their Int/native meaning so `omega`/`grind` can see through them.
-- These are the workhorses (`+ₚ -ₚ *ₚ %ₚ //`): unfolding the class projection reduces an operator
-- on a concrete numeric instance to the plain `+`/`-`/`*`/… that the arithmetic closers understand.
attribute [taste_ingr] PyModulo.hMod PyHAdd.hAdd PyHSub.hSub PyHMul.hMul PyFloorDiv.floorDiv
  pyMod pyFloorDiv pyBoolToInt
-- Bitwise + shift operators (`& | ^ << >>`) — integer, so `grind`/`omega` reason about them once the
-- projection is unfolded. Common in bit-manipulation solutions.
attribute [taste_ingr] PyBitAnd.bitAnd PyBitOr.bitOr PyBitXor.bitXor pyBitAnd pyBitOr pyBitXor
  PyShiftLeft.shiftLeft PyShiftRight.shiftRight pyShiftLeft pyShiftRight
-- Lower `pyTruthy x` (a `while`/`if` guard) to `x ≠ 0` etc. so loop-step VCs discharge.
attribute [taste_ingr] pyTruthy PyTruthy.truthy

/-- Discovered proofs (each keyed by its tactic's byte offset), for the `py2lean` prove-and-replace
pipeline — the offset lets the splicer match each proof back to its own `taste?` token. -/
initialize tasteWinnersRef : IO.Ref (Array (Nat × String)) ← IO.mkRef #[]

/-- Does the current goal mention the constant `c` anywhere? Used to branch the portfolio on the
shape PastaLean actually produces (a boxed `PyAny`, an unsplit Hoare triple). -/
private def goalMentions (c : Name) : TacticM Bool := do
  let tgt ← instantiateMVars (← getMainTarget)
  return (tgt.find? (·.isConstOf c)).isSome

/-- Simplifiers reshape the goal (lower `+ₚ`/`*ₚ`, unfold leaves, clear casts); closers must fully
discharge it. Both are re-derived against the LIVE goal each round, so the profile branches on the
goal's shape — the load-bearing PastaLean specialization. -/
def tasteProfile : Profile where
  simplifiers := do
    let mut s : Array (TSyntax `tactic) := #[← `(tactic| intros)]
    -- MONADIC branch. An unsplit Hoare triple `⦃P⦄ prog ⦃Q⦄` (`taste?` used standalone; the codegen
    -- normally runs `mvcgen … invariants` itself before `taste?`). Generate its verification
    -- conditions, seeded with the `pyRange`-loop reduction specs so index invariants recover. Fires
    -- only while a `Triple` head remains, so it cannot loop on the `SPred` VCs it produces, and stays
    -- dormant once `mvcgen` has already run.
    if ← goalMentions ``Std.Do.Triple then
      s := s.push (← `(tactic| mvcgen [taste_ingr, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start]))
    s := s ++ #[
      ← `(tactic| simp_all (config := { zetaDelta := true }) [taste_ingr]),
      ← `(tactic| push_cast at *)]
    return s
  closers := do
    -- PYANY branch. A boxed dynamic value: no arithmetic closer sees through the box, so split it
    -- into one goal per relevant runtime type FIRST, then close each. `pyany_cases` is a no-op with
    -- no `PyAny`, but branching keeps its (grind-heavy) cost off every ordinary numeric goal.
    if ← goalMentions ``PastaLean.PyAny then
      return #[
        ← `(tactic| pyany_cases <;> omega),
        ← `(tactic| pyany_cases <;> simp_all (config := { zetaDelta := true }) [taste_ingr]),
        ← `(tactic| pyany_cases <;> grind +locals),
        ← `(tactic| grind +locals +suggestions)]
    -- ARITHMETIC / general branch. Fail-fast portfolio: cheap decision procedures that close
    -- instantly or bail cheaply come first; the expensive searchers (grind-family, aesop) are last
    -- resorts. Each candidate gets a FRESH heartbeat budget and first-to-close wins, so this ordering
    -- changes only how fast a goal closes, never *whether* it does.
    return #[
      ← `(tactic| omega),
      -- Operator identities / `0 ≤ pyLen …` often close by simp alone; some VCs only surface after an
      -- mvcgen split, so this per-goal `simp_all` complements the up-front simplifier.
      ← `(tactic| simp_all (config := { zetaDelta := true }) [taste_ingr]),
      ← `(tactic| norm_num),
      ← `(tactic| decide),
      -- `if`-laden goals (floored `pyMod`/`pyFloorDiv` after unfolding) split then close arithmetically.
      ← `(tactic| split_ifs <;> omega),
      -- A branch whose body needs `taste_ingr` reductions only AFTER the split (e.g. `return [a,b]`
      -- whose `[a,b]⦋i⦌` is blocked by the enclosing `if`): split first, THEN simp+arith each branch.
      ← `(tactic| split_ifs <;> simp_all (config := { zetaDelta := true }) [taste_ingr] <;> omega),
      -- `taste_ingr` normalises `/ₚ` (true division) to `ℚ` division, so `ring` closes area/mean goals.
      ← `(tactic| simp only [taste_ingr] <;> ring),
      ← `(tactic| ring),
      ← `(tactic| positivity),
      ← `(tactic| linarith),
      ← `(tactic| grind),
      ← `(tactic| split_ifs <;> grind),
      ← `(tactic| nlinarith),
      ← `(tactic| grind +locals +suggestions),
      ← `(tactic| aesop)]
  winnersRef? := some tasteWinnersRef

syntax (name := tasteStx) "taste?" : tactic

@[tactic tasteStx]
def evalTaste : Tactic := fun stx => do
  if Refute.pastalean.taste.skip.get (← getOptions) then
    admitGoal (← getMainGoal); return
  -- A counterexample first: a false goal is reported and admitted instead of searched.
  if ← Refute.tastePrecheck stx then return
  runPastafolio tasteProfile stx

end PastaLean
