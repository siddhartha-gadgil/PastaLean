import PastaLean
import PastaLean.PyVerify.HelperLemmas
import Std.Tactic.Do

/-!
# `example_scripts/heap/42_counter_while.py` — a proven `while`-loop over the heap

`bump` is copied verbatim from

    pastalean translate example_scripts/heap/42_counter_while.py --heap --no-check

(`c : Cell`, `k : Int`). It advances a heap cell's field inside a **`while i < k`** loop; the spec
proves that after the loop the cell has advanced by exactly `k`. This is the first heap proof over a
*translated `while`-loop* (`CounterLoop` did the `for`-loop analogue).

Where a `for`-loop's `pyRange_forIn` spec hands the iteration count to `vcgen`, a `while` desugars to
`Lean.Loop.forIn` and is reasoned about by `Spec.forIn_loop`, which needs **two** supplied pieces:

* `inv2` — a *pure* decreasing measure `RepeatVariant` (`β → Nat`), here `(k - i).toNat`, witnessing
  termination. It is heap-blind, as `RepeatVariant` demands.
* `inv1` — a heap-reading loop invariant `RepeatInvariant` (`β ⊕ β → HProp`), `.inl` while looping /
  `.inr` at the break. It reads the heap (`c ↦ {cell.v + i}`) and carries the counter bounds as
  *separating* pure facts (`∗ sepPure (i ≤ k)`), so the `@[frameproc]` can still cancel `c ↦` when the
  body's read fires. The break case adds `∗ sepPure (k ≤ i)` (the loop guard failed), which with
  `i ≤ k` pins `i = k` and closes the postcondition.

`MonadTail (HeapM V)` (required by `forIn_loop`) and the `sepPure` helpers both live in
`PastaLean.PyAPI.Heap.Proof`, so `open PastaLean` brings them in with no per-file boilerplate.

This module stays at the root namespace (as the translator emits) and is built as an independent
compilation unit (lakefile `globs`), so its `Val` never collides with another example's.
-/

open Lean Std Std.Internal.Do Lean.Order
open PastaLean

set_option linter.all false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

structure Cell where
  v : Int
  deriving Inhabited, Repr, BEq

inductive Val where
  | cell (v : Int)
  | hc_Int (c : Int)
  deriving Repr, Inhabited

derive_storable% Cell

instance : Storable Val Int where
  inject := Val.hc_Int
  project := fun
    | Val.hc_Int c => some c
    | _ => none
  project_inject := fun _ => rfl

def bump := fun (c : PastaLean.Ref Cell) ↦ fun (k : Int) ↦
  ((do
      let mut i : Int := (0 : Int)
      while (i < k) do
        c ~> v <~ (← (c ~> v)) +ₚ (1 : Int)
        i := i +ₚ (1 : Int)) :
    (PastaLean.HeapM Val) _)

attribute [simp, taste_ingr] bump

/-- After `k ≥ 0` iterations, `bump c k` has advanced `c.v` by `k`. `inv1` is the heap-reading loop
invariant (the cell holds `cell.v + i` after `i` iterations, with `i ≤ k`); `inv2` is the pure
decreasing measure `(k - i).toNat` witnessing termination of the `while`. -/
theorem bump_spec (c : Ref Cell) (cell : Cell) (k : Int) (hk : 0 ≤ k) :
    ⦃ (c ↦ cell : HProp Val) ⦄ bump c k
    ⦃ fun _ => c ↦ { cell with v := cell.v +ₚ k } ⦄ := by
  vcgen [bump, readRefM_spec, writeRefM_spec] invariants
    | inv1 => Sum.elim
        (fun i => (c ↦ { cell with v := cell.v +ₚ i } ∗ sepPure (i ≤ k) : HProp Val))
        (fun i => (c ↦ { cell with v := cell.v +ₚ i } ∗ sepPure (i ≤ k) ∗ sepPure (k ≤ i) : HProp Val))
    | inv2 => fun i => (k - i).toNat
  simplifying_assumptions with try finish
  -- Entry: the cell holds `cell.v + 0 = cell.v`, and `0 ≤ k` rides as a separating pure fact.
  case vc1 =>
    show c ↦ cell ⊑ (c ↦ { v := cell.v +ₚ (0 : Int) } ∗ sepPure ((0 : Int) ≤ k))
    have e : ({ v := cell.v +ₚ (0 : Int) } : Cell) = cell := by
      rcases cell with ⟨v⟩; simp [pyAdd_int]
    rw [e]
    exact le_sepConj_sepPure (c ↦ cell) ((0 : Int) ≤ k) hk
  -- Exit: `i ≤ k` (invariant) and `k ≤ i` (loop guard failed) pin `i = k`.
  case vc2 a =>
    show (c ↦ { v := cell.v +ₚ a } ∗ sepPure (a ≤ k) ∗ sepPure (k ≤ a)) ⊑ c ↦ { v := cell.v +ₚ k }
    rw [← sepConj_assoc]
    refine sepPure_conj_elim (fun hka => ?_)
    refine sepPure_conj_elim (fun hak => ?_)
    have : a = k := _root_.le_antisymm hak hka
    subst this
    exact PartialOrder.rel_refl
  -- Read footprint: cancel `c ↦ _` (frames the pure fact); this assigns the read value `?vc5`.
  case vc3 b hb =>
    exact sepConj_sepPure_le (c ↦ { v := cell.v +ₚ b } : HProp Val) (b ≤ k)
  -- Body step: measure strictly decreases, bound `i+1 ≤ k` holds, cell advances by one.
  case vc4 b hb v1 e1 v2 e2 u =>
    subst e2
    show c ↦ { v := cell.v +ₚ b +ₚ (1 : Int) } ⊑
      ⌜(k - (b +ₚ (1 : Int))).toNat < (k - b).toNat⌝ ⊓
        (⌜b +ₚ (1 : Int) ≤ k⌝ ⊓ (c ↦ { v := cell.v +ₚ (b +ₚ (1 : Int)) } ∗ emp))
    refine le_meet _ _ _ ?_ (le_meet _ _ _ ?_ ?_)
    · exact le_ofProp _ _ (by simp only [pyAdd_int]; omega)
    · exact le_ofProp _ _ (by simp only [pyAdd_int]; omega)
    · rw [sepConj_emp]
      exact PartialOrder.rel_of_eq (by simp only [pyAdd_int, Int.add_assoc])
