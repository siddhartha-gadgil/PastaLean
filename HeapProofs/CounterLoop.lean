import PastaLean
import PastaLean.PyVerify.HelperLemmas
import Std.Tactic.Do

/-!
# `example_scripts/heap/36_counter_loop.py` — a framed loop invariant

`Counter.bump_many` is copied verbatim from

    pastalean translate example_scripts/heap/36_counter_loop.py --heap --no-check

(`k` annotated `Int`). It bumps a shared cell inside a `for`-loop; the spec proves that after `k`
iterations the counter has advanced by `k`, while a *disjoint* counter `other ↦ o` is framed across
the whole loop. This is the first heap proof that needs a user-supplied loop invariant.

`vcgen … invariants | inv1 => …` supplies the invariant as a curried function of the loop cursor's
prefix `p` (so `p.length` is the iteration count). `finish` (grind) discharges the straight-line
VCs; the three residual invariant-entailment VCs (init / step / exit) reconcile the invariant's
`p.length` arithmetic against the postcondition, which is pure `simp` + `∗`-AC reflexivity.

No per-file `sym_simp`/`grind` boilerplate: the `+ₚ`→`+` and `List.length_*` grind lemmas are
`scoped` to `PastaLean` in `Proof.lean`, so `open PastaLean` brings them in.

This module stays at the root namespace (as the translator emits) and is built as an independent
compilation unit (lakefile `globs`), so its `Val` never collides with another example's.
-/

open Lean Std Std.Internal.Do Lean.Order
open PastaLean

set_option linter.all false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

structure Counter where
  n : Int
  deriving Inhabited, Repr, BEq

inductive Val where
  | counter (n : Int)
  | hc_Int (c : Int)
  deriving Repr, Inhabited

derive_storable% Counter

instance : Storable Val Int where
  inject := Val.hc_Int
  project := fun
    | Val.hc_Int c => some c
    | _ => none
  project_inject := fun _ => rfl

def Counter.bump_many (self : PastaLean.Ref Counter) (k : Int) :=
  ((do
      for _i in (PastaLean.pyRange k) do
        self ~> n <~ (← (self ~> n)) +ₚ (1 : Int)) :
    PastaLean.HeapM Val Unit)

/-- After `k` bumps `self.n` has advanced by `k`, and a disjoint counter `other ↦ o` is framed
across the entire loop. The invariant tracks the count as the loop cursor's prefix length. -/
theorem Counter.bump_many_spec (self other : Ref Counter) (c o : Counter) (k : Int) :
    ⦃ (self ↦ c ∗ other ↦ o : HProp Val) ⦄ Counter.bump_many self k
    ⦃ fun _ => self ↦ { c with n := c.n +ₚ (k.toNat : Int) } ∗ other ↦ o ⦄ := by
  vcgen [Counter.bump_many, pyRange_forIn, readRefM_spec, writeRefM_spec] invariants
    | inv1 => fun p _ _ => (self ↦ { c with n := c.n +ₚ (p.length : Int)} ∗ other ↦ o : HProp Val)
  simplifying_assumptions with try finish
  -- The residual init/step/exit VCs: normalise the `p.length` arithmetic, then close by `∗`-AC.
  all_goals
    first
    | done
    | (simp only [List.length_range, List.length_nil, List.length_append,
          List.length_cons, List.length_singleton, pyAdd_int,
          Nat.cast_add, Nat.cast_one, Nat.cast_zero, Int.add_zero, Int.add_assoc]
        <;> first
          | exact PartialOrder.rel_of_eq (by ac_rfl)
          | grind)
