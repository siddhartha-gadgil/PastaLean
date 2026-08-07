import PastaLean
import Std.Tactic.Do

/-!
# `example_scripts/heap/31_scalar_cell.py` — framed spec + a computed value

The `add` closure below is the emitted `_running_total'add` from

    pastalean translate example_scripts/heap/31_scalar_cell.py --heap --no-check

renamed (the emitted name is `private` and mangled). The only heap use is a scalar `Ref Int`
cell, so this exercises the `…M` delegators on a non-struct ref: a read/modify/write followed by a
trailing read of the new value.

Three specs, in increasing strength: the footprint leaf spec (`runningTotalAdd_spec`); a single-call
framing demo (`runningTotalAdd_frame`, a disjoint cell `other ↦ o` auto-framed from the leaf); and
the whole program (`runningTotal_spec`), which allocates its own cell, adds 1 then 2, and returns
`3` — a value fact `⌜r = 3⌝` floated out of the freshly-allocated heap.

No per-file boilerplate: the `⌜·⌝` floaters and `+ₚ` grind lemmas are `scoped` to `PastaLean` in
`Proof.lean`, so `open PastaLean` brings them in.

This module stays at the root namespace (as the translator emits) and is built as an independent
compilation unit (lakefile `globs`), so its `Val` never collides with another example's.
-/

open Lean Std Std.Internal.Do Lean.Order
open PastaLean

set_option linter.all false
set_option mvcgen.warning false
set_option maxHeartbeats 0

inductive Val where
  | hc_Int (c : Int)
  deriving Repr, Inhabited

instance : Storable Val Int where
  inject := Val.hc_Int
  project := fun
    | Val.hc_Int c => some c
  project_inject := fun _ => rfl

def runningTotalAdd := fun (k : Int) ↦ fun (total : PastaLean.Ref Int) ↦
  ((do
      PastaLean.writeRefM total ((← PastaLean.readRefM total) +ₚ k)
      return (← PastaLean.readRefM total)) :
    (PastaLean.HeapM Val) _)

/-- Footprint leaf spec: `add k` increments the scalar cell `total` by `k`. The returned new total
is discarded by the triple (`fun _ =>`) — the heap effect is the claim. -/
theorem runningTotalAdd_spec (total : Ref Int) (t k : Int) :
    ⦃ (total ↦ t : HProp Val) ⦄ runningTotalAdd k total
    ⦃ fun _ => total ↦ (t +ₚ k) ⦄ := by
  vcgen [runningTotalAdd, readRefM_spec, writeRefM_spec] simplifying_assumptions with finish

/-- Single-call framing: a disjoint cell `other ↦ o` is carried through untouched, framed
automatically off the footprint leaf spec. -/
theorem runningTotalAdd_frame (total other : Ref Int) (t o k : Int) :
    ⦃ (total ↦ t ∗ other ↦ o : HProp Val) ⦄ runningTotalAdd k total
    ⦃ fun _ => total ↦ (t +ₚ k) ∗ other ↦ o ⦄ := by
  vcgen [runningTotalAdd_spec] simplifying_assumptions with finish

def runningTotal :=
  ((do
      let mut total := (← PastaLean.allocM (0 : Int))
      let _ ← runningTotalAdd (1 : Int) total
      let _ ← runningTotalAdd (2 : Int) total
      return (← PastaLean.readRefM total)) :
    (PastaLean.HeapM Val) _)

/-- The whole program allocates its own cell, accumulates `1 + 2`, and returns `3`. The
freshly-allocated heap is absorbed and the return value is pinned as the pure fact `⌜r = 3⌝`. -/
theorem runningTotal_spec :
    ⦃ (emp : HProp Val) ⦄ runningTotal ⦃ fun r => (⌜r = (3 : Int)⌝ : HProp Val) ⦄ := by
  vcgen [runningTotal, runningTotalAdd_spec, allocM_frame_spec, readRefM_spec]
    simplifying_assumptions with finish
