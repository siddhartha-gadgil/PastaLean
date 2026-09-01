import PastaLean
import Std.Tactic.Do

/-!
# In-place singly-linked-list `reverse` — a framed separation-logic Hoare triple on translator output

A separation-logic proof of `⦃ IsList xs head ⦄ reverse head ⦃ fun r => IsList xs.reverse r ⦄` where
`reverse` is the **verbatim Lean that `pastalean translate --heap` emits** for the textbook Python
in-place linked-list reverse (`example_scripts/heap/37_linked_list_reverse.py`): a `while` loop over
`(prev, curr)` that reads each node's `next`, splices it to point back at `prev`, and advances.

* PastaLean's heap holds one whole value per `Ref` cell, so a node is the struct `Node { val, next }`;
  a null pointer is `none : Option (Ref Node)`. The ghost list `xs : List Int` relates to the heap by
  `IsList`, quantifying each tail pointer with the lattice `⨆` (`Lean.Order.iSup`).
* The loop's decreasing quantity is the remaining spine length at `curr` — a *heap-resident* fact, not
  a pure function of the two `Ref` pointers in the loop state. `RepeatVariant` (Lean PR #14507) is
  exactly that general: its `EvalsTo : β → γ → Pred` evaluates the measure *inside* the assertion
  lattice, so `RepeatVariant.ofHeapRel` (in `PastaLean/PyAPI/Heap/Proof.lean`) turns the relation
  "`n` nodes remain at `curr`" into a measure and the loop goes through the stock `Spec.forIn_loop`.
* Leaf steps use the library's `readRefM_spec`/`writeRefM_spec` under `vcgen`; the registered
  `@[frameproc]` frames the untouched tail across each step, and the closing `example` frames an
  unrelated cell `l ↦ v` across the entire reverse.

This module stays at the root namespace (as the translator emits) and is built as an independent
compilation unit (lakefile `globs`), so its `Val` never collides with another example's.
-/

open Lean Std Std.Internal.Do Lean.Order
open PastaLean

set_option linter.all false
set_option mvcgen.warning false
set_option maxHeartbeats 0

/-! ## The node, its heap value, and `Storable` instances -/

structure Node where
  val : Int
  next : Option (PastaLean.Ref Node)
  deriving Inhabited, Repr, BEq

inductive Val where
  | node (val : Int) (next : Option (PastaLean.Ref Node))
  | hc_Int (c : Int)
  deriving Repr, Inhabited

derive_storable% Node

instance : Storable Val Int where
  inject := Val.hc_Int
  project := fun
    | Val.hc_Int c => some c
    | _ => none
  project_inject := fun _ => rfl

/-! ## The list predicate `IsList xs p`

`p` roots a null-terminated singly-linked list whose payloads are `xs`. Matching on the pointer in the
definition keeps the head `r` concrete in the cons case — only the tail pointer `n` is existential. -/

noncomputable def IsList : List Int → Option (Ref Node) → HProp Val
  | [], p => sepPure (p = none)
  | _ :: _, none => sepPure False
  | v :: vs, some r =>
      Lean.Order.iSup fun n : Option (Ref Node) => r ↦ { val := v, next := n } ∗ IsList vs n

@[grind =] theorem IsList_nil_eq (p : Option (Ref Node)) : IsList [] p = sepPure (p = none) := rfl

@[grind =] theorem IsList_cons_none (v : Int) (vs : List Int) :
    IsList (v :: vs) none = sepPure False := rfl

@[grind =] theorem IsList_cons_some (v : Int) (vs : List Int) (r : Ref Node) :
    IsList (v :: vs) (some r)
      = Lean.Order.iSup fun n : Option (Ref Node) => r ↦ { val := v, next := n } ∗ IsList vs n := rfl

@[grind =] theorem IsList_nil_none : IsList ([] : List Int) none = emp := by
  funext s; apply propext; simp [IsList_nil_eq, sepPure_apply]

/-- Rebuild a cons cell onto the front of a list: a cell holding `node` whose tail-pointer `node.next`
roots `vs` is a list `node.val :: vs`. The one introduction rule for `IsList`. -/
theorem IsList_cons_intro (node : Node) (r : Ref Node) (vs : List Int) :
    (r ↦ node ∗ IsList vs node.next) ⊑ IsList (node.val :: vs) (some r) := by
  intro s hs
  rw [IsList_cons_some]
  exact (iSup_hprop_apply _ _).mpr ⟨node.next, hs⟩

/-- After rewriting `curr`'s `next` to `prev`, rebuild the cons cell onto the accumulator; the tail
`IsList rest next` frames across. The read value fact `nd.val = v` identifies the rebuilt head. -/
theorem reverse_handoff_le (nd : Node) (v : Int) (rest acc : List Int)
    (r : Ref Node) (next prev : Option (Ref Node)) (hv : nd.val = v) (hn : nd.next = prev) :
    ((IsList acc prev ∗ IsList rest next) ∗ r ↦ nd)
      ⊑ IsList rest next ∗ IsList (v :: acc) (some r) := by
  subst hv; subst hn
  have heq : ((IsList acc nd.next ∗ IsList rest next) ∗ r ↦ nd)
      = (IsList rest next ∗ (r ↦ nd ∗ IsList acc nd.next)) := by grind
  rw [heq]
  exact sepConj_mono_r (IsList_cons_intro nd r acc)

/-! ## The loop measure and invariant

`REAL b n` is the measure relation "at cursor `b = (prev, curr)` exactly `n` nodes remain": the heap
splits as the reversed prefix `acc` at `prev` and the remaining segment `rest` at `curr`, with the
pure witness `xs = acc.reverse ++ rest ∧ rest.length = n`. `MEASURE` is that relation as a stock
`RepeatVariant`. The invariant's `.inl` (continue) case is the same thing with the measure
existentially quantified; its `.inr` (done) case is the fully reversed list. -/
noncomputable def REAL (xs : List Int) (b : Option (Ref Node) × Option (Ref Node)) (n : Nat) :
    HProp Val :=
  iSup (fun (ra : List Int × List Int) =>
    sepPure (xs = ra.2.reverse ++ ra.1 ∧ ra.1.length = n) ∗ (IsList ra.1 b.2 ∗ IsList ra.2 b.1))

noncomputable def MEASURE (xs : List Int) :
    RepeatVariant (Option (Ref Node) × Option (Ref Node)) (HProp Val) :=
  RepeatVariant.ofHeapRel (REAL xs)

noncomputable def INV (xs : List Int) :
    (Option (Ref Node) × Option (Ref Node)) ⊕ (Option (Ref Node) × Option (Ref Node)) →
    HProp Val
  | .inl b => iSup (REAL xs b)
  | .inr b => IsList xs.reverse b.1

/-! ## The translated program (verbatim from `pastalean translate --heap`, example 37) -/

def reverse := fun (head : Option (PastaLean.Ref Node)) ↦
  ((do
      let mut prev := Option.none
      let mut curr := head
      while (!PastaLean.pyIsNone curr) do
        let mut nxt := (← (((curr).getD default) ~> next))
        ((curr).getD default) ~> next <~ prev
        prev := curr
        curr := nxt
      return prev) :
    (PastaLean.HeapM Val) _)

/-! ## The spec, proved on the translated `forIn` via the stock `Spec.forIn_loop` -/

theorem reverse_spec (xs : List Int) (head : Option (Ref Node)) :
    ⦃ IsList xs head ⦄ reverse head ⦃ fun r => IsList xs.reverse r ⦄ := by
  simp only [reverse]
  refine Triple.bind _ _ (fun b => INV xs (.inr b)) ?hx ?hf
  case hf =>
    intro b
    refine Triple.pure b.1 ?_
    simp only [INV]
    exact PartialOrder.rel_refl
  case hx =>
    refine Triple.intro (PartialOrder.rel_trans
      (y := INV xs (.inl (none, head))) ?hpre ?hloop)
    case hloop =>
      refine Triple.le_wp ?_
      apply Spec.forIn_loop (measure := MEASURE xs) (inv := INV xs)
      -- `mb`'s type is `(MEASURE xs).γ`; ascribing it as `Nat` keeps `omega`/`<` usable below.
      refine fun b (mb : Nat) => ?_
      obtain ⟨prev, curr⟩ := b
      simp only [MEASURE, INV]
      -- The invariant's own `⨆` pins the measure, so the step's `EvalsTo b mb ⊓ …` collapses.
      refine Triple.intro (PartialOrder.rel_trans
        (RepeatVariant.ofHeapRel_meet_le (REAL xs) (prev, curr) mb) (Triple.le_wp ?_))
      simp only [REAL]
      refine Triple.iSup_pre _ _ _ ?_
      rintro ⟨rest, acc⟩
      refine Triple.sepPure_pre _ _ _ _ ?_
      rintro ⟨hxs, hlen⟩
      cases curr with
      | none =>
        rw [ite_eq_right (by decide)]
        cases rest with
        | nil =>
          refine Triple.pure (ForInStep.done (prev, none)) ?_
          show (IsList [] none ∗ IsList acc prev) ⊑ IsList xs.reverse prev
          have hrev : xs.reverse = acc := by rw [hxs]; simp
          rw [IsList_nil_none, emp_sepConj, hrev]
        | cons v vs =>
          refine Triple.pure (ForInStep.done (prev, none)) ?_
          intro s hs
          rw [IsList_cons_none] at hs
          exact (((sepPure_sepConj_iff False (IsList acc prev) s).mp hs).1).elim
      | some r =>
        cases rest with
        | nil =>
          refine Triple.intro (fun s hs => ?_)
          rw [IsList_nil_eq] at hs
          exact absurd (((sepPure_sepConj_iff (some r = none) (IsList acc prev) s).mp hs).1) (by simp)
        | cons v vs =>
          rw [ite_eq_left (show (!PastaLean.pyIsNone (some r)) = true from rfl)]
          simp only [Option.getD_some]
          rw [IsList_cons_some]
          refine Triple.iSup_sepConj_pre _ _ _ _ ?_
          intro nptr
          vcgen [readRefM_spec, writeRefM_spec]
          case vc1 => exact frames_sepConj _ _
          case vc2 => exact frames_sepConj _ _
          case vc3 => exact frames_sepConj _ _
          case vc4 =>
            rename_i nd1 e1 nd2 e2 _u
            subst e1
            subst e2
            have hlen' : (v :: vs).length = mb := hlen
            have hlt : vs.length < mb := by
              simp only [List.length_cons] at hlen'; omega
            have hxs' : xs = acc.reverse ++ (v :: vs) := hxs
            -- Rebuild the yield post from one entailment: `EvalsBelow` at `vs.length < mb`, and the
            -- invariant's `⨆` at the same witness.
            refine PartialOrder.rel_trans (y := REAL xs (some r, nptr) vs.length) ?_
              (le_meet _ _ _ (RepeatVariant.ofHeapRel_le_evalsBelow (REAL xs) hlt)
                (Std.Internal.Do.CompleteLattice.le_iSup_of_le vs.length PartialOrder.rel_refl))
            have hspatial :
                (IsList vs nptr ∗ IsList acc prev) ∗ r ↦ ({ val := v, next := prev } : Node)
                  ⊑ IsList vs nptr ∗ IsList (v :: acc) (some r) := by
              rw [sepConj_comm (IsList vs nptr) (IsList acc prev)]
              exact reverse_handoff_le { val := v, next := prev } v vs acc r nptr prev rfl rfl
            refine PartialOrder.rel_trans hspatial ?_
            simp only [REAL]
            refine Std.Internal.Do.CompleteLattice.le_iSup_of_le
              ((vs, v :: acc) : List Int × List Int) ?_
            intro s hs
            refine (sepPure_sepConj_iff _ _ s).mpr ⟨?_, hs⟩
            refine ⟨?_, rfl⟩
            show xs = (v :: acc).reverse ++ vs
            rw [List.reverse_cons, List.append_assoc]
            exact hxs'
    case hpre =>
      intro s hs
      simp only [INV]
      rw [iSup_hprop_apply]
      refine ⟨xs.length, ?_⟩
      simp only [REAL]
      rw [iSup_hprop_apply]
      refine ⟨(xs, []), ?_⟩
      refine (sepPure_sepConj_iff _ _ s).mpr ⟨⟨?_, rfl⟩, ?_⟩
      · simp
      · show (IsList xs head ∗ IsList [] none) s
        rw [IsList_nil_none, sepConj_emp]
        exact hs

/-- The `iFrame` moment at program scale: an unrelated cell `l ↦ v` is carried untouched across the
entire reverse, framed automatically off `reverse_spec` by the registered `@[frameproc]`. -/
example (xs : List Int) (head : Option (Ref Node)) (l : Ref Int) (v : Int) :
    ⦃ (l ↦ v ∗ IsList xs head : HProp Val) ⦄ reverse head
    ⦃ fun r => l ↦ v ∗ IsList xs.reverse r ⦄ := by
  vcgen [reverse_spec] with finish
