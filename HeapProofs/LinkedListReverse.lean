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
  lattice, so `forIn_loop_heapRel` (in `PastaLean/PyAPI/Heap/Proof.lean`) turns the relation "`n`
  nodes remain at `curr`" into a measure *and* a loop invariant, over the stock `Spec.forIn_loop`.
* Leaf steps use the library's `readRefM_spec`/`writeRefM_spec` under `vcgen`; the registered
  `@[frameproc]` frames the untouched tail across each step, and the closing `example` frames an
  unrelated cell `l ↦ v` across the entire reverse.
* The interactive glue is `sl_intro` (peel the `⨆`/`⌜⌝` layers off a precondition) and `sl_cancel`
  (cancel the shared conjuncts of an entailment), both from `PastaLean/PyAPI/Heap/Proof.lean`.

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

/-! ## The loop measure

`REAL b n` is the measure relation "at cursor `b = (prev, curr)` exactly `n` nodes remain": the heap
splits as the reversed prefix `acc` at `prev` and the remaining segment `rest` at `curr`, with the
pure witness `xs = acc.reverse ++ rest ∧ rest.length = n`. `forIn_loop_heapRel` derives both the
`RepeatVariant` and the loop invariant from it — the in-progress invariant is `⨆ n, REAL b n`, and
the break assertion is supplied at the call site as the fully reversed list. -/
noncomputable def REAL (xs : List Int) (b : Option (Ref Node) × Option (Ref Node)) (n : Nat) :
    HProp Val :=
  iSup (fun (ra : List Int × List Int) =>
    sepPure (xs = ra.2.reverse ++ ra.1 ∧ ra.1.length = n) ∗ (IsList ra.1 b.2 ∗ IsList ra.2 b.1))

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

/-! ## The spec, proved on the translated `forIn` via `forIn_loop_heapRel` -/

theorem reverse_spec (xs : List Int) (head : Option (Ref Node)) :
    ⦃ IsList xs head ⦄ reverse head ⦃ fun r => IsList xs.reverse r ⦄ := by
  simp only [reverse]
  refine Triple.bind _ _ (fun b => IsList xs.reverse b.1) ?hx ?hf
  case hf => exact fun b => Triple.pure b.1 PartialOrder.rel_refl
  case hx =>
    refine Triple.intro (PartialOrder.rel_trans
      (y := iSup (REAL xs (none, head))) ?hpre ?hloop)
    case hloop =>
      refine Triple.le_wp
        (forIn_loop_heapRel (REAL xs) (fun b => IsList xs.reverse b.1) _ ?_)
      -- `n`'s type is the measure's `γ`; ascribing it as `Nat` keeps `omega`/`<` usable below.
      refine fun b (n : Nat) => ?_
      obtain ⟨prev, curr⟩ := b
      simp only [REAL]
      sl_intro ⟨rest, acc⟩ ⟨hxs, hlen⟩
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
          exact Triple.pure _ (IsList_cons_none v vs ▸ sepPure_sepConj_le_of_not (by simp) _ _)
      | some r =>
        cases rest with
        | nil =>
          exact Triple.intro (IsList_nil_eq (some r) ▸ sepPure_sepConj_le_of_not (by simp) _ _)
        | cons v vs =>
          rw [ite_eq_left (show (!PastaLean.pyIsNone (some r)) = true from rfl)]
          simp only [Option.getD_some]
          rw [IsList_cons_some]
          sl_intro nptr
          vcgen [readRefM_spec, writeRefM_spec]
          -- The read/write footprints frame off the `↦` atom the `iSup` peel just exposed.
          case vc1 | vc2 | vc3 => grind
          case vc4 =>
            rename_i nd1 e1 nd2 e2 _u
            subst e1
            subst e2
            have hlt : vs.length < n := by
              have hlen' : (v :: vs).length = n := hlen
              simp only [List.length_cons] at hlen'; omega
            refine PartialOrder.rel_trans ?_ (le_yieldBelow (REAL xs) hlt)
            simp only [REAL]
            refine Std.Internal.Do.CompleteLattice.le_iSup_of_le
              ((vs, v :: acc) : List Int × List Int) ?_
            sl_cancel
            case _ => exact ⟨by rw [List.reverse_cons, List.append_assoc]; exact hxs, rfl⟩
            case _ =>
              rw [sepConj_comm]
              exact IsList_cons_intro { val := v, next := prev } r acc
    case hpre =>
      refine Std.Internal.Do.CompleteLattice.le_iSup_of_le xs.length ?_
      simp only [REAL]
      refine Std.Internal.Do.CompleteLattice.le_iSup_of_le ((xs, []) : List Int × List Int) ?_
      sl_cancel
      case _ => exact ⟨by simp, rfl⟩
      case _ => exact PartialOrder.rel_of_eq IsList_nil_none.symm

/-- The `iFrame` moment at program scale: an unrelated cell `l ↦ v` is carried untouched across the
entire reverse, framed automatically off `reverse_spec` by the registered `@[frameproc]`. -/
example (xs : List Int) (head : Option (Ref Node)) (l : Ref Int) (v : Int) :
    ⦃ (l ↦ v ∗ IsList xs head : HProp Val) ⦄ reverse head
    ⦃ fun r => l ↦ v ∗ IsList xs.reverse r ⦄ := by
  vcgen [reverse_spec] with finish
