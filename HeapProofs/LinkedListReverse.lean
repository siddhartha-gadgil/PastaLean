import PastaLean
import Std.Tactic.Do

/-!
# In-place singly-linked-list `reverse` — a framed separation-logic Hoare triple

A port of Lean PR #14614's showcase (an in-place doubly-linked-list reverse proven with `vcgen`)
to PastaLean's **typed** `--heap` runtime. The differences:

* PastaLean's heap holds one whole value per `Ref` cell (not raw per-field addresses), so a node is
  the struct `Node { val, next }` — exactly what `pastalean translate --heap` emits for the recursive
  `class Node: def __init__(self, val, next=None)` pattern (see `example_scripts/heap/07_optional_node.py`).
  The list is therefore *singly* linked: `reverse` only rewrites each `next` pointer to point back.
* A null pointer is `none : Option (Ref Node)`; the ghost list `xs : List Int` relates to the heap by
  `IsList`, quantifying the tail pointer with the lattice `⨆` (`Lean.Order.iSup`).
* Leaf steps reuse the library's proven `readRef_spec`/`writeRef_spec` and the registered
  `@[frameproc]`, so the framing (`l ↦ v` carried untouched across the whole reverse) is automatic.

`reverse.go`/`reverse` are hand-written (as in the PR): the program takes only a `head` pointer,
`xs` is ghost in the specification, and the accumulator `go_spec` is proved by induction on the ghost
list with the induction hypothesis fed to `vcgen` as the spec for the recursive call.

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

/-! ## Separating pure facts (`⌜φ⌝ ⊓ emp`) -/

/-- Iris-style separating pure: the heap is empty *and* `φ` holds. -/
noncomputable abbrev sepPure (φ : Prop) : HProp Val := ⌜φ⌝ ⊓ emp

theorem sepPure_apply (φ : Prop) (s : Store Val) : sepPure φ s ↔ φ ∧ emp s := by
  simp only [sepPure, hprop_meet_apply, hprop_ofProp_apply]

/-- `sepPure P ∗ Q` floats `P` out as a pure fact and leaves `Q`. -/
theorem sepPure_sepConj_iff (P : Prop) (Q : HProp Val) (s : Store Val) :
    (sepPure P ∗ Q) s ↔ P ∧ Q s := by
  rw [sepPure, sepConj_ofProp_meet_left, emp_sepConj]
  simp only [hprop_meet_apply, hprop_ofProp_apply]

@[grind =] theorem sepPure_true_eq_emp : sepPure True = emp := by
  funext s; apply propext; simp [sepPure_apply]

/-! ## Pointwise `⨆` on `HProp` -/

/-- Pointwise characterization of the lattice `⨆` on `HProp Val`. -/
theorem iSup_hprop_apply {ι : Type} (P : ι → HProp Val) (s : Store Val) :
    (Lean.Order.iSup P) s ↔ ∃ i, (P i) s := by
  unfold Lean.Order.iSup
  rw [hprop_sup_apply]
  constructor
  · rintro ⟨f, ⟨i, rfl⟩, hf⟩; exact ⟨i, hf⟩
  · rintro ⟨i, hi⟩; exact ⟨P i, ⟨i, rfl⟩, hi⟩

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

@[grind =] theorem IsList_append_nil (xs : List Int) (r : Option (Ref Node)) :
    IsList (xs ++ ([] : List Int)) r = IsList xs r := by simp

/-! ## The program: fuel-bounded in-place reverse -/

/-- Reverse accumulator: walk `curr`, splicing each cell's `next` to point at the reversed prefix
`prev`. `fuel` bounds the remaining spine length (`xs.length` in the spec). -/
def Node.reverse.go (fuel : Nat) (curr prev : Option (Ref Node)) : HeapM Val (Option (Ref Node)) :=
  match fuel with
  | 0 => pure prev
  | fuel + 1 =>
    match curr with
    | none => pure prev
    | some r => do
      let node ← readRef r
      writeRef r { node with next := prev }
      Node.reverse.go fuel node.next (some r)

/-- In-place reverse with fuel `xs.length` supplied at the specification. -/
def Node.reverse (fuel : Nat) (head : Option (Ref Node)) : HeapM Val (Option (Ref Node)) :=
  Node.reverse.go fuel head none

/-! ## Specifications -/

/-- Read a cons cell through its `IsList`: the returned `node` witnesses the head payload (`node.val`)
and the tail pointer (`node.next`). Higher priority than `readRef_spec` so `vcgen` prefers the
`IsList`-shaped precondition. -/
@[spec high] theorem readRef_cons_IsList (v : Int) (vs : List Int) (r : Ref Node) :
    ⦃ IsList (v :: vs) (some r) ⦄
      readRef r
    ⦃ fun node => (⌜node.val = v⌝ : HProp Val) ⊓ (r ↦ node ∗ IsList vs node.next) ⦄ := by
  simp only [IsList_cons_some]
  vcgen [readRef_spec] with finish

/-- After rewriting `curr`'s `next` to `prev`, rebuild the cons cell onto the accumulator; the tail
`IsList rest next` frames across. The read value fact `node.val = v` (floated out by the read spec)
identifies the rebuilt head. -/
theorem reverse_handoff_le (nd : Node) (v : Int) (rest acc : List Int)
    (r : Ref Node) (next prev : Option (Ref Node)) (hv : nd.val = v) (hn : nd.next = prev) :
    ((IsList acc prev ∗ IsList rest next) ∗ r ↦ nd)
      ⊑ IsList rest next ∗ IsList (v :: acc) (some r) := by
  subst hv; subst hn
  have heq : ((IsList acc nd.next ∗ IsList rest next) ∗ r ↦ nd)
      = (IsList rest next ∗ (r ↦ nd ∗ IsList acc nd.next)) := by grind
  rw [heq]
  exact sepConj_mono_r (IsList_cons_intro nd r acc)

/-- When the remaining segment is empty, `curr = none` and the accumulator is the whole result. -/
theorem IsList_nil_acc_le (acc : List Int) (curr prev : Option (Ref Node)) :
    (sepPure (curr = none) ∗ IsList acc prev) ⊑ IsList acc prev := by
  intro s hs
  exact ((sepPure_sepConj_iff (curr = none) (IsList acc prev) s).mp hs).2

/-- Accumulator spec — both induction cases are `vcgen` scripts.
Pre: remaining segment `rest` at `curr`, plus the already-reversed prefix `acc` at `prev`.
Post: the full reversal `rest.reverse ++ acc`. -/
@[spec] theorem Node.reverse.go_spec (fuel : Nat) (rest acc : List Int)
    (curr prev : Option (Ref Node)) (hle : rest.length ≤ fuel) :
    ⦃ IsList rest curr ∗ IsList acc prev ⦄
      Node.reverse.go fuel curr prev
    ⦃ fun r => IsList (rest.reverse ++ acc) r ⦄ := by
  induction rest generalizing fuel curr prev acc with
  | nil =>
    simp only [List.reverse_nil, List.nil_append, IsList_nil_eq]
    cases fuel with
    | zero =>
      simp only [Node.reverse.go]
      vcgen with (try finish;
                  try exact IsList_nil_acc_le acc curr prev;
                  try (intro s hs;
                       exact ((sepPure_sepConj_iff (curr = none) (IsList acc prev) s).mp hs).2))
    | succ fuel =>
      cases curr with
      | none =>
        simp only [Node.reverse.go]
        vcgen with (try finish; try exact IsList_nil_acc_le acc none prev)
      | some r =>
        constructor
        intro s hs
        exact absurd ((sepPure_sepConj_iff (some r = none) (IsList acc prev) s).mp hs).1 (by simp)
  | cons v rest ih =>
    match fuel, hle with
    | 0, hle => simp at hle
    | fuel + 1, hle =>
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons] at hle ⊢
      cases curr with
      | none =>
        constructor
        intro s hs
        rw [IsList_cons_none] at hs
        exact (((sepPure_sepConj_iff False (IsList acc prev) s).mp hs).1).elim
      | some r =>
        simp only [Node.reverse.go]
        vcgen [-readRef_spec, readRef_cons_IsList, writeRef_spec,
          fun (node : Node) => ih fuel (v :: acc) node.next (some r) (Nat.le_of_succ_le_succ hle)] with
          (try finish;
           try (rename_i nd hval _;
                exact reverse_handoff_le {nd with next := prev} v rest acc r nd.next prev hval rfl))

@[spec] theorem Node.reverse_spec (xs : List Int) (head : Option (Ref Node)) :
    ⦃ IsList xs head ⦄ Node.reverse xs.length head ⦃ fun r => IsList xs.reverse r ⦄ := by
  simp only [Node.reverse]
  vcgen [-Node.reverse.go_spec,
    Node.reverse.go_spec xs.length xs [] head none (Nat.le_refl _)] with
    (try finish; try (simp [IsList_nil_none, sepConj_emp, IsList_append_nil]; finish))

/-- The `iFrame` moment at program scale: an unrelated cell `l ↦ v` is carried untouched across the
entire reverse, framed automatically off `reverse_spec` by the registered `@[frameproc]`. -/
example (xs : List Int) (head : Option (Ref Node)) (l : Ref Int) (v : Int) :
    ⦃ (l ↦ v ∗ IsList xs head : HProp Val) ⦄ Node.reverse xs.length head
    ⦃ fun r => l ↦ v ∗ IsList xs.reverse r ⦄ := by
  vcgen [Node.reverse_spec] with finish
