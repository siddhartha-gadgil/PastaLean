import Lean
import PastaLean.PyAPI.Heap.Ops
import PastaLean.PyAPI.Heap.Monad
import PastaLean.PyAPI.Operators
import Std.Internal
import Std.Tactic.Do

/-!
# Heap runtime — separation-logic frame automation (Phase 2)

The **provability** half of `--heap`: a weakest-precondition / separation-logic layer over the
*unchanged* Phase-1 heap runtime (`Core`/`Ops`/`Storable`), mirroring HeapSL
(`/Users/pmarkopoulos/Desktop/mvcgentest/heapsl-nightly`, the stock file). It gives Hoare triples
`⦃P⦄ prog ⦃Q⦄` over `↦`/`∗` discharged by `vcgen … with finish`, with automatic framing via a
registered `@[frameproc]`.

Requires the toolchain's internal `Std.Internal.Do` WP framework + `@[frameproc]` machinery. Built
against `nightly-2026-08-09`, which carries the footprint-based auto-framing API from Lean PR #14529
(the frame procedure now returns a full `FrameSplit`: frame + a discharged split VC + residual
subgoal) and the state-dependent loop measures from PR #14507 (`RepeatVariant` is a structure whose
`EvalsTo` reads the state). Only adaptation vs upstream HeapSL: the error dimension is `PyException`
(not `String`).
-/

-- Coexistence with Mathlib (both define `Order`/`CompleteLattice`): we open the WP framework
-- (`Std.Internal.Do`) and the toolchain lattice **`Lean.Order`** (its `⊓`/`⊑`/`⊤`/`⊥`/`⌜⌝` are
-- *scoped* notations) but NOT Mathlib's `_root_.Order`. The overloaded `⊓`/`⊤`/`⊥` resolve to
-- `Lean.Order` by type (`HProp` is a `def` carrying only the `Lean.Order.CompleteLattice` instance,
-- so Mathlib's interpretations don't typecheck); `Lean.Order`'s distinct `meet`/`join`/`rel`/`ofProp`
-- vocabulary doesn't clash with Mathlib's `inf`/`sup`/`le`. Only the bare class name `CompleteLattice`
-- is ambiguous, so it is written qualified as `Lean.Order.CompleteLattice`.
open Lean Std Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option grind.warning false

namespace PastaLean

variable {V : Type} {α : Type}

/-! ## Separation algebra on stores (`Store`/`Store.single`/`Store.update` are in `Core`) -/

/-- Two stores are disjoint when no address is present in both. -/
def Store.disjoint (s₁ s₂ : Store V) : Prop := ∀ n, s₁ n = none ∨ s₂ n = none

/-- Union of stores, preferring the left value on overlap. -/
def Store.union (s₁ s₂ : Store V) : Store V := fun n => (s₁ n).or (s₂ n)

@[simp] theorem Store.union_none_iff (s₁ s₂ : Store V) (n : Nat) :
    s₁.union s₂ n = none ↔ s₁ n = none ∧ s₂ n = none := by
  simp only [Store.union]; cases s₁ n <;> simp

theorem Store.disjoint_comm {s₁ s₂ : Store V} (h : s₁.disjoint s₂) : s₂.disjoint s₁ :=
  fun n => (h n).symm

theorem Store.union_comm {s₁ s₂ : Store V} (h : s₁.disjoint s₂) : s₁.union s₂ = s₂.union s₁ := by
  funext n; simp only [Store.union]; rcases h n with hn | hn <;> simp [hn]

theorem Store.union_assoc (s₁ s₂ s₃ : Store V) :
    (s₁.union s₂).union s₃ = s₁.union (s₂.union s₃) := by
  funext n; simp only [Store.union]; cases s₁ n <;> rfl

theorem Store.disjoint_union_left {s₁ s₂ s₃ : Store V} :
    (s₁.union s₂).disjoint s₃ ↔ s₁.disjoint s₃ ∧ s₂.disjoint s₃ := by
  simp only [Store.disjoint, Store.union_none_iff]
  constructor
  · intro h; exact ⟨fun n => (h n).imp_left (·.1), fun n => (h n).imp_left (·.2)⟩
  · rintro ⟨ha, hb⟩ n; have := ha n; have := hb n; grind

theorem Store.disjoint_union_right {s₁ s₂ s₃ : Store V} :
    s₁.disjoint (s₂.union s₃) ↔ s₁.disjoint s₂ ∧ s₁.disjoint s₃ := by
  simp only [Store.disjoint, Store.union_none_iff]
  constructor
  · intro h; exact ⟨fun n => (h n).imp_right (·.1), fun n => (h n).imp_right (·.2)⟩
  · rintro ⟨ha, hb⟩ n; have := ha n; have := hb n; grind

/-! ## Heap assertions (over stores only — blind to the `next` counter, so `alloc` frames) -/

def HProp (V : Type) : Type := Store V → Prop

instance : Lean.Order.CompleteLattice (HProp V) :=
  inferInstanceAs (Lean.Order.CompleteLattice (Store V → Prop))

-- Required by the stock loop rules (`Spec.repeatM`/`Spec.forIn_loop`). The generic pointwise
-- instance is stated for `∀ s, β s` and does not unfold the `HProp` def, so bridge it explicitly.
instance (P : HProp V) : PreservesSup (meet P) :=
  inferInstanceAs (PreservesSup (meet (show Store V → Prop from P)))

/-- The empty-store assertion. -/
def emp : HProp V := fun s => ∀ n, s n = none

/-- The raw singleton assertion: the store is exactly `l ↦ v`. -/
def pointsToRaw (l : Nat) (v : V) : HProp V := fun s => s = Store.single l v

/-- Typed points-to: the reference's cell holds exactly `inject v`. -/
def pointsTo [Storable V α] (r : Ref α) (v : α) : HProp V :=
  pointsToRaw r.addr (Storable.inject v)

/-- Separating conjunction: the store splits into two disjoint parts. -/
def sepConj (P Q : HProp V) : HProp V := fun s =>
  ∃ s₁ s₂, s₁.disjoint s₂ ∧ s = s₁.union s₂ ∧ P s₁ ∧ Q s₂

@[inherit_doc pointsTo] notation:70 l:max " ↦ " v:max => pointsTo l v
@[inherit_doc sepConj] infixr:65 " ∗ " => sepConj

/-! ## Separation algebra laws -/

theorem emp_sepConj (a : HProp V) : (emp ∗ a) = a := by
  funext s; apply propext
  constructor
  · rintro ⟨s₁, s₂, _, rfl, he, ha⟩
    simp only [emp] at he
    have hs : s₁.union s₂ = s₂ := by funext n; simp only [Store.union, he n, Option.none_or]
    rw [hs]; exact ha
  · intro ha
    refine ⟨fun _ => none, s, fun _ => Or.inl rfl, ?_, fun _ => rfl, ha⟩
    funext n; simp only [Store.union, Option.none_or]

theorem sepConj_assoc (a b c : HProp V) : ((a ∗ b) ∗ c) = (a ∗ (b ∗ c)) := by
  funext s; apply propext
  constructor
  · rintro ⟨_, s₃, hd, rfl, ⟨s₁, s₂, hd12, rfl, ha, hb⟩, hc⟩
    obtain ⟨hd13, hd23⟩ := Store.disjoint_union_left.mp hd
    exact ⟨s₁, s₂.union s₃, Store.disjoint_union_right.mpr ⟨hd12, hd13⟩,
      Store.union_assoc s₁ s₂ s₃, ha, s₂, s₃, hd23, rfl, hb, hc⟩
  · rintro ⟨s₁, _, hd, rfl, ha, ⟨s₂, s₃, hd23, rfl, hb, hc⟩⟩
    obtain ⟨hd12, hd13⟩ := Store.disjoint_union_right.mp hd
    exact ⟨s₁.union s₂, s₃, Store.disjoint_union_left.mpr ⟨hd13, hd23⟩,
      (Store.union_assoc s₁ s₂ s₃).symm, ⟨s₁, s₂, hd12, rfl, ha, hb⟩, hc⟩

theorem sepConj_comm (a b : HProp V) : (a ∗ b) = (b ∗ a) := by
  funext s; apply propext
  constructor <;>
    · rintro ⟨s₁, s₂, hd, rfl, hp, hq⟩
      exact ⟨s₂, s₁, Store.disjoint_comm hd, Store.union_comm hd, hq, hp⟩

/-- Right identity for `∗` (needed by the AC path and the `LawfulIdentity` instance). -/
theorem sepConj_emp (a : HProp V) : (a ∗ emp) = a := by
  rw [sepConj_comm, emp_sepConj]

-- AC instances so `Meta.AC.rewriteUnnormalizedRefl` (in `proveSepConjLe`) can rearrange `∗`; without
-- them the frame split VC `pre ⊑ frame ∗ footprint` is deferred and reaches `finish` with an
-- unevaluated `wp`, which grind cannot discharge.
instance : Std.Associative (α := HProp V) sepConj := ⟨sepConj_assoc⟩
instance : Std.Commutative (α := HProp V) sepConj := ⟨sepConj_comm⟩
instance : Std.LawfulIdentity (α := HProp V) sepConj emp where
  left_id := emp_sepConj
  right_id := sepConj_emp

/-! ## `∗` preserves sups (needed by `of_frameClosure`) -/

theorem hprop_sup_apply (c : HProp V → Prop) (s : Store V) :
    Lean.Order.CompleteLattice.sup c s = ∃ f, c f ∧ f s := by
  apply propext
  constructor
  · exact fun hh => sup_le c (x := fun s => ∃ f, c f ∧ f s)
      (fun f hf s' hfs' => ⟨f, hf, hfs'⟩) s hh
  · rintro ⟨f, hf, hfs⟩; exact le_sup (c := c) hf s hfs

instance (F : HProp V) : PreservesSup (sepConj F) where
  map_sup c := by
    funext s
    apply propext
    simp only [sepConj, hprop_sup_apply]
    constructor
    · rintro ⟨s₁, s₂, hd, rfl, hF, g, hg, hgs₂⟩
      exact ⟨sepConj F g, ⟨g, hg, rfl⟩, s₁, s₂, hd, rfl, hF, hgs₂⟩
    · rintro ⟨f, ⟨g, hg, rfl⟩, s₁, s₂, hd, rfl, hF, hgs₂⟩
      exact ⟨s₁, s₂, hd, rfl, hF, g, hg, hgs₂⟩

/-! ## Structural lemmas for the frame split -/

theorem sepConj_mono_r {a b b' : HProp V} (h : b ⊑ b') : (a ∗ b) ⊑ (a ∗ b') := by
  rintro s ⟨s₁, s₂, hd, rfl, ha, hb⟩
  exact ⟨s₁, s₂, hd, rfl, ha, h _ hb⟩

/-- Frame introduction: to land in `F ∗ R`, cancel `F` off the right of the precondition. -/
theorem sepConj_frame_r {pre₀ F R : HProp V} (h : pre₀ ⊑ R) : (pre₀ ∗ F) ⊑ (F ∗ R) :=
  PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_comm pre₀ F)) (sepConj_mono_r h)

/-- The mirror frame rule: cancel `F` off the **left** (used by hand when auto framing lands a frame
on the left — `apply sepConj_frame_l` before re-running `vcgen`). Every argument is explicit so
`sl_cancel` can also build it with `mkAppM`. -/
theorem sepConj_frame_l (F pre₀ R : HProp V) (h : pre₀ ⊑ R) : (F ∗ pre₀) ⊑ (F ∗ R) :=
  sepConj_mono_r h

/-! ## Affine "garbage" assertion -/

/-- Holds on any store; `Q ∗ ◇` = "`Q` holds on part of the heap, ignore the rest". -/
def htop : HProp V := fun _ => True

@[inherit_doc htop] notation:max "◇" => htop

@[grind .] theorem le_htop (b : HProp V) : b ⊑ (◇ : HProp V) := fun _ _ => trivial

@[grind .] theorem sepConj_absorb {a b : HProp V} : (a ∗ b) ⊑ (a ∗ ◇) :=
  sepConj_mono_r (le_htop b)

/-! ## The frame-internalizing weakest precondition (over our `HeapM`, error = `PyException`) -/

/-- The exception-predicate dimension. -/
abbrev HeapEPred (V : Type) := PyException → HProp V

/-- Base (non-framed) wp over store-predicates: run from *every* well-formed frontier `nx` (so the wp
is blind to the counter and `alloc`'s fresh cell frames). -/
@[instance_reducible] def storeWP (α : Type) : WP (HeapM V α) α (HProp V) (HeapEPred V) where
  wpTrans x := ⟨fun post epost s => ∀ nx (hwf : ∀ a, a ≥ nx → s a = none),
    match (HeapM.run x) ⟨s, nx, hwf⟩ with
    | .ok a h'    => post a h'.store
    | .error e h' => epost e h'.store⟩
  wp_trans_monotone x := by
    intro post post' epost epost' hepost hpost s hcur nx hwf
    have hc := hcur nx hwf
    cases hxs : (HeapM.run x) ⟨s, nx, hwf⟩ with
    | ok a h'    => rw [hxs] at hc; exact hpost a h'.store hc
    | error e h' => rw [hxs] at hc; exact hepost e h'.store hc

/-- The base `WPMonad` over store-predicates. -/
@[instance_reducible] noncomputable def storeBase : WPMonad (HeapM V) (HProp V) (HeapEPred V) where
  toLawfulMonad := inferInstance
  toWP := storeWP
  pure_le_wp_pure x post epost := by intro s hp nx hwf; exact hp
  bind_le_wp_bind x f post epost := by
    intro s hb nx hwf
    have hc := hb nx hwf
    show match EStateM.bind (HeapM.run x) (fun a => HeapM.run (f a)) ⟨s, nx, hwf⟩ with
      | .ok a h' => post a h'.store | .error e h' => epost e h'.store
    simp only [EStateM.bind]
    cases hxs : (HeapM.run x) ⟨s, nx, hwf⟩ with
    | ok a h'    => rw [hxs] at hc; exact hc h'.next h'.wf
    | error e h' => rw [hxs] at hc; exact hc

/-- The frame-internalizing wp: the `frameClosure` of `storeBase` over `∗`. -/
noncomputable instance HeapM.instWPMonad : WPMonad (HeapM V) (HProp V) (HeapEPred V) :=
  WPMonad.of_frameClosure sepConj sepConj_assoc emp_sepConj storeBase

/-- Every `HeapM` program frames every store assertion `F`. -/
@[grind .]
theorem frames_sepConj {α : Type} (x : HeapM V α) (F : HProp V) : WP.Frames sepConj x F :=
  WP.Frames.of_frameClosure sepConj sepConj sepConj_assoc
    ⟨fun y E Q' => (storeWP _).wpTrans y |>.apply Q' E, fun _ _ _ => rfl⟩

/-! ## The registered frame procedure for `∗` (Lean PR #14529 footprint-based `FrameSplit` API)

The frame procedure returns a `FrameSplit`: the framed resource, a *discharged* split VC
`pre ⊑ frame ∗ residualPre`, and the residual subgoal `footprint ⊑ residualPre`. The split VC is
proved by AC-rearranging `pre` into `frame ∗ footprint` (`proveSepConjLe`) and then composing with
right-monotonicity (`sepConj_mono_r`) through `rel_trans`. -/

section FrameProc
open Lean.Meta Lean.Meta.Sym Lean.Meta.Sym.Internal
  Lean.Elab.Tactic.Do.Internal Lean.Elab.Tactic.Do.Internal.VCGen

/-- Flatten a `∗`-tree into its atoms (metavariables instantiated at the root by `sepAtoms`). -/
partial def sepAtoms.go (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOf ``sepConj then sepAtoms.go e.appFn!.appArg! ++ sepAtoms.go e.appArg!
  else #[e]

/-- Flatten a `∗`-tree, instantiating metavariables once at the root. -/
def sepAtoms (e : Expr) : MetaM (Array Expr) :=
  return sepAtoms.go (← instantiateMVars e)

/-- Peel leading `⌜p⌝ ⊓ ·` (either side) off an atom, returning the pure facts and the spatial
remainder — so a read's value fact riding along its points-to atom doesn't block a footprint match. -/
partial def stripOfProp (e : Expr) : Array Expr × Expr :=
  if e.isAppOf ``Lean.Order.meet then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    if a.isAppOf ``Lean.Order.CompleteLattice.ofProp then
      let (ps, sp) := stripOfProp b; (#[a] ++ ps, sp)
    else if b.isAppOf ``Lean.Order.CompleteLattice.ofProp then
      let (ps, sp) := stripOfProp a; (#[b] ++ ps, sp)
    else (#[], e)
  else (#[], e)

/-- Rebuild a right-nested `∗` from atoms (`emp` when empty) at value universe `V`. -/
def sepConjOfAtomsE (V : Expr) (atoms : Array Expr) : Expr :=
  if atoms.isEmpty then mkApp (mkConst ``emp) V
  else atoms.pop.foldr (fun a acc => mkApp3 (mkConst ``sepConj) V a acc) atoms.back!

/-- `sepConjOfAtomsE`, hash-consed for the split-VC builder. -/
def sepConjOfAtoms (V : Expr) (atoms : Array Expr) : SymM Expr :=
  shareCommon (sepConjOfAtomsE V atoms)

/-- Cancel `rhs` atoms against `lhs` atoms by `isDefEq`, returning the matched `lhs` atoms (in `rhs`
order) and the two leftovers. `strip` matches against a candidate's spatial remainder only, so a
pure-fact-carrying `lhs` atom still cancels. -/
def cancelSepAtoms (lhs rhs : Array Expr) (strip : Bool) :
    MetaM (Array Expr × Array Expr × Array Expr) := do
  let mut restL := lhs
  let mut matched : Array Expr := #[]
  let mut restR : Array Expr := #[]
  for atom in rhs do
    match ← restL.findIdxM? (fun cand =>
        withoutModifyingMCtx (isDefEq atom (if strip then (stripOfProp cand).2 else cand))) with
    | some idx =>
      matched := matched.push restL[idx]!
      restL := restL.eraseIdxIfInBounds idx
    | none => restR := restR.push atom
  return (matched, restL, restR)

/-- Cancel the `cancel` atoms from `pre`'s atoms by `isDefEq` against each candidate's spatial
remainder (so a pure-fact-carrying `pre` atom still matches). Returns `(leftover, matched)`, or
`none` if some `cancel` atom has no match. -/
def matchSepAtoms (pre cancel : Expr) : MetaM (Option (Array Expr × Array Expr)) := do
  let (matched, restL, restR) ← cancelSepAtoms (← sepAtoms pre) (← sepAtoms cancel) (strip := true)
  return if restR.isEmpty then some (restL, matched) else none

/-- Prove `pre ⊑ rhs` when the two are defeq or AC-equal separating conjunctions: close `pre = rhs`
by `∗`-AC-rearrangement, then lift through `PartialOrder.rel_of_eq`. `none` if AC can't normalize. -/
def proveSepConjLe (pre rhs : Expr) : MetaM (Option Expr) := do
  if ← isDefEq pre rhs then
    return some (← mkAppM ``Lean.Order.PartialOrder.rel_of_eq #[← mkEqRefl pre])
  let eqMVar ← mkFreshExprSyntheticOpaqueMVar (← mkEq pre rhs)
  try
    Lean.Meta.AC.rewriteUnnormalizedRefl eqMVar.mvarId!
    return some (← mkAppM ``Lean.Order.PartialOrder.rel_of_eq #[← instantiateMVars eqMVar])
  catch _ =>
    return none

/-- The `FrameSplit` cancelling `frame` off the precondition: the split VC `pre ⊑ frame ∗ footprint`
(proved by AC-rearrangement of `∗`) composed by right-monotonicity with the emitted residual subgoal
`footprint ⊑ residualPre`. Falls back to a deferred split VC when the AC proof fails. -/
def mkSepFrameSplit (i : FrameInferenceInfo) (V frame footprint : Expr) : SymM FrameSplit := do
  -- `.appArg!` reads the `frame ∗ ·` right-hand side off the split VC `mkSplitVCS` builds.
  let sepFF := (← i.mkSplitVCS frame footprint).appArg!
  match ← proveSepConjLe (← i.pre) sepFF with
  | none => FrameSplit.withDeferredSplitVC i frame
  | some hcl =>
    let le ← i.le
    let residualPre ← i.mkResidualPre
    let residualPreE := mkMVar residualPre
    let sepFR := (← i.mkSplitVCS frame residualPreE).appArg!
    let sub ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS le #[footprint, residualPreE])
    let mono ← mkAppNS (← mkConstS ``sepConj_mono_r) #[V, frame, footprint, residualPreE, sub]
    let args := le.getAppArgs
    let proof ← mkAppNS (← mkConstS ``Lean.Order.PartialOrder.rel_trans le.getAppFn.constLevels!)
      #[args[0]!, args[1]!, ← i.pre, sepFF, sepFR, hcl, mono]
    return FrameSplit.withDischargedSplitVC frame residualPre proof [sub.mvarId!]

/-- Automatic frame inference by domain difference: cancel the spec footprint (or an explicit
`frames` resource) from the actual precondition; the leftover atoms are the frame, the matched atoms
the footprint. -/
def sepConjFrameProc : FrameInferenceProc := fun i => do
  let V := i.Pred.appArg!
  match i.providedFrame? with
  | some frame =>
    match ← matchSepAtoms (← i.pre) frame with
    | none => return some (← FrameSplit.withDeferredSplitVC i frame)
    | some (rest, _) => return some (← mkSepFrameSplit i V frame (← sepConjOfAtoms V rest))
  | none =>
    let some specPre ← i.specPre? | return none
    let some (rest, matched) ← matchSepAtoms (← i.pre) specPre | return none
    if rest.isEmpty then return none
    return some (← mkSepFrameSplit i V (← sepConjOfAtoms V rest) (← sepConjOfAtoms V matched))

/-- Register `∗`-framing for `HeapM`. -/
@[frameproc] def heapFP : FrameProc where
  prog := ``HeapM
  opHead := ``sepConj
  mkOpAppM := fun info => Lean.Meta.mkAppOptM ``sepConj #[info.Pred.appArg!]
  mkResourceTy := fun info => pure info.Pred
  proc := sepConjFrameProc

end FrameProc

/-! ## Store singleton lemmas + grind registration -/

@[grind] theorem Store.disjoint_single_iff (s : Store V) (a : Nat) (v : V) :
    s.disjoint (Store.single a v) ↔ s a = none := by
  constructor
  · intro h; rcases h a with h1 | h2
    · exact h1
    · simp [Store.single] at h2
  · intro h n; by_cases hn : n = a
    · subst hn; exact Or.inl h
    · right; simp [Store.single, hn]

theorem Store.single_disjoint_single {a b : Nat} (v w : V) (h : a ≠ b) :
    (Store.single a v).disjoint (Store.single b w) := by
  intro n; by_cases hn : n = a
  · right; simp [Store.single, hn, h]
  · left; simp [Store.single, hn]

attribute [grind] emp_sepConj sepConj_comm sepConj_assoc sepConj_frame_r
  Store.single_disjoint_single

/-! ## Floating pure facts out of `∗` (so `vcgen`'s `simplifying_assumptions` lifts read values) -/

theorem hprop_ofProp_apply (p : Prop) (s : Store V) : (⌜p⌝ : HProp V) s = p := by
  show (⌜p⌝ : Store V → Prop) s = p
  rw [Lean.Order.CompleteLattice.ofProp_apply]; exact ofProp_prop_eq p

theorem hprop_meet_apply (P Q : HProp V) (s : Store V) : (P ⊓ Q) s = (P s ∧ Q s) :=
  (meet_apply (β := fun _ : Store V => Prop) P Q s).trans (meet_prop_eq_and (P s) (Q s))

@[simp, grind] theorem sepConj_ofProp_meet_left (p : Prop) (Q R : HProp V) :
    (⌜p⌝ ⊓ Q) ∗ R = ⌜p⌝ ⊓ (Q ∗ R) := by
  funext s
  simp only [sepConj, hprop_meet_apply, hprop_ofProp_apply]
  apply propext
  constructor
  · rintro ⟨s₁, s₂, hd, he, ⟨hp, hq⟩, hr⟩; exact ⟨hp, s₁, s₂, hd, he, hq, hr⟩
  · rintro ⟨hp, s₁, s₂, hd, he, hq, hr⟩; exact ⟨s₁, s₂, hd, he, ⟨hp, hq⟩, hr⟩

@[simp, grind] theorem sepConj_ofProp_meet_right (p : Prop) (Q R : HProp V) :
    Q ∗ (⌜p⌝ ⊓ R) = ⌜p⌝ ⊓ (Q ∗ R) := by
  funext s
  simp only [sepConj, hprop_meet_apply, hprop_ofProp_apply]
  apply propext
  constructor
  · rintro ⟨s₁, s₂, hd, he, hq, ⟨hp, hr⟩⟩; exact ⟨hp, s₁, s₂, hd, he, hq, hr⟩
  · rintro ⟨hp, s₁, s₂, hd, he, hq, hr⟩; exact ⟨s₁, s₂, hd, he, hq, ⟨hp, hr⟩⟩

-- `scoped` (not `local`): active in any file that `open PastaLean`, so heap-proof files float the
-- `⌜·⌝` read-value facts out of `∗` (value-returning reads) with no per-file boilerplate.
attribute [scoped sym_simp]
  sepConj_ofProp_meet_left sepConj_ofProp_meet_right
  Lean.Order.CompleteLattice.ofProp_intro_l Lean.Order.CompleteLattice.ofProp_intro_r

-- `finish` is grind, which ignores the `@[simp]` `+ₚ`→`+` reductions and the `⌜·⌝` order lemma;
-- expose them (scoped to `PastaLean`) so value/loop VCs close without naming them per proof.
attribute [scoped grind] Lean.Order.le_ofProp
attribute [scoped grind =]
  pyAdd_int pySub_int pyMul_int pyAdd_rat pySub_rat pyMul_rat pyDiv_rat
  List.length_range List.append_eq_nil_iff

/-! ## Leaf specifications (proved by hand), then automatic framing for composed programs -/

@[spec] theorem writeRef_spec [Storable V α] (r : Ref α) (v w : α) :
    ⦃ (r ↦ v : HProp V) ⦄ writeRef r w ⦃ fun _ => r ↦ w ⦄ := by
  constructor
  show (r ↦ v) ⊑ PreservesSup.frameClosure sepConj
    (fun Q' => (storeWP _).wpTrans (writeRef r w) |>.apply Q' ⊥) (fun _ => r ↦ w)
  refine (PreservesSup.le_frameClosure_iff sepConj _).mpr fun F => ?_
  intro s hpre nx hwf
  obtain ⟨sF, s₂, hd, rfl, hF, hpts⟩ := hpre
  simp only [pointsTo, pointsToRaw] at hpts
  subst hpts
  simp only [writeRef, HeapM.run, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, MonadState.modifyGet]
  refine ⟨sF, Store.single r.addr (Storable.inject w), ?_, ?_, hF, rfl⟩
  · intro n; rcases hd n with h1 | h2
    · exact Or.inl h1
    · right; simp only [Store.single] at h2 ⊢; grind
  · funext n
    simp only [Store.update, Store.union, Store.single]
    by_cases hn : n = r.addr
    · subst hn; have := hd r.addr; simp only [Store.single] at this; grind
    · simp [hn]

@[spec] theorem readRef_spec [Storable V α] (r : Ref α) (v : α) :
    ⦃ (r ↦ v : HProp V) ⦄ readRef r ⦃ fun x => ⌜x = v⌝ ⊓ (r ↦ v) ⦄ := by
  constructor
  show (r ↦ v) ⊑ PreservesSup.frameClosure sepConj
    (fun Q' => (storeWP _).wpTrans (readRef r) |>.apply Q' ⊥) (fun x => ⌜x = v⌝ ⊓ (r ↦ v))
  refine (PreservesSup.le_frameClosure_iff sepConj _).mpr fun F => ?_
  intro s hpre nx hwf
  obtain ⟨sF, s₂, hd, rfl, hF, hpts⟩ := hpre
  simp only [pointsTo, pointsToRaw] at hpts
  subst hpts
  have hFnone : sF r.addr = none := by
    rcases hd r.addr with h1 | h2
    · exact h1
    · simp only [Store.single] at h2; grind
  have hlook : (sF.union (Store.single r.addr (Storable.inject v))) r.addr
      = some (Storable.inject v) := by
    simp only [Store.union, Store.single, hFnone]; rfl
  have htop : (⌜True⌝ : HProp V) ⊓ (r ↦ v) = (r ↦ v) := by
    rw [show (⌜True⌝ : HProp V) = (⊤ : HProp V) by simp [Lean.Order.CompleteLattice.ofProp]]
    exact Std.Internal.Do.CompleteLattice.top_meet
  simp only [readRef, HeapM.run, bind, MonadStateOf.get, getThe, MonadState.get, get,
    EStateM.get, EStateM.bind, EStateM.pure, pure, hlook, Storable.project_inject]
  rw [htop]
  exact ⟨sF, Store.single r.addr (Storable.inject v), hd, rfl, hF, rfl⟩

theorem alloc_spec [Storable V α] (v : α) :
    ⦃ (emp : HProp V) ⦄ alloc v ⦃ fun r => r ↦ v ⦄ := by
  constructor
  show emp ⊑ PreservesSup.frameClosure sepConj
    (fun Q' => (storeWP _).wpTrans (alloc v) |>.apply Q' ⊥) (fun r => r ↦ v)
  refine (PreservesSup.le_frameClosure_iff sepConj _).mpr fun F => ?_
  intro s hpre nx hwf
  obtain ⟨sF, sE, hd, rfl, hF, hemp⟩ := hpre
  simp only [emp] at hemp
  simp only [alloc, HeapM.run, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    MonadState.modifyGet]
  have hfresh : sF nx = none := by
    have := hwf nx (Nat.le_refl nx); simp only [Store.union_none_iff] at this; exact this.1
  refine ⟨sF, Store.single nx (Storable.inject v),
    (Store.disjoint_single_iff _ _ _).mpr hfresh, ?_, hF, rfl⟩
  funext n; simp only [Store.update, Store.union, Store.single]
  by_cases hn : n = nx
  · subst hn; simp [hfresh]
  · simp [hn, hemp n]

/-- Frame-carrying `alloc` spec (the registered `@[spec]`): allocating a fresh cell preserves any
ambient `P` (the new address is provably fresh for the whole heap via `wf`). -/
@[spec] theorem alloc_frame_spec [Storable V α] (P : HProp V) (v : α) :
    ⦃ P ⦄ alloc v ⦃ fun r => P ∗ r ↦ v ⦄ := by
  constructor
  show P ⊑ PreservesSup.frameClosure sepConj
    (fun Q' => (storeWP _).wpTrans (alloc v) |>.apply Q' ⊥) (fun r => P ∗ r ↦ v)
  refine (PreservesSup.le_frameClosure_iff sepConj _).mpr fun F => ?_
  intro s hpre nx hwf
  obtain ⟨sF, sP, hd, rfl, hF, hP⟩ := hpre
  simp only [alloc, HeapM.run, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    MonadState.modifyGet]
  obtain ⟨hFn, hPn⟩ := (Store.union_none_iff sF sP nx).mp (hwf nx (Nat.le_refl nx))
  refine ⟨sF, sP.union (Store.single nx (Storable.inject v)),
    Store.disjoint_union_right.mpr ⟨hd, (Store.disjoint_single_iff _ _ _).mpr hFn⟩, ?_, hF,
    sP, Store.single nx (Storable.inject v),
    (Store.disjoint_single_iff _ _ _).mpr hPn, rfl, hP, rfl⟩
  funext n; simp only [Store.update, Store.union, Store.single]
  by_cases hn : n = nx
  · subst hn; simp [hFn, hPn]
  · simp [hn]

@[spec] theorem modifyRef_spec [Storable V α] (r : Ref α) (f : α → α) (a : α) :
    ⦃ (r ↦ a : HProp V) ⦄ modifyRef r f ⦃ fun _ => r ↦ (f a) ⦄ := by
  vcgen [modifyRef, readRef_spec, writeRef_spec] simplifying_assumptions with finish

/-! ## Monad-polymorphic `…M` delegators (the codegen gap)

Generated `--heap` code emits `readRefM`/`writeRefM`/`allocM`/`modifyRefM` (the rewired `~>`/`<~`
notation), which are *defeq* to the raw ops but not *syntactically* the same head, so `vcgen`'s spec
matching won't fire the raw `@[spec]`s. In a `HeapM V` body the lift is the identity, so each `…M`
op reduces to its raw op; these delegator `@[spec]`s expose the same triples under the emitted head. -/

@[spec] theorem readRefM_spec [Storable V α] (r : Ref α) (v : α) :
    ⦃ (r ↦ v : HProp V) ⦄ (readRefM (m := HeapM V) r) ⦃ fun x => ⌜x = v⌝ ⊓ (r ↦ v) ⦄ := by
  unfold readRefM; exact readRef_spec r v

@[spec] theorem writeRefM_spec [Storable V α] (r : Ref α) (v w : α) :
    ⦃ (r ↦ v : HProp V) ⦄ (writeRefM (m := HeapM V) r w) ⦃ fun _ => r ↦ w ⦄ := by
  unfold writeRefM; exact writeRef_spec r v w

@[spec] theorem allocM_frame_spec [Storable V α] (P : HProp V) (v : α) :
    ⦃ P ⦄ (allocM (m := HeapM V) v) ⦃ fun r => P ∗ r ↦ v ⦄ := by
  unfold allocM; exact alloc_frame_spec P v

@[spec] theorem modifyRefM_spec [Storable V α] (r : Ref α) (f : α → α) (a : α) :
    ⦃ (r ↦ a : HProp V) ⦄ (modifyRefM (m := HeapM V) r f) ⦃ fun _ => r ↦ (f a) ⦄ := by
  unfold modifyRefM; exact modifyRef_spec r f a

/-! ## Validation: composed programs closed by automatic framing (`vcgen … with finish`) -/

/-- A write frames a disjoint cell (`r2 ↦ b`) with no manual separation reasoning. -/
example [Storable V α] (r1 r2 : Ref α) (a b x : α) :
    ⦃ (r1 ↦ a ∗ r2 ↦ b : HProp V) ⦄ writeRef r1 x ⦃ fun _ => r1 ↦ x ∗ r2 ↦ b ⦄ := by
  vcgen [writeRef_spec] with finish

/-- `append` reads two refs and overwrites the first with the concatenation. -/
def append [Storable V (List α)] (listRef otherRef : Ref (List α)) : HeapM V Unit := do
  let l1 ← readRef listRef
  let l2 ← readRef otherRef
  writeRef listRef (l1 ++ l2)

/-- Composed spec: the read values thread through as pure facts and the second cell (`otherRef ↦ l2`)
frames automatically across the read of `listRef` and the write — no by-hand separation reasoning. -/
theorem append_spec [Storable V (List α)] (listRef otherRef : Ref (List α)) (l1 l2 : List α) :
    ⦃ (listRef ↦ l1 ∗ otherRef ↦ l2 : HProp V) ⦄ append listRef otherRef
    ⦃ fun _ => listRef ↦ (l1 ++ l2) ∗ otherRef ↦ l2 ⦄ := by
  vcgen [append, readRef_spec, writeRef_spec] simplifying_assumptions with finish

/-- The emitted `…M` heads (generated `~>`/`<~` code) compose and frame automatically, exactly as the
raw ops do — this guards the codegen-gap delegators (`readRefM_spec`/`writeRefM_spec`) against a
future break in `vcgen`'s head-matching. `incM` mirrors the read-modify-write a `self.x = f(self.x)`
translates to; `r2 ↦ b` frames across it with no by-hand separation reasoning. -/
def incM [Storable V α] (r : Ref α) (f : α → α) : HeapM V Unit := do
  writeRefM r (f (← readRefM r))

example [Storable V α] (r1 r2 : Ref α) (a b : α) (f : α → α) :
    ⦃ (r1 ↦ a ∗ r2 ↦ b : HProp V) ⦄ incM r1 f
    ⦃ fun _ => r1 ↦ (f a) ∗ r2 ↦ b ⦄ := by
  vcgen [incM, readRefM_spec, writeRefM_spec] simplifying_assumptions with finish

/-! ## While-loop support: a `MonadTail (HeapM V)` instance

`vcgen` reasons about a `while` (desugared to `Lean.Loop.forIn`/`repeatM`) through `Spec.forIn_loop`,
which requires `[MonadTail m]` — i.e. `HeapM V` must be a fixed-point-friendly monad (a `CCPO` with
monotone `bind`). `EStateM` has no canonical `CCPO` (its bottom would have to be state-dependent), so
we give it one with a **single fixed bottom** (`error` at an arbitrary `Nonempty` state), which is all
`MonadTail` needs. `Heap V` is `Nonempty` via `emptyHeap`, so the `HeapM V = EStateM PyException
(Heap V)` lift is `inferInstanceAs`. -/

/-- A single fixed bottom for `EStateM` (an `error` at arbitrary `Nonempty` witnesses), **not**
state-indexed — enough to make `EStateM` a `CCPO` for `MonadTail`'s fixed-point machinery. -/
noncomputable def EStateM.botR {ε σ α : Type} [Nonempty ε] [Nonempty σ] : EStateM.Result ε σ α :=
  EStateM.Result.error Classical.ofNonempty Classical.ofNonempty

instance EStateM.instCCPO {ε σ α : Type} [Nonempty ε] [Nonempty σ] : CCPO (EStateM ε σ α) where
  rel := PartialOrder.rel (α := ∀ _ : σ, FlatOrder (EStateM.botR (ε := ε) (σ := σ) (α := α)))
  rel_refl := PartialOrder.rel_refl
  rel_antisymm := PartialOrder.rel_antisymm
  rel_trans := PartialOrder.rel_trans
  has_csup hchain :=
    CCPO.has_csup (α := ∀ _ : σ, FlatOrder (EStateM.botR (ε := ε) (σ := σ) (α := α))) hchain

instance EStateM.instMonoBind {ε σ : Type} [Nonempty ε] [Nonempty σ] : MonoBind (EStateM ε σ) where
  bind_mono_left {_ _ a₁ a₂ f} h₁₂ := by
    intro s
    specialize h₁₂ s
    change FlatOrder.rel (EStateM.bind a₁ f s) (EStateM.bind a₂ f s)
    simp only [EStateM.bind]
    generalize a₁ s = a₁ at h₁₂; generalize a₂ s = a₂ at h₁₂
    cases h₁₂
    · exact .bot
    · exact .refl
  bind_mono_right {_ _ a f₁ f₂} h₁₂ := by
    intro w
    change FlatOrder.rel (EStateM.bind a f₁ w) (EStateM.bind a f₂ w)
    simp only [EStateM.bind]
    split
    · exact h₁₂ _ _
    · exact .refl

instance EStateM.instMonadTail {ε σ : Type} [Nonempty ε] [Nonempty σ] :
    Lean.Order.MonadTail (EStateM ε σ) where
  instCCPO _ := inferInstance
  bind_mono_right h := MonoBind.bind_mono_right h

instance instHeapNonempty : Nonempty (Heap V) := ⟨emptyHeap⟩

instance instHeapMCCPO : CCPO (HeapM V α) := inferInstanceAs (CCPO (HeapBase V α))

instance instHeapMMonoBind : MonoBind (HeapM V) := inferInstanceAs (MonoBind (HeapBase V))

instance instHeapMMonadTail : Lean.Order.MonadTail (HeapM V) :=
  inferInstanceAs (Lean.Order.MonadTail (HeapBase V))

/-! ## Separating pure facts (`⌜φ⌝ ⊓ emp`) — carry loop bounds as `∗`-atoms in while invariants

A `while` loop invariant that constrains the counter (`i ≤ k`) must carry that bound *and* stay in a
shape the `@[frameproc]` can cancel `↦` out of. Wrapping the whole invariant in `⌜φ⌝ ⊓ ·` buries the
`↦` atom (no `∗` to rearrange), so instead the bound rides as a separating conjunct `∗ sepPure φ`:
the `↦` stays a clean `∗`-atom the frame procedure cancels, while the pure fact frames. -/

/-- Iris-style separating pure: the heap is empty *and* `φ` holds. Kept a (reducible) `abbrev` so
`vcgen`'s `sym_simp` floats the `⌜·⌝` out of `∗` exactly as for a bare `⌜φ⌝ ⊓ emp`. -/
noncomputable abbrev sepPure (φ : Prop) : HProp V := ⌜φ⌝ ⊓ emp

theorem sepPure_apply (φ : Prop) (s : Store V) : sepPure φ s ↔ φ ∧ emp s := by
  simp only [sepPure, hprop_meet_apply, hprop_ofProp_apply]

/-- `sepPure P ∗ Q` floats `P` out as a pure fact and leaves `Q`. -/
theorem sepPure_sepConj_iff (P : Prop) (Q : HProp V) (s : Store V) :
    (sepPure P ∗ Q) s ↔ P ∧ Q s := by
  rw [sepPure, sepConj_ofProp_meet_left, emp_sepConj]
  simp only [hprop_meet_apply, hprop_ofProp_apply]

@[grind =] theorem sepPure_true_eq_emp : (sepPure True : HProp V) = emp := by
  funext s; apply propext; simp [sepPure_apply]

/-- Attach a provable pure fact as a separating conjunct. -/
theorem le_sepConj_sepPure (P : HProp V) (φ : Prop) (hφ : φ) : P ⊑ P ∗ sepPure φ := by
  intro s hs
  rw [sepConj_comm]
  exact (sepPure_sepConj_iff φ P s).mpr ⟨hφ, hs⟩

/-- Attach a provable pure fact as a *leading* separating conjunct. -/
theorem le_sepPure_sepConj (φ : Prop) (hφ : φ) (P : HProp V) : P ⊑ sepPure φ ∗ P := by
  rw [sepConj_comm]; exact le_sepConj_sepPure P φ hφ

/-- Drop a separating pure conjunct (its fact is discarded). -/
theorem sepConj_sepPure_le (P : HProp V) (φ : Prop) : (P ∗ sepPure φ) ⊑ P := by
  intro s hs
  rw [sepConj_comm] at hs
  exact ((sepPure_sepConj_iff φ P s).mp hs).2

/-- A refuted separating pure conjunct proves anything: the branch is unreachable. -/
theorem sepPure_sepConj_le_of_not {φ : Prop} (hφ : ¬φ) (Q R : HProp V) : (sepPure φ ∗ Q) ⊑ R :=
  fun s hs => absurd ((sepPure_sepConj_iff φ Q s).mp hs).1 hφ

/-- Consume a separating pure conjunct, exposing its fact to prove the remainder. -/
theorem sepPure_conj_elim {P Q : HProp V} {φ : Prop} (h : φ → P ⊑ Q) : (P ∗ sepPure φ) ⊑ Q := by
  intro s hs
  rw [sepConj_comm] at hs
  obtain ⟨hφ, hP⟩ := (sepPure_sepConj_iff φ P s).mp hs
  exact h hφ s hP

/-! ## Pointwise `⨆` on `HProp` -/

/-- Pointwise characterization of the lattice `⨆` on `HProp V`. -/
theorem iSup_hprop_apply {ι : Type} (P : ι → HProp V) (s : Store V) :
    (Lean.Order.iSup P) s ↔ ∃ i, (P i) s := by
  unfold Lean.Order.iSup
  rw [hprop_sup_apply]
  constructor
  · rintro ⟨f, ⟨i, rfl⟩, hf⟩; exact ⟨i, hf⟩
  · rintro ⟨i, hi⟩; exact ⟨P i, ⟨i, rfl⟩, hi⟩

/-! ## Heap-resident loop measures

The stock `RepeatVariant` (Lean PR #14507) is a structure whose `EvalsTo : α → γ → Pred` relates a
cursor to a measure value *inside the assertion lattice*, so the measure may read the heap — e.g. the
remaining spine length of a linked list being reversed in place. Its `total` law demands that every
store pin some value, which no store-constraining assertion satisfies on its own; `ofHeapRel`
supplies the missing default. -/

/-- Build a `RepeatVariant` from a relational, heap-reading measure `real a n` ("at cursor `a` the
measure is `n`"). Stores where `real` pins no value admit every value — that is what makes `total`
hold; the loop invariant rules that case out again at each step (`ofHeapRel_pin`). -/
noncomputable def RepeatVariant.ofHeapRel {α : Type} (real : α → Nat → HProp V) :
    Std.Internal.Do.RepeatVariant α (HProp V) where
  γ := Nat
  EvalsTo a n := fun s => real a n s ∨ ∀ m, ¬ real a m s
  total a := PartialOrder.rel_antisymm (le_top _) <| by
    intro s _
    refine (iSup_hprop_apply _ s).mpr ?_
    by_cases h : ∃ m, real a m s
    · obtain ⟨m, hm⟩ := h
      exact ⟨m, Or.inl hm⟩
    · exact ⟨0, Or.inr (fun m hm => h ⟨m, hm⟩)⟩

/-- Elimination: where the measure *is* pinned somewhere, `EvalsTo a n` pins it at `n`. -/
theorem RepeatVariant.ofHeapRel_pin {α : Type} (real : α → Nat → HProp V)
    {a : α} {n : Nat} {s : Store V} (hsome : ∃ m, real a m s)
    (h : (ofHeapRel real).EvalsTo a n s) : real a n s :=
  h.resolve_right (fun hno => hsome.elim fun m hm => hno m hm)

/-- `EvalsBelow` at `ofHeapRel`: pin the measure at any strictly smaller `n'`. -/
theorem RepeatVariant.ofHeapRel_evalsBelow {α : Type} (real : α → Nat → HProp V)
    {a : α} {n' n : Nat} {s : Store V} (hlt : n' < n) (h : real a n' s) :
    (ofHeapRel real).EvalsBelow a n s := by
  refine (iSup_hprop_apply _ s).mpr ⟨n', ?_⟩
  exact (hprop_meet_apply _ _ s) ▸ ⟨Or.inl h, (hprop_ofProp_apply _ s) ▸ hlt⟩

/-- Peel the step precondition of `Spec.forIn_loop` at `ofHeapRel`: an invariant of the shape
`⨆ n, real a n` witnesses that the measure is pinned somewhere, which kills the default disjunct. -/
theorem RepeatVariant.ofHeapRel_meet_le {α : Type} (real : α → Nat → HProp V) (a : α) (n : Nat) :
    ((ofHeapRel real).EvalsTo a n ⊓ iSup (real a)) ⊑ real a n := by
  intro s hs
  rw [hprop_meet_apply] at hs
  exact ofHeapRel_pin real ((iSup_hprop_apply _ s).mp hs.2) hs.1

/-! ### `Spec.forIn_loop` at a heap-resident measure

`forIn_loop_heapRel` packages the `ofHeapRel` boilerplate every heap loop would otherwise repeat: the
caller states only the measure relation `real` and the break assertion `done`, and the loop's
in-progress invariant *is* `⨆ n, real b n`, so `ofHeapRel_meet_le` collapses the stock rule's
`EvalsTo b n ⊓ inv (.inl b)` down to a bare `real b n` before the step ever sees it. -/

/-- A heap-reading relational termination measure on a loop cursor: `real b n` asserts "at cursor `b`
the measure is `n`". The first invariant hole of `forIn_loop_heapRel`. -/
@[spec_invariant_type] def HeapRel (V : Type) (β : Type) : Type := β → Nat → HProp V

/-- `HeapRel` as a function; see `PureMeasure.toFun` for why the coercion is spelled out. -/
def HeapRel.toFun {β : Type} (real : HeapRel V β) : β → Nat → HProp V := real

/-- What holds once a `forIn_loop_heapRel` loop breaks: the second invariant hole. -/
@[spec_invariant_type] def HeapDone (V : Type) (β : Type) : Type := β → HProp V

/-- `HeapDone` as a function; see `PureMeasure.toFun`. -/
def HeapDone.toFun {β : Type} (done : HeapDone V β) : β → HProp V := done

/-- Rebuild the yield postcondition of `forIn_loop_heapRel` at a strictly smaller measure value. -/
theorem le_yieldBelow {β : Type} (real : β → Nat → HProp V) {b : β} {n' n : Nat} (h : n' < n) :
    real b n' ⊑ ⨆ m : Nat, (real b m ⊓ (⌜m < n⌝ : HProp V)) := by
  intro s hs
  refine (iSup_hprop_apply _ s).mpr ⟨n', ?_⟩
  exact (hprop_meet_apply _ _ s) ▸ ⟨hs, (hprop_ofProp_apply _ s) ▸ h⟩

/-- The `RepeatInvariant` implied by a `HeapRel`/`HeapDone` pair. -/
noncomputable def heapRelInv {β : Type} (real : β → Nat → HProp V) (done : β → HProp V) :
    RepeatInvariant β β (HProp V)
  | .inl b => iSup (real b)
  | .inr b => done b

/-- `Spec.forIn_loop` specialised to a heap-resident measure relation. -/
theorem forIn_loop_heapRel {β : Type} {l : Lean.Loop} {init : β}
    {f : Unit → β → HeapM V (ForInStep β)}
    (real : HeapRel V β) (done : HeapDone V β) (einv : HeapEPred V)
    (step : ∀ b n, Triple (f () b) (real b n)
      (fun r => match r with
        | .yield b' => ⨆ n' : Nat, (real b' n' ⊓ (⌜n' < n⌝ : HProp V))
        | .done b' => done b') einv) :
    Triple (forIn l init f) (iSup (real init)) (fun b => done b) einv := by
  refine Spec.forIn_loop (measure := RepeatVariant.ofHeapRel real.toFun)
    (inv := heapRelInv real.toFun done.toFun) einv ?_
  intro b (n : Nat)
  simp only [heapRelInv]
  refine Triple.intro (Triple.entails_wp_of_pre_post (step b n)
    (RepeatVariant.ofHeapRel_meet_le real.toFun b n) ?_)
  intro r
  cases r with
  | done b' => exact PartialOrder.rel_refl
  | yield b' =>
    show (⨆ n' : Nat, (real b' n' ⊓ (⌜n' < n⌝ : HProp V)))
      ⊑ (RepeatVariant.ofHeapRel real.toFun).EvalsBelow b' n ⊓ iSup (real.toFun b')
    intro s hs
    rw [iSup_hprop_apply] at hs
    obtain ⟨n', hn'⟩ := hs
    rw [hprop_meet_apply, hprop_ofProp_apply] at hn'
    rw [hprop_meet_apply]
    exact ⟨RepeatVariant.ofHeapRel_evalsBelow real.toFun hn'.2 hn'.1,
      (iSup_hprop_apply _ s).mpr ⟨n', hn'.1⟩⟩

/-- `forIn_loop_heapRel` at the shape a translated `--heap` `while`-function actually has: an entry
entailment into the measure, the loop, and a trailing `return (k cursor)`. -/
theorem forIn_loop_heapRel_pure {β γ : Type} {l : Lean.Loop} {init : β}
    {f : Unit → β → HeapM V (ForInStep β)} {P : HProp V} {Q : γ → HProp V}
    (real : HeapRel V β) (k : β → γ) (einv : HeapEPred V)
    (hpre : P ⊑ iSup (real init))
    (step : ∀ b n, Triple (f () b) (real b n)
      (fun r => match r with
        | .yield b' => ⨆ n' : Nat, (real b' n' ⊓ (⌜n' < n⌝ : HProp V))
        | .done b' => Q (k b')) einv) :
    Triple ((do let b ← forIn l init f; pure (k b)) : HeapM V γ) P Q einv := by
  refine Triple.bind _ _ (fun b => Q (k b)) ?hx ?hf
  case hf => exact fun b => Triple.pure (k b) PartialOrder.rel_refl
  case hx =>
    exact Triple.intro (PartialOrder.rel_trans hpre
      (forIn_loop_heapRel real (fun b => Q (k b)) einv step).le_wp)

/-! ## Pure loop measures under framing

The stock `Spec.forIn_loop` hands the measure pin `⌜measure b = mb⌝` to the step *inside* the
precondition, where the frame procedure discards it along with everything else outside the
footprint — leaving the yield branch's `EvalsBelow b' mb` unprovable, since nothing then ties the
abstract `mb` to the cursor. Non-separating clients never see this: at `Pred = σ → Prop` the whole
precondition is lifted into the local context as a hypothesis instead. `forIn_loop_measure`
discharges the pin up front, so the step is left with the frame-friendly `⌜measure b' < measure b⌝`.
-/

/-- A pure `Nat` termination measure on the loop cursor: the second invariant hole of
`forIn_loop_measure`. -/
@[spec_invariant_type] def PureMeasure (β : Type) : Type := β → Nat

/-- `PureMeasure` as a function; unlike the bare coercion this stays type-correct under `implicit`
transparency, which `simp` checks. -/
def PureMeasure.toFun {β : Type} (measure : PureMeasure β) : β → Nat := measure

/-- `Spec.forIn_loop` specialised to a pure cursor measure, with the measure pin discharged. -/
theorem forIn_loop_measure {β : Type} {l : Lean.Loop} {init : β}
    {f : Unit → β → HeapM V (ForInStep β)}
    (measure : PureMeasure β) (inv : RepeatInvariant β β (HProp V)) (einv : HeapEPred V)
    (step : ∀ b, Triple (f () b) (inv (.inl b))
      (fun r => match r with
        | .yield b' => (⌜measure b' < measure b⌝ : HProp V) ⊓ inv (.inl b')
        | .done b' => inv (.inr b')) einv) :
    Triple (forIn l init f) (inv (.inl init)) (fun b => inv (.inr b)) einv := by
  refine Spec.forIn_loop (measure := .ofMeasure measure.toFun) inv einv ?_
  intro b mb
  simp only [RepeatVariant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    RepeatVariant.evalsBelow_ofMeasure_nat]
  refine Triple.intro (ofProp_meet_le _ _ _ (fun h => ?_))
  subst h
  exact (step b).le_wp

/-! ## Precondition-shaping helpers (peel `iSup` / `sepPure` off a heap-triple precondition) -/

theorem Triple.iSup_pre {ι : Type} {γ : Type} (P : ι → HProp V)
    (x : HeapM V γ) (Q : γ → HProp V) {epost : HeapEPred V}
    (h : ∀ i, Triple x (P i) Q epost) : Triple x (iSup P) Q epost :=
  Triple.intro (iSup_le _ _ (fun i => (h i).le_wp))

theorem Triple.sepPure_pre {γ : Type} (φ : Prop) (R : HProp V)
    (x : HeapM V γ) (Q : γ → HProp V) {epost : HeapEPred V}
    (h : φ → Triple x R Q epost) : Triple x (sepPure φ ∗ R) Q epost :=
  Triple.intro (fun s hs =>
    have hsplit := (sepPure_sepConj_iff φ R s).mp hs
    (h hsplit.1).le_wp s hsplit.2)

theorem Triple.iSup_sepConj_pre {ι : Type} {γ : Type} (P : ι → HProp V) (R : HProp V)
    (x : HeapM V γ) (Q : γ → HProp V) {epost : HeapEPred V}
    (h : ∀ i, Triple x (P i ∗ R) Q epost) : Triple x (iSup P ∗ R) Q epost := by
  refine Triple.intro (fun s hs => ?_)
  obtain ⟨s₁, s₂, hd, hun, hP, hR⟩ := hs
  rw [iSup_hprop_apply] at hP
  obtain ⟨i, hPi⟩ := hP
  exact (h i).le_wp s ⟨s₁, s₂, hd, hun, hPi, hR⟩

/-! ## Interactive separation-logic tactics -/

section Tactics
open Lean.Meta Lean.Elab.Tactic

/-- The pure fact of a `sepPure φ` atom, folded or in its `⌜φ⌝ ⊓ emp` normal form. -/
def sepPureProp? (e : Expr) : MetaM (Option Expr) := do
  if let .app (.app (.const ``sepPure _) _) φ := e then return some φ
  let_expr Lean.Order.meet _ _ a b := e | return none
  let_expr Lean.Order.CompleteLattice.ofProp _ _ φ := a | return none
  return if b.isAppOf ``emp then some φ else none

/-- Cancel the separating conjuncts shared by both sides of an `HProp` entailment goal, discharge
each `sepPure` on the right as its own side goal, and leave the residual entailment. -/
scoped elab "sl_cancel" : tactic => liftMetaTactic fun goal => do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel α _inst lhs rhs := target
    | throwError "sl_cancel: goal is not an entailment{indentExpr target}"
  let Vm ← mkFreshExprMVar (mkSort (.succ .zero))
  unless ← isDefEq α (mkApp (mkConst ``HProp) Vm) do
    throwError "sl_cancel: not an entailment between `HProp`s{indentExpr α}"
  let V ← instantiateMVars Vm
  let mut pures : Array (Expr × Expr) := #[]
  let mut spatialR : Array Expr := #[]
  for a in ← sepAtoms rhs do
    match ← sepPureProp? a with
    | some φ => pures := pures.push (a, φ)
    | none => spatialR := spatialR.push a
  -- Strict `isDefEq` here (unlike the frameproc): both AC rearrangements below must be provable.
  let (common, restL, restR) ← cancelSepAtoms (← sepAtoms lhs) spatialR (strip := false)
  if common.isEmpty && pures.isEmpty then
    throwError "sl_cancel: no shared conjunct and no pure conjunct{indentExpr target}"
  let commonE := sepConjOfAtomsE V common
  let restLE := sepConjOfAtomsE V restL
  let restRE := sepConjOfAtomsE V restR
  let some h1 ← proveSepConjLe lhs (mkApp3 (mkConst ``sepConj) V commonE restLE)
    | throwError "sl_cancel: cannot rearrange the left-hand side{indentExpr lhs}"
  let mut goals : Array MVarId := #[]
  let sub ← match ← proveSepConjLe restLE restRE with
    | some p => pure p
    | none =>
      mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Lean.Order.PartialOrder.rel #[restLE, restRE])
  let h2 ← mkAppM ``sepConj_frame_l #[commonE, restLE, restRE, sub]
  let mut cur := mkApp3 (mkConst ``sepConj) V commonE restRE
  let mut chain := h2
  for (atom, φ) in pures.reverse do
    let hφ ← mkFreshExprSyntheticOpaqueMVar φ
    goals := goals.push hφ.mvarId!
    chain ← mkAppM ``Lean.Order.PartialOrder.rel_trans
      #[chain, ← mkAppM ``le_sepPure_sepConj #[φ, hφ, cur]]
    cur := mkApp3 (mkConst ``sepConj) V atom cur
  let some h3 ← proveSepConjLe cur rhs
    | throwError "sl_cancel: cannot rearrange the right-hand side{indentExpr rhs}"
  goal.assign (← mkAppM ``Lean.Order.PartialOrder.rel_trans
    #[h1, ← mkAppM ``Lean.Order.PartialOrder.rel_trans #[chain, h3]])
  if sub.isMVar then goals := goals.push sub.mvarId!
  return goals.toList

/-- Peel one `iSup` / `sepPure` layer off a heap-triple precondition per `rintro` pattern — the
separation-logic analogue of `iIntros`. -/
scoped syntax (name := slIntro) "sl_intro" (ppSpace colGt rintroPat)+ : tactic

scoped macro_rules
  | `(tactic| sl_intro $p:rintroPat) =>
    `(tactic| first
        | (refine Triple.iSup_pre _ _ _ ?_; rintro $p)
        | (refine Triple.sepPure_pre _ _ _ _ ?_; rintro $p)
        | (refine Triple.iSup_sepConj_pre _ _ _ _ ?_; rintro $p))
  | `(tactic| sl_intro $p:rintroPat $p2:rintroPat $ps:rintroPat*) =>
    `(tactic| (sl_intro $p; sl_intro $p2 $ps*))

end Tactics

end PastaLean
