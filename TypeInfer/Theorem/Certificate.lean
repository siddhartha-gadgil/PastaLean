import TypeInfer.Theorem.Requirements
import TypeInfer.Certificate.Check

/-!
# What an accepted certificate means

`TypeInfer/Certificate/Check.lean` decides, for a program and a certificate, whether the certificate
holds up. This file says what that decision buys — once, so that every accepted certificate inherits
it instead of carrying its own proof.

Both results are proved about **`replayOk`** — the half of `validate` that depends on the certificate
alone — and then restated for `validate`. That split is not cosmetic: `replayOk` touches no `Json`,
no hash and no `Std.HashMap`, so Lean's kernel can evaluate it, which is what lets a single file ship
as a `.lean` whose kernel-check IS its certificate check. The other half of `validate` ties the
certificate to a program, is checked rather than proved, and does not reduce in the kernel.

**`validate_sound`.** If `validate` accepts, then for every slot whose uses the checker narrowed to a
type `t`, every runtime value of type `t` satisfies every use the certificate recorded. So a
committed type is not a guess: it provably works everywhere the slot is used. This is
`hasType_commit` (`Theorem/Requirements.lean`) lifted from one slot's evidence list to a whole
module's certificate.

**`validate_error_sound`.** If `validate` accepts, every diagnostic it carries whose two accused
types are scalars is a *real* error: no runtime value inhabits both. A reported type error is
therefore not merely "the checker disagreed with itself" — it is a value-level impossibility. That is
exactly the claim the seeded-error corpus in `PastaBench/typecheck_bench/negative/` is measuring.

## What these theorems do NOT say

Three limits, all of them load-bearing. State them wherever the certificate is described.

* **The evidence is taken as recorded.** `validate` replays the judgments over the requirement types
  the certificate lists; it confirms a *declared* type against the source, but a `bodyUse` requirement
  cannot be traced back to the expression it was read from, because `usageEvidence` yields a bare
  `List PyType` with no positions. A certificate that invents a plausible body-use requirement is
  accepted. Grounding every requirement in the syntax node that produced it — and proving the rule
  that read it — is the next tier.
* **`HasType` is a model, not Python.** `PyType.Val` (`Theorem/Soundness.lean`) has seven
  constructors and no set, dict, tuple or closure inhabitant, so those lattice heads denote the empty
  set and claims about them are vacuous. `isScalar` below is exactly the fragment where the model has
  real content, which is why `validate_error_sound` is stated over it.
* **Nothing here is about the inference algorithm.** No theorem connects `ofValue`, `typeOfExpr` or
  `inferFunction` to `HasType` — they are `partial def`s with no equation lemmas. A certificate routes
  around that by recording what the engine concluded and having a small validator re-derive the
  verdict from it; it does not make the engine itself verified.
-/

namespace TypeInfer

open Lean
open PyType (Val HasType)

set_option maxHeartbeats 1000000

/-- The fragment of the lattice on which `PyType.Val` has real inhabitants, and the same scalars the
checker is allowed to accuse on (`Pass.lean`'s `isScalarEvidence`). Outside it, a `HasType` claim is
either vacuous (`set`/`dict`/`tuple`/`fn` have no inhabitant in the model) or inhabited by the empty
container, which legitimately satisfies two incompatible element types at once. -/
def isScalar : PyType → Bool
  | .int | .bool | .float | .str | .none => true
  | _ => false

/-! ### Two facts about scalars

Both are finite case analyses over five types and seven value shapes. They are the missing
*introduction* direction of `Theorem/Meet.lean`'s `hasType_meet` — restricted to scalars, where it is
true and provable; the general statement is not attempted here. -/

/-- **Narrowing is complete on scalars:** a value admitted by both `a` and `b` is admitted by their
meet. `Theorem/Meet.lean` proves the elimination direction (`hasType_meet`) on the full lattice; this
is the converse, which the error soundness below needs in order to turn `a ⊓ b = ⊥` into "nothing
inhabits both". -/
theorem hasType_meet_intro_scalar {a b : PyType} (ha : isScalar a = true) (hb : isScalar b = true)
    (v : Val) (h1 : HasType v a) (h2 : HasType v b) : HasType v (PyType.meet a b) := by
  cases a <;> cases b <;> simp_all [isScalar] <;>
    cases v <;> simp_all [HasType, PyType.meet, PyType.beq]

/-- Two scalars that meet at `unknown` have no common inhabitant — the semantic content of a
use-conflict verdict. -/
theorem scalar_meet_unknown_uninhabited {a b : PyType} (ha : isScalar a = true)
    (hb : isScalar b = true) (h : PyType.meet a b = PyType.unknown) (v : Val) :
    ¬ (HasType v a ∧ HasType v b) := by
  rintro ⟨h1, h2⟩
  exact PyType.not_hasType_unknown v (h ▸ hasType_meet_intro_scalar ha hb v h1 h2)

/-- Two inconsistent scalars have no common inhabitant — the semantic content of an
annotation-mismatch verdict. `PyType.consistent` is gradual consistency, not subtyping, so this is
proved directly rather than derived from a subtyping fact. -/
theorem scalar_inconsistent_uninhabited {a b : PyType} (ha : isScalar a = true)
    (hb : isScalar b = true) (h : PyType.consistent a b = false) (v : Val) :
    ¬ (HasType v a ∧ HasType v b) := by
  rintro ⟨h1, h2⟩
  cases a <;> cases b <;> simp_all [isScalar] <;>
    cases v <;> simp_all [HasType, PyType.consistent, PyType.beq]

/-! ### Reading facts off `validate`

`validate` is a conjunction of `Bool` tests, and every equality in it goes through `decide` on the
derived `DecidableEq PyType`, so each conjunct yields a real equation rather than a `BEq` claim with
no lawfulness lemma behind it. -/

theorem slotOk_of_replay {c : Cert} (h : replayOk c = true)
    {s : Slot} (hs : s ∈ c.slots) : slotOk c s = true := by
  simp only [replayOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.2 s hs

theorem backed_of_replay {c : Cert} (h : replayOk c = true)
    {d : Diagnostic} (hd : d ∈ c.diagnostics) : backedDiagnostic c d = true := by
  simp only [replayOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 d hd

theorem replayOk_of_validate {ast : Json} {c : Cert} (h : validate ast c = true) :
    replayOk c = true := by
  simp only [validate, Bool.and_eq_true] at h; exact h.1

/-- A slot that commits a type really did narrow its recorded evidence to it. -/
theorem replay_commits {s : Slot} {t : PyType} (hwf : wellFormedSlot s = true)
    (hr : replaySlot s = true) (hv : s.verdict = .commits t) :
    (Req.ofEvidenceAll s.reqs).commit? = some t := by
  unfold wellFormedSlot at hwf
  unfold replaySlot at hr
  cases hj : s.judgment <;> rw [hj, hv] at hwf hr <;> simp_all

/-! ### Discharging one concrete certificate

`PyType.meet`, `PyType.consistent` and `PyType.beq` are well-founded recursions, so neither `decide`
nor `rfl` can evaluate `replayOk` on a literal certificate — kernel reduction gets stuck on
`WellFounded.fix`. Their *equation lemmas* do reduce, which is what `simp` uses, so this is the
tactic a generated certificate file calls. The resulting proof term is kernel-checked like any other;
`native_decide` is not used anywhere in `TypeInfer/`.

The unfolding set covers both judgments and all five verdicts, so a given certificate will leave some
of it unused — generated files silence `linter.unusedSimpArgs` rather than tailor the list. -/

/-- Prove `replayOk <cert> = true` for a concrete certificate. See
`pastalean typeinfer --emit-proof`. -/
macro "cert_replay " c:ident : tactic =>
  `(tactic| simp [$c:ident, replayOk, slotOk, wellFormedSlot, replaySlot, reportedSlot,
                  backedDiagnostic, sameDiagnostic, Slot.reqs, Slot.failed,
                  Slot.expectedDiagnostic?, certVersion, Req.ofEvidenceAll, Req.narrowAll,
                  Req.narrow, Req.ofEvidence, Req.commit?, Req.top, Req.bot, Req.contradictory,
                  Req.toPyType, checkAnnotation, checkUses, List.head?,
                  PyType.meet, PyType.consistent])

/-! ### The results -/

/-- One slot's claim, semantically. -/
def SlotSound (s : Slot) : Prop :=
  ∀ t, s.verdict = .commits t →
    ∀ v : Val, HasType v t → ∀ r ∈ s.reqs, r ≠ PyType.unknown → HasType v r

/-- Every committed type in the certificate is satisfied by every use recorded for its slot. -/
def CertSound (c : Cert) : Prop := ∀ s ∈ c.slots, SlotSound s

--------------------------------------- LANDMARK ---------------------------------------
/-- **Soundness of an accepted certificate.** If the validator accepts, then wherever the certificate
says a slot's uses narrow to `t`, every runtime value of type `t` satisfies every one of those uses.
The guarantee is proved once, here; each accepted certificate is an instance of it, which is what
makes the artifact worth shipping instead of a proof per file. -/
theorem replay_sound (c : Cert) (h : replayOk c = true) : CertSound c := by
  intro s hs t hv v hvt r hr hrne
  have hok := slotOk_of_replay h hs
  simp only [slotOk, Bool.and_eq_true] at hok
  exact hasType_commit (replay_commits hok.1.1 hok.1.2 hv) hvt r hr hrne

/-- The same, for a certificate checked against its program. -/
theorem validate_sound (ast : Json) (c : Cert) (h : validate ast c = true) : CertSound c :=
  replay_sound c (replayOk_of_validate h)
--------------------------------------- LANDMARK ---------------------------------------

/-- One slot's failure, semantically: the two types it accuses have no common inhabitant. The slot is
destructured so that casing its verdict is not blocked by the hypotheses mentioning it. -/
theorem slot_error_sound : ∀ (s : Slot) (d : Diagnostic),
    wellFormedSlot s = true → replaySlot s = true → s.expectedDiagnostic? = some d →
    isScalar d.expected = true → isScalar d.actual = true →
    ∀ v : Val, ¬ (HasType v d.expected ∧ HasType v d.actual) := by
  intro ⟨scope, name, kind, line, col, judgment, evidence, verdict⟩ d hwf hr hd hde hda v
  -- Only `conflict` and `rejects` produce a diagnostic at all; the other three verdicts refute `hd`.
  cases verdict with
  | commits t => simp [Slot.expectedDiagnostic?] at hd
  | unconstrained => simp [Slot.expectedDiagnostic?] at hd
  | agrees => simp [Slot.expectedDiagnostic?] at hd
  | conflict e a =>
      simp only [Slot.expectedDiagnostic?, Option.some.injEq] at hd
      subst hd
      cases judgment with
      | uses =>
          simp only [replaySlot, Bool.and_eq_true, decide_eq_true_eq] at hr
          exact scalar_meet_unknown_uninhabited hde hda hr.2 v
      | declared ann => simp [wellFormedSlot] at hwf
  | rejects e a =>
      simp only [Slot.expectedDiagnostic?, Option.some.injEq] at hd
      subst hd
      cases judgment with
      | uses => simp [wellFormedSlot] at hwf
      | declared ann =>
          simp only [replaySlot, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
          exact scalar_inconsistent_uninhabited hde hda (hr.1.1 ▸ hr.2) v

--------------------------------------- LANDMARK ---------------------------------------
/-- **Soundness of an accepted certificate's errors.** Every diagnostic it reports between two scalar
types is a real type error: no runtime value inhabits both. So a flagged program is not merely one the
checker disliked — the two types it was asked to be at once have no common value. -/
theorem replay_error_sound (c : Cert) (h : replayOk c = true) :
    ∀ d ∈ c.diagnostics, isScalar d.expected = true → isScalar d.actual = true →
      ∀ v : Val, ¬ (HasType v d.expected ∧ HasType v d.actual) := by
  intro d hd hde hda v
  have hb := backed_of_replay h hd
  simp only [backedDiagnostic, List.any_eq_true, Bool.and_eq_true] at hb
  obtain ⟨s, hs, _, hmatch⟩ := hb
  -- The backing slot really did produce this diagnostic, so its verdict decides the fact to use.
  revert hmatch
  cases hwant : s.expectedDiagnostic? with
  | none => intro hc; simp at hc
  | some want =>
      intro hsame
      have hok := slotOk_of_replay h hs
      simp only [slotOk, Bool.and_eq_true] at hok
      -- `sameDiagnostic` fixes both accused types, so the slot's own soundness transfers to `d`.
      simp only [sameDiagnostic, Bool.and_eq_true, decide_eq_true_eq] at hsame
      have hw := slot_error_sound s want hok.1.1 hok.1.2 hwant
        (hsame.1.2 ▸ hde) (hsame.2 ▸ hda) v
      rw [hsame.1.2, hsame.2] at hw
      exact hw

/-- The same, for a certificate checked against its program. -/
theorem validate_error_sound (ast : Json) (c : Cert) (h : validate ast c = true) :
    ∀ d ∈ c.diagnostics, isScalar d.expected = true → isScalar d.actual = true →
      ∀ v : Val, ¬ (HasType v d.expected ∧ HasType v d.actual) :=
  replay_error_sound c (replayOk_of_validate h)
--------------------------------------- LANDMARK ---------------------------------------

end TypeInfer
