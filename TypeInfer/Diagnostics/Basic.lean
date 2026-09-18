import TypeInfer.PyType

/-!
# The requirement algebra — checking, not just inferring

Inference and checking pull in opposite directions on the same lattice.

* A **value** flowing into a slot is *evidence*: the slot's type must ADMIT it, so several values
  combine with `join` (⊔), and "nothing seen yet" is `unknown` (⊥).
* A **use** of a slot is a *requirement*: the slot's type must SATISFY it, so several uses combine
  with `meet` (⊓), and "nothing required yet" is `any` (⊤).

`PyType` alone cannot express the second, because it has one bottom and the requirement domain needs
two distinct absorbing/neutral ends: "no requirement" (neutral) and "requirements that cannot all be
met" (absorbing). Folding requirements with `join` — which is what the usage back-inference did —
silently turns a *conflict* into ⊤ and then boxes it as `PyAny`, so a real type error and a genuinely
dynamic value come out indistinguishable, and a slot that IS determined (used as both `int` and
`float` ⇒ `int`) gets widened to a type one of its uses rejects.

`Req = Option PyType` supplies the missing end: `none` is "no requirement", `some t` is "must be
`t`", and `some unknown` is "contradiction" — the thing a checker reports instead of boxing.
`Req.narrow` is `meet` lifted over that extra point, and inherits commutativity, associativity and
idempotence from it (`TypeInfer.Theorem.Requirements`), so a slot's verdict does not depend on the
order its uses are visited in.

**Which evidence belongs here.** Only *exact* requirements — a use that one and only one type
satisfies, such as `p.isalpha()` (⇒ `str`, no other builtin has the method) or `p[i][j] == 1`
(⇒ `list[list[int]]`). Python's arithmetic is subtype-polymorphic, so `x + 1` does NOT require `int`:
a `float` satisfies it too. Numeric evidence is a lower bound and must keep widening through `join` in
the existing value-flow channel; routing it through `meet` would narrow `int ⊓ float` to `int` and
mis-type a genuine float. The two channels meet at `checkValue`, which uses `consistent` to verify
that what flows in satisfies what the uses demand.
-/

namespace TypeInfer

open Lean

/-- What a slot's uses demand of it. `none` = no use has constrained it yet (the neutral element);
`some unknown` = the uses cannot all be satisfied (absorbing — a reportable type error). -/
abbrev Req := Option PyType

namespace Req

/-- No requirement yet — the neutral element of `narrow`. -/
def top : Req := none

/-- A use that cannot be satisfied by any type. -/
def bot : Req := some .unknown

/-- Read one use site's evidence as a requirement. The engine's usage rules return `unknown` for
"this site says nothing about the slot", which is the NEUTRAL element here, not the absorbing one. -/
def ofEvidence : PyType → Req
  | .unknown => none
  | t => some t

/-- Combine two requirements: both must hold, so real requirements meet. -/
def narrow : Req → Req → Req
  | none, r | r, none => r
  | some a, some b => some (PyType.meet a b)

/-- Combine a whole list of requirements, starting from "no requirement". -/
def narrowAll (rs : List Req) : Req := rs.foldl narrow none

/-- Gather requirements straight from a list of per-site evidence types. -/
def ofEvidenceAll (ts : List PyType) : Req := narrowAll (ts.map ofEvidence)

/-- No type satisfies every use that produced this requirement. -/
def contradictory : Req → Bool
  | some .unknown => true
  | _ => false

/-- The type to commit for a slot. `none` when there is nothing to say: either no use constrained the
slot, or the uses contradict — and a contradiction must be REPORTED, never silently boxed as `PyAny`,
which is what made the two cases indistinguishable before. -/
def commit? : Req → Option PyType
  | none => none
  | some .unknown => none
  | some t => some t

/-- Collapse back to a plain `PyType` for callers that still want one value: `unknown` both for "no
requirement" and for "contradiction". Lossy by construction — prefer `commit?` plus `contradictory`. -/
def toPyType : Req → PyType
  | none => .unknown
  | some t => t

/-- What the CODEGEN should use. A contradiction still has to produce running Lean, and the existing
answer for that is the boxed dynamic top — so it maps to `any` (`PyAny`), exactly as folding the same
uses with `join` used to. `commit?` is the answer for a *reporting* caller; this one keeps the emitted
code unchanged while the contradiction is surfaced as a diagnostic alongside it. -/
def toInferred : Req → PyType
  | none => .unknown
  | some .unknown => .any
  | some t => t

end Req

/-! ### Diagnostics

A checker has to be able to say **no**. These are the judgments the engine can now make and could not
before, because every disagreement used to widen to `any` and get boxed. -/

/-- Why a slot failed to check. -/
inductive DiagKind where
  /-- Two uses of the same slot require types no single type satisfies (`p.upper()` and `p + 1`). -/
  | useConflict
  /-- A written annotation is not consistent with the type inferred from the body. -/
  | annotationMismatch
  /-- A value flowing into a slot is not consistent with what the slot's uses require. -/
  | valueRejected
  deriving Repr, BEq, DecidableEq, Inhabited

def DiagKind.toString : DiagKind → String
  | .useConflict => "use-conflict"
  | .annotationMismatch => "annotation-mismatch"
  | .valueRejected => "value-rejected"

instance : ToString DiagKind := ⟨DiagKind.toString⟩

/-- One reported type error, addressed to a named slot. -/
structure Diagnostic where
  /-- Enclosing function, or `""` at module scope. -/
  scope : String
  /-- Parameter, variable or `<return>`. -/
  slot : String
  kind : DiagKind
  /-- What the slot was required/annotated to be. -/
  expected : PyType
  /-- What the conflicting evidence said. -/
  actual : PyType
  deriving Repr, Inhabited

/-- The slot a diagnostic is about, as the user wrote it: `f.p`, or just `p` at module scope. -/
def Diagnostic.subject (d : Diagnostic) : String :=
  if d.scope.isEmpty then d.slot else s!"{d.scope}.{d.slot}"

/-! ### The checks

Each takes the engine's existing numbers and turns a silent widening into a verdict. They are total
and allocation-free; `checkAnnotation` is the one that makes `PyType.consistent` — proved reflexive,
symmetric and non-transitive in `TypeInfer.Theorem.Consistency`, and until now never called — actually
decide something. -/

/-- Check a written annotation against what the body infers. Gradual by design: `unknown` on either
side means "no static claim", so it never fires. -/
def checkAnnotation (scope slot : String) (annotated inferred : PyType) : Option Diagnostic :=
  match annotated, inferred with
  | .unknown, _ | _, .unknown => none
  | a, i =>
      if PyType.consistent a i then none
      else some { scope, slot, kind := .annotationMismatch, expected := a, actual := i }

/-- Check that a value reaching a slot satisfies what the slot's uses require. -/
def checkValue (scope slot : String) (required : Req) (value : PyType) : Option Diagnostic :=
  match required.commit? with
  | none => none
  | some r =>
      match value with
      | .unknown => none
      | v =>
          if PyType.consistent r v then none
          else some { scope, slot, kind := .valueRejected, expected := r, actual := v }

/-- Fold a slot's per-use requirements, reporting the first pair that cannot be satisfied together.
Returns the surviving requirement alongside the diagnostics, so a contradicting slot still yields the
best partial answer for the rest of the analysis. -/
def checkUses (scope slot : String) (evidence : List PyType) : Req × List Diagnostic :=
  evidence.foldl
    (fun (acc, diags) t =>
      let r := Req.ofEvidence t
      let next := Req.narrow acc r
      if next.contradictory && !acc.contradictory then
        (next, diags ++ [{ scope, slot, kind := .useConflict,
                           expected := acc.toPyType, actual := t }])
      else (next, diags))
    (Req.top, [])

end TypeInfer
