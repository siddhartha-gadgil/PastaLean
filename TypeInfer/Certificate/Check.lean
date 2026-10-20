import TypeInfer.Certificate.Basic
import TypeInfer.Annotation

/-!
# The validator — re-checking a certificate without the engine

**The import list is this file's point.** `TypeInfer.Certificate.Basic` brings the requirement
algebra and the judgments; `TypeInfer.Annotation` brings `ofAnnotation`, a pure reader for Python type
hints. Neither pulls `TypeInfer.Solve`, `Rules`, `Repo` or the stamper. So "this module has no type
error" can be re-checked by this file plus `Diagnostics/Basic.lean` — a few hundred lines — rather
than by trusting the whole inference engine. An engine import here would quietly undo that, which is
why the three JSON helpers below are re-declared locally instead of taken from `Solve/Env.lean`.

Four groups of checks, and they are NOT equally strong — see `Reject` and the grounding note:

1. **Identity** — the certificate names this program and this format version.
2. **Replay** — every verdict is what `checkUses` / `checkAnnotation` actually compute on the
   evidence the certificate records. This is what `TypeInfer.validate_sound` is about.
3. **Reporting** — every failing slot produced a diagnostic and every diagnostic has a failing slot,
   so a certificate can neither hide an error behind a clean `ok` nor manufacture one.
4. **Grounding** — every *declared* type in the certificate is the type the source really writes at
   that slot, and a slot judged by its uses really is an unannotated parameter.

What group 4 does *not* do: body-use evidence arrives from `usageEvidence` as a bare `List PyType`
with no source positions, so the validator cannot confirm a `bodyUse` requirement was read from a
real expression. A certificate that invents a plausible body-use requirement passes replay. Closing
that needs positions on evidence and a proved rule table — the next tier, not claimed here.

`validate` is the Bool the theorem is stated about; `validateCert` only explains a `false`, and is
consulted only after `validate` has already refused, so the two cannot disagree on the verdict.
-/

namespace TypeInfer

open Lean

/-! ### Local JSON helpers

Deliberate duplicates of `Solve/Env.lean:7-9`. Three lines of IR reading is a smaller price than an
engine dependency in the validator. -/

private def ctNodeType (j : Json) : Option String := (j.getObjValAs? String "node_type").toOption

private def ctField (j : Json) (k : String) : Option Json :=
  match (j.getObjVal? k).toOption with
  | some v => if v.isNull then none else some v
  | none => none

private def ctName (j : Json) : Option String :=
  if ctNodeType j == some "Name" then (j.getObjValAs? String "id").toOption else none

/-! ### Replay

The whole reason a certificate is cheap to check: each judgment in `Diagnostics/Basic.lean` is a
total function of a slot's evidence, so re-running it reproduces the verdict or refutes it. No
fixpoint, no interprocedural pass, no stamper, no second inference of the module.

Equalities go through `decide` on the derived `DecidableEq PyType` rather than through `BEq`, because
only the former hands `Theorem/Certificate.lean` a usable equation. -/

/-- Is a judgment/verdict pairing well formed at all? Separated from `replaySlot` so a tamper test
that moves a verdict across judgments is reported as that rather than as a replay failure. -/
def wellFormedSlot (s : Slot) : Bool :=
  match s.judgment, s.verdict with
  | .uses, .commits _ | .uses, .unconstrained | .uses, .conflict _ _ => true
  | .declared _, .agrees | .declared _, .rejects _ _ => true
  | _, _ => false

/-- Does the recorded verdict follow from the recorded evidence?

The `conflict` branch asks for one thing the engine never states: that the two accused types really
do meet at `unknown`. Every conflict `checkUses` reports satisfies it (it reports exactly when
`Req.narrow` became contradictory, which for two real requirements *is* `meet … = unknown`), so no
honest certificate is refused — and having it on the record is what lets
`TypeInfer.validate_error_sound` conclude that a reported conflict is a real one instead of
re-deriving it through the fold. -/
def replaySlot (s : Slot) : Bool :=
  match s.judgment, s.verdict with
  | .uses, .commits t => decide ((Req.ofEvidenceAll s.reqs).commit? = some t)
  | .uses, .unconstrained => decide (Req.ofEvidenceAll s.reqs = Req.top)
  | .uses, .conflict e a =>
      decide (((checkUses s.scope s.name s.reqs).2.map (fun d => (d.expected, d.actual))).head?
                = some (e, a))
        && decide (PyType.meet e a = PyType.unknown)
  | .declared ann, .agrees => s.reqs.all (fun r => (checkAnnotation s.scope s.name ann r).isNone)
  | .declared ann, .rejects e a =>
      decide (ann = e) && decide (a ∈ s.reqs) && !PyType.consistent ann a
  | _, _ => false

/-- Same slot, same kind, same pair of types. Positions are excluded: `atNode` stamps a diagnostic
from the enclosing node, which the certificate's slot position need not equal. -/
def sameDiagnostic (a b : Diagnostic) : Bool :=
  decide (a.scope = b.scope) && decide (a.slot = b.slot) && decide (a.kind = b.kind)
    && decide (a.expected = b.expected) && decide (a.actual = b.actual)

/-- Is this slot's failure actually reported? A certificate must not hide an error behind `ok`. -/
def reportedSlot (c : Cert) (s : Slot) : Bool :=
  if s.failed then
    match s.expectedDiagnostic? with
    | some want => c.diagnostics.any (sameDiagnostic want)
    | none => false
  else true

/-- Is this diagnostic accounted for by a slot that really failed? Without this a certificate could
manufacture errors it never derived. -/
def backedDiagnostic (c : Cert) (d : Diagnostic) : Bool :=
  c.slots.any fun s =>
    s.failed && (match s.expectedDiagnostic? with
                 | some want => sameDiagnostic want d
                 | none => false)

/-! ### Grounding

A certificate that replays correctly can still be about nothing: nothing above stops it declaring a
slot the program does not have. These checks read the declared types straight out of the IR and
require the certificate to agree. They cover the *declared* side only — see the module note. -/

/-- Every parameter and return the source annotates, keyed by `(scope, slot)`, together with every
parameter it leaves unannotated (recorded as `none`). Mirrors how `Pass.lean` walks a module: a
`FunctionDef` or a `ClassDef` extends the dotted scope, parameters come from the three argument
groups, and `self`/`cls` are not slots. -/
partial def declaredSlots (scope : String) (json : Json) :
    List ((String × String) × Option PyType) :=
  let inScope (n : String) : String := if scope.isEmpty then n else scope ++ "." ++ n
  let here : List ((String × String) × Option PyType) :=
    match ctNodeType json with
    | some "FunctionDef" | some "AsyncFunctionDef" =>
        let fq := inScope ((json.getObjValAs? String "name").toOption.getD "")
        let args := (ctField json "args").getD Json.null
        let group (k : String) : Array Json := (args.getObjValAs? (Array Json) k).toOption.getD #[]
        let params := (group "args" ++ group "posonlyargs" ++ group "kwonlyargs").toList.filterMap
          fun a =>
            let n := (a.getObjValAs? String "arg").toOption.getD ""
            if n.isEmpty || n == "self" || n == "cls" then none
            else some ((fq, n), (ctField a "annotation").map ofAnnotation)
        let ret : List ((String × String) × Option PyType) :=
          match ctField json "returns" with
          | some ann => [((fq, "<return>"), some (ofAnnotation ann))]
          | none => []
        params ++ ret
    | some "Assign" =>
        match (ctField json "target").bind ctName, ctField json "_decl_ty" with
        | some n, some ann => [((scope, n), some (ofAnnotation ann))]
        | _, _ => []
    | _ => []
  let scope' := match ctNodeType json with
    | some "FunctionDef" | some "AsyncFunctionDef" | some "ClassDef" =>
        inScope ((json.getObjValAs? String "name").toOption.getD "")
    | _ => scope
  let sub := match json with
    | .arr xs => xs.toList.flatMap (declaredSlots scope')
    | .obj fs => fs.toList.flatMap (fun (_, v) => declaredSlots scope' v)
    | _ => []
  here ++ sub

/-- The declaration table a certificate is checked against. A name declared twice keeps the first
reading, which is all the agreement check below needs. -/
def declarationTable (ast : Json) : Std.HashMap (String × String) (Option PyType) :=
  (declaredSlots "" ast).foldl (fun m (k, v) => if m.contains k then m else m.insert k v) {}

/-- Does the source really declare what this slot claims? A return is checked against the module as
written, so a certificate whose return slot the table cannot key is not refuted by that absence; the
same goes for a call argument, which is keyed by the callee rather than by the calling scope. -/
def groundedSlot (table : Std.HashMap (String × String) (Option PyType)) (s : Slot) : Bool :=
  match s.judgment with
  | .declared ann =>
      match table.get? (s.scope, s.name) with
      | some (some declared) => decide (declared = ann)
      | some none => false
      | none => s.kind == .returnType || s.kind == .callArgument
  | .uses =>
      match table.get? (s.scope, s.name) with
      | some none => true
      -- A local variable is bound by the body, not declared in the signature, so the declaration
      -- table has nothing to say about it; absence is what we expect rather than a refutation. A
      -- name the table DOES hold as annotated is still refused — that slot should carry the
      -- annotation as its judgment.
      | Option.none => s.kind == .localVariable
      | some (Option.some _) => false

/-! ### The verdict on the certificate

Split in two, because the halves differ in what they need and in what can be *proved* about them.

`replayOk` depends on the certificate ALONE — version, the replayed verdicts, and the reporting
rules. Everything `TypeInfer.replay_sound` and `TypeInfer.replay_error_sound` conclude comes from
here, and because it touches no `Json`, no hash and no `Std.HashMap`, it is the part Lean's **kernel**
can evaluate: that is what makes a per-file `.lean` certificate possible
(`pastalean typeinfer --emit-proof`).

The rest ties the certificate to a program — the identity hash and the declaration grounding. Both
are *checked*, neither is proved, and neither reduces in the kernel (`String.hash` is an `extern`,
and hash-map lookups do not evaluate there). `validate` is both halves, and is what a verifier
runs. -/

/-- Everything required of one slot by the certificate alone. -/
def slotOk (c : Cert) (s : Slot) : Bool :=
  wellFormedSlot s && replaySlot s && reportedSlot c s

/-- The certificate is internally sound: every verdict follows from the evidence beside it, and the
reported errors are exactly the slots that failed. Program-independent, and kernel-evaluable. -/
def replayOk (c : Cert) : Bool :=
  decide (c.version = certVersion)
    && decide (c.ok = c.diagnostics.isEmpty)
    && c.slots.all (slotOk c)
    && c.diagnostics.all (backedDiagnostic c)

/-- The certificate is about THIS program: it names it by hash, and every type it claims the source
declares really is declared there. -/
def groundedIn (ast : Json) (c : Cert) : Bool :=
  decide (c.irHash = irHashOf ast) && c.slots.all (groundedSlot (declarationTable ast))

/-- Re-check a certificate against the program it claims to be about.

`TypeInfer.validate_sound` and `TypeInfer.validate_error_sound` say what a `true` here buys. Note
what it costs: one pass over the certificate, no inference. -/
def validate (ast : Json) (c : Cert) : Bool := replayOk c && groundedIn ast c

/-! ### Explaining a refusal

Only reached when `validate` has already said no, so this cannot disagree with it about the verdict —
it just finds which check was the first to fail. -/

inductive Reject where
  /-- Written for a format version this validator does not know. -/
  | version (found expected : Nat)
  /-- The certificate is about a different program. -/
  | hash (found expected : UInt64)
  /-- `ok` disagrees with whether any diagnostic was reported. -/
  | okMismatch (ok : Bool) (diagnostics : Nat)
  /-- A verdict that does not belong to the judgment it was recorded under. -/
  | wrongJudgment (subject : String)
  /-- Replaying the judgment over the recorded evidence does not give the recorded verdict. -/
  | verdictMismatch (subject : String)
  /-- A slot failed but no diagnostic reports it. -/
  | unreportedFailure (subject : String)
  /-- The source declares a different type at this slot than the certificate claims. -/
  | declarationMismatch (subject : String) (claimed : PyType)
  /-- The certificate judges a slot by its uses that the source annotates, or names a parameter the
  source does not have. -/
  | notUnannotated (subject : String)
  /-- A reported diagnostic has no slot whose verdict accounts for it. -/
  | unbackedDiagnostic (subject : String)
  deriving Repr, Inhabited

def Reject.message : Reject → String
  | .version f e => s!"certificate format version {f}, expected {e}"
  | .hash f e => s!"certificate is for a different program (hash {f}, expected {e})"
  | .okMismatch ok n => s!"ok = {ok} with {n} diagnostics"
  | .wrongJudgment s => s!"{s}: verdict does not belong to this judgment"
  | .verdictMismatch s => s!"{s}: recorded verdict is not what the evidence yields"
  | .unreportedFailure s => s!"{s}: slot failed but no diagnostic reports it"
  | .declarationMismatch s t => s!"{s}: source does not declare {t} here"
  | .notUnannotated s => s!"{s}: judged by its uses, but the source annotates it"
  | .unbackedDiagnostic s => s!"{s}: diagnostic has no failing slot behind it"

instance : ToString Reject := ⟨Reject.message⟩

/-- `validate`, plus the first reason it refused. -/
def validateCert (ast : Json) (c : Cert) : Except Reject Unit := do
  if validate ast c then return ()
  if c.version != certVersion then throw (.version c.version certVersion)
  let h := irHashOf ast
  if c.irHash != h then throw (.hash c.irHash h)
  if c.ok != c.diagnostics.isEmpty then throw (.okMismatch c.ok c.diagnostics.length)
  let table := declarationTable ast
  for s in c.slots do
    if !wellFormedSlot s then throw (.wrongJudgment s.subject)
    if !replaySlot s then throw (.verdictMismatch s.subject)
    if !reportedSlot c s then throw (.unreportedFailure s.subject)
    if !groundedSlot table s then
      match s.judgment with
      | .declared ann => throw (.declarationMismatch s.subject ann)
      | .uses => throw (.notUnannotated s.subject)
  -- `validate` said no, so one of the checks above must have fired; this keeps the two in step if a
  -- check is ever added to one and not the other.
  for d in c.diagnostics do
    if !backedDiagnostic c d then throw (.unbackedDiagnostic d.subject)

end TypeInfer
