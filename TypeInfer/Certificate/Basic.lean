import TypeInfer.Diagnostics.Basic
import TypeInfer.PyTypeEq

/-!
# The certificate — what the checker produces besides a verdict

`checkTypes` today answers with one boolean (`ok := diags.isEmpty`). That is a claim with nothing
behind it: a reader who does not already trust the eight-thousand-line engine has no way to tell a
clean verdict from a verdict the engine failed to reach. A **certificate** is the missing artifact —
for every slot the checker judged, the evidence it judged on and the verdict it reached, in a form a
second program can re-check without running inference at all.

The split that makes this worth doing:

* **Producing** a certificate needs the whole engine — the fixpoint, the interprocedural pass, the
  stamper, `usageEvidence`.
* **Checking** one needs none of it. Every judgment in `Diagnostics/Basic.lean` is a total function
  of the slot's evidence, so re-running `checkUses` / `checkAnnotation` over the recorded evidence
  reproduces the verdict or refutes it. `Certificate/Check.lean` does exactly that, and imports
  nothing from `Solve/`.

So the trusted base for "this module has no type error" shrinks to the requirement algebra plus the
validator, and `TypeInfer/Theorem/Certificate.lean` states what an accepted certificate means.

## What is and is not recorded

`evidence` lists the types each judgment weighed, tagged with an `Origin` saying which channel
supplied it. The tag names the *judgment* that produced the item, not the syntax node: body-use
evidence arrives from `usageEvidence` as a bare `List PyType` with no positions, so an item marked
`bodyUse` cannot be traced to the expression it was read from. Pinning each item to its node (and
proving the rule that read it) is the next tier of this work and is deliberately not claimed here.
-/

namespace TypeInfer

open Lean

/-- The channel one piece of evidence came through. Coarse by construction — see the module note.
A *declared* type is not evidence and is not here: it is the judgment itself (`Judgment.declared`). -/
inductive Origin where
  /-- A use of the slot inside the function body (`usageEvidence`). -/
  | bodyUse
  /-- What the body returns, re-inferred with every annotation stripped (`stripAnnotations`). -/
  | returnBody
  /-- The type of the value assigned at this slot. -/
  | valueFlow
  /-- The type of a literal argument at a call site. -/
  | callLiteral
  deriving Repr, BEq, DecidableEq, Inhabited

def Origin.toString : Origin → String
  | .bodyUse => "body-use"
  | .returnBody => "return-body"
  | .valueFlow => "value-flow"
  | .callLiteral => "call-literal"

instance : ToString Origin := ⟨Origin.toString⟩

def Origin.ofString? : String → Option Origin
  | "body-use" => some .bodyUse
  | "return-body" => some .returnBody
  | "value-flow" => some .valueFlow
  | "call-literal" => some .callLiteral
  | _ => none

/-- One type the checker weighed, and where it came from. -/
structure Evidence where
  origin : Origin
  req : PyType
  deriving Repr, Inhabited

/-- Which judgment the checker applied. The two have different shapes and different verdicts, and the
validator refuses a verdict that does not belong to its judgment. -/
inductive Judgment where
  /-- No type was written, so the only available question is whether the uses AGREE: `checkUses`
  folds them with `Req.narrow`. -/
  | uses
  /-- A type was written; `checkAnnotation` asks whether each piece of independent evidence is
  consistent with it. -/
  | declared (ann : PyType)
  deriving Repr, Inhabited

/-- What the checker concluded. The first three belong to `Judgment.uses`, the last two to
`Judgment.declared`. -/
inductive Verdict where
  /-- The uses narrow to exactly this type. -/
  | commits (t : PyType)
  /-- No use constrained the slot at all. -/
  | unconstrained
  /-- Two uses no single type satisfies; the pair is the first one the fold hit. -/
  | conflict (expected actual : PyType)
  /-- Every piece of evidence is consistent with the written type. -/
  | agrees
  /-- This evidence contradicts the written type. -/
  | rejects (expected actual : PyType)
  deriving Repr, Inhabited

/-- What the slot is, for reporting. Carries no weight in the validator. -/
inductive SlotKind where
  | param | returnType | annotatedLocal | callArgument | localVariable
  deriving Repr, BEq, DecidableEq, Inhabited

def SlotKind.toString : SlotKind → String
  | .localVariable => "local-var"
  | .param => "param"
  | .returnType => "return"
  | .annotatedLocal => "local"
  | .callArgument => "call-arg"

instance : ToString SlotKind := ⟨SlotKind.toString⟩

def SlotKind.ofString? : String → Option SlotKind
  | "local-var" => some .localVariable
  | "param" => some .param
  | "return" => some .returnType
  | "local" => some .annotatedLocal
  | "call-arg" => some .callArgument
  | _ => none

/-- One judged slot: who it is, what was weighed, and what came out. -/
structure Slot where
  /-- Enclosing dotted scope, or `""` at module scope. -/
  scope : String
  /-- Parameter, variable or `<return>`. -/
  name : String
  kind : SlotKind
  /-- 1-based source line of the slot; `0` when the IR carried no position. -/
  line : Nat := 0
  /-- 1-based source column; `0` when unknown. -/
  col : Nat := 0
  judgment : Judgment
  evidence : List Evidence
  verdict : Verdict
  deriving Repr, Inhabited

/-- Stamp the enclosing node's source position onto a slot that has none. The same rule
`Diagnostic.at` follows: a position already set wins, because the inner judgment knows the precise
node and the caller only the node around it. -/
def Slot.at (line col : Nat) (s : Slot) : Slot :=
  if s.line == 0 then { s with line, col } else s

/-- The slot a certificate entry is about, as the user wrote it: `f.p`, or `p` at module scope. -/
def Slot.subject (s : Slot) : String :=
  if s.scope.isEmpty then s.name else s!"{s.scope}.{s.name}"

/-- Did this slot fail? Exactly the two verdicts that must come with a diagnostic. -/
def Slot.failed (s : Slot) : Bool :=
  match s.verdict with
  | .conflict _ _ | .rejects _ _ => true
  | _ => false

/-- The diagnostic a failing slot produces. Every judgment in `Diagnostics/Pass.lean` reports at most
one, built from the same two types the verdict carries — so this is a function of the verdict alone,
which is what lets the pass emit slots and read the diagnostics off them, and lets the validator
check that a certificate reports exactly the failures it recorded. -/
def Slot.expectedDiagnostic? (s : Slot) : Option Diagnostic :=
  match s.verdict with
  | .conflict e a =>
      some { scope := s.scope, slot := s.name, kind := .useConflict, expected := e, actual := a }
  | .rejects e a =>
      some { scope := s.scope, slot := s.name, kind := .annotationMismatch,
             expected := e, actual := a }
  | _ => none

/-- The diagnostic this slot contributes to a module's report, positioned at the slot. -/
def Slot.diagnostic? (s : Slot) : Option Diagnostic :=
  s.expectedDiagnostic?.map (Diagnostic.at s.line s.col)

/-- Just the types a slot's judgment weighed, in the order it weighed them — what the validator
replays and what `TypeInfer.CertSound` quantifies over. -/
def Slot.reqs (s : Slot) : List PyType := s.evidence.map (·.req)

/-- The format version. Bump when a field changes meaning; the validator refuses anything else, so an
old certificate is rejected rather than silently misread. -/
def certVersion : Nat := 1

/-- One module's checking run, in full. -/
structure Cert where
  version : Nat := certVersion
  /-- Identifies the program this certificate is about: `(Json.compress ast).hash`. An identity
  check, not a security one — it catches a certificate paired with the wrong file, not an adversary
  who can recompute the hash. -/
  irHash : UInt64
  slots : List Slot
  diagnostics : List Diagnostic
  /-- The headline verdict: no reportable type error in this module. -/
  ok : Bool
  deriving Repr, Inhabited

/-- The identity a certificate claims. Both the producer and the validator call this, so the two
always agree on what "the same program" means. -/
def irHashOf (ast : Json) : UInt64 := ast.compress.hash

/-! ### JSON

Hand-written rather than derived, because a certificate is read by people as well as programs and the
derived tagged encoding is unreadable. Decoding sits OUTSIDE the proved boundary: `validate` is stated
about an already-decoded `Cert`, so a decoder bug yields a different `Cert`, which the replay then
judges on its own merits. -/

partial def PyType.toCertJson : PyType → Json
  | .unknown => .str "?"
  | .any => .str "any"
  | .int => .str "int"
  | .bool => .str "bool"
  | .str => .str "str"
  | .float => .str "float"
  | .none => .str "None"
  | .cls n => Json.mkObj [("cls", .str n)]
  | .list e => Json.mkObj [("list", e.toCertJson)]
  | .set e => Json.mkObj [("set", e.toCertJson)]
  | .opt e => Json.mkObj [("opt", e.toCertJson)]
  | .dict k v => Json.mkObj [("dict", .arr #[k.toCertJson, v.toCertJson])]
  | .tuple es => Json.mkObj [("tuple", .arr (es.map PyType.toCertJson).toArray)]
  | .fn as r => Json.mkObj [("fn", .arr (as.map PyType.toCertJson).toArray), ("ret", r.toCertJson)]

partial def PyType.ofCertJson? (j : Json) : Option PyType :=
  match j with
  | .str "?" => some .unknown
  | .str "any" => some .any
  | .str "int" => some .int
  | .str "bool" => some .bool
  | .str "str" => some .str
  | .str "float" => some .float
  | .str "None" => some .none
  | .obj _ =>
      let one (k : String) (f : PyType → PyType) : Option PyType :=
        (j.getObjVal? k).toOption.bind PyType.ofCertJson? |>.map f
      match one "list" .list with
      | some t => some t
      | Option.none =>
      match one "set" .set with
      | some t => some t
      | Option.none =>
      match one "opt" .opt with
      | some t => some t
      | Option.none =>
      match (j.getObjValAs? String "cls").toOption with
      | some n => some (.cls n)
      | Option.none =>
      match (j.getObjValAs? (Array Json) "dict").toOption with
      | some #[k, v] => do
          let k ← PyType.ofCertJson? k
          let v ← PyType.ofCertJson? v
          pure (.dict k v)
      | _ =>
      match (j.getObjValAs? (Array Json) "tuple").toOption with
      | some es => (es.toList.mapM PyType.ofCertJson?).map .tuple
      | Option.none =>
      match (j.getObjValAs? (Array Json) "fn").toOption,
            (j.getObjVal? "ret").toOption.bind PyType.ofCertJson? with
      | some as, some r => (as.toList.mapM PyType.ofCertJson?).map (.fn · r)
      | _, _ => Option.none
  | _ => Option.none

def DiagKind.ofString? : String → Option DiagKind
  | "use-conflict" => some .useConflict
  | "annotation-mismatch" => some .annotationMismatch
  | "value-rejected" => some .valueRejected
  | _ => none

/-- A diagnostic in round-trippable form. `Diagnostic.toJson` (`Diagnostics/Render.lean`) is the
*presentation* encoding — it carries rendered English and Lean type names a parser cannot invert, so
the certificate uses this one and the task response keeps carrying that one. -/
def Diagnostic.toCertJson (d : Diagnostic) : Json :=
  Json.mkObj
    [ ("scope", .str d.scope), ("slot", .str d.slot), ("kind", .str (toString d.kind)),
      ("expected", d.expected.toCertJson), ("actual", d.actual.toCertJson),
      ("line", toJson d.line), ("col", toJson d.col) ]

def Diagnostic.ofCertJson? (j : Json) : Option Diagnostic := do
  let kind ← (j.getObjValAs? String "kind").toOption.bind DiagKind.ofString?
  let expected ← (j.getObjVal? "expected").toOption.bind PyType.ofCertJson?
  let actual ← (j.getObjVal? "actual").toOption.bind PyType.ofCertJson?
  pure { scope := (j.getObjValAs? String "scope").toOption.getD ""
         slot := (j.getObjValAs? String "slot").toOption.getD ""
         kind, expected, actual
         line := (j.getObjValAs? Nat "line").toOption.getD 0
         col := (j.getObjValAs? Nat "col").toOption.getD 0 }

def Evidence.toCertJson (e : Evidence) : Json :=
  Json.mkObj [("origin", .str (toString e.origin)), ("req", e.req.toCertJson)]

def Evidence.ofCertJson? (j : Json) : Option Evidence := do
  let origin ← (j.getObjValAs? String "origin").toOption.bind Origin.ofString?
  let req ← (j.getObjVal? "req").toOption.bind PyType.ofCertJson?
  pure { origin, req }

def Judgment.toCertJson : Judgment → Json
  | .uses => Json.mkObj [("judgment", .str "uses")]
  | .declared ann => Json.mkObj [("judgment", .str "declared"), ("declared", ann.toCertJson)]

def Judgment.ofCertJson? (j : Json) : Option Judgment :=
  match (j.getObjValAs? String "judgment").toOption with
  | some "uses" => some .uses
  | some "declared" => ((j.getObjVal? "declared").toOption.bind PyType.ofCertJson?).map .declared
  | _ => none

def Verdict.toCertJson : Verdict → Json
  | .commits t => Json.mkObj [("verdict", .str "commits"), ("type", t.toCertJson)]
  | .unconstrained => Json.mkObj [("verdict", .str "unconstrained")]
  | .conflict e a =>
      Json.mkObj [("verdict", .str "conflict"), ("expected", e.toCertJson), ("actual", a.toCertJson)]
  | .agrees => Json.mkObj [("verdict", .str "agrees")]
  | .rejects e a =>
      Json.mkObj [("verdict", .str "rejects"), ("expected", e.toCertJson), ("actual", a.toCertJson)]

def Verdict.ofCertJson? (j : Json) : Option Verdict :=
  let ty (k : String) : Option PyType := (j.getObjVal? k).toOption.bind PyType.ofCertJson?
  match (j.getObjValAs? String "verdict").toOption with
  | some "commits" => (ty "type").map .commits
  | some "unconstrained" => some .unconstrained
  | some "agrees" => some .agrees
  | some "conflict" => do pure (.conflict (← ty "expected") (← ty "actual"))
  | some "rejects" => do pure (.rejects (← ty "expected") (← ty "actual"))
  | _ => none

def Slot.toCertJson (s : Slot) : Json :=
  Json.mkObj
    [ ("scope", .str s.scope), ("slot", .str s.name), ("kind", .str (toString s.kind)),
      ("line", toJson s.line), ("col", toJson s.col),
      ("judgment", s.judgment.toCertJson), ("verdict", s.verdict.toCertJson),
      ("evidence", .arr (s.evidence.map Evidence.toCertJson).toArray) ]

def Slot.ofCertJson? (j : Json) : Option Slot := do
  let kind ← (j.getObjValAs? String "kind").toOption.bind SlotKind.ofString?
  let judgment ← ((j.getObjVal? "judgment").toOption).bind Judgment.ofCertJson?
  let verdict ← ((j.getObjVal? "verdict").toOption).bind Verdict.ofCertJson?
  let evidence ← ((j.getObjValAs? (Array Json) "evidence").toOption).bind
    (fun es => es.toList.mapM Evidence.ofCertJson?)
  pure { scope := (j.getObjValAs? String "scope").toOption.getD ""
         name := (j.getObjValAs? String "slot").toOption.getD ""
         kind
         line := (j.getObjValAs? Nat "line").toOption.getD 0
         col := (j.getObjValAs? Nat "col").toOption.getD 0
         judgment, evidence, verdict }

def Cert.toCertJson (c : Cert) : Json :=
  Json.mkObj
    [ ("version", toJson c.version), ("ir_hash", .str (toString c.irHash)),
      ("ok", .bool c.ok),
      ("slots", .arr (c.slots.map Slot.toCertJson).toArray),
      ("diagnostics", .arr (c.diagnostics.map Diagnostic.toCertJson).toArray) ]

def Cert.ofCertJson? (j : Json) : Option Cert := do
  let version ← (j.getObjValAs? Nat "version").toOption
  let hashStr ← (j.getObjValAs? String "ir_hash").toOption
  let irHash ← hashStr.toNat?.map (fun n => UInt64.ofNat n)
  let ok ← (j.getObjValAs? Bool "ok").toOption
  let slots ← ((j.getObjValAs? (Array Json) "slots").toOption).bind
    (fun ss => ss.toList.mapM Slot.ofCertJson?)
  let diagnostics ← ((j.getObjValAs? (Array Json) "diagnostics").toOption).bind
    (fun ds => ds.toList.mapM Diagnostic.ofCertJson?)
  pure { version, irHash, slots, diagnostics, ok }

end TypeInfer
