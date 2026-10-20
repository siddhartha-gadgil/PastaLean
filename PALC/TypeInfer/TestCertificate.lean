import TypeInfer.Certificate

/-! Unit checks for the certificate layer (`TypeInfer/Certificate/`).

The checks that matter here are the **tamper** ones. Every other test in this repo asks whether the
checker reaches the right verdict; a validator that returned `true` unconditionally would pass all of
them. So each case below takes a certificate that validates and breaks exactly one thing, and
requires the validator to refuse. -/

open Lean TypeInfer

/-! ### A program and the certificate for it

`def is_word(code: int) -> bool` whose body uses `code` as a `str` — the shape of
`typecheck_bench/negative/int_param_str_method.py`, written out by hand so the test needs no front
end. -/

private def nameNode (id : String) : Json :=
  Json.mkObj [("node_type", .str "Name"), ("id", .str id)]

private def ast : Json :=
  Json.mkObj
    [ ("node_type", .str "FunctionDef"), ("name", .str "is_word"),
      ("args", Json.mkObj
        [("args", .arr #[Json.mkObj [("arg", .str "code"), ("annotation", nameNode "int")]])]),
      ("returns", nameNode "bool") ]

/-- The parameter's declared `int` is contradicted by a `str` use; the return agrees with its body. -/
private def cert : Cert :=
  { version := certVersion, irHash := irHashOf ast, ok := false,
    slots :=
      [ { scope := "is_word", name := "code", kind := .param, line := 1, col := 13,
          judgment := .declared .int,
          evidence := [{ origin := .bodyUse, req := .str }],
          verdict := .rejects .int .str },
        { scope := "is_word", name := "<return>", kind := .returnType, line := 1, col := 27,
          judgment := .declared .bool,
          evidence := [{ origin := .returnBody, req := .bool }],
          verdict := .agrees } ],
    diagnostics :=
      [ { scope := "is_word", slot := "code", kind := .annotationMismatch,
          expected := .int, actual := .str, line := 1, col := 13 } ] }

#guard validate ast cert
#guard replayOk cert
#guard groundedIn ast cert

/-! ### The declaration table reads what the source actually writes -/

#guard (declarationTable ast).get? ("is_word", "code") == some (some PyType.int)
#guard (declarationTable ast).get? ("is_word", "<return>") == some (some PyType.bool)
#guard ((declarationTable ast).get? ("is_word", "absent")).isNone

/-! ### Tampering — each of these must be REFUSED -/

-- The certificate is for a different program.
#guard !validate ast { cert with irHash := 1 }
-- Written for a format this validator does not know.
#guard !validate ast { cert with version := certVersion + 1 }
-- `ok` hides the error the certificate itself records.
#guard !validate ast { cert with ok := true }
-- The error is dropped but the slot still says the slot failed.
#guard !validate ast { cert with ok := true, diagnostics := [] }
-- A diagnostic no slot accounts for.
#guard !validate ast
  { cert with diagnostics := cert.diagnostics ++
      [{ scope := "is_word", slot := "<return>", kind := .annotationMismatch,
         expected := .bool, actual := .str }] }
-- The declared type is changed to one the source does not write.
#guard !validate ast
  { cert with slots := cert.slots.map fun s =>
      if s.name == "code" then { s with judgment := .declared .str } else s }
-- The evidence behind the rejection is deleted, so the verdict no longer follows.
#guard !validate ast
  { cert with slots := cert.slots.map fun s =>
      if s.name == "code" then { s with evidence := [] } else s }
-- A verdict moved to a judgment it does not belong to.
#guard !validate ast
  { cert with slots := cert.slots.map fun s =>
      if s.name == "code" then { s with judgment := .uses } else s }

/-! ### Replay accepts only the verdict the evidence yields

`code` is used as a `str` and as an `int`, which no type satisfies. -/

private def conflictSlot : Slot :=
  { scope := "mangle", name := "token", kind := .param,
    judgment := .uses,
    evidence := [{ origin := .bodyUse, req := .str }, { origin := .bodyUse, req := .int }],
    verdict := .conflict .str .int }

#guard replaySlot conflictSlot
-- The accused pair must be the one the fold actually hit, in that order.
#guard !replaySlot { conflictSlot with verdict := .conflict .int .str }
-- Two uses that agree are not a conflict.
#guard !replaySlot { conflictSlot with
  evidence := [{ origin := .bodyUse, req := .str }, { origin := .bodyUse, req := .str }] }
-- They commit instead, and only to the type they narrow to.
#guard replaySlot { conflictSlot with
  evidence := [{ origin := .bodyUse, req := .str }, { origin := .bodyUse, req := .str }],
  verdict := .commits .str }
#guard !replaySlot { conflictSlot with
  evidence := [{ origin := .bodyUse, req := .str }, { origin := .bodyUse, req := .str }],
  verdict := .commits .int }
-- No evidence constrains nothing.
#guard replaySlot { conflictSlot with evidence := [], verdict := .unconstrained }
#guard !replaySlot { conflictSlot with evidence := [], verdict := .commits .str }

/-! ### A failing slot and its diagnostic are the same fact

This is what lets `Diagnostics/Pass.lean` emit slots and read the diagnostics off them. -/

#guard conflictSlot.failed
#guard (conflictSlot.expectedDiagnostic?.map (·.kind)) == some DiagKind.useConflict
#guard ({ conflictSlot with verdict := .commits .str } : Slot).expectedDiagnostic?.isNone
#guard (cert.slots.filterMap Slot.diagnostic?).length == 1

/-! ### JSON round-trips

A certificate that did not survive its own encoding would be refused by a verifier reading it back
from disk. -/

#guard (PyType.ofCertJson? (PyType.toCertJson (.dict .str (.list (.opt .int))))
          == some (.dict .str (.list (.opt .int))))
#guard (PyType.ofCertJson? (PyType.toCertJson (.fn [.int, .str] (.tuple [.bool, .none])))
          == some (.fn [.int, .str] (.tuple [.bool, .none])))
#guard (PyType.ofCertJson? (PyType.toCertJson (.cls "TreeNode")) == some (.cls "TreeNode"))
#guard match Cert.ofCertJson? cert.toCertJson with
       | some c => validate ast c
       | none => false
