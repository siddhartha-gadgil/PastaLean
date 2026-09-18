import TypeInfer.Diagnostics

/-! Unit checks for the checker (`TypeInfer/Diagnostics/`): the requirement algebra, the judgments
built on it, and the Lean-first rendering of a diagnostic. -/

open Lean TypeInfer

/-! ### `Req` — requirements meet, they do not join -/

-- "Nothing required yet" is the neutral element; a real requirement survives it.
#guard Req.narrow Req.top (Req.ofEvidence .str) == some PyType.str
#guard Req.ofEvidence PyType.unknown == Req.top

-- Requirements no type satisfies collapse to the absorbing point, and `commit?` refuses to answer
-- rather than boxing the conflict as `PyAny` (which is what folding with `join` used to do).
#guard (Req.ofEvidenceAll [.str, .int]).contradictory
#guard (Req.ofEvidenceAll [.str, .int]).commit? == (none : Option PyType)
#guard (Req.ofEvidenceAll [.str, .int]).toInferred == PyType.any
#guard (Req.ofEvidenceAll [.str, .str]).commit? == some PyType.str

/-! ### The judgments -/

-- Gradual by design: `unknown` on either side is "no static claim".
#guard (checkAnnotation "f" "x" .int .unknown).isNone
#guard (checkAnnotation "f" "x" .unknown .str).isNone
#guard (checkAnnotation "f" "x" .int .int).isNone
-- `bool` is an `int` in Python, so the numeric tower must not be flagged.
#guard (checkAnnotation "f" "x" .int .bool).isNone
#guard (checkAnnotation "f" "x" .int .str).isSome

#guard (checkValue "f" "x" (Req.ofEvidence .str) .int).isSome
#guard (checkValue "f" "x" Req.top .int).isNone
#guard (checkUses "f" "p" [.str, .int]).2.length == 1
#guard (checkUses "f" "p" [.str, .str]).2.isEmpty

/-! ### Rendering — Lean types first, the Python type as a line comment -/

#guard PyType.toLeanName (paren := false) (.list (.opt .int)) == "List (Option Int)"
#guard PyType.toLeanName (paren := false) (.dict .str (.list .int)) == "Std.HashMap String (List Int)"
#guard PyType.toLeanName (paren := false) (.fn [.int, .str] .bool) == "Int → String → Bool"
#guard PyType.toLeanName (paren := false) (.tuple [.int, .str]) == "Int × String"

/--
info: "error: type mismatch\n  total.n\nhas type\n  String  -- python: str\nbut is expected to have type\n  Int     -- python: int"
-/
#guard_msgs in
#eval ({ scope := "total", slot := "n", kind := .annotationMismatch,
         expected := .int, actual := .str : Diagnostic }).render

-- The file prefixes the headline, the way Lean prefixes a message with its source.
#guard (({ scope := "", slot := "p", kind := .useConflict, expected := .str,
           actual := .int : Diagnostic }).render "a.py").startsWith "a.py: error: unsatisfiable"
