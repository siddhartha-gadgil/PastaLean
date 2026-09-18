import TypeInfer.Diagnostics.Basic

/-!
# Rendering a diagnostic

The checker reports about a Python program, but what it actually enforces is the type of the LEAN
the transpiler will emit — so an error reads like a Lean type error, with the Python type it came
from as a Lean line comment next to it:

```
error: type mismatch
  total.n
has type
  String                          -- python: str
but is expected to have type
  Int                             -- python: int
```

`PyType.toLeanName` is the string mirror of `TypeInfer.toTypeSyntax?` (`TypeInfer/Emit.lean`), which
builds the same types as `Syntax` for codegen; keep the two in step. `float` is shown as the default
exact-mode `ℚ` (it is `ℝ` in a real-marked context and `Float` under `--approx`).
-/

namespace TypeInfer

open Lean

/-- The Lean type the runtime lowers a `PyType` to. `paren` wraps applied types when they sit in an
argument position (`List (Option Int)`). -/
partial def PyType.toLeanName (paren : Bool := false) : PyType → String
  | .unknown => "?"
  | .any => "PyAny"
  | .int => "Int"
  | .bool => "Bool"
  | .str => "String"
  | .float => "ℚ"
  | .none => "Unit"
  | .cls n => n
  | .list e => wrap paren s!"List {toLeanName true e}"
  | .set e => wrap paren s!"PySet {toLeanName true e}"
  | .opt e => wrap paren s!"Option {toLeanName true e}"
  | .dict k v => wrap paren s!"Std.HashMap {toLeanName true k} {toLeanName true v}"
  | .tuple es =>
      match es with
      | [] => "Unit"
      | [only] => toLeanName paren only
      | es => wrap paren (String.intercalate " × " (es.map (toLeanName true)))
  | .fn as r =>
      let args := if as.isEmpty then ["Unit"] else as.map (toLeanName true)
      wrap paren (String.intercalate " → " (args ++ [toLeanName true r]))
where
  wrap (p : Bool) (s : String) : String := if p then s!"({s})" else s

/-- One `  <lean type>    -- python: <python type>` line, the Python gloss aligned across a block. -/
private def typeLine (t : PyType) (width : Nat) : String :=
  let lean := t.toLeanName
  let pad := "".pushn ' ' (width + 2 - min width lean.length)
  s!"  {lean}{pad}-- python: {t}"

/-- Lean-style rendering: a headline, the slot, and the two types with their Python originals.
`file` prefixes the headline the way Lean prefixes a message with its source file. -/
def Diagnostic.render (d : Diagnostic) (file : String := "") : String :=
  let width := max (d.expected.toLeanName).length (d.actual.toLeanName).length
  let loc := if file.isEmpty then "" else s!"{file}: "
  let block (headline actualLabel expectedLabel : String) : String :=
    s!"{loc}error: {headline}\n  {d.subject}\n{actualLabel}\n{typeLine d.actual width}\n" ++
      s!"{expectedLabel}\n{typeLine d.expected width}"
  match d.kind with
  | .annotationMismatch | .valueRejected =>
      block "type mismatch" "has type" "but is expected to have type"
  | .useConflict =>
      block "unsatisfiable constraints" "one use requires" "another use requires" ++
        "\nno type satisfies both"

/-- One-line form, for callers that want a diagnostic per line. -/
def Diagnostic.message (d : Diagnostic) : String :=
  match d.kind with
  | .useConflict =>
      s!"{d.subject}: uses require both {d.expected.toLeanName} ({d.expected}) and " ++
        s!"{d.actual.toLeanName} ({d.actual}), which no type satisfies"
  | .annotationMismatch | .valueRejected =>
      s!"{d.subject}: has type {d.actual.toLeanName} ({d.actual}), expected " ++
        s!"{d.expected.toLeanName} ({d.expected})"

/-- Both renderings plus the raw fields, so a client can reformat without re-deriving anything. -/
def Diagnostic.toJson (d : Diagnostic) : Json :=
  Json.mkObj
    [ ("scope", .str d.scope), ("slot", .str d.slot), ("kind", .str (toString d.kind)),
      ("expected", .str (toString d.expected)), ("actual", .str (toString d.actual)),
      ("lean_expected", .str d.expected.toLeanName), ("lean_actual", .str d.actual.toLeanName),
      ("message", .str d.message), ("render", .str (d.render)) ]

end TypeInfer
