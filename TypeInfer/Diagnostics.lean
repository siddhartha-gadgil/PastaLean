import TypeInfer.Diagnostics.Basic
import TypeInfer.Diagnostics.Render
import TypeInfer.Diagnostics.Pass

/-!
# The checker

Everything that lets the engine say **no**, rather than widen a disagreement to `any` and box it:

* `Diagnostics/Basic.lean` — the requirement algebra (`Req`) and the checks over it
  (`checkAnnotation`, `checkValue`, `checkUses`), plus the `Diagnostic` record they report.
* `Diagnostics/Render.lean` — how a diagnostic is shown: Lean types (the ones codegen will emit)
  with the Python type as a line comment, in Lean's own "has type / but is expected to have type"
  shape, and the JSON the `checkTypes` task returns.
* `Diagnostics/Pass.lean` — the pass itself: walk an already-stamped module and read the verdicts
  off, against a second inference of the SAME module with every annotation stripped. It yields
  `Slot`s and derives the diagnostics from them (`certifyModule`), which is what keeps the evidence
  behind each verdict instead of discarding it — see `TypeInfer/Certificate.lean`.
-/
