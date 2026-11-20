import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Regression: a user-defined `_main` helper must not collide with the renamed entry point.
-- Python's `main()` is renamed to `main'` (not `_main`) when it coexists with a `__main__`
-- guard, precisely so the existing `_main` helper is left untouched. Here `_main` stays a
-- `private def _main` (its own name), `main` becomes `main'`, the call `main()` inside the
-- guard is rewritten to `main'`, and the guard owns Lean's `def main : IO Unit`.
private def _main :=
  "helper"

attribute [simp, taste_ingr] _main

private def _main'rn :=
  "helper"

def main' :=
  _main

attribute [simp, taste_ingr] main'

def main''rn :=
  _main'rn

def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputStream : PastaLean.ProofMode.IOStream := PastaLean.ProofMode.IOStream.ofText inputText
  let initState : PastaLean.ProofMode.IOState := { input := inputStream, output := [] }
  let (result, finalState) :=
    (((do
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg main']
          pure ()) :
        PastaLean.ProofMode.PyProofM Unit))
      initState
  let outputLines := finalState.output
  for line in outputLines do
    IO.print line
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

def main'rn : IO Unit := do
  let _ ← pyPrintIO [pyPrintArg main''rn]
  pure ()

end PastaLean.User.Root
