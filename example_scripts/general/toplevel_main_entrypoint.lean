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

-- Lean reserves `main` for the executable entry point, while Python's `main()` is just a
-- function. When both a `def main()` and an `if __name__ == "__main__"` guard exist, the
-- Python function yields the name to the guard: it is renamed to `main'` (along with every
-- call site), and the guard body becomes Lean's `def main : IO Unit`. We use `main'` rather
-- than `_main` because `'` is unusable in a Python identifier, so it can never collide with
-- a user-defined helper (a `_main` helper, by contrast, is perfectly legal Python).
def main' :=
  "hello"

attribute [simp, taste_ingr] main'

def main''rn :=
  "hello"

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
