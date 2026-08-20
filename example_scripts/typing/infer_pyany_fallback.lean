import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

-- Un-inferrable parameters that are used as containers (subscript / iterate / len) box to PyAny,
-- so the program stays total. In prove mode each PyAny binder is flagged as unprovable.
-- `data` has no annotation and its element type is never pinned (indexing is ambiguous), so it boxes
-- to PyAny and `data[0]` still elaborates via the delegating PyGetItem instance.
def first_item := fun (data : PyAny) ↦ (data⦋(0 : Int)⦌ : PastaLean.PyAny)

attribute [simp] first_item

def first_item'rn := fun (data : PyAny) ↦ (data⦋(0 : Int)⦌ : PastaLean.PyAny)

-- `xs` used by len() and a for-loop; still un-inferrable, boxed to PyAny.
def count_items := fun (xs : List Int) ↦
  Id.run
    (do
      let mut n : Int := (0 : Int)
      for _ in (PastaLean.pyIter xs) do
        n := n +ₚ (1 : Int)
      return n)

attribute [simp, taste_ingr] count_items

def count_items'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut n : Int := (0 : Int)
      for _ in (PastaLean.pyIter xs) do
        n := n +ₚ (1 : Int)
      return n)

def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputLines := String.splitOn inputText "\n"
  let inputStream : PastaLean.ProofMode.IOStream :=
    ⟨0, fun i => PastaLean.ProofMode.IOResult.success (List.getD inputLines i "")⟩
  let initState : PastaLean.ProofMode.IOState := ⟨inputStream, []⟩
  let (result, finalState) :=
    (((do
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (first_item [(10 : Int), (20 : Int), (30 : Int)])]
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (first_item ["a", "b"])]
          let _ ←
            PastaLean.ProofMode.pyPrintProof [pyPrintArg (count_items [(1 : Int), (2 : Int), (3 : Int), (4 : Int)])]
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
  let _ ← pyPrintIO [pyPrintArg (first_item'rn [(10 : Int), (20 : Int), (30 : Int)])]
  let _ ← pyPrintIO [pyPrintArg (first_item'rn ["a", "b"])]
  let _ ← pyPrintIO [pyPrintArg (count_items'rn [(1 : Int), (2 : Int), (3 : Int), (4 : Int)])]
  pure ()