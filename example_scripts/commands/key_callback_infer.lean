import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- A named nested def passed as `key=` is never called by name, so its param type must be inferred from
-- the collection the key ranges over (here `range(n)` → int). Both `min(..., key=f)` and
-- `sorted(..., key=f)` exercise it; a `key=lambda` (already handled) is included as a control.
private def _best_index'score := fun (i : Int) ↦ fun (vals : List Int) ↦ vals⦋i⦌ *ₚ (2 : Int) -ₚ i

attribute [simp, taste_ingr] _best_index'score

def best_index := fun (vals : List Int) ↦
  let n := (PastaLean.pyLen vals : Int)
  PastaLean.pyMinBy (fun (i : Int) ↦ _best_index'score i vals) (PastaLean.pyRange n)

attribute [simp, taste_ingr] best_index

private def _best_index'score'rn := fun (i : Int) ↦ fun (vals : List Int) ↦ vals⦋i⦌ *ₚ (2 : Int) -ₚ i

def best_index'rn := fun (vals : List Int) ↦
  let n := (PastaLean.pyLen vals : Int)
  PastaLean.pyMinBy (fun (i : Int) ↦ _best_index'score'rn i vals) (PastaLean.pyRange n)

private def _sort_by_last_digit'last_digit := fun (x : Int) ↦ x %ₚ (10 : Int)

attribute [simp, taste_ingr] _sort_by_last_digit'last_digit

def sort_by_last_digit := fun (nums : List Int) ↦ PastaLean.pySortBy _sort_by_last_digit'last_digit false nums

attribute [simp, taste_ingr] sort_by_last_digit

private def _sort_by_last_digit'last_digit'rn := fun (x : Int) ↦ x %ₚ (10 : Int)

def sort_by_last_digit'rn := fun (nums : List Int) ↦ PastaLean.pySortBy _sort_by_last_digit'last_digit false nums

def sort_desc := fun (nums : List Int) ↦ PastaLean.pySortBy (fun (v : Int) ↦ -v) false nums

attribute [simp, taste_ingr] sort_desc

def sort_desc'rn := fun (nums : List Int) ↦ PastaLean.pySortBy (fun (v : Int) ↦ -v) false nums

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (best_index [(5 : Int), (1 : Int), (9 : Int), (2 : Int)])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (sort_by_last_digit [(23 : Int), (41 : Int), (15 : Int), (8 : Int)])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (sort_desc [(3 : Int), (1 : Int), (4 : Int), (1 : Int), (5 : Int)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (best_index'rn [(5 : Int), (1 : Int), (9 : Int), (2 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (sort_by_last_digit'rn [(23 : Int), (41 : Int), (15 : Int), (8 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (sort_desc'rn [(3 : Int), (1 : Int), (4 : Int), (1 : Int), (5 : Int)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
