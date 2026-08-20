import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

def total := fun (xs : List Int) ↦
  Id.run
    (do
      let mut s : Int := (0 : Int)
      for x in (PastaLean.pyIter xs) do
        s := s +ₚ x
      return s)

attribute [simp, taste_ingr] total

def total'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut s : Int := (0 : Int)
      for x in (PastaLean.pyIter xs) do
        s := s +ₚ x
      return s)

def scale := fun (row : List Rat) ↦ fun (k : Rat) ↦
  Id.run
    (do
      let mut out := ([] : List Rat)
      for v in (PastaLean.pyIter row) do
        out := PastaLean.pyAppend out (v *ₚ k)
      return out)

attribute [simp, taste_ingr] scale

def scale'rn := fun (row : List Float) ↦ fun (k : Float) ↦
  Id.run
    (do
      let mut out := ([] : List Float)
      for v in (PastaLean.pyIter row) do
        out := PastaLean.pyAppend out (v *ₚ k)
      return out)

def label := fun (pairs : Std.HashMap String Int) ↦ fun (key : String) ↦ PastaLean.pyGetD pairs key (0 : Int)

attribute [simp, taste_ingr] label

def label'rn := fun (pairs : Std.HashMap String Int) ↦ fun (key : String) ↦ PastaLean.pyGetD pairs key (0 : Int)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg "total", pyPrintArg (total [(1 : Int), (2 : Int), (3 : Int), (4 : Int)])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg "scaled", pyPrintArg (scale [(1.0 : Rat), (2.0 : Rat)] (3.0 : Rat))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg "total", pyPrintArg (total'rn [(1 : Int), (2 : Int), (3 : Int), (4 : Int)])]
      let _ ← pyPrintIO [pyPrintArg "scaled", pyPrintArg (scale'rn [(1.0 : Float), (2.0 : Float)] (3.0 : Float))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()