import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

/-
Demonstration of Unsupported syntax or libraries (logging, requests, random) don't abort
the whole translation — those lines become `pyUnsupported(...)` placeholders that carry the
original Python source, and the rest of the program transpiles and runs normally.
-/
def logger :=
  pyUnsupported "logger = logging.getLogger(__name__)"

def total_score := fun (scores : List Int) ↦
  Id.run
    (do
      let _ := pyUnsupported "logger.info(\"scoring\")"
      let mut blob := pyUnsupported "blob = requests.get(\"http://x\")"
      let mut total : Int := (0 : Int)
      for s in (PastaLean.pyIter scores) do
        total := total +ₚ s
      return total)

attribute [simp, taste_ingr] total_score

def total_score'rn := fun (scores : List Int) ↦
  Id.run
    (do
      let _ := pyUnsupported "logger.info(\"scoring\")"
      let mut blob := pyUnsupported "blob = requests.get(\"http://x\")"
      let mut total : Int := (0 : Int)
      for s in (PastaLean.pyIter scores) do
        total := total +ₚ s
      return total)

def main' :=
  ((do
      let _ := pyUnsupported "logging.basicConfig(level=logging.INFO)"
      let mut scores : List Int := [(10 : Int), (20 : Int), (30 : Int), (40 : Int)]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "total", pyPrintArg (total_score scores)]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "doubled", pyPrintArg (total_score scores *ₚ (2 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ := pyUnsupported "logging.basicConfig(level=logging.INFO)"
      let mut scores : List Int := [(10 : Int), (20 : Int), (30 : Int), (40 : Int)]
      let _ ← pyPrintIO [pyPrintArg "total", pyPrintArg (total_score'rn scores)]
      let _ ← pyPrintIO [pyPrintArg "doubled", pyPrintArg (total_score'rn scores *ₚ (2 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()