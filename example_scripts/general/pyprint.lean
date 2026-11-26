import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def pyprint_basic : PastaLean.ProofMode.PyProofM Int := do
  let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "sum", pyPrintArg (3 : Int), pyPrintArg (4 : Int)]
  return (7 : Int)

attribute [simp] pyprint_basic

def pyprint_basic'rn : IO Int := do
  let _ ← pyPrintIO [pyPrintArg "sum", pyPrintArg (3 : Int), pyPrintArg (4 : Int)]
  return (7 : Int)

def pyprint_keywords : PastaLean.ProofMode.PyProofM String := do
  let mut a : List String := ["a", "b", "c"]
  let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "a", pyPrintArg "b", pyPrintArg "c"] "|" "!"
  let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "{a}"]
  return "ok"

attribute [simp] pyprint_keywords

def pyprint_keywords'rn : IO String := do
  let mut a : List String := ["a", "b", "c"]
  let _ ← pyPrintIO [pyPrintArg "a", pyPrintArg "b", pyPrintArg "c"] "|" "!"
  let _ ← pyPrintIO [pyPrintArg s! "{a}"]
  return "ok"

end PastaLean.User.Root
