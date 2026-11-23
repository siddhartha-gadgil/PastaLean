import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- A local variable's explicit annotation is authoritative and sticky: `acc: list[int] = []` stays
-- `list[int]` even though it is built by appending, and the return follows it. Regression for the
-- node_visitor dropping the annotation on an initialized `x: T = v` (collapsed to a plain Assign).
def collect := fun (xs : List Int) ↦
  Id.run
    (do
      let mut acc : List Int := []
      for x in (PastaLean.pyIter xs) do
        acc := PastaLean.pyAppend acc (x *ₚ (2 : Int))
      return acc)

attribute [simp, taste_ingr] collect

def collect'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut acc : List Int := []
      for x in (PastaLean.pyIter xs) do
        acc := PastaLean.pyAppend acc (x *ₚ (2 : Int))
      return acc)

def counts := fun (words : List String) ↦
  Id.run
    (do
      let mut d : Std.HashMap String Int := Std.HashMap.ofList []
      for w in (PastaLean.pyIter words) do
        d := PastaLean.pySetItem d w (PastaLean.pyGetD d w (0 : Int) +ₚ (1 : Int))
      return d)

attribute [simp, taste_ingr] counts

def counts'rn := fun (words : List String) ↦
  Id.run
    (do
      let mut d : Std.HashMap String Int := Std.HashMap.ofList []
      for w in (PastaLean.pyIter words) do
        d := PastaLean.pySetItem d w (PastaLean.pyGetD d w (0 : Int) +ₚ (1 : Int))
      return d)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (collect [(1 : Int), (2 : Int), (3 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (counts ["a", "b", "a"])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (collect'rn [(1 : Int), (2 : Int), (3 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (counts'rn ["a", "b", "a"])]) :
    IO _)

end PastaLean.User.Root
