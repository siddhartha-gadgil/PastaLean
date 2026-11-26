import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- A user function named `max` shadows Python's builtin AND Lean's `Max.max`; every call must resolve
-- to the user's def (renamed internally so it isn't ambiguous). `str.startswith`/`endswith` with a
-- start (and end) index restrict the check to a slice.
def max'usr := fun (a : Int) ↦ fun (b : Int) ↦ if a > b then a else b

attribute [simp, taste_ingr] max'usr

def max'usr'rn := fun (a : Int) ↦ fun (b : Int) ↦ if a > b then a else b

def best := fun (xs : List Int) ↦
  Id.run
    (do
      let mut ans : Int := xs⦋(0 : Int)⦌
      for x in (PastaLean.pyIter xs) do
        ans := max'usr ans x
      return ans)

attribute [simp, taste_ingr] best

def best'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut ans : Int := xs⦋(0 : Int)⦌
      for x in (PastaLean.pyIter xs) do
        ans := max'usr'rn ans x
      return ans)

def count_prefixes := fun (s : String) ↦ fun (p : String) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange (PastaLean.pyLen s)) do
        if h_1 : PastaLean.pyTruthy (PastaLean.pyStringStartswith s p i) then 
          total := total +ₚ (1 : Int)
      return total)

attribute [simp, taste_ingr] count_prefixes

def count_prefixes'rn := fun (s : String) ↦ fun (p : String) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange (PastaLean.pyLen s)) do
        if h_1 : PastaLean.pyTruthy (PastaLean.pyStringStartswith s p i) then 
          total := total +ₚ (1 : Int)
      return total)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof [pyPrintArg (best [(3 : Int), (7 : Int), (2 : Int), (9 : Int), (4 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (count_prefixes "ababab" "ab")]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (PastaLean.pyStringEndswith "hello world" "lo" (0 : Int) (5 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (best'rn [(3 : Int), (7 : Int), (2 : Int), (9 : Int), (4 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (count_prefixes'rn "ababab" "ab")]
      let _ ← pyPrintIO [pyPrintArg (PastaLean.pyStringEndswith "hello world" "lo" (0 : Int) (5 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
