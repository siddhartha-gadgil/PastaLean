import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

-- Test: Nested try-catch with IO
def main' :=
  ((do
      try
        let mut x : Int := PastaLean.pyInt (← (PastaLean.ProofMode.pyInputProof ""))
        let mut y := default
        try
          y := (10 : Int) /ₚ x
        catch caught =>
          if Bool.true then 
            y := (0 : Rat)
          else
            throw caught
        let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg y]
      catch caught =>
        if Bool.true then 
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "error"]
        else
          throw caught) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      try
        let mut x : Int := PastaLean.pyInt (← PastaLean.PyExcept.captureIOErrors (PastaLean.pyInputIO ""))
        let mut y := default
        try
          y := PastaLean.pyFloat (10 : Int) /ₚ x
        catch caught =>
          if Bool.true then 
            y := (0 : Float)
          else
            throw caught
        let _ ← pyPrintIO [pyPrintArg y]
      catch caught =>
        if Bool.true then 
          let _ ← pyPrintIO [pyPrintArg "error"]
        else
          throw caught) :
    PastaLean.PyExcept _)