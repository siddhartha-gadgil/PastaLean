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

-- Exercises the Array-backed list methods in the runnable twin: an O(1) stack
-- (append/pop under `while st:`), plus reverse/insert/count/index/clear.
def stack_sum := fun (n : Int) ↦
  Id.run
    (do
      let mut st : List Int := []
      for i in (PastaLean.pyRange n)do
        st := PastaLean.pyAppend st i
      let mut total : Int := (0 : Int)
      while (PastaLean.pyTruthy st) do
        let mut p'_popv_1 := PastaLean.pyPopValue st
        st := PastaLean.pyPopRest st
        total := total +ₚ p'_popv_1
      return total)

attribute [simp, taste_ingr] stack_sum

def stack_sum'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut st : Array Int := #[]
      for i in (PastaLean.pyRange n)do
        st := PastaLean.pyArrayAppend st i
      let mut total : Int := (0 : Int)
      while (PastaLean.pyTruthy st) do
        let mut p'_popv_1 := PastaLean.pyArrayPopValue st
        st := PastaLean.pyArrayPopRest st
        total := total +ₚ p'_popv_1
      return total)

def list_ops :=
  Id.run
    (do
      let mut xs : List Int := [(3 : Int), (1 : Int), (2 : Int), (1 : Int)]
      xs := PastaLean.pyInsert xs (0 : Int) (9 : Int)
      xs := PastaLean.pyReverse xs
      let mut ones : Int := PastaLean.pyCount xs (1 : Int)
      let mut two_at : Int := PastaLean.pyIndex xs (2 : Int)
      xs := PastaLean.pyClear xs
      let p'_ret_1 := ones +ₚ two_at +ₚ PastaLean.pyLen xs
      return p'_ret_1)

attribute [simp, taste_ingr] list_ops

def list_ops'rn :=
  Id.run
    (do
      let mut xs : Array Int := #[(3 : Int), (1 : Int), (2 : Int), (1 : Int)]
      xs := PastaLean.pyArrayInsert xs (0 : Int) (9 : Int)
      xs := PastaLean.pyArrayReverse xs
      let mut ones : Int := PastaLean.pyCount xs (1 : Int)
      let mut two_at : Int := PastaLean.pyIndex xs (2 : Int)
      xs := PastaLean.pyClear xs
      let p'_ret_1 := ones +ₚ two_at +ₚ PastaLean.pyLen xs
      return p'_ret_1)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (stack_sum (5 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg list_ops]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (stack_sum'rn (5 : Int))]
      let _ ← pyPrintIO [pyPrintArg list_ops'rn]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
