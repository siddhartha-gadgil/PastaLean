import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- SSA renaming on TYPE MUTATIONS: `digits` holds a list[str] before the branch and a list[int] after,
-- reassigned to a different element type inside both branches. SSA versions it (`digits`, `digits'vN`)
-- so each is typed CONCRETELY (List String / List Int) instead of boxed to PyAny, and the branch join
-- is a hoisted phi. Both branches agree on the new type, so the merge stays concrete.
def digit_parity := fun (x : Int) ↦
  Id.run
    (do
      let mut digits : List String := PastaLean.pyList (PastaLean.pyStr x)
      let mut digits'v3 : List Int := default
      if h_1 : digits⦋(0 : Int)⦌ = "-" then 
        let mut digits'v1 : List Int :=
          PastaLean.pyList (PastaLean.pyMap PastaLean.pyInt (PastaLean.pySlice digits (some (1 : Int)) none none))
        digits'v3 := digits'v1
      else
        let mut digits'v2 : List Int := PastaLean.pyList (PastaLean.pyMap PastaLean.pyInt digits)
        digits'v3 := digits'v2
      let p'_ret_1 :=
        PastaLean.pySum (List.filter (fun (d : Int) => d %ₚ (2 : Int) = (0 : Int)) (PastaLean.pyIter digits'v3))
      return p'_ret_1)

attribute [simp, taste_ingr] digit_parity

def digit_parity'rn := fun (x : Int) ↦
  Id.run
    (do
      let mut digits : List String := PastaLean.pyList (PastaLean.pyStr x)
      let mut digits'v3 : List Int := default
      if h_1 : digits⦋(0 : Int)⦌ == "-" then 
        let mut digits'v1 : List Int :=
          PastaLean.pyList (PastaLean.pyMap PastaLean.pyInt (PastaLean.pySlice digits (some (1 : Int)) none none))
        digits'v3 := digits'v1
      else
        let mut digits'v2 : List Int := PastaLean.pyList (PastaLean.pyMap PastaLean.pyInt digits)
        digits'v3 := digits'v2
      let p'_ret_1 :=
        PastaLean.pySum (List.filter (fun (d : Int) => d %ₚ (2 : Int) == (0 : Int)) (PastaLean.pyIter digits'v3))
      return p'_ret_1)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (digit_parity (2468 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (digit_parity (13579 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (digit_parity'rn (2468 : Int))]
      let _ ← pyPrintIO [pyPrintArg (digit_parity'rn (13579 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
