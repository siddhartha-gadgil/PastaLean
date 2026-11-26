import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- `global` for a read-only module global: the declaration is a no-op and the name
-- resolves to the top-level def. (A `global` that *mutates* is a loud refusal.)
def LIMIT :=
  (100 : Int)

def settings :=
  Std.HashMap.ofList [("scale", (3 : Int))]

def scaled := fun (x : Int) ↦
  Id.run
    (do
      let _ := ()
      let p'_ret_1 := x *ₚ settings⦋"scale"⦌
      return p'_ret_1)

attribute [simp, taste_ingr] scaled

def scaled'rn := fun (x : Int) ↦
  Id.run
    (do
      let _ := ()
      let p'_ret_1 := x *ₚ settings⦋"scale"⦌
      return p'_ret_1)

def within := fun (x : Int) ↦
  Id.run
    (do
      let _ := ()
      let p'_ret_1 := decide (x < LIMIT)
      return p'_ret_1)

attribute [simp, taste_ingr] within

def within'rn := fun (x : Int) ↦
  Id.run
    (do
      let _ := ()
      let p'_ret_1 := decide (x < LIMIT)
      return p'_ret_1)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (scaled (5 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (within (50 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (scaled'rn (5 : Int))]
      let _ ← pyPrintIO [pyPrintArg (within'rn (50 : Int))]) :
    IO _)

end PastaLean.User.Root
