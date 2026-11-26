import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- An array-backed `[True]*n` sieve whose slice result is assigned to a new variable.
-- Regression: the slice-result binder (`head`) must follow the source's backing — in the run twin
-- `sieve` is `Array Bool`, so `sieve[:k]` is `Array Bool`, and stamping `head : List Bool` would clash
-- (`PySlice (Array β)` returns `Array β`). Also checks `[x]*n` under a heap cell emits `pyListRepeat`
-- a bare list, not an `(← allocM …)` ref.
def count_primes := fun (n : Int) ↦
  Id.run
    (do
      let mut sieve : List Bool := PastaLean.pyListRepeat [Bool.true] n
      let mut ans : Int := (0 : Int)
      for i in (PastaLean.pyRange n (2 : Int)) do
        if h_1 : PastaLean.pyTruthy sieve⦋i⦌ then 
          ans := ans +ₚ (1 : Int)
          for j in (PastaLean.pyRange n (i +ₚ i) i) do
            sieve := PastaLean.pySetItem sieve j Bool.false
      let mut head : List Bool := PastaLean.pySlice sieve none (some (PastaLean.pyFloorDiv n (2 : Int))) none
      let p'_ret_1 := ans +ₚ PastaLean.pyLen head
      return p'_ret_1)

attribute [simp, taste_ingr] count_primes

def count_primes'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut sieve : Array Bool := PastaLean.pyArrayRepeat #[Bool.true] n
      let mut ans : Int := (0 : Int)
      for i in (PastaLean.pyRange n (2 : Int)) do
        if h_1 : PastaLean.pyTruthy sieve⦋i⦌ then 
          ans := ans +ₚ (1 : Int)
          for j in (PastaLean.pyRange n (i +ₚ i) i) do
            sieve := PastaLean.pySetItem sieve j Bool.false
      let mut head : Array Bool := PastaLean.pySlice sieve none (some (PastaLean.pyFloorDiv n (2 : Int))) none
      let p'_ret_1 := ans +ₚ PastaLean.pyLen head
      return p'_ret_1)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (count_primes (50 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (count_primes'rn (50 : Int))]) :
    IO _)

end PastaLean.User.Root
