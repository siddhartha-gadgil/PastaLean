import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Two performance patterns that must NOT be O(n²)/O(n):
-- 1. `[x]*n` array-backing — a sieve does many `a[i]=v`; without Array backing each is an O(n) copy.
-- 2. `bisect_left(range(...), key=f)` — must binary-search the range lazily, not materialize + map key.
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
      return ans)

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
      return ans)

def isqrt_via_bisect := fun (num : Int) ↦
  -- first x in [1, num+1) with x*x > num, minus 1  → floor(sqrt(num))
  Libraries.bisect.pyBisectLeftRangeKey (1 : Int) (num +ₚ (1 : Int)) (1 : Int) (num +ₚ (1 : Int)) (key :=
    fun (x : Int) ↦ x *ₚ x)

attribute [simp, taste_ingr] isqrt_via_bisect

def isqrt_via_bisect'rn := fun (num : Int) ↦
  -- first x in [1, num+1) with x*x > num, minus 1  → floor(sqrt(num))
  Libraries.bisect.pyBisectLeftRangeKey (1 : Int) (num +ₚ (1 : Int)) (1 : Int) (num +ₚ (1 : Int)) (key :=
    fun (x : Int) ↦ x *ₚ x)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (count_primes (100 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (count_primes (1000 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (isqrt_via_bisect (24 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (isqrt_via_bisect (25 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (count_primes'rn (100 : Int))]
      let _ ← pyPrintIO [pyPrintArg (count_primes'rn (1000 : Int))]
      let _ ← pyPrintIO [pyPrintArg (isqrt_via_bisect'rn (24 : Int))]
      let _ ← pyPrintIO [pyPrintArg (isqrt_via_bisect'rn (25 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
