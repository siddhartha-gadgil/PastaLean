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

partial def gcd : Int → Int → Int := fun (x : Int) ↦ fun (y : Int) ↦ if y = (0 : Int) then x else gcd y (x %ₚ y)

partial def gcd'rn : Int → Int → Int := fun (x : Int) ↦ fun (y : Int) ↦ if y == (0 : Int) then x else gcd'rn y (x %ₚ y)

def chk := fun (n1 : Int) ↦ fun (n2 : Int) ↦ if gcd n1 n2 = (1 : Int) then (1 : Int) else (0 : Int)

attribute [simp, taste_ingr] chk

def chk'rn := fun (n1 : Int) ↦ fun (n2 : Int) ↦ if gcd'rn n1 n2 == (1 : Int) then (1 : Int) else (0 : Int)

def count_beautiful_pairs := fun (nums : List Int) ↦
  Id.run
    (do
      let mut n : Int := PastaLean.pyLen nums
      let mut ans : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange n)do
        for j in (PastaLean.pyRange i)do
          ans := ans +ₚ chk nums⦋j⦌ (PastaLean.pyListGetProof nums i (PastaLean.pyRange_len_bound_of_eq rfl hb'i))
      return ans)

attribute [simp, taste_ingr] count_beautiful_pairs

def count_beautiful_pairs'rn := fun (nums : List Int) ↦
  Id.run
    (do
      let mut n : Int := PastaLean.pyLen nums
      let mut ans : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange n)do
        for j in (PastaLean.pyRange i)do
          ans := ans +ₚ chk'rn nums⦋j⦌ (PastaLean.pyListGetProof nums i (PastaLean.pyRange_len_bound_of_eq rfl hb'i))
      return ans)

mutual
  partial def is_even : Int → Bool := fun (n : Int) ↦ if n = (0 : Int) then Bool.true else is_odd (n -ₚ (1 : Int))
  partial def is_odd : Int → Bool := fun (n : Int) ↦ if n = (0 : Int) then Bool.false else is_even (n -ₚ (1 : Int))
end

mutual
  partial def is_even'rn : Int → Bool := fun (n : Int) ↦
    if n == (0 : Int) then Bool.true else is_odd'rn (n -ₚ (1 : Int))
  partial def is_odd'rn : Int → Bool := fun (n : Int) ↦
    if n == (0 : Int) then Bool.false else is_even'rn (n -ₚ (1 : Int))
end

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (count_beautiful_pairs [(2 : Int), (3 : Int), (4 : Int), (5 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (is_even (10 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (count_beautiful_pairs'rn [(2 : Int), (3 : Int), (4 : Int), (5 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (is_even'rn (10 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
