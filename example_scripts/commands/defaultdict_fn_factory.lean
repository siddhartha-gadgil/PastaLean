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

private def _count_interesting'zero :=
  (0 : Int)

attribute [simp, taste_ingr] _count_interesting'zero

def count_interesting := fun (nums : List Int) ↦ fun (m : Int) ↦ fun (k : Int) ↦
  Id.run
    (do
      let mut n : Int := PastaLean.pyLen nums
      let mut a : List Int := (PastaLean.pyRange (n +ₚ (1 : Int))).map fun (_ : Int) => (0 : Int)
      for hb'i : i in (PastaLean.pyRange n)do
        if h_1 : PastaLean.pyListGetProof nums i (PastaLean.pyRange_len_bound_of_eq rfl hb'i) %ₚ m = k then 
          a := PastaLean.pySetItem a (i +ₚ (1 : Int)) (1 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        a := PastaLean.pySetItem a i (a⦋i⦌ +ₚ a⦋i -ₚ (1 : Int)⦌)
      let mut cnt : Libraries.collections.PyDefaultDict Int Int := Libraries.collections.PyDefaultDict.empty (0 : Int)
      let mut ans : Int := (0 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)))do
        ans := ans +ₚ cnt⦋(a⦋i⦌ -ₚ k +ₚ m) %ₚ m⦌
        cnt := PastaLean.pySetItem cnt (a⦋i⦌ %ₚ m) (cnt⦋a⦋i⦌ %ₚ m⦌ +ₚ (1 : Int))
      return ans)

attribute [simp, taste_ingr] count_interesting

private def _count_interesting'zero'rn :=
  (0 : Int)

def count_interesting'rn := fun (nums : List Int) ↦ fun (m : Int) ↦ fun (k : Int) ↦
  Id.run
    (do
      let mut n : Int := PastaLean.pyLen nums
      let mut a : Array Int := ((PastaLean.pyRange (n +ₚ (1 : Int))).map fun (_ : Int) => (0 : Int)) |>.toArray
      for hb'i : i in (PastaLean.pyRange n)do
        if h_1 : PastaLean.pyListGetProof nums i (PastaLean.pyRange_len_bound_of_eq rfl hb'i) %ₚ m == k then 
          a := PastaLean.pySetItem a (i +ₚ (1 : Int)) (1 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        a := PastaLean.pySetItem a i (a⦋i⦌ +ₚ a⦋i -ₚ (1 : Int)⦌)
      let mut cnt : Libraries.collections.PyDefaultDict Int Int := Libraries.collections.PyDefaultDict.empty (0 : Int)
      let mut ans : Int := (0 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)))do
        ans := ans +ₚ cnt⦋(a⦋i⦌ -ₚ k +ₚ m) %ₚ m⦌
        cnt := PastaLean.pySetItem cnt (a⦋i⦌ %ₚ m) (cnt⦋a⦋i⦌ %ₚ m⦌ +ₚ (1 : Int))
      return ans)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (count_interesting [(3 : Int), (1 : Int), (9 : Int), (6 : Int)] (3 : Int) (0 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg (count_interesting'rn [(3 : Int), (1 : Int), (9 : Int), (6 : Int)] (3 : Int) (0 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
