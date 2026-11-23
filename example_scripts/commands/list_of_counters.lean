import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def beautiful := fun (s : String) ↦ fun (k : Int) ↦
  (show PastaLean.PyAny from
    Id.run
      (do
        let mut cc := (PastaLean.pyRange k).map fun (_ : Int) => Libraries.collections.pyCounterEmpty
        let p'_setval_1 := (1 : Int)
        cc := PastaLean.pyModifyItem cc (0 : Int) (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (0 : Int) p'_setval_1)
        let mut ans : PyAny := (0 : Int)
        let mut cur : Int := (0 : Int)
        for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate s (1 : Int))) do
          let i := Prod.fst p'_pair_1
          let x := Prod.snd p'_pair_1
          cur := cur +ₚ if PastaLean.pyContains "aeiou" x then (1 : Int) else -(1 : Int)
          ans := ans +ₚ cc⦋i %ₚ k⦌⦋cur⦌
          let p'_setval_2 := cc⦋i %ₚ k⦌⦋cur⦌ +ₚ (1 : Int)
          cc := PastaLean.pyModifyItem cc (i %ₚ k) (fun p'_row_2 => PastaLean.pySetItem p'_row_2 cur p'_setval_2)
        return (ans : PastaLean.PyAny)))

attribute [simp] beautiful

def beautiful'rn := fun (s : String) ↦ fun (k : Int) ↦
  (show PastaLean.PyAny from
    Id.run
      (do
        let mut cc := (PastaLean.pyRange k).map fun (_ : Int) => Libraries.collections.pyCounterEmpty
        let p'_setval_1 := (1 : Int)
        cc := PastaLean.pyModifyItem cc (0 : Int) (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (0 : Int) p'_setval_1)
        let mut ans : PyAny := (0 : Int)
        let mut cur : Int := (0 : Int)
        for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate s (1 : Int))) do
          let i := Prod.fst p'_pair_1
          let x := Prod.snd p'_pair_1
          cur := cur +ₚ if PastaLean.pyContains "aeiou" x then (1 : Int) else -(1 : Int)
          ans := ans +ₚ cc⦋i %ₚ k⦌⦋cur⦌
          let p'_setval_2 := cc⦋i %ₚ k⦌⦋cur⦌ +ₚ (1 : Int)
          cc := PastaLean.pyModifyItem cc (i %ₚ k) (fun p'_row_2 => PastaLean.pySetItem p'_row_2 cur p'_setval_2)
        return (ans : PastaLean.PyAny)))

def arithmetic := fun (nums : List Int) ↦
  (show PastaLean.PyAny from
    Id.run
      (do
        let mut f := (PastaLean.pyIter nums).map fun (_ : Int) => Libraries.collections.pyDefaultDictInt
        let mut ans : PyAny := (0 : Int)
        for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate nums)) do
          let i := Prod.fst p'_pair_1
          let x := Prod.snd p'_pair_1
          for j in (PastaLean.pyRange i) do
            let mut d : Int := x -ₚ nums⦋j⦌
            ans := ans +ₚ f⦋j⦌⦋d⦌
            let p'_setval_1 := f⦋i⦌⦋d⦌ +ₚ (f⦋j⦌⦋d⦌ +ₚ (1 : Int))
            f := PastaLean.pyModifyItem f i (fun p'_row_1 => PastaLean.pySetItem p'_row_1 d p'_setval_1)
        return (ans : PastaLean.PyAny)))

attribute [simp] arithmetic

def arithmetic'rn := fun (nums : List Int) ↦
  (show PastaLean.PyAny from
    Id.run
      (do
        let mut f := (PastaLean.pyIter nums).map fun (_ : Int) => Libraries.collections.pyDefaultDictInt
        let mut ans : PyAny := (0 : Int)
        for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate nums)) do
          let i := Prod.fst p'_pair_1
          let x := Prod.snd p'_pair_1
          for j in (PastaLean.pyRange i) do
            let mut d : Int := x -ₚ nums⦋j⦌
            ans := ans +ₚ f⦋j⦌⦋d⦌
            let p'_setval_1 := f⦋i⦌⦋d⦌ +ₚ (f⦋j⦌⦋d⦌ +ₚ (1 : Int))
            f := PastaLean.pyModifyItem f i (fun p'_row_1 => PastaLean.pySetItem p'_row_1 d p'_setval_1)
        return (ans : PastaLean.PyAny)))

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (beautiful "baeyh" (2 : Int))]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (arithmetic [(2 : Int), (4 : Int), (6 : Int), (8 : Int), (10 : Int)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (beautiful'rn "baeyh" (2 : Int))]
      let _ ← pyPrintIO [pyPrintArg (arithmetic'rn [(2 : Int), (4 : Int), (6 : Int), (8 : Int), (10 : Int)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
