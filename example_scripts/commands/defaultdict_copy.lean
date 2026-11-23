import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def count_pairs := fun (coordinates : List (List Int)) ↦ fun (k : Int) ↦
  Id.run
    (do
      let mut mp : Libraries.collections.PyDefaultDict (Int × Int) Int := Libraries.collections.pyDefaultDictInt
      for p'_pair_1 in (PastaLean.pyIter coordinates) do
        let x := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let y := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        mp := PastaLean.pySetItem mp (x, y) (mp⦋(x, y)⦌ +ₚ (1 : Int))
      let mut res : Int := (0 : Int)
      for i in (PastaLean.pyRange (k +ₚ (1 : Int))) do
        let mut a : Int := i
        let mut b : Int := k -ₚ i
        let mut tmp := PastaLean.pyCopy mp
        for p'_pair_1 in (PastaLean.pyIter coordinates) do
          let x := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
          let y := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
          tmp := PastaLean.pySetItem tmp (x, y) (tmp⦋(x, y)⦌ -ₚ (1 : Int))
          if h_1 : PastaLean.pyContains tmp (PastaLean.pyBitXor a x, PastaLean.pyBitXor b y) then 
            res := res +ₚ tmp⦋(PastaLean.pyBitXor a x, PastaLean.pyBitXor b y)⦌
      return res)

attribute [simp, taste_ingr] count_pairs

def count_pairs'rn := fun (coordinates : List (List Int)) ↦ fun (k : Int) ↦
  Id.run
    (do
      let mut mp : Libraries.collections.PyDefaultDict (Int × Int) Int := Libraries.collections.pyDefaultDictInt
      for p'_pair_1 in (PastaLean.pyIter coordinates) do
        let x := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let y := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        mp := PastaLean.pySetItem mp (x, y) (mp⦋(x, y)⦌ +ₚ (1 : Int))
      let mut res : Int := (0 : Int)
      for i in (PastaLean.pyRange (k +ₚ (1 : Int))) do
        let mut a : Int := i
        let mut b : Int := k -ₚ i
        let mut tmp := PastaLean.pyCopy mp
        for p'_pair_1 in (PastaLean.pyIter coordinates) do
          let x := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
          let y := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
          tmp := PastaLean.pySetItem tmp (x, y) (tmp⦋(x, y)⦌ -ₚ (1 : Int))
          if h_1 : PastaLean.pyContains tmp (PastaLean.pyBitXor a x, PastaLean.pyBitXor b y) then 
            res := res +ₚ tmp⦋(PastaLean.pyBitXor a x, PastaLean.pyBitXor b y)⦌
      return res)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (count_pairs [[(1 : Int), (2 : Int)], [(4 : Int), (5 : Int)], [(1 : Int), (2 : Int)]] (5 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg
                (count_pairs'rn [[(1 : Int), (2 : Int)], [(4 : Int), (5 : Int)], [(1 : Int), (2 : Int)]] (5 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
