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

-- 2D/3D DP tables built with a comprehension (`[[..] for _ in range(n)]`) and updated in place
-- (`f[i][j] = v`). These are Array-backed (O(1) per update via pyModifyItem); correctness must match.
def grid_dp := fun (n : Int) ↦ fun (m : Int) ↦
  Id.run
    (do
      let mut f : List (List Int) :=
        (PastaLean.pyRange (n +ₚ (1 : Int))).map fun (_ : Int) => PastaLean.pyListRepeat [(0 : Int)] (m +ₚ (1 : Int))
      let p'_setval_1 := (1 : Int)
      f := PastaLean.pyModifyItem f (0 : Int) (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (0 : Int) p'_setval_1)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)))do
        for j in (PastaLean.pyRange (m +ₚ (1 : Int)))do
          if h_1 : i > (0 : Int) then 
            let p'_setval_2 := f⦋i⦌⦋j⦌ +ₚ f⦋i -ₚ (1 : Int)⦌⦋j⦌
            f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
          if h_2 : j > (0 : Int) then 
            let p'_setval_2 := f⦋i⦌⦋j⦌ +ₚ f⦋i⦌⦋j -ₚ (1 : Int)⦌
            f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
      let p'_ret_1 := f⦋n⦌⦋m⦌
      return p'_ret_1)

attribute [simp, taste_ingr] grid_dp

def grid_dp'rn := fun (n : Int) ↦ fun (m : Int) ↦
  Id.run
    (do
      let mut f : Array (Array Int) :=
        ((PastaLean.pyRange (n +ₚ (1 : Int))).map fun (_ : Int) =>
            PastaLean.pyArrayRepeat #[(0 : Int)] (m +ₚ (1 : Int))) |>.toArray
      let p'_setval_1 := (1 : Int)
      f := PastaLean.pyModifyItem f (0 : Int) (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (0 : Int) p'_setval_1)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)))do
        for j in (PastaLean.pyRange (m +ₚ (1 : Int)))do
          if h_1 : i > (0 : Int) then 
            let p'_setval_2 := f⦋i⦌⦋j⦌ +ₚ f⦋i -ₚ (1 : Int)⦌⦋j⦌
            f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
          if h_2 : j > (0 : Int) then 
            let p'_setval_2 := f⦋i⦌⦋j⦌ +ₚ f⦋i⦌⦋j -ₚ (1 : Int)⦌
            f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
      let p'_ret_1 := f⦋n⦌⦋m⦌
      return p'_ret_1)

def cube_fill := fun (n : Int) ↦
  Id.run
    (do
      let mut g : List (List (List Int)) :=
        (PastaLean.pyRange n).map fun (_ : Int) =>
          (PastaLean.pyRange n).map fun (_ : Int) => PastaLean.pyListRepeat [(0 : Int)] n
      for i in (PastaLean.pyRange n)do
        for j in (PastaLean.pyRange n)do
          for k in (PastaLean.pyRange n)do
            let p'_setval_1 := i *ₚ (100 : Int) +ₚ j *ₚ (10 : Int) +ₚ k
            g :=
              PastaLean.pyModifyItem g i
                (fun p'_row_1 =>
                  PastaLean.pyModifyItem p'_row_1 j (fun p'_row_2 => PastaLean.pySetItem p'_row_2 k p'_setval_1))
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange n)do
        for j in (PastaLean.pyRange n)do
          for k in (PastaLean.pyRange n)do
            total := total +ₚ g⦋i⦌⦋j⦌⦋k⦌
      return total)

attribute [simp, taste_ingr] cube_fill

def cube_fill'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut g : Array (Array (Array Int)) :=
        ((PastaLean.pyRange n).map fun (_ : Int) =>
            ((PastaLean.pyRange n).map fun (_ : Int) => PastaLean.pyArrayRepeat #[(0 : Int)] n) |>.toArray) |>.toArray
      for i in (PastaLean.pyRange n)do
        for j in (PastaLean.pyRange n)do
          for k in (PastaLean.pyRange n)do
            let p'_setval_1 := i *ₚ (100 : Int) +ₚ j *ₚ (10 : Int) +ₚ k
            g :=
              PastaLean.pyModifyItem g i
                (fun p'_row_1 =>
                  PastaLean.pyModifyItem p'_row_1 j (fun p'_row_2 => PastaLean.pySetItem p'_row_2 k p'_setval_1))
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange n)do
        for j in (PastaLean.pyRange n)do
          for k in (PastaLean.pyRange n)do
            total := total +ₚ g⦋i⦌⦋j⦌⦋k⦌
      return total)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (grid_dp (3 : Int) (3 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (cube_fill (3 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (grid_dp'rn (3 : Int) (3 : Int))]
      let _ ← pyPrintIO [pyPrintArg (cube_fill'rn (3 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
