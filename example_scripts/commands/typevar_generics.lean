import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- `T = TypeVar("T")` generics are translated at the dynamic type; icontract-style contract decorators
-- are specifications and are not translated.
def pairs := fun (x : List PastaLean.PyAny) ↦
  (PastaLean.pyRange (PastaLean.pyLen x -ₚ (1 : Int))).map fun (i : Int) => (x⦋i⦌, x⦋i +ₚ (1 : Int)⦌)

attribute [simp, taste_ingr] pairs

def pairs'rn := fun (x : List PastaLean.PyAny) ↦
  (PastaLean.pyRange (PastaLean.pyLen x -ₚ (1 : Int))).map fun (i : Int) => (x⦋i⦌, x⦋i +ₚ (1 : Int)⦌)

def to_dict := fun (s : List PastaLean.PyAny) ↦ PastaLean.pyDict (PastaLean.pyZip s s)

attribute [simp, taste_ingr] to_dict

def to_dict'rn := fun (s : List PastaLean.PyAny) ↦ PastaLean.pyDict (PastaLean.pyZip s s)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (PastaLean.pyLen (pairs [(1 : Int), (2 : Int), (3 : Int)])),
              pyPrintArg (PastaLean.pyLen (to_dict [(1 : Int), (1 : Int), (2 : Int)]))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg (PastaLean.pyLen (pairs'rn [(1 : Int), (2 : Int), (3 : Int)])),
              pyPrintArg (PastaLean.pyLen (to_dict'rn [(1 : Int), (1 : Int), (2 : Int)]))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
