import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- A captured local's type is read off its literal shape (TypeInfer.ofValue), so the lifted helper
-- gets a typed parameter Lean can resolve; an unannotated class field is typed the same way.
structure Counter where
  c : List Int
  tag : String
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy Counter where truthy _ := true

instance : PastaLean.PyBool Counter where pyBool _ := true

instance : PastaLean.PyTyped Counter where pyTypeOf _ := TypeInfer.PyType.cls "Counter"

instance : Coe Counter (Option Counter) :=
  ⟨some⟩

def Counter.new : Int → Counter := fun (n : Int) ↦ ({ c := PastaLean.pyListRepeat [(0 : Int)] n, tag := "x" } : Counter)

structure Counter'rn where
  c : List Int
  tag : String
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy Counter'rn where truthy _ := true

instance : PastaLean.PyBool Counter'rn where pyBool _ := true

instance : PastaLean.PyTyped Counter'rn where pyTypeOf _ := TypeInfer.PyType.cls "Counter"

instance : Coe Counter'rn (Option Counter'rn) :=
  ⟨some⟩

def Counter'rn.new : Int → Counter'rn := fun (n : Int) ↦
  ({ c := PastaLean.pyListRepeat [(0 : Int)] n, tag := "x" } : Counter'rn)

private partial def _solve'go : Int → Int → List Int → Int := fun (i : Int) ↦ fun (n : Int) ↦ fun (grid : List Int) ↦
  if i ≥ n then (0 : Int) else grid⦋i⦌ +ₚ _solve'go (i +ₚ (1 : Int)) n grid

def solve := fun (n : Int) ↦
  let grid := (PastaLean.pyListRepeat [(0 : Int)] n : List Int)
  _solve'go (0 : Int) n grid

attribute [simp, taste_ingr] solve

private partial def _solve'go'rn : Int → Int → List Int → Int := fun (i : Int) ↦ fun (n : Int) ↦
  fun (grid : List Int) ↦ if i ≥ n then (0 : Int) else grid⦋i⦌ +ₚ _solve'go'rn (i +ₚ (1 : Int)) n grid

def solve'rn := fun (n : Int) ↦
  let grid := (PastaLean.pyListRepeat [(0 : Int)] n : List Int)
  _solve'go'rn (0 : Int) n grid

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (solve (3 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (solve'rn (3 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
