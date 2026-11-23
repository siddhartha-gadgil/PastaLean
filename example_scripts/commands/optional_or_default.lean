import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- `x or default` on an Optional takes the payload type (None is falsy): in a constructor's field
-- initialiser and in a plain function.
structure Cart where
  items : List (String × Int)
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy Cart where truthy _ := true

instance : PastaLean.PyBool Cart where pyBool _ := true

instance : PastaLean.PyTyped Cart where pyTypeOf _ := TypeInfer.PyType.cls "Cart"

instance : Coe Cart (Option Cart) :=
  ⟨some⟩

def Cart.new (items : Option (List (String × Int)) := Option.none) : Cart :=
  ({ items := PastaLean.pyOrElse items [] } : Cart)

structure Cart'rn where
  items : List (String × Int)
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy Cart'rn where truthy _ := true

instance : PastaLean.PyBool Cart'rn where pyBool _ := true

instance : PastaLean.PyTyped Cart'rn where pyTypeOf _ := TypeInfer.PyType.cls "Cart"

instance : Coe Cart'rn (Option Cart'rn) :=
  ⟨some⟩

def Cart'rn.new (items : Option (List (String × Int)) := Option.none) : Cart'rn :=
  ({ items := PastaLean.pyOrElse items [] } : Cart'rn)

def count := fun (xs : Option (List Int)) ↦
  let ys := (PastaLean.pyOrElse xs [(0 : Int)] : List Int)
  PastaLean.pyLen ys

attribute [simp, taste_ingr] count

def count'rn := fun (xs : Option (List Int)) ↦
  let ys := (PastaLean.pyOrElse xs [(0 : Int)] : List Int)
  PastaLean.pyLen ys

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (PastaLean.pyLen Cart.new.items),
              pyPrintArg (PastaLean.pyLen (Cart.new [("a", (1 : Int))]).items), pyPrintArg (count Option.none),
              pyPrintArg (count [(1 : Int), (2 : Int)]), pyPrintArg (count [(5 : Int)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg (PastaLean.pyLen Cart'rn.new.items),
              pyPrintArg (PastaLean.pyLen (Cart'rn.new [("a", (1 : Int))]).items), pyPrintArg (count'rn Option.none),
              pyPrintArg (count'rn [(1 : Int), (2 : Int)]), pyPrintArg (count'rn [(5 : Int)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
