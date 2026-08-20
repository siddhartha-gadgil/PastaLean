import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

-- !/usr/bin/env python3
/-
Names Python rebinds to a DIFFERENT type.

A Lean `let mut` has one fixed type, so reassigning across types is an "invalid reassignment", and a
`let mut` cannot be shadowed either. The loop variable is therefore bound plainly and the rebind
introduces its own binding over it — which is what Python does: code before the rebind saw the old
value, code after sees the new.
-/
-- Single loop target rebound from str to int.
def letter_sum := fun (s : String) ↦
  Id.run
    (do
      let mut total : PyAny := (0 : Int)
      for __py_loop_1 in (PastaLean.pyIter s) do
        let ch := __py_loop_1
        let mut ch := PastaLean.pyOrd ch -ₚ PastaLean.pyOrd "a"
        total := total +ₚ ch
      return total)

attribute [simp, taste_ingr] letter_sum

def letter_sum'rn := fun (s : String) ↦
  Id.run
    (do
      let mut total : PyAny := (0 : Int)
      for __py_loop_1 in (PastaLean.pyIter s) do
        let ch := __py_loop_1
        let mut ch := PastaLean.pyOrd ch -ₚ PastaLean.pyOrd "a"
        total := total +ₚ ch
      return total)

-- TUPLE loop target where only the second element is rebound (a different codegen path).
def appeal := fun (s : String) ↦
  Id.run
    (do
      let mut __chain_1 := (0 : Int)
      let mut ans := __chain_1
      let mut t := __chain_1
      let mut pos : List Int := PastaLean.pyListRepeat [-(1 : Int)] (26 : Int)
      for _pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate s)) do
        let i := Prod.fst _pair_1
        let c := Prod.snd _pair_1
        let mut c := PastaLean.pyOrd c -ₚ PastaLean.pyOrd "a"
        t := t +ₚ (i -ₚ pos⦋c⦌)
        ans := ans +ₚ t
        pos := PastaLean.pySetItem pos c i
      return ans)

attribute [simp, taste_ingr] appeal

def appeal'rn := fun (s : String) ↦
  Id.run
    (do
      let mut __chain_1 := (0 : Int)
      let mut ans := __chain_1
      let mut t := __chain_1
      let mut pos : List Int := PastaLean.pyListRepeat [-(1 : Int)] (26 : Int)
      for _pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate s)) do
        let i := Prod.fst _pair_1
        let c := Prod.snd _pair_1
        let mut c := PastaLean.pyOrd c -ₚ PastaLean.pyOrd "a"
        t := t +ₚ (i -ₚ pos⦋c⦌)
        ans := ans +ₚ t
        pos := PastaLean.pySetItem pos c i
      return ans)

-- The rebound name is itself reassigned afterwards, so its new binding must stay mutable.
def shifted := fun (words : List String) ↦
  Id.run
    (do
      let mut total : PyAny := (0 : Int)
      for __py_loop_1 in (PastaLean.pyIter words) do
        let w := __py_loop_1
        let mut w := PastaLean.pyLen w
        w := w +ₚ (1 : Int)
        total := total +ₚ w
      return total)

attribute [simp, taste_ingr] shifted

def shifted'rn := fun (words : List String) ↦
  Id.run
    (do
      let mut total : PyAny := (0 : Int)
      for __py_loop_1 in (PastaLean.pyIter words) do
        let w := __py_loop_1
        let mut w := PastaLean.pyLen w
        w := w +ₚ (1 : Int)
        total := total +ₚ w
      return total)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (letter_sum "abc")]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (appeal "abbca")]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (shifted ["a", "bb"])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (letter_sum'rn "abc")]
      let _ ← pyPrintIO [pyPrintArg (appeal'rn "abbca")]
      let _ ← pyPrintIO [pyPrintArg (shifted'rn ["a", "bb"])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()