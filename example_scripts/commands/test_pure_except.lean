import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- !/usr/bin/env python3
/-
Test that pure exceptions (no IO) use PyExceptId in prove mode.
-/
def validate : Int → PastaLean.ProofMode.PyProofM Int := fun (x : Int) ↦ do
  if h_1 : x < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  let p'_ret_1 := x *ₚ (2 : Int)
  return p'_ret_1

attribute [simp] validate

def validate'rn : Int → PastaLean.PyExcept Int := fun (x : Int) ↦ do
  if h_1 : x < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  let p'_ret_1 := x *ₚ (2 : Int)
  return p'_ret_1

def validate_with_print : Int → PastaLean.ProofMode.PyProofM Int := fun (x : Int) ↦ do
  let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg x]
  if h_1 : x < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  let p'_ret_1 := x *ₚ (2 : Int)
  return p'_ret_1

attribute [simp] validate_with_print

def validate_with_print'rn : Int → PastaLean.PyExcept Int := fun (x : Int) ↦ do
  let _ ← pyPrintIO [pyPrintArg x]
  if h_1 : x < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  let p'_ret_1 := x *ₚ (2 : Int)
  return p'_ret_1

end PastaLean.User.Root
