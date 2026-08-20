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
Test that exceptions with real IO use PyExcept.
-/
-- CHECK: def get_validated : PyExcept Int
def get_validated : PastaLean.ProofMode.PyProofM Int := do
  let mut x : Int := PastaLean.pyInt (← (PastaLean.ProofMode.pyInputProof ""))
  if h_1 : x < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  else
    let _ := ()
  return x

attribute [simp] get_validated

def get_validated'rn : PastaLean.PyExcept Int := do
  let mut x : Int := PastaLean.pyInt (← (PastaLean.pyInputIO ""))
  if h_1 : x < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  else
    let _ := ()
  return x