import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

def read_line : PastaLean.ProofMode.PyProofM String := do
  let mut raw : String := (← (PastaLean.ProofMode.pyInputProof ""))
  return raw

attribute [simp] read_line

def read_line'rn : IO String := do
  let mut raw : String := (← (PastaLean.pyInputIO ""))
  return raw

def read_prompted : PastaLean.ProofMode.PyProofM String := do
  let __py_ret_1 := (← (PastaLean.ProofMode.pyInputProof "n = "))
  return __py_ret_1

attribute [simp] read_prompted

def read_prompted'rn : IO String := do
  let __py_ret_1 := (← (PastaLean.pyInputIO "n = "))
  return __py_ret_1

def read_nested_int : PastaLean.ProofMode.PyProofM (Int × String) := do
  let mut a : Int := PastaLean.pyInt (← (PastaLean.ProofMode.pyInputProof ""))
  let mut b : Int := PastaLean.pyInt (← (PastaLean.ProofMode.pyInputProof ""))
  let mut c : String := (← (PastaLean.ProofMode.pyInputProof ""))
  a := a +ₚ b
  let __py_ret_1 := (a, c)
  return __py_ret_1

attribute [simp] read_nested_int

def read_nested_int'rn : IO (Int × String) := do
  let mut a : Int := PastaLean.pyInt (← (PastaLean.pyInputIO ""))
  let mut b : Int := PastaLean.pyInt (← (PastaLean.pyInputIO ""))
  let mut c : String := (← (PastaLean.pyInputIO ""))
  a := a +ₚ b
  let __py_ret_1 := (a, c)
  return __py_ret_1

def echo_input : PastaLean.ProofMode.PyProofM Int := do
  let _ ←
    ((do
          let __py_input0 ← PastaLean.ProofMode.pyInputProof ""
          let __py_result ← PastaLean.ProofMode.pyPrintProof [pyPrintArg __py_input0]
          return __py_result) :
        PastaLean.ProofMode.PyProofM _)
  return (0 : Int)

attribute [simp] echo_input

def echo_input'rn : IO Int := do
  let _ ←
    ((do
          let __py_input0 ← PastaLean.pyInputIO ""
          let __py_result ← pyPrintIO [pyPrintArg __py_input0]
          return __py_result) :
        IO _)
  return (0 : Int)

def input_inside_print :=
  ((do
      let _ ←
        ((do
              let __py_input0 ← PastaLean.ProofMode.pyInputProof ""
              let __py_result ←
                PastaLean.ProofMode.pyPrintProof
                    [pyPrintArg
                        (String.append (String.append "" "Enter a number: ")
                          (ToString.toString (PastaLean.pyInt __py_input0)))]
              return __py_result) :
            PastaLean.ProofMode.PyProofM _)) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] input_inside_print

def input_inside_print'rn :=
  ((do
      let _ ←
        ((do
              let __py_input0 ← PastaLean.pyInputIO ""
              let __py_result ←
                pyPrintIO
                    [pyPrintArg
                        (String.append (String.append "" "Enter a number: ")
                          (ToString.toString (PastaLean.pyInt __py_input0)))]
              return __py_result) :
            IO _)) :
    IO _)