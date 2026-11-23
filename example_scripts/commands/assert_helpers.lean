import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 800000

namespace PastaLean.User.Root

def check_code := fun (code : String) ↦
  (show Unit from
    have ht_1 : PastaLean.pyLen code = (2 : Int) := by sorry
    ())

attribute [simp] check_code

def check_code'rn := fun (code : String) ↦ (show Unit from ())

def check_codes : List String → PastaLean.ProofMode.PyProofM Unit := fun (codes : List String) ↦ do
  if h_1 : PastaLean.pyLen codes = (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "no codes"))
  for c in (PastaLean.pyIter codes) do
    let _ := check_code c

attribute [simp] check_codes

def check_codes'rn : List String → PastaLean.PyExcept Unit := fun (codes : List String) ↦ do
  if h_1 : PastaLean.pyLen codes == (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "no codes"))
  for c in (PastaLean.pyIter codes) do
    let _ := check_code'rn c

def describe : List String → Option String → PastaLean.ProofMode.PyProofM String := fun (codes : List String) ↦
  fun (fallback : Option String) ↦ do
  let _ ← check_codes codes
  if let some fallback := fallback then 
    let _ := check_code fallback
  let p'_ret_1 := PastaLean.pyStringJoin "," codes
  return p'_ret_1

attribute [simp] describe

def describe'rn : List String → Option String → PastaLean.PyExcept String := fun (codes : List String) ↦
  fun (fallback : Option String) ↦ do
  let _ ← check_codes'rn codes
  if let some fallback := fallback then 
    let _ := check_code'rn fallback
  let p'_ret_1 := PastaLean.pyStringJoin "," codes
  return p'_ret_1

def is_short := fun (code : String) ↦
  (show Unit from
    have ht_1 : PastaLean.pyLen code ≤ (3 : Int) := by sorry
    ())

attribute [simp] is_short

def is_short'rn := fun (code : String) ↦ (show Unit from ())

def all_short := fun (codes : List String) ↦
  Id.run
    (do
      for c in (PastaLean.pyIter codes) do
        let _ := is_short c
      return Bool.true)

attribute [simp, taste_ingr] all_short

def all_short'rn := fun (codes : List String) ↦
  Id.run
    (do
      for c in (PastaLean.pyIter codes) do
        let _ := is_short'rn c
      return Bool.true)

def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputStream : PastaLean.ProofMode.IOStream := PastaLean.ProofMode.IOStream.ofText inputText
  let initState : PastaLean.ProofMode.IOState := { input := inputStream, output := [] }
  let (result, finalState) :=
    (((do
          let _ ←
            ((do
                  let p'_arg0 ← describe ["en", "fr"] Option.none
                  let __py_result ← PastaLean.ProofMode.pyPrintProof [pyPrintArg p'_arg0]
                  return __py_result) :
                PastaLean.ProofMode.PyProofM _)
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (all_short ["abc", "de"])]
          try
            let _ ← check_codes []
          catch caught =>
            if PastaLean.pyExcIsA caught "ValueError" then 
              let e := caught
              let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "error:", pyPrintArg e]
            else
              throw caught
          pure ()) :
        PastaLean.ProofMode.PyProofM Unit))
      initState
  let outputLines := finalState.output
  for line in outputLines do
    IO.print line
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

def main'rn : IO Unit := do
  let result ←
    (((do
            let _ ←
              ((do
                    let p'_arg0 ← describe'rn ["en", "fr"] Option.none
                    let __py_result ← pyPrintIO [pyPrintArg p'_arg0]
                    return __py_result) :
                  PastaLean.PyExcept _)
            let _ ← pyPrintIO [pyPrintArg (all_short'rn ["abc", "de"])]
            try
              let _ ← check_codes'rn []
            catch caught =>
              if PastaLean.pyExcIsA caught "ValueError" then 
                let e := caught
                let _ ← pyPrintIO [pyPrintArg "error:", pyPrintArg e]
              else
                throw caught
            pure ()) :
          PastaLean.PyExcept Unit)).run
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

end PastaLean.User.Root
