import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

def GLOBAL_VAR :=
  (42 : Int)

def get_global :=
  GLOBAL_VAR

attribute [simp, taste_ingr] get_global

def get_global'rn :=
  GLOBAL_VAR

def pass_func :=
  Id.run do
    if h_1 : Bool.true then 
      let _ := ()
    else
      let _ := ()
    let mut x : Int := (1 : Int)
    x := x +ₚ (1 : Int)
    let _ := ()

attribute [simp, taste_ingr] pass_func

def pass_func'rn :=
  Id.run do
    if h_1 : Bool.true then 
      let _ := ()
    else
      let _ := ()
    let mut x : Int := (1 : Int)
    x := x +ₚ (1 : Int)
    let _ := ()

def answer :=
  (42 : Int)

def fruits :=
  ["apple", "banana", "cherry"]

def scores :=
  Std.HashMap.ofList [("math", (95 : Int)), ("science", (90 : Int))]

def greet := fun (name : Int) ↦ s! "Hello, {name}!"

attribute [simp, taste_ingr] greet

def greet'rn := fun (name : Int) ↦ s! "Hello, {name}!"

def calculate_sum :=
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange (10 : Int)) do
        total := total +ₚ i
      return total)

attribute [simp, taste_ingr] calculate_sum

def calculate_sum'rn :=
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange (10 : Int)) do
        total := total +ₚ i
      return total)

def not_sure :=
  if answer = (42 : Int) then "The answer to the Ultimate Question of Life, The Universe, and Everything."
  else if answer < (42 : Int) then "The sky is the limit." else "I don't know the answer."

attribute [simp, taste_ingr] not_sure

def not_sure'rn :=
  if answer == (42 : Int) then "The answer to the Ultimate Question of Life, The Universe, and Everything."
  else if answer < (42 : Int) then "The sky is the limit." else "I don't know the answer."

def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputLines := String.splitOn inputText "\n"
  let inputStream : PastaLean.ProofMode.IOStream :=
    ⟨0, fun i => PastaLean.ProofMode.IOResult.success (List.getD inputLines i "")⟩
  let initState : PastaLean.ProofMode.IOState := ⟨inputStream, []⟩
  let (result, finalState) :=
    (((do
          for _ in (PastaLean.pyRange (10 : Int)) do
            let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (greet (1 : Int))]
            let _ := calculate_sum
          let _ := get_global
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
  for _ in (PastaLean.pyRange (10 : Int)) do
    let _ ← pyPrintIO [pyPrintArg (greet'rn (1 : Int))]
    let _ := calculate_sum'rn
  let _ := get_global'rn
  pure ()