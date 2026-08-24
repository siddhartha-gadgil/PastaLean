import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

structure Cell where
  v : Int
  deriving Inhabited, Repr, BEq

structure Cell'rn where
  v : Int
  deriving Inhabited, Repr, BEq

inductive Val where
  | cell (v : Int)
  | cell'rn (v : Int)
  | hc_Float (c : Float)
  | hc_Bool (c : Bool)
  | hc_String (c : String)
  | hc_Rat (c : Rat)
  | hc_Int (c : Int)
  | hc_Ref_Cell_rn (c : Ref Cell'rn)
  | hc_Ref_Cell (c : Ref Cell)
  deriving Repr, Inhabited

derive_storable% Cell

derive_storable% Cell'rn

instance : Storable Val (Float) where
  inject := Val.hc_Float
  project := fun
    | Val.hc_Float c => some c
    | _ => none
  project_inject := fun _ => rfl

instance : Storable Val (Bool) where
  inject := Val.hc_Bool
  project := fun
    | Val.hc_Bool c => some c
    | _ => none
  project_inject := fun _ => rfl

instance : Storable Val (String) where
  inject := Val.hc_String
  project := fun
    | Val.hc_String c => some c
    | _ => none
  project_inject := fun _ => rfl

instance : Storable Val (Rat) where
  inject := Val.hc_Rat
  project := fun
    | Val.hc_Rat c => some c
    | _ => none
  project_inject := fun _ => rfl

instance : Storable Val (Int) where
  inject := Val.hc_Int
  project := fun
    | Val.hc_Int c => some c
    | _ => none
  project_inject := fun _ => rfl

instance : Storable Val (Ref Cell'rn) where
  inject := Val.hc_Ref_Cell_rn
  project := fun
    | Val.hc_Ref_Cell_rn c => some c
    | _ => none
  project_inject := fun _ => rfl

instance : Storable Val (Ref Cell) where
  inject := Val.hc_Ref_Cell
  project := fun
    | Val.hc_Ref_Cell c => some c
    | _ => none
  project_inject := fun _ => rfl

def Cell.new : Int → PastaLean.HeapM Val (PastaLean.Ref Cell) := fun (v : Int) ↦
  ((do
      PastaLean.alloc ({ v := v } : Cell)) :
    PastaLean.HeapM Val (PastaLean.Ref Cell))

def Cell'rn.new : Int → PastaLean.HeapM Val (PastaLean.Ref Cell'rn) := fun (v : Int) ↦
  ((do
      PastaLean.alloc ({ v := v } : Cell'rn)) :
    PastaLean.HeapM Val (PastaLean.Ref Cell'rn))

def bump := fun (c : PastaLean.Ref Cell) ↦ fun (k : Int) ↦
  ((do
      let mut i : Int := (0 : Int)
      while (i < k) do
        c ~> v <~ (← (c ~> v)) +ₚ (1 : Int)
        i := i +ₚ (1 : Int)) :
    (PastaLean.HeapM Val) _)

attribute [simp, taste_ingr] bump

def bump'rn := fun (c : PastaLean.Ref Cell'rn) ↦ fun (k : Int) ↦
  ((do
      let mut i : Int := (0 : Int)
      while (i < k) do
        c ~> v <~ (← (c ~> v)) +ₚ (1 : Int)
        i := i +ₚ (1 : Int)) :
    (PastaLean.HeapM Val) _)

def main' :=
  ((do
      let mut c := (← Cell.new (10 : Int))
      let _ ← bump c (3 : Int)
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (← (c ~> v))]) :
    (PastaLean.PyHeapProofM Val) _)

attribute [simp] main'

def main''rn :=
  ((do
      let mut c := (← Cell'rn.new (10 : Int))
      let _ ← bump'rn c (3 : Int)
      let _ ← pyPrintIO [pyPrintArg (← (c ~> v))]) :
    (PastaLean.PyHeapIO Val) _)

def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputLines := String.splitOn inputText "\n"
  let inputStream : PastaLean.ProofMode.IOStream :=
    ⟨0, fun i => PastaLean.ProofMode.IOResult.success (List.getD inputLines i "")⟩
  let initState : PastaLean.HeapIOState Val := ⟨PastaLean.emptyHeap, ⟨inputStream, []⟩⟩
  let (result, finalState) :=
    PastaLean.PyHeapProofM.runProgram (V := Val)
      (do
        let _ ← main'
        pure ())
      initState
  let outputLines := finalState.io.output
  for line in outputLines do
    IO.print line
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

def main'rn : IO Unit := do
  let (result, _heap) ←
    PastaLean.PyHeapIO.runProgram (V := Val)
        (do
          let _ ← main''rn
          pure ())
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))
