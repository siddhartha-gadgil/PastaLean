import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

structure Node where
  val : Int
  next : Option (PastaLean.Ref Node)
  deriving Inhabited, Repr, BEq

structure Node'rn where
  val : Int
  next : Option (PastaLean.Ref Node'rn)
  deriving Inhabited, Repr, BEq

inductive Val where
  | node (val : Int) (next : Option (PastaLean.Ref Node))
  | node'rn (val : Int) (next : Option (PastaLean.Ref Node'rn))
  | hc_Float (c : Float)
  | hc_Bool (c : Bool)
  | hc_String (c : String)
  | hc_Rat (c : Rat)
  | hc_Int (c : Int)
  | hc_Ref_Node_rn (c : Ref Node'rn)
  | hc_Ref_Node (c : Ref Node)
  deriving Repr, Inhabited

derive_storable% Node

derive_storable% Node'rn

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

instance : Storable Val (Ref Node'rn) where
  inject := Val.hc_Ref_Node_rn
  project := fun
    | Val.hc_Ref_Node_rn c => some c
    | _ => none
  project_inject := fun _ => rfl

instance : Storable Val (Ref Node) where
  inject := Val.hc_Ref_Node
  project := fun
    | Val.hc_Ref_Node c => some c
    | _ => none
  project_inject := fun _ => rfl

-- Iterative linked-list reversal (--heap). Exercises `Optional[C]` threaded through the heap tier
-- end-to-end: `reverse` takes and returns `Optional[Node]` (lowered to `Option (Ref Node)`), its
-- cursors (`prev`/`curr`/`nxt`) are ref locals whose `.next` read and `.next` write hit the heap via
-- `((x).getD default) ~> next`, and in `__main__` the object-returning call `head = reverse(a)`
-- registers `head` as a heap ref so the print traversal derefs correctly. Each cursor is
-- single-assignment-per-role so its `Option (Ref Node)` type stays unambiguous.
def Node.new (val : Int) (next : Option (PastaLean.Ref Node) := Option.none) :
    PastaLean.HeapM Val (PastaLean.Ref Node) :=
  ((do
      PastaLean.alloc ({ val := val, next := next } : Node)) :
    PastaLean.HeapM Val (PastaLean.Ref Node))

def Node'rn.new (val : Int) (next : Option (PastaLean.Ref Node'rn) := Option.none) :
    PastaLean.HeapM Val (PastaLean.Ref Node'rn) :=
  ((do
      PastaLean.alloc ({ val := val, next := next } : Node'rn)) :
    PastaLean.HeapM Val (PastaLean.Ref Node'rn))

def reverse := fun (head : Option (PastaLean.Ref Node)) ↦
  ((do
      let mut prev := Option.none
      let mut curr := head
      while (!PastaLean.pyIsNone curr) do
        let mut nxt := (← (((curr).getD default) ~> next))
        ((curr).getD default) ~> next <~ prev
        prev := curr
        curr := nxt
      return prev) :
    (PastaLean.HeapM Val) _)

attribute [simp, taste_ingr] reverse

def reverse'rn := fun (head : Option (PastaLean.Ref Node'rn)) ↦
  ((do
      let mut prev := Option.none
      let mut curr := head
      while (!PastaLean.pyIsNone curr) do
        let mut nxt := (← (((curr).getD default) ~> next))
        ((curr).getD default) ~> next <~ prev
        prev := curr
        curr := nxt
      return prev) :
    (PastaLean.HeapM Val) _)

def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputLines := String.splitOn inputText "\n"
  let inputStream : PastaLean.ProofMode.IOStream :=
    ⟨0, fun i => PastaLean.ProofMode.IOResult.success (List.getD inputLines i "")⟩
  let initState : PastaLean.HeapIOState Val := ⟨PastaLean.emptyHeap, ⟨inputStream, []⟩⟩
  let (result, finalState) :=
    PastaLean.PyHeapProofM.runProgram (V := Val)
      (do
        let mut a := (← Node.new (1 : Int))
        let mut b := (← Node.new (2 : Int))
        let mut c := (← Node.new (3 : Int))
        a ~> next <~ b
        b ~> next <~ c
        let mut head := (← reverse a)
        let mut node := head
        while (!PastaLean.pyIsNone node) do
          let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (← (((node).getD default) ~> val))]
          node := (← (((node).getD default) ~> next))
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
          let mut a := (← Node'rn.new (1 : Int))
          let mut b := (← Node'rn.new (2 : Int))
          let mut c := (← Node'rn.new (3 : Int))
          a ~> next <~ b
          b ~> next <~ c
          let mut head := (← reverse'rn a)
          let mut node := head
          while (!PastaLean.pyIsNone node) do
            let _ ← pyPrintIO [pyPrintArg (← (((node).getD default) ~> val))]
            node := (← (((node).getD default) ~> next))
          pure ())
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))
