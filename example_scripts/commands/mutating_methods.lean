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
Methods that return a value AND mutate the receiver.

The subtle one is `pop`: arity alone decides the container. `xs.pop(i)` indexes a list, while
`d.pop(k, default)` is a *dict* pop whose second argument is a default, not an index — so the two
lower to different runtime pairs. `setdefault` is the same value+mutate shape.
-/
-- 2-arg pop is a DICT pop (key, default) — not a list pop with an index.
def take := fun counts ↦ fun (key : Int) ↦
  Id.run
    (do
      let mut counts := counts
      let mut hit := PastaLean.pyDictPopValue counts key (-(1 : Int))
      counts := PastaLean.pyDictPopRest counts key
      let mut miss := PastaLean.pyDictPopValue counts (999999 : Int) (-(1 : Int))
      counts := PastaLean.pyDictPopRest counts (999999 : Int)
      let __py_ret_1 := hit +ₚ miss
      return __py_ret_1)

attribute [simp, taste_ingr] take

def take'rn := fun counts ↦ fun (key : Int) ↦
  Id.run
    (do
      let mut counts := counts
      let mut hit := PastaLean.pyDictPopValue counts key (-(1 : Int))
      counts := PastaLean.pyDictPopRest counts key
      let mut miss := PastaLean.pyDictPopValue counts (999999 : Int) (-(1 : Int))
      counts := PastaLean.pyDictPopRest counts (999999 : Int)
      let __py_ret_1 := hit +ₚ miss
      return __py_ret_1)

-- 0-/1-arg pop is a LIST pop (optional index), value + shortened list.
def drain := fun (xs : List Int) ↦
  Id.run
    (do
      let mut xs := xs
      let mut last := PastaLean.pyPopValue xs
      xs := PastaLean.pyPopRest xs
      let mut first := PastaLean.pyPopValue xs (0 : Int)
      xs := PastaLean.pyPopRest xs (0 : Int)
      let __py_ret_1 := last +ₚ first
      return __py_ret_1)

attribute [simp, taste_ingr] drain

def drain'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut xs := xs
      let mut last := PastaLean.pyPopValue xs
      xs := PastaLean.pyPopRest xs
      let mut first := PastaLean.pyPopValue xs (0 : Int)
      xs := PastaLean.pyPopRest xs (0 : Int)
      let __py_ret_1 := last +ₚ first
      return __py_ret_1)

-- `setdefault` returns d[k]-or-default and inserts only when the key is absent.
def tally := fun (nums : List Int) ↦
  Id.run
    (do
      let mut d : Std.HashMap Int Int := Std.HashMap.ofList []
      for n in (PastaLean.pyIter nums) do
        let mut seen := PastaLean.pyGetD d n (0 : Int)
        d := PastaLean.pyDictSetdefaultRest d n (0 : Int)
        d := PastaLean.pySetItem d n (seen +ₚ (1 : Int))
      let __py_ret_1 := PastaLean.pyLen d
      return __py_ret_1)

attribute [simp, taste_ingr] tally

def tally'rn := fun (nums : List Int) ↦
  Id.run
    (do
      let mut d : Std.HashMap Int Int := Std.HashMap.ofList []
      for n in (PastaLean.pyIter nums) do
        let mut seen := PastaLean.pyGetD d n (0 : Int)
        d := PastaLean.pyDictSetdefaultRest d n (0 : Int)
        d := PastaLean.pySetItem d n (seen +ₚ (1 : Int))
      let __py_ret_1 := PastaLean.pyLen d
      return __py_ret_1)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (take (Std.HashMap.ofList [((1 : Int), (10 : Int)), ((2 : Int), (20 : Int))]) (1 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (drain [(3 : Int), (4 : Int), (5 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (tally [(1 : Int), (1 : Int), (2 : Int)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg (take'rn (Std.HashMap.ofList [((1 : Int), (10 : Int)), ((2 : Int), (20 : Int))]) (1 : Int))]
      let _ ← pyPrintIO [pyPrintArg (drain'rn [(3 : Int), (4 : Int), (5 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (tally'rn [(1 : Int), (1 : Int), (2 : Int)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()