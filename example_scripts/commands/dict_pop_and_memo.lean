import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- `d.pop(key)` (1 arg) on a dict is the DICT pop (remove key, return value) — it shares its name with
-- 1-arg `list.pop(i)`, so the receiver's dict-ness must route it. Covers a plain dict AND a Counter.
def dict_pop_demo :=
  Id.run
    (do
      let mut d : Std.HashMap Int Int :=
        Std.HashMap.ofList [((1 : Int), (10 : Int)), ((2 : Int), (20 : Int)), ((3 : Int), (30 : Int))]
      let mut v := PastaLean.pyDictKeyPopValue d (2 : Int)
      d := PastaLean.pyDictKeyPopRest d (2 : Int)
      d := PastaLean.pyDictKeyPopRest d (1 : Int)
      let mut total : Int := v
      for k in (PastaLean.pyIter d) do
        total := total +ₚ d⦋k⦌
      return total)

attribute [simp, taste_ingr] dict_pop_demo

def dict_pop_demo'rn :=
  Id.run
    (do
      let mut d : Std.HashMap Int Int :=
        Std.HashMap.ofList [((1 : Int), (10 : Int)), ((2 : Int), (20 : Int)), ((3 : Int), (30 : Int))]
      let mut v := PastaLean.pyDictKeyPopValue d (2 : Int)
      d := PastaLean.pyDictKeyPopRest d (2 : Int)
      d := PastaLean.pyDictKeyPopRest d (1 : Int)
      let mut total : Int := v
      for k in (PastaLean.pyIter d) do
        total := total +ₚ d⦋k⦌
      return total)

def counter_pop_demo := fun (s : String) ↦
  Id.run
    (do
      let mut c : Libraries.collections.PyDefaultDict String Int := Libraries.collections.pyCounter s
      let mut removed : Int := (0 : Int)
      for ch in (PastaLean.pyIter "abc") do
        if h_1 : PastaLean.pyContains c ch then 
          let mut p'_popv_1 := PastaLean.pyDictKeyPopValue c ch
          c := PastaLean.pyDictKeyPopRest c ch
          removed := removed +ₚ p'_popv_1
      let p'_ret_1 := removed +ₚ PastaLean.pyLen c
      return p'_ret_1)

attribute [simp, taste_ingr] counter_pop_demo

def counter_pop_demo'rn := fun (s : String) ↦
  Id.run
    (do
      let mut c : Libraries.collections.PyDefaultDict String Int := Libraries.collections.pyCounter s
      let mut removed : Int := (0 : Int)
      for ch in (PastaLean.pyIter "abc") do
        if h_1 : PastaLean.pyContains c ch then 
          let mut p'_popv_1 := PastaLean.pyDictKeyPopValue c ch
          c := PastaLean.pyDictKeyPopRest c ch
          removed := removed +ₚ p'_popv_1
      let p'_ret_1 := removed +ₚ PastaLean.pyLen c
      return p'_ret_1)

-- A memoized DP whose param is reassigned to a value of the SAME type (`x = 3*x+1`) — the run-twin must
-- reassign the param shadow, not emit a fresh (shadowing) `let mut x`.
partial def collatz_steps : Int → Int := fun (x : Int) ↦
  Id.run
    (do
      let mut x := x
      if h_1 : x = (1 : Int) then 
        return (0 : Int)
      if h_2 : x %ₚ (2 : Int) = (0 : Int) then 
        x := PastaLean.pyFloorDiv x (2 : Int)
      else
        x := (3 : Int) *ₚ x +ₚ (1 : Int)
      let p'_ret_1 := (1 : Int) +ₚ collatz_steps x
      return p'_ret_1)

partial def collatz_steps'memo'rn : Int → StateM (Std.HashMap Int Int) Int := fun (x : Int) ↦ do
  match (← get)[x]? with
  | some v =>
    return v
  | none =>
    let v ←
      ((do
            let mut x := x
            if h_1 : x == (1 : Int) then 
              return (0 : Int)
            if h_2 : x %ₚ (2 : Int) == (0 : Int) then 
              x := PastaLean.pyFloorDiv x (2 : Int)
            else
              x := (3 : Int) *ₚ x +ₚ (1 : Int)
            let p'_ret_1 := (1 : Int) +ₚ (← collatz_steps'memo'rn x)
            return p'_ret_1) :
          StateM (Std.HashMap Int Int) Int)
    modify (·.insert x v)
    return v

def collatz_steps'rn : Int → Int := fun (x : Int) ↦ (collatz_steps'memo'rn x).run' ∅

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg dict_pop_demo]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (counter_pop_demo "aabbccd")]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (collatz_steps (6 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg dict_pop_demo'rn]
      let _ ← pyPrintIO [pyPrintArg (counter_pop_demo'rn "aabbccd")]
      let _ ← pyPrintIO [pyPrintArg (collatz_steps'rn (6 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
