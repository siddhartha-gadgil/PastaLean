import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- A `@cache` DP whose recursion sits inside a list comprehension: the runnable twin memoizes it
-- via a monadic `mapM` over the shared `StateM` cache (turning exponential into polynomial).
private partial def _max_score'dfs : Int → List Int → Int → Int := fun (i : Int) ↦ fun (nums : List Int) ↦
  fun (n : Int) ↦
  if i ≥ n -ₚ (1 : Int) then (0 : Int)
  else
    PastaLean.pyMax
      (((PastaLean.pyRange n (i +ₚ (1 : Int))).map fun (j : Int) => (j -ₚ i) *ₚ nums⦋j⦌ +ₚ _max_score'dfs j nums n) +ₚ
        [(0 : Int)])

def max_score := fun (nums : List Int) ↦
  let n := (PastaLean.pyLen nums : Int)
  _max_score'dfs (0 : Int) nums n

attribute [simp, taste_ingr] max_score

partial def _max_score'dfs'memo'rn : Int → List Int → Int → StateM (Std.HashMap Int Int) Int := fun (i : Int) ↦
  fun (nums : List Int) ↦ fun (n : Int) ↦ do
  match (← get)[i]? with
  | some v =>
    return v
  | none =>
    let v ←
      ((do
            if h_1 : i ≥ n -ₚ (1 : Int) then 
              return (0 : Int)
            let p'_ret_1 :=
              PastaLean.pyMax
                ((←
                    (PastaLean.pyRange n (i +ₚ (1 : Int))).mapM fun (j : Int) =>
                        (do
                          return (j -ₚ i) *ₚ nums⦋j⦌ +ₚ (← _max_score'dfs'memo'rn j nums n))) +ₚ
                  [(0 : Int)])
            return p'_ret_1) :
          StateM (Std.HashMap Int Int) Int)
    modify (·.insert i v)
    return v

def _max_score'dfs'rn : Int → List Int → Int → Int := fun (i : Int) ↦ fun (nums : List Int) ↦ fun (n : Int) ↦
  (((_max_score'dfs'memo'rn i) nums) n).run' ∅

def max_score'rn := fun (nums : List Int) ↦
  let n := (PastaLean.pyLen nums : Int)
  _max_score'dfs'rn (0 : Int) nums n

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (max_score [(1 : Int), (5 : Int), (8 : Int), (2 : Int), (9 : Int)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (max_score'rn [(1 : Int), (5 : Int), (8 : Int), (2 : Int), (9 : Int)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
