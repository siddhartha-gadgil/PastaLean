import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- A @cache-memoized recursive DP whose body REASSIGNS a parameter (`k += ...`). The memoized run-twin
-- binds params as immutable binders, so each mutated param needs a `let mut k := k` shadow — without it
-- the reassignment fails to elaborate ("`k` cannot be mutated").
private partial def _ways'dfs : Int → Int → String → Int → Int := fun (i : Int) ↦ fun (k : Int) ↦
  fun (corridor : String) ↦ fun (n : Int) ↦
  Id.run
    (do
      let mut k := k
      if h_1 : i ≥ n then 
        let p'_ret_1 := PastaLean.pyInt (k == (2 : Int))
        return p'_ret_1
      k := k +ₚ PastaLean.pyInt (corridor⦋i⦌ == "S")
      if h_2 : k > (2 : Int) then 
        return (0 : Int)
      let mut ans : Int := _ways'dfs (i +ₚ (1 : Int)) k corridor n
      if h_3 : k = (2 : Int) then 
        ans := ans +ₚ _ways'dfs (i +ₚ (1 : Int)) (0 : Int) corridor n
      return ans)

def ways := fun (corridor : String) ↦
  let n := (PastaLean.pyLen corridor : Int)
  _ways'dfs (0 : Int) (0 : Int) corridor n

attribute [simp, taste_ingr] ways

partial def _ways'dfs'memo'rn : Int → Int → String → Int → StateM (Std.HashMap (Int × Int) Int) Int := fun (i : Int) ↦
  fun (k : Int) ↦ fun (corridor : String) ↦ fun (n : Int) ↦ do
  match (← get)[(i, k)]? with
  | some v =>
    return v
  | none =>
    let v ←
      ((do
            let mut k := k
            if h_1 : i ≥ n then 
              let p'_ret_1 := PastaLean.pyInt (k == (2 : Int))
              return p'_ret_1
            k := k +ₚ PastaLean.pyInt (corridor⦋i⦌ == "S")
            if h_2 : k > (2 : Int) then 
              return (0 : Int)
            let mut ans : Int := (← _ways'dfs'memo'rn (i +ₚ (1 : Int)) k corridor n)
            if h_3 : k == (2 : Int) then 
              ans := ans +ₚ (← _ways'dfs'memo'rn (i +ₚ (1 : Int)) (0 : Int) corridor n)
            return ans) :
          StateM (Std.HashMap (Int × Int) Int) Int)
    modify (·.insert (i, k) v)
    return v

def _ways'dfs'rn : Int → Int → String → Int → Int := fun (i : Int) ↦ fun (k : Int) ↦ fun (corridor : String) ↦
  fun (n : Int) ↦ ((((_ways'dfs'memo'rn i) k) corridor) n).run' ∅

def ways'rn := fun (corridor : String) ↦
  let n := (PastaLean.pyLen corridor : Int)
  _ways'dfs'rn (0 : Int) (0 : Int) corridor n

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (ways "SSPPSPS")]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (ways "PPSPSP")]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (ways'rn "SSPPSPS")]
      let _ ← pyPrintIO [pyPrintArg (ways'rn "PPSPSP")]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
