import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- A nested def that MUTATES a captured var (`vis`, so it is state-threaded) AND returns a TUPLE, whose
-- result is TUPLE-UNPACKED (`a, b = dfs(i)`) inside a `for` loop. The threaded call rewrites to
-- `((a, b), vis) = dfs'(i, vis)` — a NESTED tuple target in a `do` block — which nests null-node
-- wrappers; the do-sequence flattener must recurse or the inner wrapper leaks as a stray `null`.
private partial def _count_components'dfs := fun (i : Int) ↦ fun (adj : List (List Int)) ↦ fun (vis : List Bool) ↦
  Id.run
    (do
      let mut vis := vis
      vis := PastaLean.pySetItem vis i Bool.true
      let mut nodes : Int := (1 : Int)
      let mut edges : Int := PastaLean.pyLen adj⦋i⦌
      for j in (PastaLean.pyIter adj⦋i⦌) do
        if h_1 : ¬PastaLean.pyTruthy vis⦋j⦌ = true then 
          let p'_unpack_value_1 := _count_components'dfs j adj vis
          let p'_unpack_pair_1 := p'_unpack_value_1
          vis := Prod.snd p'_unpack_pair_1
          let p'_unpack_nested_1 := Prod.fst p'_unpack_pair_1
          let mut a : Int := Prod.fst p'_unpack_nested_1
          let mut b : Int := Prod.snd p'_unpack_nested_1
          nodes := nodes +ₚ a
          edges := edges +ₚ b
      let p'_ret_1 := ((nodes, edges), vis)
      return p'_ret_1)

def count_components := fun (n : Int) ↦ fun (adj : List (List Int)) ↦
  Id.run
    (do
      let mut vis : List Bool := PastaLean.pyListRepeat [Bool.false] n
      let mut complete : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        if h_1 : ¬PastaLean.pyTruthy vis⦋i⦌ = true then 
          let p'_unpack_value_1 := _count_components'dfs i adj vis
          let p'_unpack_pair_1 := p'_unpack_value_1
          vis := Prod.snd p'_unpack_pair_1
          let p'_unpack_nested_1 := Prod.fst p'_unpack_pair_1
          let mut v : Int := Prod.fst p'_unpack_nested_1
          let mut e : Int := Prod.snd p'_unpack_nested_1
          if h_2 : e = v *ₚ (v -ₚ (1 : Int)) then 
            complete := complete +ₚ (1 : Int)
      return complete)

attribute [simp, taste_ingr] count_components

private partial def _count_components'dfs'rn := fun (i : Int) ↦ fun (adj : List (List Int)) ↦ fun (vis : List Bool) ↦
  Id.run
    (do
      let mut vis := vis
      vis := PastaLean.pySetItem vis i Bool.true
      let mut nodes : Int := (1 : Int)
      let mut edges : Int := PastaLean.pyLen adj⦋i⦌
      for j in (PastaLean.pyIter adj⦋i⦌) do
        if h_1 : !PastaLean.pyTruthy vis⦋j⦌ then 
          let p'_unpack_value_1 := _count_components'dfs'rn j adj vis
          let p'_unpack_pair_1 := p'_unpack_value_1
          vis := Prod.snd p'_unpack_pair_1
          let p'_unpack_nested_1 := Prod.fst p'_unpack_pair_1
          let mut a : Int := Prod.fst p'_unpack_nested_1
          let mut b : Int := Prod.snd p'_unpack_nested_1
          nodes := nodes +ₚ a
          edges := edges +ₚ b
      let p'_ret_1 := ((nodes, edges), vis)
      return p'_ret_1)

def count_components'rn := fun (n : Int) ↦ fun (adj : List (List Int)) ↦
  Id.run
    (do
      let mut vis : List Bool := PastaLean.pyListRepeat [Bool.false] n
      let mut complete : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        if h_1 : !PastaLean.pyTruthy vis⦋i⦌ then 
          let p'_unpack_value_1 := _count_components'dfs'rn i adj vis
          let p'_unpack_pair_1 := p'_unpack_value_1
          vis := Prod.snd p'_unpack_pair_1
          let p'_unpack_nested_1 := Prod.fst p'_unpack_pair_1
          let mut v : Int := Prod.fst p'_unpack_nested_1
          let mut e : Int := Prod.snd p'_unpack_nested_1
          if h_2 : e == v *ₚ (v -ₚ (1 : Int)) then 
            complete := complete +ₚ (1 : Int)
      return complete)

def main' :=
  ((do
      -- two triangles (complete) + one path of 2 (complete) → 3 complete components
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (count_components (8 : Int)
                  [[(1 : Int), (2 : Int)], [(0 : Int), (2 : Int)], [(0 : Int), (1 : Int)], [(4 : Int), (5 : Int)],
                    [(3 : Int), (5 : Int)], [(3 : Int), (4 : Int)], [(7 : Int)], [(6 : Int)]])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof [pyPrintArg (count_components (3 : Int) [[(1 : Int)], [(0 : Int)], []])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      -- two triangles (complete) + one path of 2 (complete) → 3 complete components
      let _ ←
        pyPrintIO
            [pyPrintArg
                (count_components'rn (8 : Int)
                  [[(1 : Int), (2 : Int)], [(0 : Int), (2 : Int)], [(0 : Int), (1 : Int)], [(4 : Int), (5 : Int)],
                    [(3 : Int), (5 : Int)], [(3 : Int), (4 : Int)], [(7 : Int)], [(6 : Int)]])]
      let _ ← pyPrintIO [pyPrintArg (count_components'rn (3 : Int) [[(1 : Int)], [(0 : Int)], []])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
