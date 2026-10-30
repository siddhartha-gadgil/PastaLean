import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- !/usr/bin/env python3
/-
Numeric widening — a binder/container is typed by the JOIN of every value written to it
(design-choices.md §27). The hard part is that the widening SOURCE is only visible after desugaring
(chained assign) or only if a library call is typed (heappop), so these exercise the pipeline order
`desugar → infer` and the library-typing rules that keep an `unknown` from poisoning the join.
-/
-- Chained assign + true-division widening: `pre` starts int (0) via `ans = pre = 0`, then widens to ℚ
-- via `pre = t`, where `t = a / b` is a true division. Splitting the chain per-target BEFORE inference
-- is what lets `pre` be ℚ while `ans` stays int. (This is LeetCode car-fleet.)
def car_fleet := fun (target : Int) ↦ fun (position : List Int) ↦ fun (speed : List Int) ↦
  Id.run
    (do
      let mut idx : List Int :=
        PastaLean.pySortBy (fun (i : Int) ↦ position⦋i⦌) false (PastaLean.pyRange (PastaLean.pyLen position))
      let mut ans : Int := (0 : Int)
      let mut pre := (0 : Rat)
      for i in (PastaLean.pyIter (PastaLean.pySlice idx none none (some (-(1 : Int)))))do
        let mut t := (target -ₚ position⦋i⦌) /ₚ speed⦋i⦌
        if h_1 : t > pre then 
          ans := ans +ₚ (1 : Int)
          pre := t
      return ans)

attribute [simp, taste_ingr] car_fleet

def car_fleet'rn := fun (target : Int) ↦ fun (position : List Int) ↦ fun (speed : List Int) ↦
  Id.run
    (do
      let mut idx : List Int :=
        PastaLean.pySortBy (fun (i : Int) ↦ position⦋i⦌) false (PastaLean.pyRange (PastaLean.pyLen position))
      let mut ans : Int := (0 : Int)
      let mut pre := (0 : Float)
      for i in (PastaLean.pyIter (PastaLean.pySlice idx none none (some (-(1 : Int)))))do
        let mut t := PastaLean.pyTrueDiv (target -ₚ position⦋i⦌) speed⦋i⦌
        if h_1 : t > pre then 
          ans := ans +ₚ (1 : Int)
          pre := t
      return ans)

-- `heappush` must teach the heap its element type and `heappop` must return it, else `x` is `unknown`,
-- `acc + x` is `unknown` (not float), and `acc` never widens to ℚ. Scalar-float heap (no tuple key).
def heap_float_sum := fun (vals : List Int) ↦
  (show Rat from
    Id.run
      (do
        let mut h := ([] : List Rat)
        for v in (PastaLean.pyIter vals)do
          h := Libraries.heapq.pyHeappush h (v /ₚ (2 : Int))
        let mut acc := (0 : Rat)
        while (PastaLean.pyTruthy h) do
          let mut p'_popv_1 := Libraries.heapq.pyHeappopVal h
          h := Libraries.heapq.pyHeappopRest h
          acc := acc +ₚ p'_popv_1
        return acc))

attribute [simp, taste_ingr] heap_float_sum

def heap_float_sum'rn := fun (vals : List Int) ↦
  (show Float from
    Id.run
      (do
        let mut h := ([] : List Float)
        for v in (PastaLean.pyIter vals)do
          h := Libraries.heapq.pyHeappush h (PastaLean.pyTrueDiv v (2 : Int))
        let mut acc := (0 : Float)
        while (PastaLean.pyTruthy h) do
          let mut p'_popv_1 := Libraries.heapq.pyHeappopVal h
          h := Libraries.heapq.pyHeappopRest h
          acc := acc +ₚ p'_popv_1
        return acc))

-- Container-element widening via an indexed write: `dist` starts `list[int]` (`[0]*n`), then a float
-- write (`dist[i] = s / t`) widens the whole container to `List ℚ`, with the `0`s coerced.
def widen_container := fun (n : Int) ↦ fun (s : Int) ↦ fun (t : Int) ↦
  (show Rat from
    Id.run
      (do
        let mut dist := (PastaLean.pyListRepeat [(0 : Rat)] n : List Rat)
        dist := PastaLean.pySetItem dist (0 : Int) (1 : Rat)
        for i in (PastaLean.pyRange n (1 : Int))do
          dist := PastaLean.pySetItem dist i (dist⦋i -ₚ (1 : Int)⦌ *ₚ s /ₚ t : Rat)
        let p'_ret_1 := dist⦋n -ₚ (1 : Int)⦌
        return p'_ret_1))

attribute [simp, taste_ingr] widen_container

def widen_container'rn := fun (n : Int) ↦ fun (s : Int) ↦ fun (t : Int) ↦
  (show Float from
    Id.run
      (do
        let mut dist := (PastaLean.pyArrayRepeat #[(0 : Float)] n : Array Float)
        dist := PastaLean.pySetItem dist (0 : Int) (1 : Float)
        for i in (PastaLean.pyRange n (1 : Int))do
          dist := PastaLean.pySetItem dist i (PastaLean.pyTrueDiv (dist⦋i -ₚ (1 : Int)⦌ *ₚ s) t : Float)
        let p'_ret_1 := dist⦋n -ₚ (1 : Int)⦌
        return p'_ret_1))

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (car_fleet (12 : Int) [(10 : Int), (8 : Int), (0 : Int), (5 : Int), (3 : Int)]
                  [(2 : Int), (4 : Int), (1 : Int), (1 : Int), (3 : Int)])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof [pyPrintArg (heap_float_sum [(4 : Int), (2 : Int), (8 : Int), (6 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (widen_container (4 : Int) (3 : Int) (2 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg
                (car_fleet'rn (12 : Int) [(10 : Int), (8 : Int), (0 : Int), (5 : Int), (3 : Int)]
                  [(2 : Int), (4 : Int), (1 : Int), (1 : Int), (3 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (heap_float_sum'rn [(4 : Int), (2 : Int), (8 : Int), (6 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (widen_container'rn (4 : Int) (3 : Int) (2 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
