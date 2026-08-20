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
A nested function that MUTATES captured state, called inside a comprehension.

Under value semantics the mutation is threaded through each call, but a comprehension has no
statement position to thread through. Each such comprehension (an aggregator over a generator, or a
bare list/set/dict comprehension) is rewritten to its explicit accumulator loop, where the threaded
call lands in a statement and the mutated state carries across iterations. A comprehension is exactly
that loop by definition, so this is semantics-preserving.
-/
-- `sum(dfs(i) for i in …)`: `dfs` mutates the captured `seen` set; the visited state must persist
-- across the generator's iterations (a flood-fill / connected-components shape).
private partial def _count_components'dfs := fun (i : Int) ↦ fun (adj : List (List Int)) ↦ fun seen ↦
  Id.run
    (do
      let mut seen := seen
      if h_1 : PastaLean.pyContains seen i then 
        let __py_ret_1 := ((0 : Int), seen)
        return __py_ret_1
      else
        let _ := ()
      seen := PastaLean.pySetAdd seen i
      for j in (PastaLean.pyIter adj⦋i⦌) do
        let __unpack_value_1 := _count_components'dfs j adj seen
        let __unpack_pair_1 := __unpack_value_1
        let mut __thread_t1 := Prod.fst __unpack_pair_1
        seen := Prod.snd __unpack_pair_1
      let __py_ret_1 := ((1 : Int), seen)
      return __py_ret_1)

def count_components := fun (n : Int) ↦ fun (adj : List (List Int)) ↦
  Id.run
    (do
      let mut seen := PastaLean.pySetFromList []
      let mut __cc2 := []
      for i in (PastaLean.pyRange n) do
        let __unpack_value_1 := _count_components'dfs i adj seen
        let __unpack_pair_1 := __unpack_value_1
        let mut __thread_t3 := Prod.fst __unpack_pair_1
        seen := Prod.snd __unpack_pair_1
        __cc2 := PastaLean.pyAppend __cc2 __thread_t3
      let __py_ret_1 := PastaLean.pySum __cc2
      return __py_ret_1)

attribute [simp, taste_ingr] count_components

private partial def _count_components'dfs'rn := fun (i : Int) ↦ fun (adj : List (List Int)) ↦ fun seen ↦
  Id.run
    (do
      let mut seen := seen
      if h_1 : PastaLean.pyContains seen i then 
        let __py_ret_1 := ((0 : Int), seen)
        return __py_ret_1
      else
        let _ := ()
      seen := PastaLean.pySetAdd seen i
      for j in (PastaLean.pyIter adj⦋i⦌) do
        let __unpack_value_1 := _count_components'dfs'rn j adj seen
        let __unpack_pair_1 := __unpack_value_1
        let mut __thread_t1 := Prod.fst __unpack_pair_1
        seen := Prod.snd __unpack_pair_1
      let __py_ret_1 := ((1 : Int), seen)
      return __py_ret_1)

def count_components'rn := fun (n : Int) ↦ fun (adj : List (List Int)) ↦
  Id.run
    (do
      let mut seen := PastaLean.pySetFromList []
      let mut __cc2 := []
      for i in (PastaLean.pyRange n) do
        let __unpack_value_1 := _count_components'dfs'rn i adj seen
        let __unpack_pair_1 := __unpack_value_1
        let mut __thread_t3 := Prod.fst __unpack_pair_1
        seen := Prod.snd __unpack_pair_1
        __cc2 := PastaLean.pyAppend __cc2 __thread_t3
      let __py_ret_1 := PastaLean.pySum __cc2
      return __py_ret_1)

-- A bare LIST comprehension whose element mutates captured `total` (via a helper that returns the
-- running value): the accumulator loop threads `total` correctly.
private def _running'step := fun (x : Int) ↦ fun (total : Int) ↦
  let total := (total +ₚ x : Int)
  (total, total)

attribute [simp, taste_ingr] _running'step

def running := fun (xs : List Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      let mut __cc1 := []
      for x in (PastaLean.pyIter xs) do
        let __unpack_value_1 := _running'step x total
        let __unpack_pair_1 := __unpack_value_1
        let mut __thread_t2 := Prod.fst __unpack_pair_1
        total := Prod.snd __unpack_pair_1
        __cc1 := PastaLean.pyAppend __cc1 __thread_t2
      return __cc1)

attribute [simp, taste_ingr] running

private def _running'step'rn := fun (x : Int) ↦ fun (total : Int) ↦
  let total := (total +ₚ x : Int)
  (total, total)

def running'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      let mut __cc1 := []
      for x in (PastaLean.pyIter xs) do
        let __unpack_value_1 := _running'step'rn x total
        let __unpack_pair_1 := __unpack_value_1
        let mut __thread_t2 := Prod.fst __unpack_pair_1
        total := Prod.snd __unpack_pair_1
        __cc1 := PastaLean.pyAppend __cc1 __thread_t2
      return __cc1)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (count_components (6 : Int)
                  [[(1 : Int)], [(0 : Int), (2 : Int)], [(1 : Int)], [(4 : Int)], [(3 : Int)], []])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (running [(1 : Int), (2 : Int), (3 : Int), (4 : Int)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg
                (count_components'rn (6 : Int)
                  [[(1 : Int)], [(0 : Int), (2 : Int)], [(1 : Int)], [(4 : Int)], [(3 : Int)], []])]
      let _ ← pyPrintIO [pyPrintArg (running'rn [(1 : Int), (2 : Int), (3 : Int), (4 : Int)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()