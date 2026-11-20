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
Iterating and consuming n-tuples.

A Python tuple is immutable and stays a tuple (a nested Lean product `a × (b × …)`), NOT a list. But
a *homogeneous* tuple is still a sequence: it can be iterated, paired up, summed. That works through a
recursive `PyIterable (α × β) α` instance that flattens an all-`α` tuple to a `List α` at the point of
iteration — the tuple itself is never rewritten to a list.
-/
-- The classic direction-deltas idiom: a fixed tuple iterated via `pairwise`.
def neighbours := fun (i : Int) ↦ fun (j : Int) ↦
  Id.run
    (do
      let mut dirs : Int × Int × Int × Int × Int := (-(1 : Int), ((0 : Int), ((1 : Int), ((0 : Int), -(1 : Int)))))
      let mut out : List (Int × Int) := []
      for p'_pair_1 in (PastaLean.pyIter (Libraries.itertools.pyPairwise dirs))do
        let a := Prod.fst p'_pair_1
        let b := Prod.snd p'_pair_1
        out := PastaLean.pyAppend out (i +ₚ a, j +ₚ b)
      return out)

attribute [simp, taste_ingr] neighbours

def neighbours'rn := fun (i : Int) ↦ fun (j : Int) ↦
  Id.run
    (do
      let mut dirs : Int × Int × Int × Int × Int := (-(1 : Int), ((0 : Int), ((1 : Int), ((0 : Int), -(1 : Int)))))
      let mut out : List (Int × Int) := []
      for p'_pair_1 in (PastaLean.pyIter (Libraries.itertools.pyPairwise dirs))do
        let a := Prod.fst p'_pair_1
        let b := Prod.snd p'_pair_1
        out := PastaLean.pyAppend out (i +ₚ a, j +ₚ b)
      return out)

-- A homogeneous tuple consumed by `sum` / `max` and iterated by a `for`.
def stats := fun (t : Int × Int × Int × Int × Int × Int × Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for x in (PastaLean.pyIter t)do
        total := total +ₚ x
      let p'_ret_1 := (total, (PastaLean.pyMax t, PastaLean.pyMin t))
      return p'_ret_1)

attribute [simp, taste_ingr] stats

def stats'rn := fun (t : Int × Int × Int × Int × Int × Int × Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for x in (PastaLean.pyIter t)do
        total := total +ₚ x
      let p'_ret_1 := (total, (PastaLean.pyMax t, PastaLean.pyMin t))
      return p'_ret_1)

-- A homogeneous tuple is indexable (`t[k]`) and sliceable (`t[1:]`, `t[:]`) — a variable-length
-- slice flattens to a list, since it can't stay a fixed-arity product.
def homog_index :=
  let t := (((3 : Int), ((1 : Int), ((4 : Int), ((1 : Int), (5 : Int))))) : Int × Int × Int × Int × Int)
  (Prod.fst t,
    (Prod.fst (Prod.snd (Prod.snd t)),
      (PastaLean.pySlice (PastaLean.pyIter t) (some (1 : Int)) none none,
        PastaLean.pySlice (PastaLean.pyIter t) none none none)))

attribute [simp, taste_ingr] homog_index

def homog_index'rn :=
  let t := (((3 : Int), ((1 : Int), ((4 : Int), ((1 : Int), (5 : Int))))) : Int × Int × Int × Int × Int)
  (Prod.fst t,
    (Prod.fst (Prod.snd (Prod.snd t)),
      (PastaLean.pySlice (PastaLean.pyIter t) (some (1 : Int)) none none,
        PastaLean.pySlice (PastaLean.pyIter t) none none none)))

-- A heterogeneous tuple keeps a distinct type per slot; a constant index projects the exact one.
def heterog_index :=
  let t := (((1 : Int), ("a", (3 : Int))) : Int × String × Int)
  (Prod.fst t, (Prod.fst (Prod.snd t), Prod.snd (Prod.snd t)))

attribute [simp, taste_ingr] heterog_index

def heterog_index'rn :=
  let t := (((1 : Int), ("a", (3 : Int))) : Int × String × Int)
  (Prod.fst t, (Prod.fst (Prod.snd t), Prod.snd (Prod.snd t)))

-- Nested for-target: `(a, b)` comes from `zip` (a Prod), so it must unpack via Prod, not list index.
def nested_for_unpack := fun (xs : List Int) ↦ fun (ys : List Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate (PastaLean.pyZip xs ys) (1 : Int)))do
        let i := Prod.fst p'_pair_1
        let p'_for_unpack_1 := Prod.snd p'_pair_1
        let p'_unpack_value_1 := p'_for_unpack_1
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut a : Int := Prod.fst p'_unpack_pair_1
        let mut b : Int := Prod.snd p'_unpack_pair_1
        total := total +ₚ i *ₚ (a +ₚ b)
      return total)

attribute [simp, taste_ingr] nested_for_unpack

def nested_for_unpack'rn := fun (xs : List Int) ↦ fun (ys : List Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate (PastaLean.pyZip xs ys) (1 : Int)))do
        let i := Prod.fst p'_pair_1
        let p'_for_unpack_1 := Prod.snd p'_pair_1
        let p'_unpack_value_1 := p'_for_unpack_1
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut a : Int := Prod.fst p'_unpack_pair_1
        let mut b : Int := Prod.snd p'_unpack_pair_1
        total := total +ₚ i *ₚ (a +ₚ b)
      return total)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (neighbours (5 : Int) (5 : Int))]
      let _ ←
        PastaLean.ProofMode.pyPrintProof [pyPrintArg (nested_for_unpack [(1 : Int), (2 : Int)] [(3 : Int), (4 : Int)])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (stats ((3 : Int), ((1 : Int), ((4 : Int), ((1 : Int), ((5 : Int), ((9 : Int), (2 : Int))))))))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg homog_index]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg heterog_index]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (neighbours'rn (5 : Int) (5 : Int))]
      let _ ← pyPrintIO [pyPrintArg (nested_for_unpack'rn [(1 : Int), (2 : Int)] [(3 : Int), (4 : Int)])]
      let _ ←
        pyPrintIO
            [pyPrintArg
                (stats'rn ((3 : Int), ((1 : Int), ((4 : Int), ((1 : Int), ((5 : Int), ((9 : Int), (2 : Int))))))))]
      let _ ← pyPrintIO [pyPrintArg homog_index'rn]
      let _ ← pyPrintIO [pyPrintArg heterog_index'rn]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
