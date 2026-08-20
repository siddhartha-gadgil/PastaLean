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
`float('inf')` used as a DP sentinel in an INTEGER context.

Python compares `-inf` against ints freely, but Lean needs one type per slot. A monomorphic `ℚ`
sentinel made `-inf` unusable inside an `-> int` function, so the sentinel is polymorphic in its
numeric type and the surrounding slot picks it.
-/
def inf {α : Type} [PastaLean.PyNonFinite α] : α :=
  PastaLean.pyNonFinite "inf"

-- The sentinel flows through an int-annotated recursive DP.
private partial def _best_pair'dfs : Int → Int → List Int → Int := fun (i : Int) ↦ fun (j : Int) ↦
  fun (rods : List Int) ↦
  if i ≥ PastaLean.pyLen rods then if j = (0 : Int) then (0 : Int) else -inf
  else
    let ans :=
      PastaLean.pyMax [_best_pair'dfs (i +ₚ (1 : Int)) j rods, _best_pair'dfs (i +ₚ (1 : Int)) (j +ₚ rods⦋i⦌) rods]
    PastaLean.pyMax
      [ans, _best_pair'dfs (i +ₚ (1 : Int)) (PastaLean.pyAbs (rods⦋i⦌ -ₚ j)) rods +ₚ PastaLean.pyMin [j, rods⦋i⦌]]

def best_pair := fun (rods : List Int) ↦ _best_pair'dfs (0 : Int) (0 : Int) rods

attribute [simp, taste_ingr] best_pair

private partial def _best_pair'dfs'rn : Int → Int → List Int → Int := fun (i : Int) ↦ fun (j : Int) ↦
  fun (rods : List Int) ↦
  if i ≥ PastaLean.pyLen rods then if j == (0 : Int) then (0 : Int) else -inf
  else
    let ans :=
      PastaLean.pyMax
        [_best_pair'dfs'rn (i +ₚ (1 : Int)) j rods, _best_pair'dfs'rn (i +ₚ (1 : Int)) (j +ₚ rods⦋i⦌) rods]
    PastaLean.pyMax
      [ans, _best_pair'dfs'rn (i +ₚ (1 : Int)) (PastaLean.pyAbs (rods⦋i⦌ -ₚ j)) rods +ₚ PastaLean.pyMin [j, rods⦋i⦌]]

def best_pair'rn := fun (rods : List Int) ↦ _best_pair'dfs'rn (0 : Int) (0 : Int) rods

-- `inf` as a minimisation seed, still an int result.
def smallest := fun (xs : List Int) ↦
  Id.run
    (do
      let mut lo := inf
      for x in (PastaLean.pyIter xs) do
        lo := PastaLean.pyMin [lo, x]
      return lo)

attribute [simp, taste_ingr] smallest

def smallest'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut lo := inf
      for x in (PastaLean.pyIter xs) do
        lo := PastaLean.pyMin [lo, x]
      return lo)

-- The same global in a float slot — must still be usable there.
def scaled := fun (xs : List Rat) ↦
  Id.run
    (do
      let mut hi := -inf
      for x in (PastaLean.pyIter xs) do
        hi := PastaLean.pyMax [hi, x *ₚ (2.0 : Rat)]
      return hi)

attribute [simp, taste_ingr] scaled

def scaled'rn := fun (xs : List Float) ↦
  Id.run
    (do
      let mut hi := -inf
      for x in (PastaLean.pyIter xs) do
        hi := PastaLean.pyMax [hi, x *ₚ (2.0 : Float)]
      return hi)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (best_pair [(1 : Int), (2 : Int), (3 : Int), (6 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (smallest [(4 : Int), (2 : Int), (9 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (scaled [(1.5 : Rat), (0.5 : Rat)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (best_pair'rn [(1 : Int), (2 : Int), (3 : Int), (6 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (smallest'rn [(4 : Int), (2 : Int), (9 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (scaled'rn [(1.5 : Float), (0.5 : Float)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()