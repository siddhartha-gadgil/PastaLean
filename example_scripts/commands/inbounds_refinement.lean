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

/-
`for i in range(len(xs))` proves every `xs[i]` in range, so those reads lower to the
proof-carrying `pyListGetProof` instead of the defaulting `pyGetItem`. Each function below is a
shape the refinement must either take (the first three) or correctly refuse (the rest).
-/
def total := fun (xs : List Int) ↦
  Id.run
    (do
      let mut s : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        s := s +ₚ PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
      return s)

attribute [simp, taste_ingr] total

def total'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut s : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        s := s +ₚ PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
      return s)

def pairwise_max := fun (xs : List Int) ↦
  Id.run
    (do
      let mut best : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        -- A second, non-refinable read of the same list in the same body: `i + 1` is not the loop
        -- variable, so it keeps the defaulting lowering while `xs[i]` gets the proof.
        if h_1 : PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i) > best then 
          best := PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
      return best)

attribute [simp, taste_ingr] pairwise_max

def pairwise_max'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut best : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        -- A second, non-refinable read of the same list in the same body: `i + 1` is not the loop
        -- variable, so it keeps the defaulting lowering while `xs[i]` gets the proof.
        if h_1 : PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i) > best then 
          best := PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
      return best)

def grid_sum := fun (g : List (List Int)) ↦
  Id.run
    (do
      let mut s : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen g))do
        let mut row : List Int := PastaLean.pyListGetProof g i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
        for j in (PastaLean.pyRange (PastaLean.pyLen row))do
          s := s +ₚ row⦋j⦌
      return s)

attribute [simp, taste_ingr] grid_sum

def grid_sum'rn := fun (g : List (List Int)) ↦
  Id.run
    (do
      let mut s : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen g))do
        let mut row : List Int := PastaLean.pyListGetProof g i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
        for j in (PastaLean.pyRange (PastaLean.pyLen row))do
          s := s +ₚ row⦋j⦌
      return s)

def grow_while_reading := fun (xs : List Int) ↦
  Id.run
    (do
      let mut xs := xs
      -- `xs` grows inside the loop, so `len(xs)` at entry bounds nothing.
      let mut s : Int := (0 : Int)
      for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        s := s +ₚ xs⦋i⦌
        xs := PastaLean.pyAppend xs s
      return s)

attribute [simp, taste_ingr] grow_while_reading

def grow_while_reading'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut xs := xs
      -- `xs` grows inside the loop, so `len(xs)` at entry bounds nothing.
      let mut s : Int := (0 : Int)
      for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        s := s +ₚ xs⦋i⦌
        xs := PastaLean.pyAppend xs s
      return s)

def store_through_index := fun (xs : List Int) ↦
  Id.run
    (do
      let mut xs := xs
      -- An indexed STORE also invalidates the refinement's reasoning about `xs`.
      for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        xs := PastaLean.pySetItem xs i (xs⦋i⦌ *ₚ (2 : Int))
      return xs)

attribute [simp, taste_ingr] store_through_index

def store_through_index'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut xs := xs
      -- An indexed STORE also invalidates the refinement's reasoning about `xs`.
      for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        xs := PastaLean.pySetItem xs i (xs⦋i⦌ *ₚ (2 : Int))
      return xs)

def shifted_reads := fun (xs : List Int) ↦
  Id.run
    (do
      -- `i + 1` and `len(xs) - 1 - i` are not the loop variable; both stay defaulting.
      let mut s : Int := (0 : Int)
      for i in (PastaLean.pyRange (PastaLean.pyLen xs -ₚ (1 : Int)))do
        s := s +ₚ xs⦋i +ₚ (1 : Int)⦌
      return s)

attribute [simp, taste_ingr] shifted_reads

def shifted_reads'rn := fun (xs : List Int) ↦
  Id.run
    (do
      -- `i + 1` and `len(xs) - 1 - i` are not the loop variable; both stay defaulting.
      let mut s : Int := (0 : Int)
      for i in (PastaLean.pyRange (PastaLean.pyLen xs -ₚ (1 : Int)))do
        s := s +ₚ xs⦋i +ₚ (1 : Int)⦌
      return s)

def shadowed_index := fun (xs : List Int) ↦
  Id.run
    (do
      let mut s : Int := (0 : Int)
      for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        let mut f := fun i ↦ i *ₚ (2 : Int)
        s := s +ₚ f xs⦋i⦌
      return s)

attribute [simp, taste_ingr] shadowed_index

def shadowed_index'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut s : Int := (0 : Int)
      for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        let mut f := fun i ↦ i *ₚ (2 : Int)
        s := s +ₚ f xs⦋i⦌
      return s)

def aliased_len := fun (xs : List Int) ↦
  Id.run
    (do
      -- `n = len(xs)` once, then `range(n)`: the bound is still `xs`'s length, proved through the alias.
      let mut n : Int := PastaLean.pyLen xs
      let mut s : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange n)do
        s := s +ₚ PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
      return s)

attribute [simp, taste_ingr] aliased_len

def aliased_len'rn := fun (xs : List Int) ↦
  Id.run
    (do
      -- `n = len(xs)` once, then `range(n)`: the bound is still `xs`'s length, proved through the alias.
      let mut n : Int := PastaLean.pyLen xs
      let mut s : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange n)do
        s := s +ₚ PastaLean.pyListGetProof xs i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
      return s)

def rebound_alias := fun (xs : List Int) ↦
  Id.run
    (do
      -- `n` is reassigned, so it is no longer a stable alias for `len(xs)`.
      let mut n : Int := PastaLean.pyLen xs
      let mut s : Int := (0 : Int)
      n := n -ₚ (1 : Int)
      for i in (PastaLean.pyRange n)do
        s := s +ₚ xs⦋i⦌
      return s)

attribute [simp, taste_ingr] rebound_alias

def rebound_alias'rn := fun (xs : List Int) ↦
  Id.run
    (do
      -- `n` is reassigned, so it is no longer a stable alias for `len(xs)`.
      let mut n : Int := PastaLean.pyLen xs
      let mut s : Int := (0 : Int)
      n := n -ₚ (1 : Int)
      for i in (PastaLean.pyRange n)do
        s := s +ₚ xs⦋i⦌
      return s)

def main' :=
  ((do
      let mut data : List Int := [(3 : Int), (1 : Int), (4 : Int), (1 : Int), (5 : Int)]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (total data)]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (pairwise_max data)]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (grid_sum [[(1 : Int), (2 : Int)], [(3 : Int), (4 : Int), (5 : Int)]])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (grow_while_reading [(1 : Int), (2 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (store_through_index [(1 : Int), (2 : Int), (3 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (shifted_reads data)]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (shadowed_index data)]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (aliased_len data)]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (rebound_alias data)]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let mut data : List Int := [(3 : Int), (1 : Int), (4 : Int), (1 : Int), (5 : Int)]
      let _ ← pyPrintIO [pyPrintArg (total'rn data)]
      let _ ← pyPrintIO [pyPrintArg (pairwise_max'rn data)]
      let _ ← pyPrintIO [pyPrintArg (grid_sum'rn [[(1 : Int), (2 : Int)], [(3 : Int), (4 : Int), (5 : Int)]])]
      let _ ← pyPrintIO [pyPrintArg (grow_while_reading'rn [(1 : Int), (2 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (store_through_index'rn [(1 : Int), (2 : Int), (3 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (shifted_reads'rn data)]
      let _ ← pyPrintIO [pyPrintArg (shadowed_index'rn data)]
      let _ ← pyPrintIO [pyPrintArg (aliased_len'rn data)]
      let _ ← pyPrintIO [pyPrintArg (rebound_alias'rn data)]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
