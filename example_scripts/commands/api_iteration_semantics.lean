import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Three Python semantics that differ from a naive Lean lowering:
-- 1. `for x in q` where the body APPENDS to `q` visits the appended items (BFS/topological idiom) —
-- Python re-reads the list each step; a snapshot `for` would miss them.
-- 2. `sum(<bool generator>)` is an int (True counts as 1), not a bool.
-- 3. a nested `and`/`or` with a non-bool operand in a condition (`a or (b and n)`) truthiness-tests it.
def topo_order_count := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut g : List (List Int) := (PastaLean.pyRange n).map fun (_ : Int) => []
      let mut indeg : List Int := PastaLean.pyListRepeat [(0 : Int)] n
      for p'_pair_1 in (PastaLean.pyIter edges) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        g := PastaLean.pySetItem g b (PastaLean.pyAppend g⦋b⦌ a)
        indeg := PastaLean.pySetItem indeg a (indeg⦋a⦌ +ₚ (1 : Int))
      let mut q : List Int := List.filter (fun (i : Int) => indeg⦋i⦌ = (0 : Int)) (PastaLean.pyRange n)
      let mut seen : Int := (0 : Int)
      let mut p'_fi'_1 : Int := -1
      while (p'_fi'_1 +ₚ (1 : Int)) < PastaLean.pyLen q do
        p'_fi'_1 := p'_fi'_1 +ₚ (1 : Int)
        let i := PastaLean.pyGetItem q p'_fi'_1
        seen := seen +ₚ (1 : Int)
        for j in (PastaLean.pyIter g⦋i⦌) do
          indeg := PastaLean.pySetItem indeg j (indeg⦋j⦌ -ₚ (1 : Int))
          if h_1 : indeg⦋j⦌ = (0 : Int) then 
            q := PastaLean.pyAppend q j
      return seen)

attribute [simp, taste_ingr] topo_order_count

def topo_order_count'rn := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut g : List (List Int) := (PastaLean.pyRange n).map fun (_ : Int) => []
      let mut indeg : Array Int := PastaLean.pyArrayRepeat #[(0 : Int)] n
      for p'_pair_1 in (PastaLean.pyIter edges) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        g := PastaLean.pySetItem g b (PastaLean.pyAppend g⦋b⦌ a)
        indeg := PastaLean.pySetItem indeg a (indeg⦋a⦌ +ₚ (1 : Int))
      let mut q : Array Int := List.filter (fun (i : Int) => indeg⦋i⦌ == (0 : Int)) (PastaLean.pyRange n) |>.toArray
      let mut seen : Int := (0 : Int)
      let mut p'_fi'_1 : Int := -1
      while (p'_fi'_1 +ₚ (1 : Int)) < PastaLean.pyLen q do
        p'_fi'_1 := p'_fi'_1 +ₚ (1 : Int)
        let i := PastaLean.pyGetItem q p'_fi'_1
        seen := seen +ₚ (1 : Int)
        for j in (PastaLean.pyIter g⦋i⦌) do
          indeg := PastaLean.pySetItem indeg j (indeg⦋j⦌ -ₚ (1 : Int))
          if h_1 : indeg⦋j⦌ == (0 : Int) then 
            q := PastaLean.pyArrayAppend q j
      return seen)

def count_vowels := fun (s : String) ↦
  let vowels := (PastaLean.pySet "aeiou" : PastaLean.PySet String)
  PastaLean.pySum ((PastaLean.pyIter s).map fun (c : String) => PastaLean.pyContains vowels c)

attribute [simp, taste_ingr] count_vowels

def count_vowels'rn := fun (s : String) ↦
  let vowels := (PastaLean.pySet "aeiou" : PastaLean.PySet String)
  PastaLean.pySum ((PastaLean.pyIter s).map fun (c : String) => PastaLean.pyContains vowels c)

def feb_days := fun (y : Int) ↦
  -- `y % 100` is a truthy int inside the nested `and` — the condition must truthiness-test it.
  if y %ₚ (400 : Int) = (0 : Int) ∨ y %ₚ (4 : Int) = (0 : Int) ∧ PastaLean.pyTruthy (y %ₚ (100 : Int)) = true then
    (29 : Int)
  else (28 : Int)

attribute [simp, taste_ingr] feb_days

def feb_days'rn := fun (y : Int) ↦
  -- `y % 100` is a truthy int inside the nested `and` — the condition must truthiness-test it.
  if y %ₚ (400 : Int) == (0 : Int) || y %ₚ (4 : Int) == (0 : Int) && PastaLean.pyTruthy (y %ₚ (100 : Int)) then
    (29 : Int)
  else (28 : Int)

def greedy_flips := fun (nums : List Int) ↦
  Id.run
    (do
      let mut nums := nums
      -- `for i, x in enumerate(nums): nums[i+1] ^= 1` mutates a LATER index; Python's live `enumerate`
      -- sees it on the next iteration, so the container must be re-read by index.
      let mut ops : Int := (0 : Int)
      let mut p'_fi'_1 : Int := -1
      while (p'_fi'_1 +ₚ (1 : Int)) < PastaLean.pyLen nums do
        p'_fi'_1 := p'_fi'_1 +ₚ (1 : Int)
        let p'_pair_1 := (p'_fi'_1, PastaLean.pyGetItem nums p'_fi'_1)
        let i := Prod.fst p'_pair_1
        let x := Prod.snd p'_pair_1
        if h_1 : x = (0 : Int) then 
          if h_2 : i +ₚ (2 : Int) ≥ PastaLean.pyLen nums then 
            let p'_ret_1 := -(1 : Int)
            return p'_ret_1
          nums := PastaLean.pySetItem nums (i +ₚ (1 : Int)) (PastaLean.pyBitXor nums⦋i +ₚ (1 : Int)⦌ (1 : Int))
          nums := PastaLean.pySetItem nums (i +ₚ (2 : Int)) (PastaLean.pyBitXor nums⦋i +ₚ (2 : Int)⦌ (1 : Int))
          ops := ops +ₚ (1 : Int)
      return ops)

attribute [simp, taste_ingr] greedy_flips

def greedy_flips'rn := fun (nums : List Int) ↦
  Id.run
    (do
      let mut nums := nums
      -- `for i, x in enumerate(nums): nums[i+1] ^= 1` mutates a LATER index; Python's live `enumerate`
      -- sees it on the next iteration, so the container must be re-read by index.
      let mut ops : Int := (0 : Int)
      let mut p'_fi'_1 : Int := -1
      while (p'_fi'_1 +ₚ (1 : Int)) < PastaLean.pyLen nums do
        p'_fi'_1 := p'_fi'_1 +ₚ (1 : Int)
        let p'_pair_1 := (p'_fi'_1, PastaLean.pyGetItem nums p'_fi'_1)
        let i := Prod.fst p'_pair_1
        let x := Prod.snd p'_pair_1
        if h_1 : x == (0 : Int) then 
          if h_2 : i +ₚ (2 : Int) ≥ PastaLean.pyLen nums then 
            let p'_ret_1 := -(1 : Int)
            return p'_ret_1
          nums := PastaLean.pySetItem nums (i +ₚ (1 : Int)) (PastaLean.pyBitXor nums⦋i +ₚ (1 : Int)⦌ (1 : Int))
          nums := PastaLean.pySetItem nums (i +ₚ (2 : Int)) (PastaLean.pyBitXor nums⦋i +ₚ (2 : Int)⦌ (1 : Int))
          ops := ops +ₚ (1 : Int)
      return ops)

def flip_invert := fun (image : List (List Int)) ↦
  Id.run
    (do
      let mut image := image
      -- `for row in image: <mutate row in place>` must write the mutated row back into `image` — the
      -- loop var is a value copy under our semantics.
      let mut p'_fi'_1 : Int := -1
      while (p'_fi'_1 +ₚ (1 : Int)) < PastaLean.pyLen image do
        p'_fi'_1 := p'_fi'_1 +ₚ (1 : Int)
        let p'_loop_1 := PastaLean.pyGetItem image p'_fi'_1
        let mut row := p'_loop_1
        row := PastaLean.pyReverse row
        for i in (PastaLean.pyRange (PastaLean.pyLen row)) do
          row := PastaLean.pySetItem row i (PastaLean.pyBitXor row⦋i⦌ (1 : Int))
        image := PastaLean.pySetItem image p'_fi'_1 row
      return image)

attribute [simp, taste_ingr] flip_invert

def flip_invert'rn := fun (image : List (List Int)) ↦
  Id.run
    (do
      let mut image := image
      -- `for row in image: <mutate row in place>` must write the mutated row back into `image` — the
      -- loop var is a value copy under our semantics.
      let mut p'_fi'_1 : Int := -1
      while (p'_fi'_1 +ₚ (1 : Int)) < PastaLean.pyLen image do
        p'_fi'_1 := p'_fi'_1 +ₚ (1 : Int)
        let p'_loop_1 := PastaLean.pyGetItem image p'_fi'_1
        let mut row := p'_loop_1
        row := PastaLean.pyReverse row
        for i in (PastaLean.pyRange (PastaLean.pyLen row)) do
          row := PastaLean.pySetItem row i (PastaLean.pyBitXor row⦋i⦌ (1 : Int))
        image := PastaLean.pySetItem image p'_fi'_1 row
      return image)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (topo_order_count (4 : Int)
                  [[(1 : Int), (0 : Int)], [(2 : Int), (0 : Int)], [(3 : Int), (1 : Int)], [(3 : Int), (2 : Int)]])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (topo_order_count (2 : Int) [[(1 : Int), (0 : Int)], [(0 : Int), (1 : Int)]])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (count_vowels "leetcode")]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (feb_days (2004 : Int)), pyPrintArg (feb_days (1900 : Int)), pyPrintArg (feb_days (2000 : Int))]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (greedy_flips [(0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (flip_invert
                  [[(1 : Int), (1 : Int), (0 : Int)], [(1 : Int), (0 : Int), (1 : Int)],
                    [(0 : Int), (0 : Int), (0 : Int)]])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg
                (topo_order_count'rn (4 : Int)
                  [[(1 : Int), (0 : Int)], [(2 : Int), (0 : Int)], [(3 : Int), (1 : Int)], [(3 : Int), (2 : Int)]])]
      let _ ← pyPrintIO [pyPrintArg (topo_order_count'rn (2 : Int) [[(1 : Int), (0 : Int)], [(0 : Int), (1 : Int)]])]
      let _ ← pyPrintIO [pyPrintArg (count_vowels'rn "leetcode")]
      let _ ←
        pyPrintIO
            [pyPrintArg (feb_days'rn (2004 : Int)), pyPrintArg (feb_days'rn (1900 : Int)),
              pyPrintArg (feb_days'rn (2000 : Int))]
      let _ ←
        pyPrintIO [pyPrintArg (greedy_flips'rn [(0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)])]
      let _ ←
        pyPrintIO
            [pyPrintArg
                (flip_invert'rn
                  [[(1 : Int), (1 : Int), (0 : Int)], [(1 : Int), (0 : Int), (1 : Int)],
                    [(0 : Int), (0 : Int), (0 : Int)]])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
