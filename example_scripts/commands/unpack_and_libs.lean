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

-- Nested tuple target with a starred inner element: `(_, *rest)` unpacks the tail of each row.
def heads_and_tails := fun (rows : List (List Int)) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate rows))do
        let i := Prod.fst p'_pair_1
        let p'_for_unpack_1 := Prod.snd p'_pair_1
        let p'_unpack_value_1 := p'_for_unpack_1
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut head : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (0 : Int)
        let mut rest := PastaLean.pyListSlice p'_unpack_pair_1 (some (1 : Int)) (none : Option Int)
        total := total +ₚ (head +ₚ PastaLean.pyLen rest)
      return total)

attribute [simp, taste_ingr] heads_and_tails

def heads_and_tails'rn := fun (rows : List (List Int)) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate rows))do
        let i := Prod.fst p'_pair_1
        let p'_for_unpack_1 := Prod.snd p'_pair_1
        let p'_unpack_value_1 := p'_for_unpack_1
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut head : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (0 : Int)
        let mut rest := PastaLean.pyListSlice p'_unpack_pair_1 (some (1 : Int)) (none : Option Int)
        total := total +ₚ (head +ₚ PastaLean.pyLen rest)
      return total)

-- defaultdict with scalar factories: float → 0.0, str → "".
def scalar_defaults := fun (keys : List PyAny) ↦
  Id.run
    (do
      let mut sums := Libraries.collections.PyDefaultDict.empty (0.0 : Float)
      let mut names : Libraries.collections.PyDefaultDict PyAny String := Libraries.collections.PyDefaultDict.empty ""
      for k in (PastaLean.pyIter keys)do
        sums := PastaLean.pySetItem sums k (sums⦋k⦌ +ₚ (1.5 : Rat))
        names := PastaLean.pySetItem names k (names⦋k⦌ +ₚ "x")
      let p'_ret_1 := names⦋keys⦋(0 : Int)⦌⦌ +ₚ PastaLean.pyStr (PastaLean.pyLen sums)
      return p'_ret_1)

attribute [simp, taste_ingr] scalar_defaults

def scalar_defaults'rn := fun (keys : List PyAny) ↦
  Id.run
    (do
      let mut sums := Libraries.collections.PyDefaultDict.empty (0.0 : Float)
      let mut names : Libraries.collections.PyDefaultDict PyAny String := Libraries.collections.PyDefaultDict.empty ""
      for k in (PastaLean.pyIter keys)do
        sums := PastaLean.pySetItem sums k (sums⦋k⦌ +ₚ (1.5 : Float))
        names := PastaLean.pySetItem names k (names⦋k⦌ +ₚ "x")
      let p'_ret_1 := names⦋keys⦋(0 : Int)⦌⦌ +ₚ PastaLean.pyStr (PastaLean.pyLen sums)
      return p'_ret_1)

-- chain.from_iterable flattens a list of lists.
def flatten_count := fun (xss : List (List Int)) ↦
  PastaLean.pyLen (PastaLean.pyList (Libraries.itertools.pyChain xss))

attribute [simp, taste_ingr] flatten_count

def flatten_count'rn := fun (xss : List (List Int)) ↦
  PastaLean.pyLen (PastaLean.pyList (Libraries.itertools.pyChain xss))

-- `count()` zipped with a finite list is bounded by it: `zip(xs, count(1))` pairs each with 1,2,3,...
def indexed_sum := fun (xs : List Int) ↦
  PastaLean.pySum
    ((PastaLean.pyIter (PastaLean.pyZip xs (PastaLean.pyRange ((1 : Int) +ₚ PastaLean.pyLen xs) (1 : Int)))).map
      fun (p'_pair_1 : Int × Int) =>
      let v := Prod.fst p'_pair_1;
      let i := Prod.snd p'_pair_1;
      v *ₚ i)

attribute [simp, taste_ingr] indexed_sum

def indexed_sum'rn := fun (xs : List Int) ↦
  PastaLean.pySum
    ((PastaLean.pyIter (PastaLean.pyZip xs (PastaLean.pyRange ((1 : Int) +ₚ PastaLean.pyLen xs) (1 : Int)))).map
      fun (p'_pair_1 : Int × Int) =>
      let v := Prod.fst p'_pair_1;
      let i := Prod.snd p'_pair_1;
      v *ₚ i)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (heads_and_tails [[(10 : Int), (1 : Int), (2 : Int), (3 : Int)], [(20 : Int), (4 : Int)]])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (scalar_defaults ["a", "a", "b"])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (flatten_count [[(1 : Int), (2 : Int)], [(3 : Int)], [(4 : Int), (5 : Int), (6 : Int)]])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (indexed_sum [(10 : Int), (20 : Int), (30 : Int)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg (heads_and_tails'rn [[(10 : Int), (1 : Int), (2 : Int), (3 : Int)], [(20 : Int), (4 : Int)]])]
      let _ ← pyPrintIO [pyPrintArg (scalar_defaults'rn ["a", "a", "b"])]
      let _ ←
        pyPrintIO
            [pyPrintArg (flatten_count'rn [[(1 : Int), (2 : Int)], [(3 : Int)], [(4 : Int), (5 : Int), (6 : Int)]])]
      let _ ← pyPrintIO [pyPrintArg (indexed_sum'rn [(10 : Int), (20 : Int), (30 : Int)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
