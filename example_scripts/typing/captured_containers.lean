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
Containers built in one scope and captured by a nested `def`.

Lambda lifting turns each capture into a real parameter, and Lean will not infer a `def`'s parameter
types from its body — so an un-inferred capture becomes `PyGetItem ?m …` and instance resolution
gets stuck. Each local below is only pinned down by a *later* statement, not by its initialiser.
-/
-- `graph` starts as `{}`; its key/value types come from the loop that fills it, and the loop target
-- is a TUPLE (`for a, b in pairs`) — which the inference used to skip entirely.
private def _pick'first_one := fun (pairs : List (List Int)) ↦ fun (graph : Std.HashMap Int Int) ↦
  Id.run
    (do
      for u in (PastaLean.pyIter (PastaLean.pyKeys graph)) do
        if h_1 : graph⦋u⦌ = (1 : Int) then 
          return u
        else
          let _ := ()
      let __py_ret_1 := pairs⦋(0 : Int)⦌⦋(0 : Int)⦌
      return __py_ret_1)

attribute [simp, taste_ingr] _pick'first_one

def pick := fun (pairs : List (List Int)) ↦
  Id.run
    (do
      let mut graph : Std.HashMap Int Int := Std.HashMap.ofList []
      for _pair_1 in (PastaLean.pyIter pairs) do
        let a := PastaLean.pyListGetItem _pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem _pair_1 (1 : Int)
        graph := PastaLean.pySetItem graph a b
      let __py_ret_1 := _pick'first_one pairs graph
      return __py_ret_1)

attribute [simp, taste_ingr] pick

private def _pick'first_one'rn := fun (pairs : List (List Int)) ↦ fun (graph : Std.HashMap Int Int) ↦
  Id.run
    (do
      for u in (PastaLean.pyIter (PastaLean.pyKeys graph)) do
        if h_1 : graph⦋u⦌ == (1 : Int) then 
          return u
        else
          let _ := ()
      let __py_ret_1 := pairs⦋(0 : Int)⦌⦋(0 : Int)⦌
      return __py_ret_1)

def pick'rn := fun (pairs : List (List Int)) ↦
  Id.run
    (do
      let mut graph : Std.HashMap Int Int := Std.HashMap.ofList []
      for _pair_1 in (PastaLean.pyIter pairs) do
        let a := PastaLean.pyListGetItem _pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem _pair_1 (1 : Int)
        graph := PastaLean.pySetItem graph a b
      let __py_ret_1 := _pick'first_one'rn pairs graph
      return __py_ret_1)

-- `seen` is refined by `+=` through a subscript, and `buckets` by `.append` through a subscript.
private def _tally'score := fun (seen : Std.HashMap String Int) ↦ fun (buckets : Std.HashMap Int (List String)) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for w in (PastaLean.pyIter (PastaLean.pyKeys seen)) do
        total := total +ₚ (seen⦋w⦌ +ₚ PastaLean.pyLen buckets⦋PastaLean.pyLen w⦌)
      return total)

attribute [simp, taste_ingr] _tally'score

def tally := fun (words : List String) ↦
  Id.run
    (do
      let mut seen : Std.HashMap String Int := Std.HashMap.ofList []
      let mut buckets : Std.HashMap Int (List String) := Std.HashMap.ofList []
      for w in (PastaLean.pyIter words) do
        seen := PastaLean.pySetItem seen w (PastaLean.pyGetD seen w (0 : Int) +ₚ (1 : Int))
        buckets := PastaLean.pySetItem buckets (PastaLean.pyLen w) []
      for w in (PastaLean.pyIter words) do
        buckets := PastaLean.pySetItem buckets (PastaLean.pyLen w) (PastaLean.pyAppend buckets⦋PastaLean.pyLen w⦌ w)
      let __py_ret_1 := _tally'score seen buckets
      return __py_ret_1)

attribute [simp, taste_ingr] tally

private def _tally'score'rn := fun (seen : Std.HashMap String Int) ↦ fun (buckets : Std.HashMap Int (List String)) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for w in (PastaLean.pyIter (PastaLean.pyKeys seen)) do
        total := total +ₚ (seen⦋w⦌ +ₚ PastaLean.pyLen buckets⦋PastaLean.pyLen w⦌)
      return total)

def tally'rn := fun (words : List String) ↦
  Id.run
    (do
      let mut seen : Std.HashMap String Int := Std.HashMap.ofList []
      let mut buckets : Std.HashMap Int (List String) := Std.HashMap.ofList []
      for w in (PastaLean.pyIter words) do
        seen := PastaLean.pySetItem seen w (PastaLean.pyGetD seen w (0 : Int) +ₚ (1 : Int))
        buckets := PastaLean.pySetItem buckets (PastaLean.pyLen w) []
      for w in (PastaLean.pyIter words) do
        buckets := PastaLean.pySetItem buckets (PastaLean.pyLen w) (PastaLean.pyAppend buckets⦋PastaLean.pyLen w⦌ w)
      let __py_ret_1 := _tally'score'rn seen buckets
      return __py_ret_1)

-- `defaultdict`/`Counter` are backed by `PyDefaultDict`, NOT the plain dict a `dict[_,_]`
-- annotation emits — so a captured one needs that exact type, not merely *a* type. `todo` is a list
-- of pairs, and `i, j = todo[k]` reads a TUPLE out of it (not a list, despite the subscript).
private def _walk'total := fun (graph : Libraries.collections.PyDefaultDict Int (List Int)) ↦
  fun (seen : Libraries.collections.PyDefaultDict Int Int) ↦ fun (todo : List (Int × Int)) ↦
  Id.run
    (do
      let mut acc : Int := (0 : Int)
      for k in (PastaLean.pyRange (PastaLean.pyLen todo)) do
        let __unpack_value_1 := todo⦋k⦌
        let __unpack_pair_1 := __unpack_value_1
        let mut i := Prod.fst __unpack_pair_1
        let mut j := Prod.snd __unpack_pair_1
        acc := acc +ₚ (PastaLean.pyLen graph⦋i⦌ +ₚ seen⦋i⦌ +ₚ j)
      return acc)

attribute [simp, taste_ingr] _walk'total

def walk := fun (pairs : List (List Int)) ↦
  Id.run
    (do
      let mut graph : Libraries.collections.PyDefaultDict Int (List Int) := Libraries.collections.pyDefaultDictList
      let mut seen : Libraries.collections.PyDefaultDict Int Int := Libraries.collections.pyCounterEmpty
      let mut todo : List (Int × Int) := []
      for _pair_1 in (PastaLean.pyIter pairs) do
        let a := PastaLean.pyListGetItem _pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem _pair_1 (1 : Int)
        graph := PastaLean.pySetItem graph a (PastaLean.pyAppend graph⦋a⦌ b)
        seen := PastaLean.pySetItem seen a (seen⦋a⦌ +ₚ (1 : Int))
        todo := PastaLean.pyAppend todo (a, b)
      let __py_ret_1 := _walk'total graph seen todo
      return __py_ret_1)

attribute [simp, taste_ingr] walk

private def _walk'total'rn := fun (graph : Libraries.collections.PyDefaultDict Int (List Int)) ↦
  fun (seen : Libraries.collections.PyDefaultDict Int Int) ↦ fun (todo : List (Int × Int)) ↦
  Id.run
    (do
      let mut acc : Int := (0 : Int)
      for k in (PastaLean.pyRange (PastaLean.pyLen todo)) do
        let __unpack_value_1 := todo⦋k⦌
        let __unpack_pair_1 := __unpack_value_1
        let mut i := Prod.fst __unpack_pair_1
        let mut j := Prod.snd __unpack_pair_1
        acc := acc +ₚ (PastaLean.pyLen graph⦋i⦌ +ₚ seen⦋i⦌ +ₚ j)
      return acc)

def walk'rn := fun (pairs : List (List Int)) ↦
  Id.run
    (do
      let mut graph : Libraries.collections.PyDefaultDict Int (List Int) := Libraries.collections.pyDefaultDictList
      let mut seen : Libraries.collections.PyDefaultDict Int Int := Libraries.collections.pyCounterEmpty
      let mut todo : List (Int × Int) := []
      for _pair_1 in (PastaLean.pyIter pairs) do
        let a := PastaLean.pyListGetItem _pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem _pair_1 (1 : Int)
        graph := PastaLean.pySetItem graph a (PastaLean.pyAppend graph⦋a⦌ b)
        seen := PastaLean.pySetItem seen a (seen⦋a⦌ +ₚ (1 : Int))
        todo := PastaLean.pyAppend todo (a, b)
      let __py_ret_1 := _walk'total'rn graph seen todo
      return __py_ret_1)

-- A capturing helper passed as a VALUE (`key=`), not called directly. Lifting it leaves a partial
-- application, so the wrapper lambda needs its parameter TYPED — an untyped binder is exactly what
-- an inference-hungry callback cannot resolve.
private def _ranked'score := fun (x : Int) ↦ fun (weights : List Int) ↦ x *ₚ weights⦋x %ₚ PastaLean.pyLen weights⦌

attribute [simp, taste_ingr] _ranked'score

def ranked := fun (items : List Int) ↦ fun (weights : List Int) ↦
  PastaLean.pySortBy (fun (x : Int) ↦ _ranked'score x weights) false items

attribute [simp, taste_ingr] ranked

private def _ranked'score'rn := fun (x : Int) ↦ fun (weights : List Int) ↦ x *ₚ weights⦋x %ₚ PastaLean.pyLen weights⦌

def ranked'rn := fun (items : List Int) ↦ fun (weights : List Int) ↦
  PastaLean.pySortBy (fun (x : Int) ↦ _ranked'score'rn x weights) false items

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (pick [[(1 : Int), (1 : Int)], [(2 : Int), (3 : Int)]])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (tally ["ab", "ab", "c"])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (walk [[(1 : Int), (2 : Int)], [(1 : Int), (3 : Int)]])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (ranked [(1 : Int), (2 : Int), (3 : Int)] [(10 : Int), (1 : Int)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (pick'rn [[(1 : Int), (1 : Int)], [(2 : Int), (3 : Int)]])]
      let _ ← pyPrintIO [pyPrintArg (tally'rn ["ab", "ab", "c"])]
      let _ ← pyPrintIO [pyPrintArg (walk'rn [[(1 : Int), (2 : Int)], [(1 : Int), (3 : Int)]])]
      let _ ← pyPrintIO [pyPrintArg (ranked'rn [(1 : Int), (2 : Int), (3 : Int)] [(10 : Int), (1 : Int)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()