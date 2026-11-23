import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 800000

def maxWidthOfVerticalArea := fun (points : List (List Int)) ↦
  Id.run
    (do
      let mut points := points
      points := PastaLean.pySort points
      let __py_ret_1 :=
        PastaLean.pyMax
          ((PastaLean.pyIter (Libraries.itertools.pyPairwise points)).map fun _pair_1 =>
            let a := Prod.fst _pair_1;
            let b := Prod.snd _pair_1;
            b⦋(0 : Int)⦌ -ₚ a⦋(0 : Int)⦌)
      return __py_ret_1)

attribute [simp, taste_ingr] maxWidthOfVerticalArea

def maxWidthOfVerticalArea'rn := fun (points : List (List Int)) ↦
  Id.run
    (do
      let mut points := points
      points := PastaLean.pySort points
      let __py_ret_1 :=
        PastaLean.pyMax
          ((PastaLean.pyIter (Libraries.itertools.pyPairwise points)).map fun _pair_1 =>
            let a := Prod.fst _pair_1;
            let b := Prod.snd _pair_1;
            b⦋(0 : Int)⦌ -ₚ a⦋(0 : Int)⦌)
      return __py_ret_1)
