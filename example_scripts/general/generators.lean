import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def squares := fun (n : Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- A generator: `yield` in the body. PastaLean materialises it to a `List Int` (each `yield`
      -- becomes an append), so `list(...)`, `sum(...)`, `for`, and comprehensions consume it directly
      -- via the `PyIterable` protocol.
      for i in (PastaLean.pyRange n) do
        __gen'acc := PastaLean.pyAppend __gen'acc (i *ₚ i)
      return __gen'acc)

attribute [simp, taste_ingr] squares

def squares'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- A generator: `yield` in the body. PastaLean materialises it to a `List Int` (each `yield`
      -- becomes an append), so `list(...)`, `sum(...)`, `for`, and comprehensions consume it directly
      -- via the `PyIterable` protocol.
      for i in (PastaLean.pyRange n) do
        __gen'acc := PastaLean.pyAppend __gen'acc (i *ₚ i)
      return __gen'acc)

def evens_with_tag := fun (xs : List Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- Conditional yields plus a trailing yield.
      for x in (PastaLean.pyIter xs) do
        if h_1 : x %ₚ (2 : Int) = (0 : Int) then 
          __gen'acc := PastaLean.pyAppend __gen'acc x
      __gen'acc := PastaLean.pyAppend __gen'acc (-(1 : Int))
      return __gen'acc)

attribute [simp, taste_ingr] evens_with_tag

def evens_with_tag'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- Conditional yields plus a trailing yield.
      for x in (PastaLean.pyIter xs) do
        if h_1 : x %ₚ (2 : Int) == (0 : Int) then 
          __gen'acc := PastaLean.pyAppend __gen'acc x
      __gen'acc := PastaLean.pyAppend __gen'acc (-(1 : Int))
      return __gen'acc)

def chained := fun (a : List Int) ↦ fun (b : List Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- `yield from` delegates to a sub-iterable (extend); mixes with a plain `yield`.
      __gen'acc := PastaLean.pyExtend __gen'acc a
      __gen'acc := PastaLean.pyExtend __gen'acc b
      __gen'acc := PastaLean.pyAppend __gen'acc (99 : Int)
      return __gen'acc)

attribute [simp, taste_ingr] chained

def chained'rn := fun (a : List Int) ↦ fun (b : List Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- `yield from` delegates to a sub-iterable (extend); mixes with a plain `yield`.
      __gen'acc := PastaLean.pyExtend __gen'acc a
      __gen'acc := PastaLean.pyExtend __gen'acc b
      __gen'acc := PastaLean.pyAppend __gen'acc (99 : Int)
      return __gen'acc)

def first_three := fun (n : Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- A generator `return` just *stops* iteration — the values yielded so far are the output.
      let mut i : Int := (0 : Int)
      while (i < n) do
        __gen'acc := PastaLean.pyAppend __gen'acc i
        i := i +ₚ (1 : Int)
        if h_1 : i = (3 : Int) then 
          return __gen'acc
      return __gen'acc)

attribute [simp, taste_ingr] first_three

def first_three'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- A generator `return` just *stops* iteration — the values yielded so far are the output.
      let mut i : Int := (0 : Int)
      while (i < n) do
        __gen'acc := PastaLean.pyAppend __gen'acc i
        i := i +ₚ (1 : Int)
        if h_1 : i == (3 : Int) then 
          return __gen'acc
      return __gen'acc)

partial def subsets : List Int → Int → List (List Int) := fun (nums : List Int) ↦ fun (start : Int) ↦
  Id.run
    (do
      let mut __gen'acc : List (List Int) := []
      -- A RECURSIVE generator (backtracking): `yield []` then recurse. The materialised accumulator is
      -- typed by TypeInfer (run *after* generator lowering), so `[nums[i]] + tail` stays list-concat —
      -- without that the empty-list seed defaults the element type wrong under recursion.
      __gen'acc := PastaLean.pyAppend __gen'acc []
      for i in (PastaLean.pyRange (PastaLean.pyLen nums) start) do
        for tail in (PastaLean.pyIter (subsets nums (i +ₚ (1 : Int)))) do
          __gen'acc := PastaLean.pyAppend __gen'acc ([nums⦋i⦌] +ₚ tail)
      return __gen'acc)

partial def subsets'rn : List Int → Int → List (List Int) := fun (nums : List Int) ↦ fun (start : Int) ↦
  Id.run
    (do
      let mut __gen'acc : List (List Int) := []
      -- A RECURSIVE generator (backtracking): `yield []` then recurse. The materialised accumulator is
      -- typed by TypeInfer (run *after* generator lowering), so `[nums[i]] + tail` stays list-concat —
      -- without that the empty-list seed defaults the element type wrong under recursion.
      __gen'acc := PastaLean.pyAppend __gen'acc []
      for i in (PastaLean.pyRange (PastaLean.pyLen nums) start) do
        for tail in (PastaLean.pyIter (subsets'rn nums (i +ₚ (1 : Int)))) do
          __gen'acc := PastaLean.pyAppend __gen'acc ([nums⦋i⦌] +ₚ tail)
      return __gen'acc)

def evens := fun (xs : List Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      for x in (PastaLean.pyIter xs) do
        if h_1 : x %ₚ (2 : Int) = (0 : Int) then 
          __gen'acc := PastaLean.pyAppend __gen'acc x
      return __gen'acc)

attribute [simp, taste_ingr] evens

def evens'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      for x in (PastaLean.pyIter xs) do
        if h_1 : x %ₚ (2 : Int) == (0 : Int) then 
          __gen'acc := PastaLean.pyAppend __gen'acc x
      return __gen'acc)

def doubled := fun (xs : List Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      for x in (PastaLean.pyIter xs) do
        __gen'acc := PastaLean.pyAppend __gen'acc (x *ₚ (2 : Int))
      return __gen'acc)

attribute [simp, taste_ingr] doubled

def doubled'rn := fun (xs : List Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      for x in (PastaLean.pyIter xs) do
        __gen'acc := PastaLean.pyAppend __gen'acc (x *ₚ (2 : Int))
      return __gen'acc)

def fib := fun (n : Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- Stateful generator: the `a, b = b, a + b` swap threads through the materialised loop.
      let mut a : Int := (0 : Int)
      let mut b : Int := (1 : Int)
      for _ in (PastaLean.pyRange n) do
        __gen'acc := PastaLean.pyAppend __gen'acc a
        let p'_unpack_value_1 := (b, a +ₚ b)
        let p'_unpack_pair_1 := p'_unpack_value_1
        a := Prod.fst p'_unpack_pair_1
        b := Prod.snd p'_unpack_pair_1
      return __gen'acc)

attribute [simp, taste_ingr] fib

def fib'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut __gen'acc : List Int := []
      -- Stateful generator: the `a, b = b, a + b` swap threads through the materialised loop.
      let mut a : Int := (0 : Int)
      let mut b : Int := (1 : Int)
      for _ in (PastaLean.pyRange n) do
        __gen'acc := PastaLean.pyAppend __gen'acc a
        let p'_unpack_value_1 := (b, a +ₚ b)
        let p'_unpack_pair_1 := p'_unpack_value_1
        a := Prod.fst p'_unpack_pair_1
        b := Prod.snd p'_unpack_pair_1
      return __gen'acc)

def use_generators :=
  let a := (PastaLean.pyList (squares (4 : Int)) : List Int)
  let b := (PastaLean.pyList (evens_with_tag [(1 : Int), (2 : Int), (3 : Int), (4 : Int)]) : List Int)
  let c := (PastaLean.pyList (chained [(1 : Int), (2 : Int)] [(3 : Int), (4 : Int)]) : List Int)
  let d := ((PastaLean.pyIter (squares (3 : Int))).map fun (x : Int) => x +ₚ (1 : Int) : List Int)
  let e := (PastaLean.pyList (first_three (10 : Int)) : List Int)
  let f := (PastaLean.pyList (subsets [(1 : Int), (2 : Int), (3 : Int)] (0 : Int)) : List (List Int))
  let g :=
    (PastaLean.pyList (doubled (evens [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)])) : List Int)
  let h := (PastaLean.pyList (fib (8 : Int)) : List Int)
  PastaLean.pySum a +ₚ PastaLean.pyLen b +ₚ PastaLean.pyLen c +ₚ PastaLean.pySum d +ₚ PastaLean.pyLen e +ₚ
        PastaLean.pyLen f +ₚ
      PastaLean.pySum g +ₚ
    PastaLean.pySum h

attribute [simp, taste_ingr] use_generators

def use_generators'rn :=
  let a := (PastaLean.pyList (squares'rn (4 : Int)) : List Int)
  let b := (PastaLean.pyList (evens_with_tag'rn [(1 : Int), (2 : Int), (3 : Int), (4 : Int)]) : List Int)
  let c := (PastaLean.pyList (chained'rn [(1 : Int), (2 : Int)] [(3 : Int), (4 : Int)]) : List Int)
  let d := (((PastaLean.pyIter (squares'rn (3 : Int))).map fun (x : Int) => x +ₚ (1 : Int)) |>.toArray : Array Int)
  let e := (PastaLean.pyList (first_three'rn (10 : Int)) : List Int)
  let f := (PastaLean.pyList (subsets'rn [(1 : Int), (2 : Int), (3 : Int)] (0 : Int)) : List (List Int))
  let g :=
    (PastaLean.pyList (doubled'rn (evens'rn [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)])) :
      List Int)
  let h := (PastaLean.pyList (fib'rn (8 : Int)) : List Int)
  PastaLean.pySum a +ₚ PastaLean.pyLen b +ₚ PastaLean.pyLen c +ₚ PastaLean.pySum d +ₚ PastaLean.pyLen e +ₚ
        PastaLean.pyLen f +ₚ
      PastaLean.pySum g +ₚ
    PastaLean.pySum h

end PastaLean.User.Root
