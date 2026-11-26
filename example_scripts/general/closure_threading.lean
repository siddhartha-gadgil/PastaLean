import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Regression tests for nested-def state threading (ClosureConvert).
-- Each function exercises a pattern that was a convert/compile failure before the
-- SCC-grouping + cross-helper + mutable-param + comprehension-hoist work.
-- Union-find: `find` (self-recursive, mutates captured `p` via path compression) plus a
-- sibling `union` that CALLS `find`. `union -> find` is a DAG, so they lift as separate
-- threaded helpers and `union`'s `find` calls thread `p` across the boundary.
private partial def _count_components'find := fun (x : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      if h_1 : p⦋x⦌ ≠ x then 
        let p'_unpack_value_1 := _count_components'find p⦋x⦌ p
        let p'_unpack_pair_1 := p'_unpack_value_1
        p := Prod.snd p'_unpack_pair_1
        p := PastaLean.pySetItem p x (Prod.fst p'_unpack_pair_1)
      let p'_ret_1 := (p⦋x⦌, p)
      return p'_ret_1)

private def _count_components'union := fun (a : Int) ↦ fun (b : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      let p'_unpack_value_1 := _count_components'find a p
      let p'_unpack_pair_1 := p'_unpack_value_1
      p := Prod.snd p'_unpack_pair_1
      let mut pa : Int := Prod.fst p'_unpack_pair_1
      let p'_unpack_value_2 := _count_components'find b p
      let p'_unpack_pair_2 := p'_unpack_value_2
      p := Prod.snd p'_unpack_pair_2
      let mut pb : Int := Prod.fst p'_unpack_pair_2
      if h_1 : pa ≠ pb then 
        p := PastaLean.pySetItem p pa pb
      return p)

attribute [simp, taste_ingr] _count_components'union

def count_components := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut p : List Int := PastaLean.pyList (PastaLean.pyRange n)
      for p'_pair_1 in (PastaLean.pyIter edges) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        p := _count_components'union a b p
      let mut p'_cc1 := []
      for i in (PastaLean.pyRange n) do
        let p'_unpack_value_1 := _count_components'find i p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t2 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        p'_cc1 := PastaLean.pyAppend p'_cc1 p'_thread_t2
      let mut p'_cv1 := PastaLean.pySet p'_cc1
      let p'_ret_1 := PastaLean.pyLen p'_cv1
      return p'_ret_1)

attribute [simp, taste_ingr] count_components

private partial def _count_components'find'rn := fun (x : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      if h_1 : p⦋x⦌ != x then 
        let p'_unpack_value_1 := _count_components'find'rn p⦋x⦌ p
        let p'_unpack_pair_1 := p'_unpack_value_1
        p := Prod.snd p'_unpack_pair_1
        p := PastaLean.pySetItem p x (Prod.fst p'_unpack_pair_1)
      let p'_ret_1 := (p⦋x⦌, p)
      return p'_ret_1)

private def _count_components'union'rn := fun (a : Int) ↦ fun (b : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      let p'_unpack_value_1 := _count_components'find'rn a p
      let p'_unpack_pair_1 := p'_unpack_value_1
      p := Prod.snd p'_unpack_pair_1
      let mut pa : Int := Prod.fst p'_unpack_pair_1
      let p'_unpack_value_2 := _count_components'find'rn b p
      let p'_unpack_pair_2 := p'_unpack_value_2
      p := Prod.snd p'_unpack_pair_2
      let mut pb : Int := Prod.fst p'_unpack_pair_2
      if h_1 : pa != pb then 
        p := PastaLean.pySetItem p pa pb
      return p)

def count_components'rn := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut p : List Int := PastaLean.pyList (PastaLean.pyRange n)
      for p'_pair_1 in (PastaLean.pyIter edges) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        p := _count_components'union'rn a b p
      let mut p'_cc1 := []
      for i in (PastaLean.pyRange n) do
        let p'_unpack_value_1 := _count_components'find'rn i p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t2 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        p'_cc1 := PastaLean.pyAppend p'_cc1 p'_thread_t2
      let mut p'_cv1 := PastaLean.pySet p'_cc1
      let p'_ret_1 := PastaLean.pyLen p'_cv1
      return p'_ret_1)

-- `while find(a) != find(b):` — a threaded call in a `while` TEST (re-evaluated each
-- iteration). Lowers to `while True: <thread test>; if not test: break; <body>`.
private partial def _connect_until_joined'find := fun (x : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      if h_1 : p⦋x⦌ ≠ x then 
        let p'_unpack_value_1 := _connect_until_joined'find p⦋x⦌ p
        let p'_unpack_pair_1 := p'_unpack_value_1
        p := Prod.snd p'_unpack_pair_1
        p := PastaLean.pySetItem p x (Prod.fst p'_unpack_pair_1)
      let p'_ret_1 := (p⦋x⦌, p)
      return p'_ret_1)

def connect_until_joined := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut p : List Int := PastaLean.pyList (PastaLean.pyRange n)
      let mut steps : Int := (0 : Int)
      let mut i : Int := (0 : Int)
      while (Bool.true) do
        let p'_unpack_value_1 := _connect_until_joined'find (0 : Int) p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t1 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        let p'_unpack_value_2 := _connect_until_joined'find (n -ₚ (1 : Int)) p
        let p'_unpack_pair_2 := p'_unpack_value_2
        let mut p'_thread_t2 := Prod.fst p'_unpack_pair_2
        p := Prod.snd p'_unpack_pair_2
        if h_1 : ¬(p'_thread_t1 ≠ p'_thread_t2 ∧ i < PastaLean.pyLen edges) then 
          break
        let p'_unpack_value_3 := edges⦋i⦌
        let p'_unpack_pair_3 := p'_unpack_value_3
        let mut a : Int := PastaLean.pyListGetItem p'_unpack_pair_3 (0 : Int)
        let mut b : Int := PastaLean.pyListGetItem p'_unpack_pair_3 (1 : Int)
        let p'_unpack_value_4 := _connect_until_joined'find a p
        let p'_unpack_pair_4 := p'_unpack_value_4
        let mut p'_thread_t3 := Prod.fst p'_unpack_pair_4
        p := Prod.snd p'_unpack_pair_4
        let p'_unpack_value_5 := _connect_until_joined'find b p
        let p'_unpack_pair_5 := p'_unpack_value_5
        p := Prod.snd p'_unpack_pair_5
        p := PastaLean.pySetItem p p'_thread_t3 (Prod.fst p'_unpack_pair_5)
        steps := steps +ₚ (1 : Int)
        i := i +ₚ (1 : Int)
      return steps)

attribute [simp, taste_ingr] connect_until_joined

private partial def _connect_until_joined'find'rn := fun (x : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      if h_1 : p⦋x⦌ != x then 
        let p'_unpack_value_1 := _connect_until_joined'find'rn p⦋x⦌ p
        let p'_unpack_pair_1 := p'_unpack_value_1
        p := Prod.snd p'_unpack_pair_1
        p := PastaLean.pySetItem p x (Prod.fst p'_unpack_pair_1)
      let p'_ret_1 := (p⦋x⦌, p)
      return p'_ret_1)

def connect_until_joined'rn := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut p : List Int := PastaLean.pyList (PastaLean.pyRange n)
      let mut steps : Int := (0 : Int)
      let mut i : Int := (0 : Int)
      while (Bool.true) do
        let p'_unpack_value_1 := _connect_until_joined'find'rn (0 : Int) p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t1 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        let p'_unpack_value_2 := _connect_until_joined'find'rn (n -ₚ (1 : Int)) p
        let p'_unpack_pair_2 := p'_unpack_value_2
        let mut p'_thread_t2 := Prod.fst p'_unpack_pair_2
        p := Prod.snd p'_unpack_pair_2
        if h_1 : !(p'_thread_t1 != p'_thread_t2 && decide (i < PastaLean.pyLen edges)) then 
          break
        let p'_unpack_value_3 := edges⦋i⦌
        let p'_unpack_pair_3 := p'_unpack_value_3
        let mut a : Int := PastaLean.pyListGetItem p'_unpack_pair_3 (0 : Int)
        let mut b : Int := PastaLean.pyListGetItem p'_unpack_pair_3 (1 : Int)
        let p'_unpack_value_4 := _connect_until_joined'find'rn a p
        let p'_unpack_pair_4 := p'_unpack_value_4
        let mut p'_thread_t3 := Prod.fst p'_unpack_pair_4
        p := Prod.snd p'_unpack_pair_4
        let p'_unpack_value_5 := _connect_until_joined'find'rn b p
        let p'_unpack_pair_5 := p'_unpack_value_5
        p := Prod.snd p'_unpack_pair_5
        p := PastaLean.pySetItem p p'_thread_t3 (Prod.fst p'_unpack_pair_5)
        steps := steps +ₚ (1 : Int)
        i := i +ₚ (1 : Int)
      return steps)

-- Mutable PARAMETER threading: `push` mutates its `pq` argument in place (heappush /
-- heappop) and its caller must see the change — the arg is rebound at the call site.
private def _k_smallest_after_pushes'push := fun (pq : List Int) ↦ fun (x : Int) ↦ fun (k : Int) ↦
  Id.run
    (do
      let mut pq := pq
      pq := Libraries.heapq.pyHeappush pq (-x)
      if h_1 : PastaLean.pyLen pq > k then 
        pq := Libraries.heapq.pyHeappopRest pq
      return pq)

attribute [simp, taste_ingr] _k_smallest_after_pushes'push

def k_smallest_after_pushes := fun (nums : List Int) ↦ fun (k : Int) ↦
  Id.run
    (do
      let mut heap : List Int := []
      for v in (PastaLean.pyIter nums) do
        heap := _k_smallest_after_pushes'push heap v k
      let p'_ret_1 := PastaLean.pySort ((PastaLean.pyIter heap).map fun (x : Int) => -x)
      return p'_ret_1)

attribute [simp, taste_ingr] k_smallest_after_pushes

private def _k_smallest_after_pushes'push'rn := fun (pq : List Int) ↦ fun (x : Int) ↦ fun (k : Int) ↦
  Id.run
    (do
      let mut pq := pq
      pq := Libraries.heapq.pyHeappush pq (-x)
      if h_1 : PastaLean.pyLen pq > k then 
        pq := Libraries.heapq.pyHeappopRest pq
      return pq)

def k_smallest_after_pushes'rn := fun (nums : List Int) ↦ fun (k : Int) ↦
  Id.run
    (do
      let mut heap : List Int := []
      for v in (PastaLean.pyIter nums) do
        heap := _k_smallest_after_pushes'push'rn heap v k
      let p'_ret_1 := PastaLean.pySort ((PastaLean.pyIter heap).map fun (x : Int) => -x)
      return p'_ret_1)

-- A mutated parameter via a tuple-of-subscripts target (`arr[i], arr[j] = arr[j], arr[i]`).
private def _selection_sort'swap := fun (a : List Int) ↦ fun (i : Int) ↦ fun (j : Int) ↦
  Id.run
    (do
      let mut a := a
      let p'_unpack_value_1 := (a⦋j⦌, a⦋i⦌)
      let p'_unpack_pair_1 := p'_unpack_value_1
      a := PastaLean.pySetItem a i (Prod.fst p'_unpack_pair_1)
      a := PastaLean.pySetItem a j (Prod.snd p'_unpack_pair_1)
      return a)

attribute [simp, taste_ingr] _selection_sort'swap

def selection_sort := fun (arr : List Int) ↦
  Id.run
    (do
      let mut arr := arr
      for i in (PastaLean.pyRange (PastaLean.pyLen arr)) do
        let mut m : Int := i
        for j in (PastaLean.pyRange (PastaLean.pyLen arr) (i +ₚ (1 : Int))) do
          if h_1 : arr⦋j⦌ < arr⦋m⦌ then 
            m := j
        arr := _selection_sort'swap arr i m
      return arr)

attribute [simp, taste_ingr] selection_sort

private def _selection_sort'swap'rn := fun (a : List Int) ↦ fun (i : Int) ↦ fun (j : Int) ↦
  Id.run
    (do
      let mut a := a
      let p'_unpack_value_1 := (a⦋j⦌, a⦋i⦌)
      let p'_unpack_pair_1 := p'_unpack_value_1
      a := PastaLean.pySetItem a i (Prod.fst p'_unpack_pair_1)
      a := PastaLean.pySetItem a j (Prod.snd p'_unpack_pair_1)
      return a)

def selection_sort'rn := fun (arr : List Int) ↦
  Id.run
    (do
      let mut arr := arr
      for i in (PastaLean.pyRange (PastaLean.pyLen arr)) do
        let mut m : Int := i
        for j in (PastaLean.pyRange (PastaLean.pyLen arr) (i +ₚ (1 : Int))) do
          if h_1 : arr⦋j⦌ < arr⦋m⦌ then 
            m := j
        arr := _selection_sort'swap'rn arr i m
      return arr)

-- Short-circuited threaded call in an accumulator comprehension: `dfs` (mutating captured
-- `color`) runs only when `color[i] == 0` — the `or` is lowered to an `if` per item so the
-- mutation stays behind the short-circuit.
private partial def _is_bipartite'dfs := fun (i : Int) ↦ fun (c : Int) ↦ fun (graph : List (List Int)) ↦
  fun (color : List Int) ↦
  Id.run
    (do
      let mut color := color
      color := PastaLean.pySetItem color i c
      for j in (PastaLean.pyIter graph⦋i⦌) do
        if h_1 : color⦋j⦌ = c then 
          let p'_ret_1 := (Bool.false, color)
          return p'_ret_1
        let p'_unpack_value_1 := _is_bipartite'dfs j (-c) graph color
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t1 := Prod.fst p'_unpack_pair_1
        color := Prod.snd p'_unpack_pair_1
        if h_2 : color⦋j⦌ = (0 : Int) ∧ ¬PastaLean.pyTruthy p'_thread_t1 = true then 
          let p'_ret_1 := (Bool.false, color)
          return p'_ret_1
      let p'_ret_1 := (Bool.true, color)
      return p'_ret_1)

def is_bipartite := fun (n : Int) ↦ fun (graph : List (List Int)) ↦
  Id.run
    (do
      let mut color : List Int := PastaLean.pyListRepeat [(0 : Int)] n
      let mut p'_cc2 := []
      for i in (PastaLean.pyRange n) do
        if h_1 : color⦋i⦌ ≠ (0 : Int) then 
          p'_cc2 := PastaLean.pyAppend p'_cc2 (color⦋i⦌ != (0 : Int))
        else
          let p'_unpack_value_1 := _is_bipartite'dfs i (1 : Int) graph color
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut p'_thread_t3 := Prod.fst p'_unpack_pair_1
          color := Prod.snd p'_unpack_pair_1
          p'_cc2 := PastaLean.pyAppend p'_cc2 p'_thread_t3
      let p'_ret_1 := PastaLean.pyAll p'_cc2
      return p'_ret_1)

attribute [simp, taste_ingr] is_bipartite

private partial def _is_bipartite'dfs'rn := fun (i : Int) ↦ fun (c : Int) ↦ fun (graph : List (List Int)) ↦
  fun (color : List Int) ↦
  Id.run
    (do
      let mut color := color
      color := PastaLean.pySetItem color i c
      for j in (PastaLean.pyIter graph⦋i⦌) do
        if h_1 : color⦋j⦌ == c then 
          let p'_ret_1 := (Bool.false, color)
          return p'_ret_1
        let p'_unpack_value_1 := _is_bipartite'dfs'rn j (-c) graph color
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t1 := Prod.fst p'_unpack_pair_1
        color := Prod.snd p'_unpack_pair_1
        if h_2 : color⦋j⦌ == (0 : Int) && !PastaLean.pyTruthy p'_thread_t1 then 
          let p'_ret_1 := (Bool.false, color)
          return p'_ret_1
      let p'_ret_1 := (Bool.true, color)
      return p'_ret_1)

def is_bipartite'rn := fun (n : Int) ↦ fun (graph : List (List Int)) ↦
  Id.run
    (do
      let mut color : List Int := PastaLean.pyListRepeat [(0 : Int)] n
      let mut p'_cc2 := []
      for i in (PastaLean.pyRange n) do
        if h_1 : color⦋i⦌ != (0 : Int) then 
          p'_cc2 := PastaLean.pyAppend p'_cc2 (color⦋i⦌ != (0 : Int))
        else
          let p'_unpack_value_1 := _is_bipartite'dfs'rn i (1 : Int) graph color
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut p'_thread_t3 := Prod.fst p'_unpack_pair_1
          color := Prod.snd p'_unpack_pair_1
          p'_cc2 := PastaLean.pyAppend p'_cc2 p'_thread_t3
      let p'_ret_1 := PastaLean.pyAll p'_cc2
      return p'_ret_1)

-- A nested def that calls a sibling needing a capture the caller never names directly:
-- `evaluate` binds `n`; `outer` calls `check` which reads `n`, so `outer` must forward it.
private def _any_valid_pair'check := fun (i : Int) ↦ fun (j : Int) ↦ fun (s : String) ↦ fun (n : Int) ↦
  if (((0 : Int) ≤ i ∧ i < n) ∧ (0 : Int) ≤ j ∧ j < n) ∧ s⦋i⦌ = s⦋j⦌ then (1 : Int) else (0 : Int)

attribute [simp, taste_ingr] _any_valid_pair'check

private def _any_valid_pair'outer := fun (i : Int) ↦ fun (s : String) ↦ fun (n : Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for j in (PastaLean.pyRange n) do
        if h_1 : PastaLean.pyTruthy (_any_valid_pair'check i j s n) then 
          total := total +ₚ (1 : Int)
      return total)

attribute [simp, taste_ingr] _any_valid_pair'outer

def any_valid_pair := fun (s : String) ↦
  let n := (PastaLean.pyLen s : Int)
  PastaLean.pySum ((PastaLean.pyRange n).map fun (i : Int) => _any_valid_pair'outer i s n)

attribute [simp, taste_ingr] any_valid_pair

private def _any_valid_pair'check'rn := fun (i : Int) ↦ fun (j : Int) ↦ fun (s : String) ↦ fun (n : Int) ↦
  if decide ((0 : Int) ≤ i) && decide (i < n) && (decide ((0 : Int) ≤ j) && decide (j < n)) && s⦋i⦌ == s⦋j⦌ then
    (1 : Int)
  else (0 : Int)

private def _any_valid_pair'outer'rn := fun (i : Int) ↦ fun (s : String) ↦ fun (n : Int) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for j in (PastaLean.pyRange n) do
        if h_1 : PastaLean.pyTruthy (_any_valid_pair'check'rn i j s n) then 
          total := total +ₚ (1 : Int)
      return total)

def any_valid_pair'rn := fun (s : String) ↦
  let n := (PastaLean.pyLen s : Int)
  PastaLean.pySum ((PastaLean.pyRange n).map fun (i : Int) => _any_valid_pair'outer'rn i s n)

-- False-positive guard: a `lambda` sort key and a threaded `find` call live in the SAME
-- statement, but `find` is NOT inside the lambda, so it must still thread.
private partial def _sort_then_union'find := fun (x : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      if h_1 : p⦋x⦌ ≠ x then 
        let p'_unpack_value_1 := _sort_then_union'find p⦋x⦌ p
        let p'_unpack_pair_1 := p'_unpack_value_1
        p := Prod.snd p'_unpack_pair_1
        p := PastaLean.pySetItem p x (Prod.fst p'_unpack_pair_1)
      let p'_ret_1 := (p⦋x⦌, p)
      return p'_ret_1)

def sort_then_union := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut p : List Int := PastaLean.pyList (PastaLean.pyRange n)
      for p'_pair_1 in (PastaLean.pyIter (PastaLean.pySortBy (fun (e : List Int) ↦ e⦋(2 : Int)⦌) false edges)) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        let w := PastaLean.pyListGetItem p'_pair_1 (2 : Int)
        let p'_unpack_value_1 := _sort_then_union'find a p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t1 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        let p'_unpack_value_2 := _sort_then_union'find b p
        let p'_unpack_pair_2 := p'_unpack_value_2
        p := Prod.snd p'_unpack_pair_2
        p := PastaLean.pySetItem p p'_thread_t1 (Prod.fst p'_unpack_pair_2)
      let mut p'_cc2 := []
      for i in (PastaLean.pyRange n) do
        let p'_unpack_value_1 := _sort_then_union'find i p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t3 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        p'_cc2 := PastaLean.pyAppend p'_cc2 p'_thread_t3
      let mut p'_cv2 := PastaLean.pySet p'_cc2
      let p'_ret_1 := PastaLean.pyLen p'_cv2
      return p'_ret_1)

attribute [simp, taste_ingr] sort_then_union

private partial def _sort_then_union'find'rn := fun (x : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      if h_1 : p⦋x⦌ != x then 
        let p'_unpack_value_1 := _sort_then_union'find'rn p⦋x⦌ p
        let p'_unpack_pair_1 := p'_unpack_value_1
        p := Prod.snd p'_unpack_pair_1
        p := PastaLean.pySetItem p x (Prod.fst p'_unpack_pair_1)
      let p'_ret_1 := (p⦋x⦌, p)
      return p'_ret_1)

def sort_then_union'rn := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut p : List Int := PastaLean.pyList (PastaLean.pyRange n)
      for p'_pair_1 in (PastaLean.pyIter (PastaLean.pySortBy (fun (e : List Int) ↦ e⦋(2 : Int)⦌) false edges)) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        let w := PastaLean.pyListGetItem p'_pair_1 (2 : Int)
        let p'_unpack_value_1 := _sort_then_union'find'rn a p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t1 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        let p'_unpack_value_2 := _sort_then_union'find'rn b p
        let p'_unpack_pair_2 := p'_unpack_value_2
        p := Prod.snd p'_unpack_pair_2
        p := PastaLean.pySetItem p p'_thread_t1 (Prod.fst p'_unpack_pair_2)
      let mut p'_cc2 := []
      for i in (PastaLean.pyRange n) do
        let p'_unpack_value_1 := _sort_then_union'find'rn i p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t3 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        p'_cc2 := PastaLean.pyAppend p'_cc2 p'_thread_t3
      let mut p'_cv2 := PastaLean.pySet p'_cc2
      let p'_ret_1 := PastaLean.pyLen p'_cv2
      return p'_ret_1)

-- Threaded call in an `if` TEST comprehension: `if any(hasCycle(v) for v):` hoists the
-- accumulator loop before the `if`.
private partial def _has_any_cycle'hasCycle := fun (u : Int) ↦ fun (graph : List (List Int)) ↦
  fun (state : List Int) ↦
  Id.run
    (do
      let mut state := state
      if h_1 : state⦋u⦌ = (1 : Int) then 
        let p'_ret_1 := (Bool.true, state)
        return p'_ret_1
      if h_2 : state⦋u⦌ = (2 : Int) then 
        let p'_ret_1 := (Bool.false, state)
        return p'_ret_1
      state := PastaLean.pySetItem state u (1 : Int)
      let mut p'_cc1 := []
      for v in (PastaLean.pyIter graph⦋u⦌) do
        let p'_unpack_value_1 := _has_any_cycle'hasCycle v graph state
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t2 := Prod.fst p'_unpack_pair_1
        state := Prod.snd p'_unpack_pair_1
        p'_cc1 := PastaLean.pyAppend p'_cc1 p'_thread_t2
      let mut p'_cv1 := PastaLean.pyStdAny p'_cc1
      if h_3 : PastaLean.pyTruthy p'_cv1 then 
        let p'_ret_1 := (Bool.true, state)
        return p'_ret_1
      state := PastaLean.pySetItem state u (2 : Int)
      let p'_ret_1 := (Bool.false, state)
      return p'_ret_1)

def has_any_cycle := fun (n : Int) ↦ fun (graph : List (List Int)) ↦
  Id.run
    (do
      let mut state : List Int := PastaLean.pyListRepeat [(0 : Int)] n
      let mut p'_cc3 := []
      for u in (PastaLean.pyRange n) do
        if h_1 : state⦋u⦌ = (0 : Int) then 
          let p'_unpack_value_1 := _has_any_cycle'hasCycle u graph state
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut p'_thread_t4 := Prod.fst p'_unpack_pair_1
          state := Prod.snd p'_unpack_pair_1
          p'_cc3 := PastaLean.pyAppend p'_cc3 p'_thread_t4
      let p'_ret_1 := PastaLean.pyStdAny p'_cc3
      return p'_ret_1)

attribute [simp, taste_ingr] has_any_cycle

private partial def _has_any_cycle'hasCycle'rn := fun (u : Int) ↦ fun (graph : List (List Int)) ↦
  fun (state : List Int) ↦
  Id.run
    (do
      let mut state := state
      if h_1 : state⦋u⦌ == (1 : Int) then 
        let p'_ret_1 := (Bool.true, state)
        return p'_ret_1
      if h_2 : state⦋u⦌ == (2 : Int) then 
        let p'_ret_1 := (Bool.false, state)
        return p'_ret_1
      state := PastaLean.pySetItem state u (1 : Int)
      let mut p'_cc1 := []
      for v in (PastaLean.pyIter graph⦋u⦌) do
        let p'_unpack_value_1 := _has_any_cycle'hasCycle'rn v graph state
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t2 := Prod.fst p'_unpack_pair_1
        state := Prod.snd p'_unpack_pair_1
        p'_cc1 := PastaLean.pyAppend p'_cc1 p'_thread_t2
      let mut p'_cv1 := PastaLean.pyStdAny p'_cc1
      if h_3 : PastaLean.pyTruthy p'_cv1 then 
        let p'_ret_1 := (Bool.true, state)
        return p'_ret_1
      state := PastaLean.pySetItem state u (2 : Int)
      let p'_ret_1 := (Bool.false, state)
      return p'_ret_1)

def has_any_cycle'rn := fun (n : Int) ↦ fun (graph : List (List Int)) ↦
  Id.run
    (do
      let mut state : List Int := PastaLean.pyListRepeat [(0 : Int)] n
      let mut p'_cc3 := []
      for u in (PastaLean.pyRange n) do
        if h_1 : state⦋u⦌ == (0 : Int) then 
          let p'_unpack_value_1 := _has_any_cycle'hasCycle'rn u graph state
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut p'_thread_t4 := Prod.fst p'_unpack_pair_1
          state := Prod.snd p'_unpack_pair_1
          p'_cc3 := PastaLean.pyAppend p'_cc3 p'_thread_t4
      let p'_ret_1 := PastaLean.pyStdAny p'_cc3
      return p'_ret_1)

-- Full-slice assignment on a non-name container (`row[:] = ...`): a full slice replaces the
-- whole row, equivalent to a plain subscript assign under value semantics.
def reset_grid := fun (grid : List (List Int)) ↦ fun (m : Int) ↦
  Id.run
    (do
      let mut grid := grid
      for i in (PastaLean.pyRange (PastaLean.pyLen grid)) do
        grid := PastaLean.pySetItem grid i (PastaLean.pyListRepeat [(0 : Int)] m)
      return grid)

attribute [simp, taste_ingr] reset_grid

def reset_grid'rn := fun (grid : List (List Int)) ↦ fun (m : Int) ↦
  Id.run
    (do
      let mut grid := grid
      for i in (PastaLean.pyRange (PastaLean.pyLen grid)) do
        grid := PastaLean.pySetItem grid i (PastaLean.pyListRepeat [(0 : Int)] m)
      return grid)

-- Threaded call in an `IfExp` CONDITION inside a list comprehension: `find` runs only when
-- both endpoints are known (short-circuit `or`), lowered to a per-item guard.
private partial def _query_connected'find := fun (x : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      if h_1 : p⦋x⦌ ≠ x then 
        let p'_unpack_value_1 := _query_connected'find p⦋x⦌ p
        let p'_unpack_pair_1 := p'_unpack_value_1
        p := Prod.snd p'_unpack_pair_1
        p := PastaLean.pySetItem p x (Prod.fst p'_unpack_pair_1)
      let p'_ret_1 := (p⦋x⦌, p)
      return p'_ret_1)

def query_connected := fun (n : Int) ↦ fun (edges : List (List Int)) ↦ fun (queries : List (List Int)) ↦
  Id.run
    (do
      let mut p : List Int := PastaLean.pyList (PastaLean.pyRange n)
      for p'_pair_1 in (PastaLean.pyIter edges) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        let p'_unpack_value_1 := _query_connected'find a p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t1 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        let p'_unpack_value_2 := _query_connected'find b p
        let p'_unpack_pair_2 := p'_unpack_value_2
        p := Prod.snd p'_unpack_pair_2
        p := PastaLean.pySetItem p p'_thread_t1 (Prod.fst p'_unpack_pair_2)
      let mut p'_cc2 := []
      for p'_pair_1 in (PastaLean.pyIter queries) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        let mut p'_cc2cond :=
          if PastaLean.pyTruthy (decide (a < (0 : Int))) then decide (a < (0 : Int)) else decide (b < (0 : Int))
        if h_1 : ¬PastaLean.pyTruthy p'_cc2cond = true then 
          let p'_unpack_value_1 := _query_connected'find a p
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut p'_thread_t3 := Prod.fst p'_unpack_pair_1
          p := Prod.snd p'_unpack_pair_1
          let p'_unpack_value_2 := _query_connected'find b p
          let p'_unpack_pair_2 := p'_unpack_value_2
          let mut p'_thread_t4 := Prod.fst p'_unpack_pair_2
          p := Prod.snd p'_unpack_pair_2
          p'_cc2cond := p'_thread_t3 != p'_thread_t4
        p'_cc2 := PastaLean.pyAppend p'_cc2 (if PastaLean.pyTruthy p'_cc2cond then (0 : Int) else (1 : Int))
      return p'_cc2)

attribute [simp, taste_ingr] query_connected

private partial def _query_connected'find'rn := fun (x : Int) ↦ fun (p : List Int) ↦
  Id.run
    (do
      let mut p := p
      if h_1 : p⦋x⦌ != x then 
        let p'_unpack_value_1 := _query_connected'find'rn p⦋x⦌ p
        let p'_unpack_pair_1 := p'_unpack_value_1
        p := Prod.snd p'_unpack_pair_1
        p := PastaLean.pySetItem p x (Prod.fst p'_unpack_pair_1)
      let p'_ret_1 := (p⦋x⦌, p)
      return p'_ret_1)

def query_connected'rn := fun (n : Int) ↦ fun (edges : List (List Int)) ↦ fun (queries : List (List Int)) ↦
  Id.run
    (do
      let mut p : List Int := PastaLean.pyList (PastaLean.pyRange n)
      for p'_pair_1 in (PastaLean.pyIter edges) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        let p'_unpack_value_1 := _query_connected'find'rn a p
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut p'_thread_t1 := Prod.fst p'_unpack_pair_1
        p := Prod.snd p'_unpack_pair_1
        let p'_unpack_value_2 := _query_connected'find'rn b p
        let p'_unpack_pair_2 := p'_unpack_value_2
        p := Prod.snd p'_unpack_pair_2
        p := PastaLean.pySetItem p p'_thread_t1 (Prod.fst p'_unpack_pair_2)
      let mut p'_cc2 := []
      for p'_pair_1 in (PastaLean.pyIter queries) do
        let a := PastaLean.pyListGetItem p'_pair_1 (0 : Int)
        let b := PastaLean.pyListGetItem p'_pair_1 (1 : Int)
        let mut p'_cc2cond :=
          if PastaLean.pyTruthy (decide (a < (0 : Int))) then decide (a < (0 : Int)) else decide (b < (0 : Int))
        if h_1 : !PastaLean.pyTruthy p'_cc2cond then 
          let p'_unpack_value_1 := _query_connected'find'rn a p
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut p'_thread_t3 := Prod.fst p'_unpack_pair_1
          p := Prod.snd p'_unpack_pair_1
          let p'_unpack_value_2 := _query_connected'find'rn b p
          let p'_unpack_pair_2 := p'_unpack_value_2
          let mut p'_thread_t4 := Prod.fst p'_unpack_pair_2
          p := Prod.snd p'_unpack_pair_2
          p'_cc2cond := p'_thread_t3 != p'_thread_t4
        p'_cc2 := PastaLean.pyAppend p'_cc2 (if PastaLean.pyTruthy p'_cc2cond then (0 : Int) else (1 : Int))
      return p'_cc2)

end PastaLean.User.Root
