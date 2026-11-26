import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def check_nesting := fun (n : Int) ↦ fun (m : Int) ↦
  if n > (0 : Int) then if m ≥ (0 : Int) then "Both positive" else "n positive, m non-positive"
  else if m > (0 : Int) then "n non-positive, m positive" else "Both non-positive"

attribute [simp, taste_ingr] check_nesting

def check_nesting'rn := fun (n : Int) ↦ fun (m : Int) ↦
  if n > (0 : Int) then if m ≥ (0 : Int) then "Both positive" else "n positive, m non-positive"
  else if m > (0 : Int) then "n non-positive, m positive" else "Both non-positive"

def super_nested_if := fun (a : Bool) ↦ fun (b : Bool) ↦ fun (c : Bool) ↦ fun (d : Bool) ↦
  if PastaLean.pyTruthy a then
    if PastaLean.pyTruthy b then
      if PastaLean.pyTruthy c then if PastaLean.pyTruthy d then (1 : Int) else (2 : Int) else (3 : Int)
    else (4 : Int)
  else (5 : Int)

attribute [simp, taste_ingr] super_nested_if

def super_nested_if'rn := fun (a : Bool) ↦ fun (b : Bool) ↦ fun (c : Bool) ↦ fun (d : Bool) ↦
  if PastaLean.pyTruthy a then
    if PastaLean.pyTruthy b then
      if PastaLean.pyTruthy c then if PastaLean.pyTruthy d then (1 : Int) else (2 : Int) else (3 : Int)
    else (4 : Int)
  else (5 : Int)

def complex_branching := fun (x : Int) ↦
  if x = (1 : Int) then "one" else if x = (2 : Int) then "two" else if x = (3 : Int) then "three" else "other"

attribute [simp, taste_ingr] complex_branching

def complex_branching'rn := fun (x : Int) ↦
  if x == (1 : Int) then "one" else if x == (2 : Int) then "two" else if x == (3 : Int) then "three" else "other"

def cond_multi := fun (x : Int) ↦
  (show Unit from
    Id.run do
      let mut x := x
      let mut a : Int := (1 : Int)
      let mut b : Int := (2 : Int)
      let mut c : Int := (1 : Int)
      if h_1 : a < b ∧ b > c then 
        x := x +ₚ (1 : Int))

attribute [simp, taste_ingr] cond_multi

def cond_multi'rn := fun (x : Int) ↦
  (show Unit from
    Id.run do
      let mut x := x
      let mut a : Int := (1 : Int)
      let mut b : Int := (2 : Int)
      let mut c : Int := (1 : Int)
      if h_1 : decide (a < b) && decide (b > c) then 
        x := x +ₚ (1 : Int))

def cond_none := fun (x : PyAny) ↦
  Id.run
    (do
      let mut s : String := ""
      if h_1 : PastaLean.pyIsNone x then 
        s := "x is None"
      let mut y : Int := (10 : Int)
      if h_2 : !PastaLean.pyIsNone y then 
        s := s +ₚ "y is not None"
      if h_3 : true ∧ true then 
        s := s +ₚ "None is None"
      if h_4 : false ∨ false then 
        s := s +ₚ "None is not None"
      return s)

attribute [simp, taste_ingr] cond_none

def cond_none'rn := fun (x : PyAny) ↦
  Id.run
    (do
      let mut s : String := ""
      if h_1 : PastaLean.pyIsNone x then 
        s := "x is None"
      let mut y : Int := (10 : Int)
      if h_2 : !PastaLean.pyIsNone y then 
        s := s +ₚ "y is not None"
      if h_3 : true && true then 
        s := s +ₚ "None is None"
      if h_4 : false || false then 
        s := s +ₚ "None is not None"
      return s)

def value_or_default := fun (xs : List PyAny) ↦
  (show PastaLean.PyAny from
    -- `a or b` in a VALUE position returns the deciding operand, not a Bool: `xs or [0]` is the list.
    PastaLean.pyMax (if PastaLean.pyTruthy xs then xs else [(0 : Int)]))

attribute [simp] value_or_default

def value_or_default'rn := fun (xs : List PyAny) ↦
  (show PastaLean.PyAny from
    -- `a or b` in a VALUE position returns the deciding operand, not a Bool: `xs or [0]` is the list.
    PastaLean.pyMax (if PastaLean.pyTruthy xs then xs else [(0 : Int)]))

def hoist_conflicting_branches := fun (c : Int) ↦
  Id.run
    (do
      -- A name Python assigns at DIFFERENT types across branches leaks out of the `if` (Python has no
      -- block scope; Lean does). It is hoisted to `let mut v : PyAny := emptyPyAny` before the `if`, and
      -- each branch REASSIGNS (boxing): `v = 5` / `v = "hi"` all mutate one PyAny variable.
      let mut v : PyAny := default
      if h_1 : c > (0 : Int) then 
        v := (5 : Int)
      else
        v := "hi"
      let p'_ret_1 := PastaLean.pyStr v
      return p'_ret_1)

attribute [simp, taste_ingr] hoist_conflicting_branches

def hoist_conflicting_branches'rn := fun (c : Int) ↦
  Id.run
    (do
      -- A name Python assigns at DIFFERENT types across branches leaks out of the `if` (Python has no
      -- block scope; Lean does). It is hoisted to `let mut v : PyAny := emptyPyAny` before the `if`, and
      -- each branch REASSIGNS (boxing): `v = 5` / `v = "hi"` all mutate one PyAny variable.
      let mut v : PyAny := default
      if h_1 : c > (0 : Int) then 
        v := (5 : Int)
      else
        v := "hi"
      let p'_ret_1 := PastaLean.pyStr v
      return p'_ret_1)

def hoist_partial_branch := fun (c : Int) ↦
  Id.run
    (do
      -- `total` is first bound inside a branch and read after the `if`; hoisted with its inferred type
      -- (`let mut total : Int := default`) so the post-`if` read sees a single variable.
      let mut total : Int := default
      if h_1 : c > (0 : Int) then 
        total := c *ₚ (2 : Int)
      else
        total := -(1 : Int)
      return total)

attribute [simp, taste_ingr] hoist_partial_branch

def hoist_partial_branch'rn := fun (c : Int) ↦
  Id.run
    (do
      -- `total` is first bound inside a branch and read after the `if`; hoisted with its inferred type
      -- (`let mut total : Int := default`) so the post-`if` read sees a single variable.
      let mut total : Int := default
      if h_1 : c > (0 : Int) then 
        total := c *ₚ (2 : Int)
      else
        total := -(1 : Int)
      return total)

end PastaLean.User.Root
