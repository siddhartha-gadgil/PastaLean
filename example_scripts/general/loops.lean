import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

def nested_loops := fun n ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        for j in (PastaLean.pyRange i) do
          total := total +ₚ j
      return total)

attribute [simp, taste_ingr] nested_loops

def nested_loops'rn := fun n ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        for j in (PastaLean.pyRange i) do
          total := total +ₚ j
      return total)

def super_nested_loops := fun n ↦
  Id.run
    (do
      let mut res : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        for j in (PastaLean.pyRange n) do
          for k in (PastaLean.pyRange n) do
            for l in (PastaLean.pyRange n) do
              res := res +ₚ (i +ₚ j +ₚ k +ₚ l)
      return res)

attribute [simp, taste_ingr] super_nested_loops

def super_nested_loops'rn := fun n ↦
  Id.run
    (do
      let mut res : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        for j in (PastaLean.pyRange n) do
          for k in (PastaLean.pyRange n) do
            for l in (PastaLean.pyRange n) do
              res := res +ₚ (i +ₚ j +ₚ k +ₚ l)
      return res)

def while_in_for := fun n ↦
  Id.run
    (do
      let mut count : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        let mut j : Int := i
        while (j > (0 : Int)) do
          count := count +ₚ (1 : Int)
          j := j -ₚ (1 : Int)
      return count)

attribute [simp, taste_ingr] while_in_for

def while_in_for'rn := fun n ↦
  Id.run
    (do
      let mut count : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        let mut j : Int := i
        while (j > (0 : Int)) do
          count := count +ₚ (1 : Int)
          j := j -ₚ (1 : Int)
      return count)

def breakable_loop := fun n ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        if h_1 : i = (5 : Int) then 
          break
        else
          let _ := ()
        total := total +ₚ i
      let mut j : Int := (0 : Int)
      while (j < n) do
        if h_1 : j ≤ (3 : Int) then 
          continue
        else
          let _ := ()
        total := total +ₚ j
        j := j +ₚ (1 : Int)
      return total)

attribute [simp, taste_ingr] breakable_loop

def breakable_loop'rn := fun n ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for i in (PastaLean.pyRange n) do
        if h_1 : i == (5 : Int) then 
          break
        else
          let _ := ()
        total := total +ₚ i
      let mut j : Int := (0 : Int)
      while (j < n) do
        if h_1 : j ≤ (3 : Int) then 
          continue
        else
          let _ := ()
        total := total +ₚ j
        j := j +ₚ (1 : Int)
      return total)

def for_leaks_out := fun (n : Int) ↦
  Id.run
    (do
      -- A name first bound inside a loop leaks OUT of it (Python is function-scoped; Lean's loop body is
      -- its own scope). `x` is read after the loop, so it is hoisted to `let mut x : Int := default`
      -- before the loop and the body reassigns it.
      let mut x : Int := default
      for i in (PastaLean.pyRange n) do
        x := i *ₚ (2 : Int)
      return x)

attribute [simp, taste_ingr] for_leaks_out

def for_leaks_out'rn := fun (n : Int) ↦
  Id.run
    (do
      -- A name first bound inside a loop leaks OUT of it (Python is function-scoped; Lean's loop body is
      -- its own scope). `x` is read after the loop, so it is hoisted to `let mut x : Int := default`
      -- before the loop and the body reassigns it.
      let mut x : Int := default
      for i in (PastaLean.pyRange n) do
        x := i *ₚ (2 : Int)
      return x)

def nested_leaks_out := fun (n : Int) ↦
  Id.run
    (do
      -- `y` is first bound in the INNERMOST loop yet read after the OUTERMOST — it hoists all the way to
      -- the function scope (the annotate pass collects an inner-bound name at the outer loop).
      let mut y : Int := default
      for i in (PastaLean.pyRange n) do
        for j in (PastaLean.pyRange n) do
          y := i *ₚ j
      return y)

attribute [simp, taste_ingr] nested_leaks_out

def nested_leaks_out'rn := fun (n : Int) ↦
  Id.run
    (do
      -- `y` is first bound in the INNERMOST loop yet read after the OUTERMOST — it hoists all the way to
      -- the function scope (the annotate pass collects an inner-bound name at the outer loop).
      let mut y : Int := default
      for i in (PastaLean.pyRange n) do
        for j in (PastaLean.pyRange n) do
          y := i *ₚ j
      return y)

def loop_leak_conflicting := fun (n : Int) ↦
  Id.run
    (do
      -- A loop-body name bound at DIFFERENT types across branches leaks out as `PyAny` (hoisted before
      -- the loop as `let mut z : PyAny := emptyPyAny`; each branch reassigns, boxing).
      let mut z : PyAny := default
      for i in (PastaLean.pyRange n) do
        if h_1 : i %ₚ (2 : Int) = (0 : Int) then 
          z := i
        else
          z := "odd"
      let __py_ret_1 := PastaLean.pyStr z
      return __py_ret_1)

attribute [simp, taste_ingr] loop_leak_conflicting

def loop_leak_conflicting'rn := fun (n : Int) ↦
  Id.run
    (do
      -- A loop-body name bound at DIFFERENT types across branches leaks out as `PyAny` (hoisted before
      -- the loop as `let mut z : PyAny := emptyPyAny`; each branch reassigns, boxing).
      let mut z : PyAny := default
      for i in (PastaLean.pyRange n) do
        if h_1 : i %ₚ (2 : Int) == (0 : Int) then 
          z := i
        else
          z := "odd"
      let __py_ret_1 := PastaLean.pyStr z
      return __py_ret_1)