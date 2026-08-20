import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

def lmbda_expr := fun x ↦ x +ₚ (1 : Int)

attribute [simp, taste_ingr] lmbda_expr

def lmbda_expr'rn := fun x ↦ x +ₚ (1 : Int)

def lmbda_with_condition := fun x ↦ if x %ₚ (2 : Int) = (0 : Int) then x +ₚ (1 : Int) else x -ₚ (1 : Int)

attribute [simp, taste_ingr] lmbda_with_condition

def lmbda_with_condition'rn := fun x ↦ if x %ₚ (2 : Int) == (0 : Int) then x +ₚ (1 : Int) else x -ₚ (1 : Int)

def lmbda_with_array :=
  let a := ([(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)] : List Int)
  let b := fun x ↦ if PastaLean.pyContains a x then some (x *ₚ x) else none
  let c := b
  c

attribute [simp, taste_ingr] lmbda_with_array

def lmbda_with_array'rn :=
  let a := ([(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)] : List Int)
  let b := fun x ↦ if PastaLean.pyContains a x then some (x *ₚ x) else none
  let c := b
  c

def lmbda_with_string :=
  let s := ("hello" : String)
  fun char ↦ PastaLean.pyContains (s +ₚ " world") char

attribute [simp, taste_ingr] lmbda_with_string

def lmbda_with_string'rn :=
  let s := ("hello" : String)
  fun char ↦ PastaLean.pyContains (s +ₚ " world") char

def nested_lmbda := fun () ↦ fun x ↦ x *ₚ x

attribute [simp, taste_ingr] nested_lmbda

def nested_lmbda'rn := fun () ↦ fun x ↦ x *ₚ x

private def _lmbda_with_function_call'add_one := fun x ↦ x +ₚ (1 : Int)

attribute [simp, taste_ingr] _lmbda_with_function_call'add_one

def lmbda_with_function_call := fun x ↦ _lmbda_with_function_call'add_one x

attribute [simp, taste_ingr] lmbda_with_function_call

private def _lmbda_with_function_call'add_one'rn := fun x ↦ x +ₚ (1 : Int)

def lmbda_with_function_call'rn := fun x ↦ _lmbda_with_function_call'add_one'rn x

def lmbda_ds := fun x ↦ [x, x *ₚ (2 : Int), x *ₚ (3 : Int)]

attribute [simp, taste_ingr] lmbda_ds

def lmbda_ds'rn := fun x ↦ [x, x *ₚ (2 : Int), x *ₚ (3 : Int)]

def lmbda_with_nested_conditions := fun x ↦
  if x %ₚ (2 : Int) = (0 : Int) ∧ x %ₚ (3 : Int) = (0 : Int) ∨ x %ₚ (5 : Int) = (0 : Int) then x +ₚ (1 : Int)
  else x -ₚ (1 : Int)

attribute [simp, taste_ingr] lmbda_with_nested_conditions

def lmbda_with_nested_conditions'rn := fun x ↦
  if x %ₚ (2 : Int) == (0 : Int) && x %ₚ (3 : Int) == (0 : Int) || x %ₚ (5 : Int) == (0 : Int) then x +ₚ (1 : Int)
  else x -ₚ (1 : Int)

def lmbda_with_tuple_unpacking := fun {α β} [ToString α] [ToString β] (pair : α × β) ↦
  s!"{(Prod.fst pair)}:{Prod.snd pair}"

attribute [simp, taste_ingr] lmbda_with_tuple_unpacking

def lmbda_with_tuple_unpacking'rn := fun {α β} [ToString α] [ToString β] (pair : α × β) ↦
  s!"{(Prod.fst pair)}:{Prod.snd pair}"

def lmbda_with_side_effects :=
  Id.run
    (do
      let mut result : List Int := []
      for x in (PastaLean.pyRange (5 : Int)) do
        result := PastaLean.pyAppend result (x *ₚ x)
      let __py_ret_1 := fun (y : Unit) ↦ result
      return __py_ret_1)

attribute [simp, taste_ingr] lmbda_with_side_effects

def lmbda_with_side_effects'rn :=
  Id.run
    (do
      let mut result : List Int := []
      for x in (PastaLean.pyRange (5 : Int)) do
        result := PastaLean.pyAppend result (x *ₚ x)
      let __py_ret_1 := fun (y : Unit) ↦ result
      return __py_ret_1)

def lmbda_with_generator_expression := fun () ↦
  (PastaLean.pyIter ((PastaLean.pyRange (5 : Int)).map fun i => i)).map fun x => x *ₚ x

attribute [simp, taste_ingr] lmbda_with_generator_expression

def lmbda_with_generator_expression'rn := fun () ↦
  (PastaLean.pyIter ((PastaLean.pyRange (5 : Int)).map fun i => i)).map fun x => x *ₚ x