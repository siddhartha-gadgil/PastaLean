import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def add := fun (a : PyAny) ↦ fun (b : Int) ↦ (show PastaLean.PyAny from a +ₚ b)

attribute [simp] add

def add'rn := fun (a : PyAny) ↦ fun (b : Int) ↦ (show PastaLean.PyAny from a +ₚ b)

def call_add := fun n ↦ add n (1 : Int)

attribute [simp, taste_ingr] call_add

def call_add'rn := fun n ↦ add'rn n (1 : Int)

def keyword_call := fun n ↦ add (a := n) (b := (2 : Int))

attribute [simp, taste_ingr] keyword_call

def keyword_call'rn := fun n ↦ add'rn (a := n) (b := (2 : Int))

def many_args := fun (a : PyAny) ↦ fun (b : PyAny) ↦ fun (c : PyAny) ↦ fun (d : PyAny) ↦ fun (e : PyAny) ↦
  (show PastaLean.PyAny from a +ₚ b +ₚ c +ₚ d +ₚ e)

attribute [simp] many_args

def many_args'rn := fun (a : PyAny) ↦ fun (b : PyAny) ↦ fun (c : PyAny) ↦ fun (d : PyAny) ↦ fun (e : PyAny) ↦
  (show PastaLean.PyAny from a +ₚ b +ₚ c +ₚ d +ₚ e)

def complex_func := fun x ↦ fun y ↦ fun z ↦
  let res := x *ₚ y
  let res := res +ₚ z
  res

attribute [simp, taste_ingr] complex_func

def complex_func'rn := fun x ↦ fun y ↦ fun z ↦
  let res := x *ₚ y
  let res := res +ₚ z
  res

end PastaLean.User.Root
