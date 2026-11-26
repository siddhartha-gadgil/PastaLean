import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def basic_switch := fun num ↦
  match num with
  | (1 : Int) => "one"
  | (2 : Int) => "two"
  | _ => "other"

attribute [simp, taste_ingr] basic_switch

def basic_switch'rn := fun num ↦
  match num with
  | (1 : Int) => "one"
  | (2 : Int) => "two"
  | _ => "other"

def switch_with_guard := fun num ↦
  if Bool.true then
    let x := num
    if decide (x < (0 : Int)) then "negative"
    else
      if num == (0 : Int) then "zero"
      else
        if Bool.true then
          let x := num
          if decide (x > (0 : Int)) then "positive"
          else
            match num with
            | _ => "other"
        else
          match num with
          | _ => "other"
  else
    if num == (0 : Int) then "zero"
    else
      if Bool.true then
        let x := num
        if decide (x > (0 : Int)) then "positive"
        else
          match num with
          | _ => "other"
      else
        match num with
        | _ => "other"

attribute [simp, taste_ingr] switch_with_guard

def switch_with_guard'rn := fun num ↦
  if Bool.true then
    let x := num
    if decide (x < (0 : Int)) then "negative"
    else
      if num == (0 : Int) then "zero"
      else
        if Bool.true then
          let x := num
          if decide (x > (0 : Int)) then "positive"
          else
            match num with
            | _ => "other"
        else
          match num with
          | _ => "other"
  else
    if num == (0 : Int) then "zero"
    else
      if Bool.true then
        let x := num
        if decide (x > (0 : Int)) then "positive"
        else
          match num with
          | _ => "other"
      else
        match num with
        | _ => "other"

def switch_with_pattern := fun num ↦
  match num with
  | (0 : Int) => "zero"
  | (1 : Int) => "small number"
  | (2 : Int) => "small number"
  | (3 : Int) => "small number"
  | _ => "other number"

attribute [simp, taste_ingr] switch_with_pattern

def switch_with_pattern'rn := fun num ↦
  match num with
  | (0 : Int) => "zero"
  | (1 : Int) => "small number"
  | (2 : Int) => "small number"
  | (3 : Int) => "small number"
  | _ => "other number"

def switch_with_tuple := fun point ↦
  match point with
  | ((0 : Int), (0 : Int)) => "origin"
  | (x, (0 : Int)) => s! "x-axis at {x}"
  | ((0 : Int), y) => s! "y-axis at {y}"
  | (x, y) => s! "point at ({x }, {y})"

attribute [simp, taste_ingr] switch_with_tuple

def switch_with_tuple'rn := fun point ↦
  match point with
  | ((0 : Int), (0 : Int)) => "origin"
  | (x, (0 : Int)) => s! "x-axis at {x}"
  | ((0 : Int), y) => s! "y-axis at {y}"
  | (x, y) => s! "point at ({x }, {y})"

def switch_with_default := fun (num : Int) ↦
  match num with
  | (1 : Int) => if num = (1 : Int) then "one" else "not one"
  | (2 : Int) => "two"
  | _ => "other"

attribute [simp, taste_ingr] switch_with_default

def switch_with_default'rn := fun (num : Int) ↦
  match num with
  | (1 : Int) => if num == (1 : Int) then "one" else "not one"
  | (2 : Int) => "two"
  | _ => "other"

end PastaLean.User.Root
