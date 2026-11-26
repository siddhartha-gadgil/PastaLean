import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def arr :=
  [(1 : Int), (2 : Int), (3 : Int)]

def result :=
  arr⦋(0 : Int)⦌

def foo :=
  let x := ("hi" : String)
  let y := (x⦋(0 : Int)⦌ : String)
  let y := (y *ₚ (10 : Int) : String)
  let z := (PastaLean.pySlice y (some (2 : Int)) (some (-(3 : Int))) none : String)
  z

attribute [simp, taste_ingr] foo

def foo'rn :=
  let x := ("hi" : String)
  let y := (x⦋(0 : Int)⦌ : String)
  let y := (y *ₚ (10 : Int) : String)
  let z := (PastaLean.pySlice y (some (2 : Int)) (some (-(3 : Int))) none : String)
  z

def bar :=
  let x := ("hi" : String)
  let y := (PastaLean.pySlice x (some (100 : Int)) (some (-(2000 : Int))) none : String)
  y

attribute [simp, taste_ingr] bar

def bar'rn :=
  let x := ("hi" : String)
  let y := (PastaLean.pySlice x (some (100 : Int)) (some (-(2000 : Int))) none : String)
  y

end PastaLean.User.Root
