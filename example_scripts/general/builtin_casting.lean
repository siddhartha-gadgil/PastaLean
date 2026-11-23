import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def builtin_casting :=
  let a := (PastaLean.pyInt "42" : Int)
  let b := (PastaLean.pyStr [(1 : Int), (2 : Int), (3 : Int)] : String)
  let c := (PastaLean.pyList "abc" : List String)
  let d := (PastaLean.pyStr Bool.true : String)
  let e := (PastaLean.pyList ((1 : Int), (2 : Int)) : List Int)
  (a, (b, (c, (d, e))))

attribute [simp, taste_ingr] builtin_casting

def builtin_casting'rn :=
  let a := (PastaLean.pyInt "42" : Int)
  let b := (PastaLean.pyStr [(1 : Int), (2 : Int), (3 : Int)] : String)
  let c := (PastaLean.pyList "abc" : List String)
  let d := (PastaLean.pyStr Bool.true : String)
  let e := (PastaLean.pyList ((1 : Int), (2 : Int)) : List Int)
  (a, (b, (c, (d, e))))

def zero_arg_casts :=
  -- `int()`/`str()` with no argument are Python's `0` / `""` (e.g. `defaultdict(int)`-style seeds).
  let n := ((0 : Int) : Int)
  let s := ("" : String)
  let n := (n +ₚ (5 : Int) : Int)
  (n, s)

attribute [simp, taste_ingr] zero_arg_casts

def zero_arg_casts'rn :=
  -- `int()`/`str()` with no argument are Python's `0` / `""` (e.g. `defaultdict(int)`-style seeds).
  let n := ((0 : Int) : Int)
  let s := ("" : String)
  let n := (n +ₚ (5 : Int) : Int)
  (n, s)

end PastaLean.User.Root
