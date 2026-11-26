import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def dict_get_variants :=
  let d := (Std.HashMap.ofList [("apple", (10 : Int)), ("banana", (20 : Int))] : Std.HashMap String Int)
  let found := (PastaLean.pyGetOpt? d "apple" : Option Int)
  let missing := (PastaLean.pyGetOpt? d "pear" : Option Int)
  let fallback := (PastaLean.pyGetD d "pear" (999 : Int) : Int)
  (found, (missing, fallback))

attribute [simp, taste_ingr] dict_get_variants

def dict_get_variants'rn :=
  let d := (Std.HashMap.ofList [("apple", (10 : Int)), ("banana", (20 : Int))] : Std.HashMap String Int)
  let found := (PastaLean.pyGetOpt? d "apple" : Option Int)
  let missing := (PastaLean.pyGetOpt? d "pear" : Option Int)
  let fallback := (PastaLean.pyGetD d "pear" (999 : Int) : Int)
  (found, (missing, fallback))

def dict_get_len_mix :=
  let d := (Std.HashMap.ofList [("x", (7 : Int)), ("y", (9 : Int))] : Std.HashMap String Int)
  let got := (PastaLean.pyGetD d "x" (0 : Int) : Int)
  let size := (PastaLean.pyLen d : Int)
  (got, size)

attribute [simp, taste_ingr] dict_get_len_mix

def dict_get_len_mix'rn :=
  let d := (Std.HashMap.ofList [("x", (7 : Int)), ("y", (9 : Int))] : Std.HashMap String Int)
  let got := (PastaLean.pyGetD d "x" (0 : Int) : Int)
  let size := (PastaLean.pyLen d : Int)
  (got, size)

end PastaLean.User.Root
