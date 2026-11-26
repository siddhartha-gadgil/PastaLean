import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def len_protocols :=
  let xs := ([(1 : Int), (2 : Int), (3 : Int)] : List Int)
  let s := ("hello" : String)
  let d := (Std.HashMap.ofList [("a", (1 : Int))] : Std.HashMap String Int)
  let lx := (PastaLean.pyLen xs : Int)
  let ls := (PastaLean.pyLen s : Int)
  let ld := (PastaLean.pyLen d : Int)
  (lx, (ls, ld))

attribute [simp, taste_ingr] len_protocols

def len_protocols'rn :=
  let xs := (#[(1 : Int), (2 : Int), (3 : Int)] : Array Int)
  let s := ("hello" : String)
  let d := (Std.HashMap.ofList [("a", (1 : Int))] : Std.HashMap String Int)
  let lx := (PastaLean.pyLen xs : Int)
  let ls := (PastaLean.pyLen s : Int)
  let ld := (PastaLean.pyLen d : Int)
  (lx, (ls, ld))

def iteration_protocols :=
  let xs := ([(4 : Int), (5 : Int), (6 : Int)] : List Int)
  PastaLean.pyIter xs

attribute [simp, taste_ingr] iteration_protocols

def iteration_protocols'rn :=
  let xs := ([(4 : Int), (5 : Int), (6 : Int)] : List Int)
  PastaLean.pyIter xs

end PastaLean.User.Root
