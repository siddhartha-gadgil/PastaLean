import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def builtin_len_sorted :=
  let xs := ([(5 : Int), (1 : Int), (3 : Int)] : List Int)
  let s := ("dbca" : String)
  let d := (Std.HashMap.ofList [("z", (9 : Int)), ("a", (1 : Int)), ("m", (4 : Int))] : Std.HashMap String Int)
  let lx := (PastaLean.pyLen xs : Int)
  let ls := (PastaLean.pyLen s : Int)
  let ld := (PastaLean.pyLen d : Int)
  let sx := (PastaLean.pySort xs : List Int)
  let ss := (PastaLean.pySort s : List String)
  let sd := (PastaLean.pySort d : List String)
  (lx, (ls, (ld, (sx, (ss, sd)))))

attribute [simp, taste_ingr] builtin_len_sorted

def builtin_len_sorted'rn :=
  let xs := ([(5 : Int), (1 : Int), (3 : Int)] : List Int)
  let s := ("dbca" : String)
  let d := (Std.HashMap.ofList [("z", (9 : Int)), ("a", (1 : Int)), ("m", (4 : Int))] : Std.HashMap String Int)
  let lx := (PastaLean.pyLen xs : Int)
  let ls := (PastaLean.pyLen s : Int)
  let ld := (PastaLean.pyLen d : Int)
  let sx := (PastaLean.pySort xs : List Int)
  let ss := (PastaLean.pySort s : List String)
  let sd := (PastaLean.pySort d : List String)
  (lx, (ls, (ld, (sx, (ss, sd)))))

def in_place_sort :=
  Id.run
    (do
      let mut xs : List Int := [(4 : Int), (1 : Int), (3 : Int), (2 : Int)]
      xs := PastaLean.pySort xs
      return xs)

attribute [simp, taste_ingr] in_place_sort

def in_place_sort'rn :=
  Id.run
    (do
      let mut xs : List Int := [(4 : Int), (1 : Int), (3 : Int), (2 : Int)]
      xs := PastaLean.pySort xs
      return xs)

end PastaLean.User.Root
