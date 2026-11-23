import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def list_append_once :=
  Id.run
    (do
      let mut xs : List Int := [(1 : Int), (2 : Int)]
      xs := PastaLean.pyAppend xs (3 : Int)
      return xs)

attribute [simp, taste_ingr] list_append_once

def list_append_once'rn :=
  Id.run
    (do
      let mut xs : List Int := [(1 : Int), (2 : Int)]
      xs := PastaLean.pyAppend xs (3 : Int)
      return xs)

def list_append_twice :=
  Id.run
    (do
      let mut xs : List Int := [(1 : Int), (2 : Int), (3 : Int)]
      xs := PastaLean.pyAppend xs (4 : Int)
      xs := PastaLean.pyAppend xs (5 : Int)
      return xs)

attribute [simp, taste_ingr] list_append_twice

def list_append_twice'rn :=
  Id.run
    (do
      let mut xs : List Int := [(1 : Int), (2 : Int), (3 : Int)]
      xs := PastaLean.pyAppend xs (4 : Int)
      xs := PastaLean.pyAppend xs (5 : Int)
      return xs)

def list_len :=
  let xs := ([(10 : Int), (20 : Int), (30 : Int), (40 : Int)] : List Int)
  PastaLean.pyLen xs

attribute [simp, taste_ingr] list_len

def list_len'rn :=
  let xs := (#[(10 : Int), (20 : Int), (30 : Int), (40 : Int)] : Array Int)
  PastaLean.pyLen xs

def list_membership :=
  let xs := ([(1 : Int), (2 : Int), (3 : Int)] : List Int)
  let present := (PastaLean.pyContains xs (2 : Int) : Bool)
  let missing := (PastaLean.pyContains xs (9 : Int) : Bool)
  (present, missing)

attribute [simp, taste_ingr] list_membership

def list_membership'rn :=
  let xs := ([(1 : Int), (2 : Int), (3 : Int)] : List Int)
  let present := (PastaLean.pyContains xs (2 : Int) : Bool)
  let missing := (PastaLean.pyContains xs (9 : Int) : Bool)
  (present, missing)

end PastaLean.User.Root
