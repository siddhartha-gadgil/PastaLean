import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def string_pipeline :=
  let s := ("  Py Ast Lean  " : String)
  let trimmed := (PastaLean.pyStringStrip s : String)
  let lowered := (PastaLean.pyStringLower trimmed : String)
  let parts := (PastaLean.pyStringSplit lowered : List String)
  let glued := (PastaLean.pyStringJoin "-" parts : String)
  glued

attribute [simp, taste_ingr] string_pipeline

def string_pipeline'rn :=
  let s := ("  Py Ast Lean  " : String)
  let trimmed := (PastaLean.pyStringStrip s : String)
  let lowered := (PastaLean.pyStringLower trimmed : String)
  let parts := (PastaLean.pyStringSplit lowered : List String)
  let glued := (PastaLean.pyStringJoin "-" parts : String)
  glued

def list_pipeline :=
  Id.run
    (do
      let mut xs : List Int := [(3 : Int), (1 : Int)]
      xs := PastaLean.pyAppend xs (2 : Int)
      xs := PastaLean.pySort xs
      let mut count : Int := PastaLean.pyLen xs
      let p'_ret_1 := (xs, count)
      return p'_ret_1)

attribute [simp, taste_ingr] list_pipeline

def list_pipeline'rn :=
  Id.run
    (do
      let mut xs : List Int := [(3 : Int), (1 : Int)]
      xs := PastaLean.pyAppend xs (2 : Int)
      xs := PastaLean.pySort xs
      let mut count : Int := PastaLean.pyLen xs
      let p'_ret_1 := (xs, count)
      return p'_ret_1)

end PastaLean.User.Root
