import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def fail_for_else :=
  (show Unit from
    Id.run do
      let mut p'_broke_1 := false
      for i in (PastaLean.pyRange (10 : Int)) do
        let _ := ()
      if (!p'_broke_1) then 
        let _ := ()
      else
        let _ := ())

attribute [simp, taste_ingr] fail_for_else

def fail_for_else'rn :=
  (show Unit from
    Id.run do
      let mut p'_broke_1 := false
      for i in (PastaLean.pyRange (10 : Int)) do
        let _ := ()
      if (!p'_broke_1) then 
        let _ := ()
      else
        let _ := ())

end PastaLean.User.Root
