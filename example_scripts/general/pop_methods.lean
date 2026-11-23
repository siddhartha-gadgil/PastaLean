import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- `list.pop()` removes and returns the last element; `list.pop(i)` the element at index i.
-- Both lower to a value read (`pyPopValue`) plus a container update (`pyPopRest`), since the
-- runtime containers are immutable values. `pop` mutates its receiver, so the function body is
-- threaded monadically (`Id.run do`) with the container bound `let mut`.
def list_pop_last :=
  Id.run
    (do
      let mut xs : List Int := [(10 : Int), (20 : Int), (30 : Int), (40 : Int)]
      let mut last := PastaLean.pyPopValue xs
      xs := PastaLean.pyPopRest xs
      return last)

attribute [simp, taste_ingr] list_pop_last

def list_pop_last'rn :=
  Id.run
    (do
      let mut xs : Array Int := #[(10 : Int), (20 : Int), (30 : Int), (40 : Int)]
      let mut last := PastaLean.pyArrayPopValue xs
      xs := PastaLean.pyArrayPopRest xs
      return last)

def list_pop_index :=
  Id.run
    (do
      let mut ys : List Int := [(10 : Int), (20 : Int), (30 : Int), (40 : Int)]
      let mut first := PastaLean.pyPopValue ys (0 : Int)
      ys := PastaLean.pyPopRest ys (0 : Int)
      return first)

attribute [simp, taste_ingr] list_pop_index

def list_pop_index'rn :=
  Id.run
    (do
      let mut ys : Array Int := #[(10 : Int), (20 : Int), (30 : Int), (40 : Int)]
      let mut first := PastaLean.pyArrayPopValue ys (0 : Int)
      ys := PastaLean.pyArrayPopRest ys (0 : Int)
      return first)

-- Sets are modelled as deduplicated lists; `set.pop()` removes an arbitrary element.
def set_pop :=
  Id.run
    (do
      let mut seen : PastaLean.PySet Int := PastaLean.pySet [(1 : Int), (2 : Int), (3 : Int)]
      seen := PastaLean.pySetDiscard seen (2 : Int)
      let mut x := PastaLean.pyPopValue seen
      seen := PastaLean.pyPopRest seen
      return x)

attribute [simp, taste_ingr] set_pop

def set_pop'rn :=
  Id.run
    (do
      let mut seen : PastaLean.PySet Int := PastaLean.pySet [(1 : Int), (2 : Int), (3 : Int)]
      seen := PastaLean.pySetDiscard seen (2 : Int)
      let mut x := PastaLean.pyPopValue seen
      seen := PastaLean.pyPopRest seen
      return x)

end PastaLean.User.Root
