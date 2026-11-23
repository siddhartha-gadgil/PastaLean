import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Bare top-level `for`/`if`/`while` are not executable in Lean, so we thread the names
-- each block mutates as state: the block becomes a value returning the updated names,
-- which are then re-exported as fresh `def`s. Names assigned once before a block are
-- versioned (`x₀`) so the clean name (`x`) holds the block's result, and each result def
-- is named after a short position-based hash so distinct blocks never collide.
--
-- A standalone `def main()` (with no `__main__` guard) is renamed to `main'` in Lean, since
-- Lean reserves the top-level name `main` for the program entry point (which must have type
-- `IO (UInt32 | Unit | PUnit)`). Here it is just a normal helper, so it yields the name.
def main' :=
  "hi"

attribute [simp, taste_ingr] main'

def main''rn :=
  "hi"

-- for: single-variable fold
def x₀ :=
  (0 : Int)

def p'_for_205bfb :=
  List.foldl
    (fun p'_state_1 i =>
      Id.run
        (do
          let mut x := p'_state_1
          x := x +ₚ i
          return x))
    x₀ (PastaLean.pyRange (5 : Int))

def x :=
  p'_for_205bfb

-- if: swap two globals (native tuple unpacking lowers through Prod.fst/snd)
def AX₀ :=
  (3 : Int)

def BX₀ :=
  (2 : Int)

def p'_if_1cfc86 :=
  Id.run
    (do
      let mut AX := AX₀
      let mut BX := BX₀
      if h_1 : AX > BX then 
        let p'_unpack_value_1 := (BX, AX)
        let p'_unpack_pair_1 := p'_unpack_value_1
        AX := Prod.fst p'_unpack_pair_1
        BX := Prod.snd p'_unpack_pair_1
      return (AX, BX))

def AX :=
  Prod.fst p'_if_1cfc86

def BX :=
  Prod.snd p'_if_1cfc86

-- while: thread two globals through one Id.run block
def total₀ :=
  (0 : Int)

def i₀ :=
  (0 : Int)

def p'_while_958610 :=
  Id.run
    (do
      let mut i := i₀
      let mut total := total₀
      while (i < (5 : Int)) do
        total := total +ₚ i
        i := i +ₚ (1 : Int)
      return (i, total))

def i :=
  Prod.fst p'_while_958610

def total :=
  Prod.snd p'_while_958610

end PastaLean.User.Root
