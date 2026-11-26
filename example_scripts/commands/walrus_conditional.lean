import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Walrus in an `and`-test, evaluated conditionally: the walrus target must NOT be computed when the
-- left operand is false (here `d[t]` would KeyError). The desugarer unfolds the short-circuit into
-- nested ifs / break-guards so `k`/`m` run at their real position and still reach the body.
def scan := fun (d : Std.HashMap PyAny Int) ↦ fun (xs : List PyAny) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for t in (PastaLean.pyIter xs) do
        if h_1 : PastaLean.pyContains d t then 
          let mut k : Int := d⦋t⦌
          if h_2 : k < (100 : Int) then 
            total := total +ₚ k
      return total)

attribute [simp, taste_ingr] scan

def scan'rn := fun (d : Std.HashMap PyAny Int) ↦ fun (xs : List PyAny) ↦
  Id.run
    (do
      let mut total : Int := (0 : Int)
      for t in (PastaLean.pyIter xs) do
        if h_1 : PastaLean.pyContains d t then 
          let mut k : Int := d⦋t⦌
          if h_2 : k < (100 : Int) then 
            total := total +ₚ k
      return total)

def window := fun (s : List Int) ↦ fun (limit : Int) ↦
  Id.run
    (do
      let mut i : Int := (0 : Int)
      let mut best : Int := (0 : Int)
      while (Bool.true) do
        if h_1 : ¬i < PastaLean.pyLen s then 
          break
        let mut m : Int := s⦋i⦌ *ₚ (2 : Int)
        if h_2 : ¬m ≤ limit then 
          break
        best := PastaLean.pyMax [best, m]
        i := i +ₚ (1 : Int)
      return best)

attribute [simp, taste_ingr] window

def window'rn := fun (s : List Int) ↦ fun (limit : Int) ↦
  Id.run
    (do
      let mut i : Int := (0 : Int)
      let mut best : Int := (0 : Int)
      while (Bool.true) do
        if h_1 : !decide (i < PastaLean.pyLen s) then 
          break
        let mut m : Int := s⦋i⦌ *ₚ (2 : Int)
        if h_2 : !decide (m ≤ limit) then 
          break
        best := PastaLean.pyMax [best, m]
        i := i +ₚ (1 : Int)
      return best)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (scan (Std.HashMap.ofList [((1 : Int), (10 : Int)), ((2 : Int), (50 : Int)), ((3 : Int), (200 : Int))])
                  [(1 : Int), (2 : Int), (3 : Int), (4 : Int)])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (window [(1 : Int), (2 : Int), (3 : Int), (40 : Int)] (10 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg
                (scan'rn
                  (Std.HashMap.ofList [((1 : Int), (10 : Int)), ((2 : Int), (50 : Int)), ((3 : Int), (200 : Int))])
                  [(1 : Int), (2 : Int), (3 : Int), (4 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (window'rn [(1 : Int), (2 : Int), (3 : Int), (40 : Int)] (10 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
