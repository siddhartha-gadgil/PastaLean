import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- A value-and-mutate call (`pop`) as a comprehension element: it mutates per iteration, so it can't be
-- hoisted out — the comprehension is unfolded to an explicit `acc = []; for …: acc.append(x.pop())`
-- loop, and the `pop` is then split inside the loop body.
def drain_last := fun (buckets : Std.HashMap Int (List Int)) ↦
  Id.run
    (do
      let mut buckets := buckets
      let mut p'_comp_1 : List Int := []
      for k in (PastaLean.pyIter [(1 : Int), (2 : Int), (1 : Int)]) do
        let mut p'_popv_4 := PastaLean.pyPopValue (PastaLean.pyGetItem buckets k)
        buckets := PastaLean.pySetItem buckets k (PastaLean.pyPopRest (PastaLean.pyGetItem buckets k))
        p'_comp_1 := PastaLean.pyAppend p'_comp_1 p'_popv_4
      return p'_comp_1)

attribute [simp, taste_ingr] drain_last

def drain_last'rn := fun (buckets : Std.HashMap Int (List Int)) ↦
  Id.run
    (do
      let mut buckets := buckets
      let mut p'_comp_1 : List Int := []
      for k in (PastaLean.pyIter [(1 : Int), (2 : Int), (1 : Int)]) do
        let mut p'_popv_4 := PastaLean.pyPopValue (PastaLean.pyGetItem buckets k)
        buckets := PastaLean.pySetItem buckets k (PastaLean.pyPopRest (PastaLean.pyGetItem buckets k))
        p'_comp_1 := PastaLean.pyAppend p'_comp_1 p'_popv_4
      return p'_comp_1)

-- An `if` clause inside the comprehension must guard the (mutating) append.
def drain_if := fun (buckets : Std.HashMap Int (List Int)) ↦ fun (ks : List Int) ↦
  Id.run
    (do
      let mut buckets := buckets
      let mut p'_comp_2 : List Int := []
      for k in (PastaLean.pyIter ks) do
        if h_1 : PastaLean.pyTruthy buckets⦋k⦌ then 
          let mut p'_popv_5 := PastaLean.pyPopValue (PastaLean.pyGetItem buckets k)
          buckets := PastaLean.pySetItem buckets k (PastaLean.pyPopRest (PastaLean.pyGetItem buckets k))
          p'_comp_2 := PastaLean.pyAppend p'_comp_2 p'_popv_5
      return p'_comp_2)

attribute [simp, taste_ingr] drain_if

def drain_if'rn := fun (buckets : Std.HashMap Int (List Int)) ↦ fun (ks : List Int) ↦
  Id.run
    (do
      let mut buckets := buckets
      let mut p'_comp_2 : List Int := []
      for k in (PastaLean.pyIter ks) do
        if h_1 : PastaLean.pyTruthy buckets⦋k⦌ then 
          let mut p'_popv_5 := PastaLean.pyPopValue (PastaLean.pyGetItem buckets k)
          buckets := PastaLean.pySetItem buckets k (PastaLean.pyPopRest (PastaLean.pyGetItem buckets k))
          p'_comp_2 := PastaLean.pyAppend p'_comp_2 p'_popv_5
      return p'_comp_2)

def join_pops := fun (groups : Std.HashMap Int (List String)) ↦
  Id.run
    (do
      let mut groups := groups
      let mut p'_comp_3 : List String := []
      for i in (PastaLean.pyRange (3 : Int)) do
        let mut p'_popv_6 := PastaLean.pyPopValue (PastaLean.pyGetItem groups i)
        groups := PastaLean.pySetItem groups i (PastaLean.pyPopRest (PastaLean.pyGetItem groups i))
        p'_comp_3 := PastaLean.pyAppend p'_comp_3 p'_popv_6
      let p'_ret_1 := PastaLean.pyStringJoin "" p'_comp_3
      return p'_ret_1)

attribute [simp, taste_ingr] join_pops

def join_pops'rn := fun (groups : Std.HashMap Int (List String)) ↦
  Id.run
    (do
      let mut groups := groups
      let mut p'_comp_3 : List String := []
      for i in (PastaLean.pyRange (3 : Int)) do
        let mut p'_popv_6 := PastaLean.pyPopValue (PastaLean.pyGetItem groups i)
        groups := PastaLean.pySetItem groups i (PastaLean.pyPopRest (PastaLean.pyGetItem groups i))
        p'_comp_3 := PastaLean.pyAppend p'_comp_3 p'_popv_6
      let p'_ret_1 := PastaLean.pyStringJoin "" p'_comp_3
      return p'_ret_1)

def main' :=
  ((do
      let mut b : Std.HashMap Int (List Int) :=
        Std.HashMap.ofList [((1 : Int), [(10 : Int), (11 : Int)]), ((2 : Int), [(20 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (drain_last b)]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (drain_if (Std.HashMap.ofList [((1 : Int), [(7 : Int)]), ((2 : Int), [])])
                  [(1 : Int), (2 : Int), (1 : Int)])]
      let mut g : Std.HashMap Int (List String) :=
        Std.HashMap.ofList [((0 : Int), ["a", "b"]), ((1 : Int), ["c"]), ((2 : Int), ["d", "e"])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (join_pops g)]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let mut b : Std.HashMap Int (List Int) :=
        Std.HashMap.ofList [((1 : Int), [(10 : Int), (11 : Int)]), ((2 : Int), [(20 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (drain_last'rn b)]
      let _ ←
        pyPrintIO
            [pyPrintArg
                (drain_if'rn (Std.HashMap.ofList [((1 : Int), [(7 : Int)]), ((2 : Int), [])])
                  [(1 : Int), (2 : Int), (1 : Int)])]
      let mut g : Std.HashMap Int (List String) :=
        Std.HashMap.ofList [((0 : Int), ["a", "b"]), ((1 : Int), ["c"]), ((2 : Int), ["d", "e"])]
      let _ ← pyPrintIO [pyPrintArg (join_pops'rn g)]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
