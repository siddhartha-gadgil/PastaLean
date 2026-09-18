import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- A value+mutate method: `union` BOTH mutates self (path/rank updates) AND returns whether it
-- merged, used as `if uf.union(a, b):` and `count += uf.union(a, b)`. `find` is likewise a
-- value+mutator (path compression writes self.parent AND returns the root), including a nested
-- `self.parent[x] = self.find(...)` self-attribute write.
structure DSU where
  parent : List Int
  rank : List Int
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy DSU where truthy _ := true

instance : PastaLean.PyTyped DSU where pyTypeOf _ := TypeInfer.PyType.cls "DSU"

instance : Coe DSU (Option DSU) :=
  ⟨some⟩

def DSU.new : Int → DSU := fun (n : Int) ↦
  ({ parent := PastaLean.pyList (PastaLean.pyRange n), rank := PastaLean.pyListRepeat [(0 : Int)] n } : DSU)

partial def DSU.find := fun (self : DSU) ↦ fun (x : Int) ↦
  Id.run
    (do
      let mut self := self
      if h_1 : self.parent⦋x⦌ ≠ x then 
        let _popval'rb1 := DSU.find self self.parent⦋x⦌ |>.1
        self := DSU.find self self.parent⦋x⦌ |>.2
        self := { self with parent := PastaLean.pySetItem self.parent x _popval'rb1 }
      let p'_ret_1 := (self.parent⦋x⦌, self)
      return p'_ret_1)

def DSU.union := fun (self : DSU) ↦ fun (a : Int) ↦ fun (b : Int) ↦
  Id.run
    (do
      let mut self := self
      let mut ra := DSU.find self a |>.1
      self := DSU.find self a |>.2
      let mut rb := DSU.find self b |>.1
      self := DSU.find self b |>.2
      if h_1 : ra = rb then 
        return (Bool.false, self)
      if h_2 : self.rank⦋ra⦌ < self.rank⦋rb⦌ then 
        let p'_unpack_value_1 := (rb, ra)
        let p'_unpack_pair_1 := p'_unpack_value_1
        ra := Prod.fst p'_unpack_pair_1
        rb := Prod.snd p'_unpack_pair_1
      self := { self with parent := PastaLean.pySetItem self.parent rb ra }
      if h_3 : self.rank⦋ra⦌ = self.rank⦋rb⦌ then 
        self := { self with rank := PastaLean.pySetItem self.rank ra (self.rank⦋ra⦌ +ₚ (1 : Int)) }
      return (Bool.true, self))

attribute [simp, taste_ingr] DSU.union

structure DSU'rn where
  parent : List Int
  rank : List Int
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy DSU'rn where truthy _ := true

instance : PastaLean.PyTyped DSU'rn where pyTypeOf _ := TypeInfer.PyType.cls "DSU"

instance : Coe DSU'rn (Option DSU'rn) :=
  ⟨some⟩

def DSU'rn.new : Int → DSU'rn := fun (n : Int) ↦
  ({ parent := PastaLean.pyList (PastaLean.pyRange n), rank := PastaLean.pyListRepeat [(0 : Int)] n } : DSU'rn)

partial def DSU'rn.find := fun (self : DSU'rn) ↦ fun (x : Int) ↦
  Id.run
    (do
      let mut self := self
      if h_1 : self.parent⦋x⦌ != x then 
        let _popval'rb1 := DSU'rn.find self self.parent⦋x⦌ |>.1
        self := DSU'rn.find self self.parent⦋x⦌ |>.2
        self := { self with parent := PastaLean.pySetItem self.parent x _popval'rb1 }
      let p'_ret_1 := (self.parent⦋x⦌, self)
      return p'_ret_1)

def DSU'rn.union := fun (self : DSU'rn) ↦ fun (a : Int) ↦ fun (b : Int) ↦
  Id.run
    (do
      let mut self := self
      let mut ra := DSU'rn.find self a |>.1
      self := DSU'rn.find self a |>.2
      let mut rb := DSU'rn.find self b |>.1
      self := DSU'rn.find self b |>.2
      if h_1 : ra == rb then 
        return (Bool.false, self)
      if h_2 : self.rank⦋ra⦌ < self.rank⦋rb⦌ then 
        let p'_unpack_value_1 := (rb, ra)
        let p'_unpack_pair_1 := p'_unpack_value_1
        ra := Prod.fst p'_unpack_pair_1
        rb := Prod.snd p'_unpack_pair_1
      self := { self with parent := PastaLean.pySetItem self.parent rb ra }
      if h_3 : self.rank⦋ra⦌ == self.rank⦋rb⦌ then 
        self := { self with rank := PastaLean.pySetItem self.rank ra (self.rank⦋ra⦌ +ₚ (1 : Int)) }
      return (Bool.true, self))

def count_components := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut dsu := DSU.new n
      let mut count : Int := n
      for e in (PastaLean.pyIter edges)do
        let mut p'_popv_2 := DSU.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.1
        dsu := DSU.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.2
        if h_1 : PastaLean.pyTruthy p'_popv_2 then 
          count := count -ₚ (1 : Int)
      return count)

attribute [simp, taste_ingr] count_components

def count_components'rn := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut dsu := DSU'rn.new n
      let mut count : Int := n
      for e in (PastaLean.pyIter edges)do
        let mut p'_popv_2 := DSU'rn.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.1
        dsu := DSU'rn.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.2
        if h_1 : PastaLean.pyTruthy p'_popv_2 then 
          count := count -ₚ (1 : Int)
      return count)

def count_merges := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut dsu := DSU.new n
      let mut merges : Int := (0 : Int)
      for e in (PastaLean.pyIter edges)do
        let mut p'_popv_3 := DSU.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.1
        dsu := DSU.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.2
        merges := merges +ₚ p'_popv_3
      return merges)

attribute [simp, taste_ingr] count_merges

def count_merges'rn := fun (n : Int) ↦ fun (edges : List (List Int)) ↦
  Id.run
    (do
      let mut dsu := DSU'rn.new n
      let mut merges : Int := (0 : Int)
      for e in (PastaLean.pyIter edges)do
        let mut p'_popv_3 := DSU'rn.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.1
        dsu := DSU'rn.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.2
        merges := merges +ₚ p'_popv_3
      return merges)

def count_gated := fun (n : Int) ↦ fun (edges : List (List Int)) ↦ fun (gate : List Int) ↦
  Id.run
    (do
      -- `gate[i] == 1 and dsu.union(...)`: the union (and its mutation) must run ONLY when the gate is
      -- open — a value+mutate call inside a short-circuit `and`.
      let mut dsu := DSU.new n
      let mut merges : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen edges))do
        let mut e : List Int := PastaLean.pyListGetProof edges i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
        let mut p'_sc'1 : Bool := Bool.false
        if h_1 : gate⦋i⦌ = (1 : Int) then 
          p'_sc'1 := DSU.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.1
          dsu := DSU.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.2
        if h_2 : PastaLean.pyTruthy p'_sc'1 then 
          merges := merges +ₚ (1 : Int)
      return merges)

attribute [simp, taste_ingr] count_gated

def count_gated'rn := fun (n : Int) ↦ fun (edges : List (List Int)) ↦ fun (gate : List Int) ↦
  Id.run
    (do
      -- `gate[i] == 1 and dsu.union(...)`: the union (and its mutation) must run ONLY when the gate is
      -- open — a value+mutate call inside a short-circuit `and`.
      let mut dsu := DSU'rn.new n
      let mut merges : Int := (0 : Int)
      for hb'i : i in (PastaLean.pyRange (PastaLean.pyLen edges))do
        let mut e : List Int := PastaLean.pyListGetProof edges i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
        let mut p'_sc'1 : Bool := Bool.false
        if h_1 : gate⦋i⦌ == (1 : Int) then 
          p'_sc'1 := DSU'rn.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.1
          dsu := DSU'rn.union dsu e⦋(0 : Int)⦌ e⦋(1 : Int)⦌ |>.2
        if h_2 : PastaLean.pyTruthy p'_sc'1 then 
          merges := merges +ₚ (1 : Int)
      return merges)

def main' :=
  ((do
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (count_components (5 : Int) [[(0 : Int), (1 : Int)], [(1 : Int), (2 : Int)], [(3 : Int), (4 : Int)]])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (count_merges (6 : Int)
                  [[(0 : Int), (1 : Int)], [(2 : Int), (3 : Int)], [(4 : Int), (5 : Int)], [(1 : Int), (2 : Int)],
                    [(0 : Int), (2 : Int)]])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg
                (count_gated (5 : Int)
                  [[(0 : Int), (1 : Int)], [(1 : Int), (2 : Int)], [(2 : Int), (3 : Int)], [(3 : Int), (4 : Int)]]
                  [(1 : Int), (0 : Int), (1 : Int), (0 : Int)])]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ←
        pyPrintIO
            [pyPrintArg
                (count_components'rn (5 : Int)
                  [[(0 : Int), (1 : Int)], [(1 : Int), (2 : Int)], [(3 : Int), (4 : Int)]])]
      let _ ←
        pyPrintIO
            [pyPrintArg
                (count_merges'rn (6 : Int)
                  [[(0 : Int), (1 : Int)], [(2 : Int), (3 : Int)], [(4 : Int), (5 : Int)], [(1 : Int), (2 : Int)],
                    [(0 : Int), (2 : Int)]])]
      let _ ←
        pyPrintIO
            [pyPrintArg
                (count_gated'rn (5 : Int)
                  [[(0 : Int), (1 : Int)], [(1 : Int), (2 : Int)], [(2 : Int), (3 : Int)], [(3 : Int), (4 : Int)]]
                  [(1 : Int), (0 : Int), (1 : Int), (0 : Int)])]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
