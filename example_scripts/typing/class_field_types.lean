import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- !/usr/bin/env python3
/-
Class fields whose type comes from what `__init__` assigns, plus self-recursive methods.

An unannotated field used to fall back to `Int` unless its initialiser was a bare literal, so
`self.p = list(range(n))` produced `p : Int` and every later `self.p[x]` failed to resolve. A method
that calls itself (path compression) also has no termination proof, so it must be emitted `partial`.
-/
structure UnionFind where
  p : List Int
  size : List Int
  count : Int
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy UnionFind where truthy _ := true

instance : PastaLean.PyBool UnionFind where pyBool _ := true

instance : PastaLean.PyTyped UnionFind where pyTypeOf _ := TypeInfer.PyType.cls "UnionFind"

instance : Coe UnionFind (Option UnionFind) :=
  ⟨some⟩

def UnionFind.new : Int → UnionFind := fun (n : Int) ↦
  ({ p := PastaLean.pyList (PastaLean.pyRange n), size := PastaLean.pyListRepeat [(1 : Int)] n, count := n } :
    UnionFind)

partial def UnionFind.find := fun (self : UnionFind) ↦ fun (x : Int) ↦
  Id.run
    (do
      let mut self := self
      if h_1 : self.p⦋x⦌ ≠ x then 
        let _popval'rb0 := UnionFind.find self self.p⦋x⦌ |>.1
        self := UnionFind.find self self.p⦋x⦌ |>.2
        self := { self with p := PastaLean.pySetItem self.p x _popval'rb0 }
      let p'_ret_1 := (self.p⦋x⦌, self)
      return p'_ret_1)

def UnionFind.union := fun (self : UnionFind) ↦ fun (a : Int) ↦ fun (b : Int) ↦
  Id.run
    (do
      let mut self := self
      let mut ra := UnionFind.find self a |>.1
      self := UnionFind.find self a |>.2
      let mut rb := UnionFind.find self b |>.1
      self := UnionFind.find self b |>.2
      if h_1 : ra ≠ rb then 
        self := { self with p := PastaLean.pySetItem self.p ra rb }
        self := { self with count := self.count -ₚ (1 : Int) }
      return self)

attribute [simp, taste_ingr] UnionFind.union

structure UnionFind'rn where
  p : List Int
  size : List Int
  count : Int
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy UnionFind'rn where truthy _ := true

instance : PastaLean.PyBool UnionFind'rn where pyBool _ := true

instance : PastaLean.PyTyped UnionFind'rn where pyTypeOf _ := TypeInfer.PyType.cls "UnionFind"

instance : Coe UnionFind'rn (Option UnionFind'rn) :=
  ⟨some⟩

def UnionFind'rn.new : Int → UnionFind'rn := fun (n : Int) ↦
  ({ p := PastaLean.pyList (PastaLean.pyRange n), size := PastaLean.pyListRepeat [(1 : Int)] n, count := n } :
    UnionFind'rn)

partial def UnionFind'rn.find := fun (self : UnionFind'rn) ↦ fun (x : Int) ↦
  Id.run
    (do
      let mut self := self
      if h_1 : self.p⦋x⦌ != x then 
        let _popval'rb0 := UnionFind'rn.find self self.p⦋x⦌ |>.1
        self := UnionFind'rn.find self self.p⦋x⦌ |>.2
        self := { self with p := PastaLean.pySetItem self.p x _popval'rb0 }
      let p'_ret_1 := (self.p⦋x⦌, self)
      return p'_ret_1)

def UnionFind'rn.union := fun (self : UnionFind'rn) ↦ fun (a : Int) ↦ fun (b : Int) ↦
  Id.run
    (do
      let mut self := self
      let mut ra := UnionFind'rn.find self a |>.1
      self := UnionFind'rn.find self a |>.2
      let mut rb := UnionFind'rn.find self b |>.1
      self := UnionFind'rn.find self b |>.2
      if h_1 : ra != rb then 
        self := { self with p := PastaLean.pySetItem self.p ra rb }
        self := { self with count := self.count -ₚ (1 : Int) }
      return self)

structure Bag where
  words : List String
  n : Int
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy Bag where truthy _ := true

instance : PastaLean.PyBool Bag where pyBool _ := true

instance : PastaLean.PyTyped Bag where pyTypeOf _ := TypeInfer.PyType.cls "Bag"

instance : Coe Bag (Option Bag) :=
  ⟨some⟩

def Bag.new : List String → Bag := fun (words : List String) ↦
  ({ words := PastaLean.pySort words, n := PastaLean.pyLen words } : Bag)

def Bag.first := fun (self : Bag) ↦ self.words⦋(0 : Int)⦌

attribute [simp, taste_ingr] Bag.first

structure Bag'rn where
  words : List String
  n : Int
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy Bag'rn where truthy _ := true

instance : PastaLean.PyBool Bag'rn where pyBool _ := true

instance : PastaLean.PyTyped Bag'rn where pyTypeOf _ := TypeInfer.PyType.cls "Bag"

instance : Coe Bag'rn (Option Bag'rn) :=
  ⟨some⟩

def Bag'rn.new : List String → Bag'rn := fun (words : List String) ↦
  ({ words := PastaLean.pySort words, n := PastaLean.pyLen words } : Bag'rn)

def Bag'rn.first := fun (self : Bag'rn) ↦ self.words⦋(0 : Int)⦌

def main' :=
  ((do
      let mut uf := UnionFind.new (6 : Int)
      uf := UnionFind.union uf (0 : Int) (1 : Int)
      uf := UnionFind.union uf (1 : Int) (2 : Int)
      let mut p'_popv_1 := UnionFind.find uf (0 : Int) |>.1
      uf := UnionFind.find uf (0 : Int) |>.2
      let mut p'_popv_2 := UnionFind.find uf (2 : Int) |>.1
      uf := UnionFind.find uf (2 : Int) |>.2
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (p'_popv_1 == p'_popv_2)]
      let mut p'_popv_3 := UnionFind.find uf (0 : Int) |>.1
      uf := UnionFind.find uf (0 : Int) |>.2
      let mut p'_popv_4 := UnionFind.find uf (5 : Int) |>.1
      uf := UnionFind.find uf (5 : Int) |>.2
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (p'_popv_3 == p'_popv_4)]
      let mut b := Bag.new ["pear", "apple"]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg b.first]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg b.n]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let mut uf := UnionFind'rn.new (6 : Int)
      uf := UnionFind'rn.union uf (0 : Int) (1 : Int)
      uf := UnionFind'rn.union uf (1 : Int) (2 : Int)
      let mut p'_popv_1 := UnionFind'rn.find uf (0 : Int) |>.1
      uf := UnionFind'rn.find uf (0 : Int) |>.2
      let mut p'_popv_2 := UnionFind'rn.find uf (2 : Int) |>.1
      uf := UnionFind'rn.find uf (2 : Int) |>.2
      let _ ← pyPrintIO [pyPrintArg (p'_popv_1 == p'_popv_2)]
      let mut p'_popv_3 := UnionFind'rn.find uf (0 : Int) |>.1
      uf := UnionFind'rn.find uf (0 : Int) |>.2
      let mut p'_popv_4 := UnionFind'rn.find uf (5 : Int) |>.1
      uf := UnionFind'rn.find uf (5 : Int) |>.2
      let _ ← pyPrintIO [pyPrintArg (p'_popv_3 == p'_popv_4)]
      let mut b := Bag'rn.new ["pear", "apple"]
      let _ ← pyPrintIO [pyPrintArg b.first]
      let _ ← pyPrintIO [pyPrintArg b.n]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
