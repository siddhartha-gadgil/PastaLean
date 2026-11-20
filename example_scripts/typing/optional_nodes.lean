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

-- !/usr/bin/env python3
/-
Optional-typed recursive nodes (TreeNode/ListNode), the shape LeetCode tree problems use.

Each function below broke a different part of the `Option` handling: the unwrap used to fire only on
the outermost receiver, and a field *write* through an `Option` produced invalid Lean.
-/
structure TreeNode where
  val : Int
  left : Option TreeNode
  right : Option TreeNode
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy TreeNode where truthy _ := true

instance : PastaLean.PyBool TreeNode where pyBool _ := true

instance : PastaLean.PyTyped TreeNode where pyTypeOf _ := TypeInfer.PyType.cls "TreeNode"

instance : Coe TreeNode (Option TreeNode) :=
  ⟨some⟩

def TreeNode.new (val : Int := (0 : Int)) (left : Option TreeNode := Option.none)
    (right : Option TreeNode := Option.none) : TreeNode :=
  ({ val := val, left := left, right := right } : TreeNode)

structure TreeNode'rn where
  val : Int
  left : Option TreeNode'rn
  right : Option TreeNode'rn
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy TreeNode'rn where truthy _ := true

instance : PastaLean.PyBool TreeNode'rn where pyBool _ := true

instance : PastaLean.PyTyped TreeNode'rn where pyTypeOf _ := TypeInfer.PyType.cls "TreeNode"

instance : Coe TreeNode'rn (Option TreeNode'rn) :=
  ⟨some⟩

def TreeNode'rn.new (val : Int := (0 : Int)) (left : Option TreeNode'rn := Option.none)
    (right : Option TreeNode'rn := Option.none) : TreeNode'rn :=
  ({ val := val, left := left, right := right } : TreeNode'rn)

structure ListNode where
  val : Int
  next : Option ListNode
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy ListNode where truthy _ := true

instance : PastaLean.PyBool ListNode where pyBool _ := true

instance : PastaLean.PyTyped ListNode where pyTypeOf _ := TypeInfer.PyType.cls "ListNode"

instance : Coe ListNode (Option ListNode) :=
  ⟨some⟩

def ListNode.new (val : Int := (0 : Int)) (next : Option ListNode := Option.none) : ListNode :=
  ({ val := val, next := next } : ListNode)

structure ListNode'rn where
  val : Int
  next : Option ListNode'rn
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy ListNode'rn where truthy _ := true

instance : PastaLean.PyBool ListNode'rn where pyBool _ := true

instance : PastaLean.PyTyped ListNode'rn where pyTypeOf _ := TypeInfer.PyType.cls "ListNode"

instance : Coe ListNode'rn (Option ListNode'rn) :=
  ⟨some⟩

def ListNode'rn.new (val : Int := (0 : Int)) (next : Option ListNode'rn := Option.none) : ListNode'rn :=
  ({ val := val, next := next } : ListNode'rn)

-- Field read straight off an `Option` receiver.
partial def depth : Option TreeNode → Int := fun (root : Option TreeNode) ↦
  if ¬PastaLean.pyTruthy root = true then (0 : Int)
  else (1 : Int) +ₚ PastaLean.pyMax [depth ((root).getD default).left, depth ((root).getD default).right]

partial def depth'rn : Option TreeNode'rn → Int := fun (root : Option TreeNode'rn) ↦
  if !PastaLean.pyTruthy root then (0 : Int)
  else (1 : Int) +ₚ PastaLean.pyMax [depth'rn ((root).getD default).left, depth'rn ((root).getD default).right]

-- Chained read: `root.left` is itself `Option TreeNode`, so `.val` needs a SECOND unwrap.
def left_val := fun (root : Option TreeNode) ↦
  if PastaLean.pyIsNone root ∨ PastaLean.pyIsNone ((root).getD default).left then (0 : Int)
  else ((((root).getD default).left).getD default).val

attribute [simp, taste_ingr] left_val

def left_val'rn := fun (root : Option TreeNode'rn) ↦
  if PastaLean.pyIsNone root || PastaLean.pyIsNone ((root).getD default).left then (0 : Int)
  else ((((root).getD default).left).getD default).val

-- Field WRITE through an `Option`: needs unwrap + re-wrap, not a bare record update.
def bump := fun (head : Option ListNode) ↦
  Id.run
    (do
      let mut head := head
      let mut n : Int := (0 : Int)
      while (PastaLean.pyTruthy head) do
        head := some { (head).getD default with val := ((head).getD default).val +ₚ (1 : Int) }
        n := n +ₚ (1 : Int)
        head := ((head).getD default).next
      return n)

attribute [simp, taste_ingr] bump

def bump'rn := fun (head : Option ListNode'rn) ↦
  Id.run
    (do
      let mut head := head
      let mut n : Int := (0 : Int)
      while (PastaLean.pyTruthy head) do
        head := some { (head).getD default with val := ((head).getD default).val +ₚ (1 : Int) }
        n := n +ₚ (1 : Int)
        head := ((head).getD default).next
      return n)

-- Reassigning the Option-typed cursor itself, the standard linked-list walk.
def total := fun (head : Option ListNode) ↦
  Id.run
    (do
      let mut head := head
      let mut acc : Int := (0 : Int)
      while (PastaLean.pyTruthy head) do
        acc := acc +ₚ ((head).getD default).val
        head := ((head).getD default).next
      return acc)

attribute [simp, taste_ingr] total

def total'rn := fun (head : Option ListNode'rn) ↦
  Id.run
    (do
      let mut head := head
      let mut acc : Int := (0 : Int)
      while (PastaLean.pyTruthy head) do
        acc := acc +ₚ ((head).getD default).val
        head := ((head).getD default).next
      return acc)

end PastaLean.User.Root
