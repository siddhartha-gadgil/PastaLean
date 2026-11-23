import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def set_method_ops := fun (a : PastaLean.PySet Int) ↦ fun (b : PastaLean.PySet Int) ↦
  -- The pure (non-mutating) set methods return a new set, mirroring the `|`/`&`/`-`/`^` operators.
  let u := PastaLean.pySetUnion a b
  let i := PastaLean.pySetIntersection a b
  let d := PastaLean.pySetDifference a b
  let s := PastaLean.pySetSymmetricDifference a b
  (u, (i, (d, s)))

attribute [simp, taste_ingr] set_method_ops

def set_method_ops'rn := fun (a : PastaLean.PySet Int) ↦ fun (b : PastaLean.PySet Int) ↦
  -- The pure (non-mutating) set methods return a new set, mirroring the `|`/`&`/`-`/`^` operators.
  let u := PastaLean.pySetUnion a b
  let i := PastaLean.pySetIntersection a b
  let d := PastaLean.pySetDifference a b
  let s := PastaLean.pySetSymmetricDifference a b
  (u, (i, (d, s)))

def set_method_predicates := fun (a : PastaLean.PySet Int) ↦ fun (b : PastaLean.PySet Int) ↦
  -- issubset / issuperset / isdisjoint return Bool.
  (PastaLean.pySetSubset a b, (PastaLean.pySetSuperset a b, PastaLean.pySetIsDisjoint a b))

attribute [simp, taste_ingr] set_method_predicates

def set_method_predicates'rn := fun (a : PastaLean.PySet Int) ↦ fun (b : PastaLean.PySet Int) ↦
  -- issubset / issuperset / isdisjoint return Bool.
  (PastaLean.pySetSubset a b, (PastaLean.pySetSuperset a b, PastaLean.pySetIsDisjoint a b))

def set_operator_ops := fun (a : PastaLean.PySet Int) ↦ fun (b : PastaLean.PySet Int) ↦
  -- The operator forms lower to the same runtime functions as the methods above.
  (PastaLean.pyBitOr a b, (PastaLean.pyBitAnd a b, (a -ₚ b, PastaLean.pyBitXor a b)))

attribute [simp, taste_ingr] set_operator_ops

def set_operator_ops'rn := fun (a : PastaLean.PySet Int) ↦ fun (b : PastaLean.PySet Int) ↦
  -- The operator forms lower to the same runtime functions as the methods above.
  (PastaLean.pyBitOr a b, (PastaLean.pyBitAnd a b, (a -ₚ b, PastaLean.pyBitXor a b)))

end PastaLean.User.Root
