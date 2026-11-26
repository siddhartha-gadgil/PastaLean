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
Decorators — user-defined (nested) wrappers, and the OOP method-binding markers.

A decorator `@d` means `f = d(f)`; stacked decorators apply bottom-up (nearest the `def` first), so
`@a
@b
def f` is `a(b(f))`. Non-transparent user wrappers are lowered by emitting the raw function
and binding the decorated name to the application. Transparent decorators — `@cache` (memoisation is
recompute-equal here) and the class-body markers `@staticmethod`/`@classmethod`/`@property` — leave
the function's value unchanged; the class markers only drop the `self`/`cls` binding.
-/
-- User decorators with NO annotation on the wrapped `f`: TypeInfer unifies each decorator's parameter
-- with the function it decorates (`inc`, typed `int -> int`), so `f` is inferred `Callable[[int], int]`
-- and `f(x)` in the lifted wrapper elaborates — no `Callable` annotation needed.
private def _double'w := fun (x : Int) ↦ fun (f : Int → Int) ↦ (2 : Int) *ₚ f x

attribute [simp, taste_ingr] _double'w

def double := fun (f : Int → Int) ↦ fun (x : Int) ↦ _double'w x f

attribute [simp, taste_ingr] double

private def _double'w'rn := fun (x : Int) ↦ fun (f : Int → Int) ↦ (2 : Int) *ₚ f x

def double'rn := fun (f : Int → Int) ↦ fun (x : Int) ↦ _double'w'rn x f

private def _plus_one'w := fun (x : Int) ↦ fun (f : Int → Int) ↦ f x +ₚ (1 : Int)

attribute [simp, taste_ingr] _plus_one'w

def plus_one := fun (f : Int → Int) ↦ fun (x : Int) ↦ _plus_one'w x f

attribute [simp, taste_ingr] plus_one

private def _plus_one'w'rn := fun (x : Int) ↦ fun (f : Int → Int) ↦ f x +ₚ (1 : Int)

def plus_one'rn := fun (f : Int → Int) ↦ fun (x : Int) ↦ _plus_one'w'rn x f

-- Stacked user decorators: inc(x) = double(plus_one(base))(x) = 2 * ((x+1) + 1).
def inc'undecorated := fun (x : Int) ↦ x +ₚ (1 : Int)

attribute [simp, taste_ingr] inc'undecorated

def inc :=
  double (plus_one inc'undecorated)

def inc'undecorated'rn := fun (x : Int) ↦ x +ₚ (1 : Int)

def inc'rn :=
  double'rn (plus_one'rn inc'undecorated'rn)

-- The reverse direction: the decorator's `Callable` parameter type flows BACK into the decorated
-- function, pinning `add`'s otherwise-unknown params to `int` (they would be boxed as PyAny otherwise).
private def _checked'w := fun (a : Int) ↦ fun (b : Int) ↦ fun (f : Int → Int → Int) ↦ f a b

attribute [simp, taste_ingr] _checked'w

def checked := fun (f : Int → Int → Int) ↦ fun (a : Int) ↦ fun (b : Int) ↦ _checked'w a b f

attribute [simp, taste_ingr] checked

private def _checked'w'rn := fun (a : Int) ↦ fun (b : Int) ↦ fun (f : Int → Int → Int) ↦ f a b

def checked'rn := fun (f : Int → Int → Int) ↦ fun (a : Int) ↦ fun (b : Int) ↦ _checked'w'rn a b f

def add'undecorated := fun (a : Int) ↦ fun (b : Int) ↦ a +ₚ b

attribute [simp, taste_ingr] add'undecorated

def add :=
  checked add'undecorated

def add'undecorated'rn := fun (a : Int) ↦ fun (b : Int) ↦ a +ₚ b

def add'rn :=
  checked'rn add'undecorated'rn

-- `@cache`/`@lru_cache`: the RUNNABLE twin memoises (a `StateM`-threaded `HashMap` cache shared across
-- the recursion, seeded fresh per top-level call) so exponential DP runs in polynomial time; recursive
-- self-calls become `(← fib'memo'rn …)`. The PROVABLE twin `fib` stays the plain pure recursion.
partial def fib : Int → Int := fun (n : Int) ↦ if n < (2 : Int) then n else fib (n -ₚ (1 : Int)) +ₚ fib (n -ₚ (2 : Int))

partial def fib'memo'rn : Int → StateM (Std.HashMap Int Int) Int := fun (n : Int) ↦ do
  match (← get)[n]? with
  | some v =>
    return v
  | none =>
    let v ←
      ((do
            if h_1 : n < (2 : Int) then 
              return n
            let p'_ret_1 := (← fib'memo'rn (n -ₚ (1 : Int))) +ₚ (← fib'memo'rn (n -ₚ (2 : Int)))
            return p'_ret_1) :
          StateM (Std.HashMap Int Int) Int)
    modify (·.insert n v)
    return v

def fib'rn : Int → Int := fun (n : Int) ↦ (fib'memo'rn n).run' ∅

-- OOP: the method-binding markers. `@staticmethod` drops `self`; `@property` reads as an attribute;
-- `@classmethod` drops `cls`.
structure Vec where
  x : Int
  y : Int
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy Vec where truthy _ := true

instance : PastaLean.PyBool Vec where pyBool _ := true

instance : PastaLean.PyTyped Vec where pyTypeOf _ := TypeInfer.PyType.cls "Vec"

instance : Coe Vec (Option Vec) :=
  ⟨some⟩

def Vec.new : Int → Int → Vec := fun (x : Int) ↦ fun (y : Int) ↦ ({ x := x, y := y } : Vec)

def Vec.unit :=
  (1 : Int)

attribute [simp, taste_ingr] Vec.unit

def Vec.norm2 := fun (self : Vec) ↦ self.x *ₚ self.x +ₚ self.y *ₚ self.y

attribute [simp, taste_ingr] Vec.norm2

def Vec.diag := fun (n : Int) ↦ n +ₚ n

attribute [simp, taste_ingr] Vec.diag

structure Vec'rn where
  x : Int
  y : Int
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy Vec'rn where truthy _ := true

instance : PastaLean.PyBool Vec'rn where pyBool _ := true

instance : PastaLean.PyTyped Vec'rn where pyTypeOf _ := TypeInfer.PyType.cls "Vec"

instance : Coe Vec'rn (Option Vec'rn) :=
  ⟨some⟩

def Vec'rn.new : Int → Int → Vec'rn := fun (x : Int) ↦ fun (y : Int) ↦ ({ x := x, y := y } : Vec'rn)

def Vec'rn.unit :=
  (1 : Int)

def Vec'rn.norm2 := fun (self : Vec'rn) ↦ self.x *ₚ self.x +ₚ self.y *ₚ self.y

def Vec'rn.diag := fun (n : Int) ↦ n +ₚ n

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (inc (5 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (fib (10 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (add (3 : Int) (4 : Int))]
      let mut v := Vec.new (3 : Int) (4 : Int)
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg v.norm2]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg Vec.unit]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (Vec.diag (7 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (inc'rn (5 : Int))]
      let _ ← pyPrintIO [pyPrintArg (fib'rn (10 : Int))]
      let _ ← pyPrintIO [pyPrintArg (add'rn (3 : Int) (4 : Int))]
      let mut v := Vec'rn.new (3 : Int) (4 : Int)
      let _ ← pyPrintIO [pyPrintArg v.norm2]
      let _ ← pyPrintIO [pyPrintArg Vec'rn.unit]
      let _ ← pyPrintIO [pyPrintArg (Vec'rn.diag (7 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
