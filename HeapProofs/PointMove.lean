import PastaLean
import Std.Tactic.Do

/-!
# `example_scripts/heap/15_point_move.py` — framed separation-logic specs

The `def`s below are copied verbatim from

    pastalean translate example_scripts/heap/15_point_move.py --heap --no-check

trimmed to the proof-mode (`Point`, not `Point'rn`) declarations and with the translator's
type-inferred binders (`dx`/`dy`) annotated `Int` so each `def` stands alone. Every proof runs
against the *emitted* code — `~>`/`<~` desugars to `readRefM`/`writeRefM` over the whole struct
with a record update, and `vcgen … with finish` frames the untouched sibling cell automatically.

These modules stay at the root namespace (as the translator emits) and are built as independent
compilation units (lakefile `globs`), so each file's own `Val` never collides with another's.
-/

open Lean Std Std.Internal.Do Lean.Order
open PastaLean

set_option linter.all false
set_option mvcgen.warning false
set_option maxHeartbeats 0

structure Point where
  x : Int
  y : Int
  deriving Inhabited, Repr, BEq

inductive Val where
  | point (x : Int) (y : Int)
  deriving Repr, Inhabited

derive_storable% Point

def Point.move (self : PastaLean.Ref Point) (dx dy : Int) :=
  ((do
      self ~> x <~ (← (self ~> x)) +ₚ dx
      self ~> y <~ (← (self ~> y)) +ₚ dy) :
    PastaLean.HeapM Val Unit)

def Point.manhattan (self : PastaLean.Ref Point) :=
  ((do
      let __py_ret_1 := (← (self ~> x)) +ₚ (← (self ~> y))
      return __py_ret_1) :
    PastaLean.HeapM Val _)

/-- Moving `self` updates both of its fields and frames a disjoint point `other ↦ o` untouched.
The two field writes read/modify/write the same cell in sequence; `other ↦ o` is auto-framed. -/
theorem Point.move_spec (self other : Ref Point) (pt o : Point) (dx dy : Int) :
    ⦃ (self ↦ pt ∗ other ↦ o : HProp Val) ⦄ Point.move self dx dy
    ⦃ fun _ => self ↦ { pt with x := pt.x +ₚ dx, y := pt.y +ₚ dy } ∗ other ↦ o ⦄ := by
  vcgen [Point.move, readRefM_spec, writeRefM_spec] simplifying_assumptions with finish

/-- The getter is read-only: `manhattan` touches neither its own cell nor a disjoint `other ↦ o`,
so both are framed intact. (Capturing the returned `x + y` as a `⌜r = …⌝` fact is a separate,
currently-unavailable idiom — see the `finish` gap noted in `BankAccount.lean`.) -/
theorem Point.manhattan_frame (self other : Ref Point) (pt o : Point) :
    ⦃ (self ↦ pt ∗ other ↦ o : HProp Val) ⦄ Point.manhattan self
    ⦃ fun _ => self ↦ pt ∗ other ↦ o ⦄ := by
  vcgen [Point.manhattan, readRefM_spec] simplifying_assumptions with finish
