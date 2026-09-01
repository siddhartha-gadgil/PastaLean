import Mathlib
import PastaLean.PyAPI

namespace Libraries.operator

open PastaLean

/-! Python's `operator` module: the infix operators as ordinary functions, so they can be passed to
`reduce`/`map`/`accumulate` (`reduce(or_, xs)`). Each one delegates to the same runtime the
corresponding `BinOp` lowers to, so `or_(a, b)` and `a | b` are the *same* term. -/

def pyOperatorAdd {α β γ : Type} [PyHAdd α β γ] (a : α) (b : β) : γ := a +ₚ b
def pyOperatorSub {α β γ : Type} [PyHSub α β γ] (a : α) (b : β) : γ := a -ₚ b
def pyOperatorMul {α β γ : Type} [PyHMul α β γ] (a : α) (b : β) : γ := a *ₚ b
def pyOperatorTrueDiv {α β γ : Type} [PyHDiv α β γ] (a : α) (b : β) : γ := a /ₚ b
def pyOperatorFloorDiv {α β γ : Type} [PyFloorDiv α β γ] (a : α) (b : β) : γ := pyFloorDiv a b
def pyOperatorMod {α β γ : Type} [PyModulo α β γ] (a : α) (b : β) : γ := a %ₚ b
def pyOperatorPow {α β γ : Type} [PyHPow α β γ] (a : α) (b : β) : γ := a ^ₚ b

def pyOperatorAnd {α β γ : Type} [PyBitAnd α β γ] (a : α) (b : β) : γ := pyBitAnd a b
def pyOperatorOr {α β γ : Type} [PyBitOr α β γ] (a : α) (b : β) : γ := pyBitOr a b
def pyOperatorXor {α β γ : Type} [PyBitXor α β γ] (a : α) (b : β) : γ := pyBitXor a b
def pyOperatorLShift {α β γ : Type} [PyShiftLeft α β γ] (a : α) (b : β) : γ := pyShiftLeft a b
def pyOperatorRShift {α β γ : Type} [PyShiftRight α β γ] (a : α) (b : β) : γ := pyShiftRight a b

def pyOperatorNeg {α : Type} [Neg α] (a : α) : α := -a
def pyOperatorPos {α : Type} (a : α) : α := a
def pyOperatorAbs {α : Type} [PyAbs α] (a : α) : α := pyAbs a
/-- Python `~a` on integers: `-a - 1`. -/
def pyOperatorInvert (a : Int) : Int := -a - 1

def pyOperatorEq {α : Type} [BEq α] (a b : α) : Bool := a == b
def pyOperatorNe {α : Type} [BEq α] (a b : α) : Bool := a != b
def pyOperatorLt {α : Type} [LT α] [DecidableLT α] (a b : α) : Bool := decide (a < b)
def pyOperatorLe {α : Type} [LE α] [DecidableLE α] (a b : α) : Bool := decide (a ≤ b)
def pyOperatorGt {α : Type} [LT α] [DecidableLT α] (a b : α) : Bool := decide (b < a)
def pyOperatorGe {α : Type} [LE α] [DecidableLE α] (a b : α) : Bool := decide (b ≤ a)

def pyOperatorNot {α : Type} [PyTruthy α] (a : α) : Bool := !pyTruthy a
def pyOperatorTruth {α : Type} [PyTruthy α] (a : α) : Bool := pyTruthy a
def pyOperatorConcat {α : Type} (a b : List α) : List α := a ++ b
def pyOperatorContains {α β : Type} [PyContains α β] (a : α) (b : β) : Bool := pyContains a b

end Libraries.operator
