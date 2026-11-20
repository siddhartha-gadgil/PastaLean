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

/-- Amounts in cents; arithmetic validates, mirroring datetime's overloaded `-`. -/
structure Money where
  cents : Int
  currency : String
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy Money where truthy _ := true

instance : PastaLean.PyBool Money where pyBool _ := true

instance : PastaLean.PyTyped Money where pyTypeOf _ := TypeInfer.PyType.cls "Money"

instance : Coe Money (Option Money) :=
  ⟨some⟩

def Money.new (cents : Int) (currency : String := "EUR") : PastaLean.ProofMode.PyProofM Money :=
  ((do
      let mut self : Money := default
      if h_1 : cents < -(10 : Int) ^ₚ (9 : Int) then 
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString s! "amount too small: {PastaLean.PyPrintable.pyReprify cents}"))
      self := { self with cents := cents }
      self := { self with currency := currency }
      return self) :
    PastaLean.ProofMode.PyProofM Money)

def Money.parse := fun (text : String) ↦
  ((do
      let p'_unpack_value_1 := PastaLean.pyStringSplit text "."
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut whole : String := PastaLean.pyListGetItem p'_unpack_pair_1 (0 : Int)
      let mut frac : String := PastaLean.pyListGetItem p'_unpack_pair_1 (1 : Int)
      let p'_ret_1 := (← Money.new (PastaLean.pyInt whole *ₚ (100 : Int) +ₚ PastaLean.pyInt frac))
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] Money.parse

def Money.__add__ := fun (self : Money) ↦ fun (other : Money) ↦
  ((do
      if h_1 : self.currency ≠ other.currency then 
        throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "currency mismatch"))
      let p'_ret_1 := (← Money.new (self.cents +ₚ other.cents) self.currency)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] Money.__add__

instance : PastaLean.PyHAdd Money Money (PastaLean.ProofMode.PyProofM Money) where hAdd := Money.__add__

private def Money.__sub__'Money := fun (self : Money) ↦ fun (other : Money) ↦
  ((do
      let p'_ret_1 := (← Money.new (self.cents -ₚ other.cents) self.currency)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] Money.__sub__'Money

instance : PastaLean.PyHSub Money Money (PastaLean.ProofMode.PyProofM Money) where hSub := Money.__sub__'Money

private def Money.__sub__'int := fun (self : Money) ↦ fun (other : Int) ↦
  ((do
      let p'_ret_1 := (← Money.new (self.cents -ₚ other) self.currency)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] Money.__sub__'int

instance : PastaLean.PyHSub Money Int (PastaLean.ProofMode.PyProofM Money) where hSub := Money.__sub__'int

def Money.__neg__ := fun (self : Money) ↦
  ((do
      let p'_ret_1 := (← Money.new (-self.cents) self.currency)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] Money.__neg__

def Money.__lt__ := fun (self : Money) ↦ fun (other : Money) ↦ decide (self.cents < other.cents)

attribute [simp, taste_ingr] Money.__lt__

instance : LT Money :=
  ⟨fun a b => Money.__lt__ a b = true⟩

instance : DecidableRel (α := Money) (· < ·) := fun a b => inferInstanceAs (Decidable (Money.__lt__ a b = true))

instance : Ord Money :=
  ⟨fun a b => if Money.__lt__ a b then .lt else if Money.__lt__ b a then .gt else .eq⟩

def Money.__eq__ := fun (self : Money) ↦ fun (other : Money) ↦
  if PastaLean.pyTruthy (self.cents == other.cents) then self.currency == other.currency else self.cents == other.cents

attribute [simp, taste_ingr] Money.__eq__

instance : BEq Money where beq := Money.__eq__

def Money.__bool__ := fun (self : Money) ↦ self.cents != (0 : Int)

attribute [simp, taste_ingr] Money.__bool__

instance : PastaLean.PyTruthy Money :=
  ⟨Money.__bool__⟩

instance : PastaLean.PyBool Money :=
  ⟨Money.__bool__⟩

instance : PastaLean.PyPrintable Money
    where
  pyStringify := fun (self : Money) ↦
    s!"{(PastaLean.pyFloorDiv self.cents
        (100 : Int))}.{(PastaLean.pyFormatSpec (self.cents %ₚ (100 : Int)) "02d")} {self.currency}"
  pyReprify := fun (self : Money) ↦ s! "Money({self.cents }, {PastaLean.PyPrintable.pyReprify self.currency})"

/-- Amounts in cents; arithmetic validates, mirroring datetime's overloaded `-`. -/
structure Money'rn where
  cents : Int
  currency : String
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy Money'rn where truthy _ := true

instance : PastaLean.PyBool Money'rn where pyBool _ := true

instance : PastaLean.PyTyped Money'rn where pyTypeOf _ := TypeInfer.PyType.cls "Money"

instance : Coe Money'rn (Option Money'rn) :=
  ⟨some⟩

def Money'rn.new (cents : Int) (currency : String := "EUR") : PastaLean.PyExcept Money'rn :=
  ((do
      let mut self : Money'rn := default
      if h_1 : cents < -(10 : Int) ^ₚ (9 : Int) then 
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString s! "amount too small: {PastaLean.PyPrintable.pyReprify cents}"))
      self := { self with cents := cents }
      self := { self with currency := currency }
      return self) :
    PastaLean.PyExcept Money'rn)

def Money'rn.parse := fun (text : String) ↦
  ((do
      let p'_unpack_value_1 := PastaLean.pyStringSplit text "."
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut whole : String := PastaLean.pyListGetItem p'_unpack_pair_1 (0 : Int)
      let mut frac : String := PastaLean.pyListGetItem p'_unpack_pair_1 (1 : Int)
      let p'_ret_1 := (← Money'rn.new (PastaLean.pyInt whole *ₚ (100 : Int) +ₚ PastaLean.pyInt frac))
      return p'_ret_1) :
    PastaLean.PyExcept _)

def Money'rn.__add__ := fun (self : Money'rn) ↦ fun (other : Money'rn) ↦
  ((do
      if h_1 : self.currency != other.currency then 
        throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "currency mismatch"))
      let p'_ret_1 := (← Money'rn.new (self.cents +ₚ other.cents) self.currency)
      return p'_ret_1) :
    PastaLean.PyExcept _)

instance : PastaLean.PyHAdd Money'rn Money'rn (PastaLean.PyExcept Money'rn) where hAdd := Money'rn.__add__

private def Money'rn.__sub__'Money := fun (self : Money'rn) ↦ fun (other : Money'rn) ↦
  ((do
      let p'_ret_1 := (← Money'rn.new (self.cents -ₚ other.cents) self.currency)
      return p'_ret_1) :
    PastaLean.PyExcept _)

instance : PastaLean.PyHSub Money'rn Money'rn (PastaLean.PyExcept Money'rn) where hSub := Money'rn.__sub__'Money

private def Money'rn.__sub__'int := fun (self : Money'rn) ↦ fun (other : Int) ↦
  ((do
      let p'_ret_1 := (← Money'rn.new (self.cents -ₚ other) self.currency)
      return p'_ret_1) :
    PastaLean.PyExcept _)

instance : PastaLean.PyHSub Money'rn Int (PastaLean.PyExcept Money'rn) where hSub := Money'rn.__sub__'int

def Money'rn.__neg__ := fun (self : Money'rn) ↦
  ((do
      let p'_ret_1 := (← Money'rn.new (-self.cents) self.currency)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def Money'rn.__lt__ := fun (self : Money'rn) ↦ fun (other : Money'rn) ↦ decide (self.cents < other.cents)

instance : LT Money'rn :=
  ⟨fun a b => Money'rn.__lt__ a b = true⟩

instance : DecidableRel (α := Money'rn) (· < ·) := fun a b =>
  inferInstanceAs (Decidable (Money'rn.__lt__ a b = true))

instance : Ord Money'rn :=
  ⟨fun a b => if Money'rn.__lt__ a b then .lt else if Money'rn.__lt__ b a then .gt else .eq⟩

def Money'rn.__eq__ := fun (self : Money'rn) ↦ fun (other : Money'rn) ↦
  if PastaLean.pyTruthy (self.cents == other.cents) then self.currency == other.currency else self.cents == other.cents

instance : BEq Money'rn where beq := Money'rn.__eq__

def Money'rn.__bool__ := fun (self : Money'rn) ↦ self.cents != (0 : Int)

instance : PastaLean.PyTruthy Money'rn :=
  ⟨Money'rn.__bool__⟩

instance : PastaLean.PyBool Money'rn :=
  ⟨Money'rn.__bool__⟩

instance : PastaLean.PyPrintable Money'rn
    where
  pyStringify := fun (self : Money'rn) ↦
    s!"{(PastaLean.pyFloorDiv self.cents
        (100 : Int))}.{(PastaLean.pyFormatSpec (self.cents %ₚ (100 : Int)) "02d")} {self.currency}"
  pyReprify := fun (self : Money'rn) ↦ s! "Money({self.cents }, {PastaLean.PyPrintable.pyReprify self.currency})"

def total (prices : List Money) (discount : Option Int := Option.none) : PastaLean.ProofMode.PyProofM Money := do
  let mut acc := (← Money.new (0 : Int))
  for p in (PastaLean.pyIter prices)do
    acc := (← acc +ₚ p)
  if let some discount := discount then 
    acc := (← acc -ₚ discount)
  return acc

attribute [simp] total

def total'rn (prices : List Money'rn) (discount : Option Int := Option.none) : PastaLean.PyExcept Money'rn := do
  let mut acc := (← Money'rn.new (0 : Int))
  for p in (PastaLean.pyIter prices)do
    acc := (← acc +ₚ p)
  if let some discount := discount then 
    acc := (← acc -ₚ discount)
  return acc

def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputStream : PastaLean.ProofMode.IOStream := PastaLean.ProofMode.IOStream.ofText inputText
  let initState : PastaLean.ProofMode.IOState := { input := inputStream, output := [] }
  let (result, finalState) :=
    (((do
          let mut a := (← Money.parse "12.50")
          let mut b := (← Money.new (375 : Int))
          let _ ←
            ((do
                  let p'_arg0 ← a +ₚ b
                  let p'_arg1 ← a -ₚ b
                  let p'_arg2 ← a -ₚ (50 : Int)
                  let p'_arg3 ← Money.__neg__ b
                  let __py_result ←
                    PastaLean.ProofMode.pyPrintProof
                        [pyPrintArg p'_arg0, pyPrintArg p'_arg1, pyPrintArg p'_arg2, pyPrintArg p'_arg3,
                          pyPrintArg (PastaLean.PyPrintable.pyReprify a)]
                  return __py_result) :
                PastaLean.ProofMode.PyProofM _)
          let _ ←
            ((do
                  let p'_arg1 ← total [a] (discount := (250 : Int))
                  let __py_result ←
                    PastaLean.ProofMode.pyPrintProof
                        [pyPrintArg (← total [a, b, (← Money.new (5 : Int))]), pyPrintArg p'_arg1]
                  return __py_result) :
                PastaLean.ProofMode.PyProofM _)
          let _ ←
            PastaLean.ProofMode.pyPrintProof
                [pyPrintArg (PastaLean.pySort [a, b, (← Money.new (1 : Int))]), pyPrintArg (decide (a < b)),
                  pyPrintArg (a == (← Money.new (1250 : Int))), pyPrintArg (PastaLean.pyBool (← Money.new (0 : Int))),
                  pyPrintArg (PastaLean.pyIsBool (← Money.new (0 : Int)) Bool.true)]
          try
            let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (← a +ₚ (← Money.new (1 : Int) "USD"))]
          catch caught =>
            if PastaLean.pyExcIsA caught "ValueError" then 
              let e := caught
              let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "error:", pyPrintArg e]
            else
              throw caught
          try
            let _ ← Money.new (-(10 : Int) ^ₚ (10 : Int))
          catch caught =>
            if PastaLean.pyExcIsA caught "ValueError" then 
              let e := caught
              let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "error:", pyPrintArg e]
            else
              throw caught
          pure ()) :
        PastaLean.ProofMode.PyProofM Unit))
      initState
  let outputLines := finalState.output
  for line in outputLines do
    IO.print line
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

def main'rn : IO Unit := do
  let result ←
    (((do
            let mut a := (← Money'rn.parse "12.50")
            let mut b := (← Money'rn.new (375 : Int))
            let _ ←
              ((do
                    let p'_arg0 ← a +ₚ b
                    let p'_arg1 ← a -ₚ b
                    let p'_arg2 ← a -ₚ (50 : Int)
                    let p'_arg3 ← Money'rn.__neg__ b
                    let __py_result ←
                      pyPrintIO
                          [pyPrintArg p'_arg0, pyPrintArg p'_arg1, pyPrintArg p'_arg2, pyPrintArg p'_arg3,
                            pyPrintArg (PastaLean.PyPrintable.pyReprify a)]
                    return __py_result) :
                  PastaLean.PyExcept _)
            let _ ←
              ((do
                    let p'_arg1 ← total'rn [a] (discount := (250 : Int))
                    let __py_result ←
                      pyPrintIO [pyPrintArg (← total'rn [a, b, (← Money'rn.new (5 : Int))]), pyPrintArg p'_arg1]
                    return __py_result) :
                  PastaLean.PyExcept _)
            let _ ←
              pyPrintIO
                  [pyPrintArg (PastaLean.pySort [a, b, (← Money'rn.new (1 : Int))]), pyPrintArg (decide (a < b)),
                    pyPrintArg (a == (← Money'rn.new (1250 : Int))),
                    pyPrintArg (PastaLean.pyBool (← Money'rn.new (0 : Int))),
                    pyPrintArg (PastaLean.pyIsBool (← Money'rn.new (0 : Int)) Bool.true)]
            try
              let _ ←
                pyPrintIO
                    [pyPrintArg
                        (←
                          PastaLean.PyExcept.captureIOErrors
                            (a +ₚ (← PastaLean.PyExcept.captureIOErrors (Money'rn.new (1 : Int) "USD"))))]
            catch caught =>
              if PastaLean.pyExcIsA caught "ValueError" then 
                let e := caught
                let _ ← pyPrintIO [pyPrintArg "error:", pyPrintArg e]
              else
                throw caught
            try
              let _ ← Money'rn.new (-(10 : Int) ^ₚ (10 : Int))
            catch caught =>
              if PastaLean.pyExcIsA caught "ValueError" then 
                let e := caught
                let _ ← pyPrintIO [pyPrintArg "error:", pyPrintArg e]
              else
                throw caught
            pure ()) :
          PastaLean.PyExcept Unit)).run
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

end PastaLean.User.Root
