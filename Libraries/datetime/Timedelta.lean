import Libraries.datetime.Basic
import Std.Tactic.Do

open PastaLean
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace Libraries.datetime

/-- A duration, normalised to days, seconds (0..86399) and microseconds (0..999999). -/
structure timedelta where
  _days : Int
  _seconds : Int
  _microseconds : Int
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy timedelta where truthy _ := true

instance : PastaLean.PyBool timedelta where pyBool _ := true

instance : PastaLean.PyTyped timedelta where pyTypeOf _ := TypeInfer.PyType.cls "timedelta"

instance : Coe timedelta (Option timedelta) :=
  ⟨some⟩

/-- The normalising constructor without Python's magnitude check: for values in range by construction. -/
def timedelta.ofParts (days : Int := (0 : Int)) (seconds : Int := (0 : Int)) (microseconds : Int := (0 : Int))
    (milliseconds : Int := (0 : Int)) (minutes : Int := (0 : Int)) (hours : Int := (0 : Int))
    (weeks : Int := (0 : Int)) : timedelta :=
  Id.run
    (do
      let mut self : timedelta := default
      let mut us : Int :=
        (((weeks *ₚ (7 : Int) +ₚ days) *ₚ (24 : Int) +ₚ hours) *ₚ (60 : Int) +ₚ minutes) *ₚ (60 : Int) +ₚ seconds
      us := us *ₚ (1000000 : Int) +ₚ milliseconds *ₚ (1000 : Int) +ₚ microseconds
      let p'_unpack_value_1 := PastaLean.pyDivmod us ((86400 : Int) *ₚ (1000000 : Int))
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut d := Prod.fst p'_unpack_pair_1
      let mut rest := Prod.snd p'_unpack_pair_1
      let p'_unpack_value_2 := PastaLean.pyDivmod rest (1000000 : Int)
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut s := Prod.fst p'_unpack_pair_2
      let mut usec := Prod.snd p'_unpack_pair_2
      self := { self with _days := d }
      self := { self with _seconds := s }
      self := { self with _microseconds := usec }
      return self)

/-- Python bounds a `timedelta` to 999999999 days either way (`OverflowError`). -/
def timedelta.checked (t : timedelta) : PastaLean.ProofMode.PyProofM timedelta :=
  if t._days.natAbs > 999999999 then
    throw (PastaLean.PyException.Raise "OverflowError" s!"days={t._days}; must have magnitude <= 999999999")
  else pure t

/-- `timedelta(days, seconds, microseconds, milliseconds, minutes, hours, weeks)`. -/
def timedelta.new (days : Int := 0) (seconds : Int := 0) (microseconds : Int := 0) (milliseconds : Int := 0)
    (minutes : Int := 0) (hours : Int := 0) (weeks : Int := 0) : PastaLean.ProofMode.PyProofM timedelta :=
  timedelta.checked (timedelta.ofParts days seconds microseconds milliseconds minutes hours weeks)

def timedelta.days := fun (self : timedelta) ↦ self._days

attribute [simp, taste_ingr] timedelta.days

def timedelta.seconds := fun (self : timedelta) ↦ self._seconds

attribute [simp, taste_ingr] timedelta.seconds

def timedelta.microseconds := fun (self : timedelta) ↦ self._microseconds

attribute [simp, taste_ingr] timedelta.microseconds

def timedelta._to_microseconds := fun (self : timedelta) ↦
  (self._days *ₚ (86400 : Int) +ₚ self._seconds) *ₚ (1000000 : Int) +ₚ self._microseconds

attribute [simp, taste_ingr] timedelta._to_microseconds

def timedelta.total_seconds := fun (self : timedelta) ↦ self._to_microseconds /ₚ (1000000 : Int)

attribute [simp, taste_ingr] timedelta.total_seconds

def timedelta.__add__ := fun (self : timedelta) ↦ fun (other : timedelta) ↦
  timedelta.checked <| timedelta.ofParts (self._days +ₚ other._days) (self._seconds +ₚ other._seconds)
    (self._microseconds +ₚ other._microseconds)

attribute [simp] timedelta.__add__

instance : PastaLean.PyHAdd timedelta timedelta (PastaLean.ProofMode.PyProofM timedelta) where hAdd := timedelta.__add__

def timedelta.__sub__ := fun (self : timedelta) ↦ fun (other : timedelta) ↦
  timedelta.checked <| timedelta.ofParts (self._days -ₚ other._days) (self._seconds -ₚ other._seconds)
    (self._microseconds -ₚ other._microseconds)

attribute [simp] timedelta.__sub__

instance : PastaLean.PyHSub timedelta timedelta (PastaLean.ProofMode.PyProofM timedelta) where hSub := timedelta.__sub__

def timedelta.__neg__ := fun (self : timedelta) ↦ timedelta.checked <| timedelta.ofParts (-self._days) (-self._seconds) (-self._microseconds)

attribute [simp] timedelta.__neg__

/-- Negation without the magnitude check, for the library's own in-range values; Python's `-td` calls
`timedelta.__neg__` (TypeInfer stamps it), which raises. -/
instance : Neg timedelta :=
  ⟨fun t => timedelta.ofParts (-t._days) (-t._seconds) (-t._microseconds)⟩

def timedelta.__abs__ := fun (self : timedelta) ↦ if self._days < (0 : Int) then -self else self

attribute [simp, taste_ingr] timedelta.__abs__

instance : PastaLean.PyAbs timedelta :=
  ⟨timedelta.__abs__⟩

def timedelta.__mul__ := fun (self : timedelta) ↦ fun (other : Int) ↦
  timedelta.checked <| timedelta.ofParts (0 : Int) (0 : Int) (self._to_microseconds *ₚ other)

attribute [simp] timedelta.__mul__

instance : PastaLean.PyHMul timedelta Int (PastaLean.ProofMode.PyProofM timedelta) where hMul := timedelta.__mul__

def timedelta.__floordiv__ := fun (self : timedelta) ↦ fun (other : Int) ↦
  timedelta.checked <| timedelta.ofParts (0 : Int) (0 : Int) (PastaLean.pyFloorDiv self._to_microseconds other)

attribute [simp] timedelta.__floordiv__

instance : PastaLean.PyFloorDiv timedelta Int (PastaLean.ProofMode.PyProofM timedelta) where floorDiv := timedelta.__floordiv__

def timedelta.__eq__ := fun (self : timedelta) ↦ fun (other : timedelta) ↦
  self._to_microseconds == other._to_microseconds

attribute [simp, taste_ingr] timedelta.__eq__

instance : BEq timedelta where beq := timedelta.__eq__

def timedelta.__lt__ := fun (self : timedelta) ↦ fun (other : timedelta) ↦
  decide (self._to_microseconds < other._to_microseconds)

attribute [simp, taste_ingr] timedelta.__lt__

instance : LT timedelta :=
  ⟨fun a b => timedelta.__lt__ a b = true⟩

instance : DecidableRel (α := timedelta) (· < ·) := fun a b =>
  inferInstanceAs (Decidable (timedelta.__lt__ a b = true))

instance : Ord timedelta :=
  ⟨fun a b => if timedelta.__lt__ a b then .lt else if timedelta.__lt__ b a then .gt else .eq⟩

def timedelta.__le__ := fun (self : timedelta) ↦ fun (other : timedelta) ↦
  decide (self._to_microseconds ≤ other._to_microseconds)

attribute [simp, taste_ingr] timedelta.__le__

instance : LE timedelta :=
  ⟨fun a b => timedelta.__le__ a b = true⟩

instance : DecidableRel (α := timedelta) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (timedelta.__le__ a b = true))

def timedelta.__hash__ := fun (self : timedelta) ↦ hash self._to_microseconds

attribute [simp, taste_ingr] timedelta.__hash__

instance : Hashable timedelta :=
  ⟨fun a => hash (timedelta.__hash__ a)⟩

def timedelta.__bool__ := fun (self : timedelta) ↦
  if PastaLean.pyTruthy (self._days != (0 : Int)) then self._days != (0 : Int)
  else
    if PastaLean.pyTruthy (self._seconds != (0 : Int)) then self._seconds != (0 : Int)
    else self._microseconds != (0 : Int)

attribute [simp, taste_ingr] timedelta.__bool__

instance : PastaLean.PyTruthy timedelta :=
  ⟨timedelta.__bool__⟩

instance : PastaLean.PyBool timedelta :=
  ⟨timedelta.__bool__⟩

instance : PastaLean.PyPrintable timedelta
    where
  pyStringify := fun (self : timedelta) ↦
    Id.run
      (do
        let p'_unpack_value_1 := PastaLean.pyDivmod self._seconds (60 : Int)
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut mm := Prod.fst p'_unpack_pair_1
        let mut ss := Prod.snd p'_unpack_pair_1
        let p'_unpack_value_2 := PastaLean.pyDivmod mm (60 : Int)
        let p'_unpack_pair_2 := p'_unpack_value_2
        let mut hh := Prod.fst p'_unpack_pair_2
        mm := Prod.snd p'_unpack_pair_2
        let mut s : String := PastaLean.pyStr hh +ₚ ":" +ₚ _pad mm (2 : Int) +ₚ ":" +ₚ _pad ss (2 : Int)
        if h_1 : PastaLean.pyTruthy self._days then 
          let mut plural : String := ""
          if h_2 : PastaLean.pyAbs self._days ≠ (1 : Int) then 
            plural := "s"
          s := PastaLean.pyStr self._days +ₚ " day" +ₚ plural +ₚ ", " +ₚ s
        if h_2 : PastaLean.pyTruthy self._microseconds then 
          s := s +ₚ "." +ₚ _pad self._microseconds (6 : Int)
        return s)
  pyReprify := fun (self : timedelta) ↦
    Id.run
      (do
        let mut args : List String := []
        if h_1 : PastaLean.pyTruthy self._days then 
          args := PastaLean.pyAppend args s! "days={self._days}"
        if h_2 : PastaLean.pyTruthy self._seconds then 
          args := PastaLean.pyAppend args s! "seconds={self._seconds}"
        if h_3 : PastaLean.pyTruthy self._microseconds then 
          args := PastaLean.pyAppend args s! "microseconds={self._microseconds}"
        if h_4 : ¬PastaLean.pyTruthy args = true then 
          args := PastaLean.pyAppend args "0"
        let p'_ret_1 := "datetime.timedelta(" +ₚ PastaLean.pyStringJoin ", " args +ₚ ")"
        return p'_ret_1)

/-- A duration, normalised to days, seconds (0..86399) and microseconds (0..999999). -/
structure timedelta'rn where
  _days : Int
  _seconds : Int
  _microseconds : Int
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy timedelta'rn where truthy _ := true

instance : PastaLean.PyBool timedelta'rn where pyBool _ := true

instance : PastaLean.PyTyped timedelta'rn where pyTypeOf _ := TypeInfer.PyType.cls "timedelta"

instance : Coe timedelta'rn (Option timedelta'rn) :=
  ⟨some⟩

/-- The normalising constructor without Python's magnitude check: for values in range by construction. -/
def timedelta'rn.ofParts (days : Int := (0 : Int)) (seconds : Int := (0 : Int)) (microseconds : Int := (0 : Int))
    (milliseconds : Int := (0 : Int)) (minutes : Int := (0 : Int)) (hours : Int := (0 : Int))
    (weeks : Int := (0 : Int)) : timedelta'rn :=
  Id.run
    (do
      let mut self : timedelta'rn := default
      let mut us : Int :=
        (((weeks *ₚ (7 : Int) +ₚ days) *ₚ (24 : Int) +ₚ hours) *ₚ (60 : Int) +ₚ minutes) *ₚ (60 : Int) +ₚ seconds
      us := us *ₚ (1000000 : Int) +ₚ milliseconds *ₚ (1000 : Int) +ₚ microseconds
      let p'_unpack_value_1 := PastaLean.pyDivmod us ((86400 : Int) *ₚ (1000000 : Int))
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut d := Prod.fst p'_unpack_pair_1
      let mut rest := Prod.snd p'_unpack_pair_1
      let p'_unpack_value_2 := PastaLean.pyDivmod rest (1000000 : Int)
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut s := Prod.fst p'_unpack_pair_2
      let mut usec := Prod.snd p'_unpack_pair_2
      self := { self with _days := d }
      self := { self with _seconds := s }
      self := { self with _microseconds := usec }
      return self)

/-- Python bounds a `timedelta` to 999999999 days either way (`OverflowError`). -/
def timedelta'rn.checked (t : timedelta'rn) : PastaLean.PyExcept timedelta'rn :=
  if t._days.natAbs > 999999999 then
    throw (PastaLean.PyException.Raise "OverflowError" s!"days={t._days}; must have magnitude <= 999999999")
  else pure t

/-- `timedelta(days, seconds, microseconds, milliseconds, minutes, hours, weeks)`. -/
def timedelta'rn.new (days : Int := 0) (seconds : Int := 0) (microseconds : Int := 0) (milliseconds : Int := 0)
    (minutes : Int := 0) (hours : Int := 0) (weeks : Int := 0) : PastaLean.PyExcept timedelta'rn :=
  timedelta'rn.checked (timedelta'rn.ofParts days seconds microseconds milliseconds minutes hours weeks)

def timedelta'rn.days := fun (self : timedelta'rn) ↦ self._days

def timedelta'rn.seconds := fun (self : timedelta'rn) ↦ self._seconds

def timedelta'rn.microseconds := fun (self : timedelta'rn) ↦ self._microseconds

def timedelta'rn._to_microseconds := fun (self : timedelta'rn) ↦
  (self._days *ₚ (86400 : Int) +ₚ self._seconds) *ₚ (1000000 : Int) +ₚ self._microseconds

def timedelta'rn.total_seconds := fun (self : timedelta'rn) ↦ PastaLean.pyTrueDiv self._to_microseconds (1000000 : Int)

def timedelta'rn.__add__ := fun (self : timedelta'rn) ↦ fun (other : timedelta'rn) ↦
  timedelta'rn.checked <| timedelta'rn.ofParts (self._days +ₚ other._days) (self._seconds +ₚ other._seconds)
    (self._microseconds +ₚ other._microseconds)

instance : PastaLean.PyHAdd timedelta'rn timedelta'rn (PastaLean.PyExcept timedelta'rn) where hAdd := timedelta'rn.__add__

def timedelta'rn.__sub__ := fun (self : timedelta'rn) ↦ fun (other : timedelta'rn) ↦
  timedelta'rn.checked <| timedelta'rn.ofParts (self._days -ₚ other._days) (self._seconds -ₚ other._seconds)
    (self._microseconds -ₚ other._microseconds)

instance : PastaLean.PyHSub timedelta'rn timedelta'rn (PastaLean.PyExcept timedelta'rn) where hSub := timedelta'rn.__sub__

def timedelta'rn.__neg__ := fun (self : timedelta'rn) ↦
  timedelta'rn.checked <| timedelta'rn.ofParts (-self._days) (-self._seconds) (-self._microseconds)

/-- Negation without the magnitude check, for the library's own in-range values; Python's `-td` calls
`timedelta'rn.__neg__` (TypeInfer stamps it), which raises. -/
instance : Neg timedelta'rn :=
  ⟨fun t => timedelta'rn.ofParts (-t._days) (-t._seconds) (-t._microseconds)⟩

def timedelta'rn.__abs__ := fun (self : timedelta'rn) ↦ if self._days < (0 : Int) then -self else self

instance : PastaLean.PyAbs timedelta'rn :=
  ⟨timedelta'rn.__abs__⟩

def timedelta'rn.__mul__ := fun (self : timedelta'rn) ↦ fun (other : Int) ↦
  timedelta'rn.checked <| timedelta'rn.ofParts (0 : Int) (0 : Int) (self._to_microseconds *ₚ other)

instance : PastaLean.PyHMul timedelta'rn Int (PastaLean.PyExcept timedelta'rn) where hMul := timedelta'rn.__mul__

def timedelta'rn.__floordiv__ := fun (self : timedelta'rn) ↦ fun (other : Int) ↦
  timedelta'rn.checked <| timedelta'rn.ofParts (0 : Int) (0 : Int) (PastaLean.pyFloorDiv self._to_microseconds other)

instance : PastaLean.PyFloorDiv timedelta'rn Int (PastaLean.PyExcept timedelta'rn) where floorDiv := timedelta'rn.__floordiv__

def timedelta'rn.__eq__ := fun (self : timedelta'rn) ↦ fun (other : timedelta'rn) ↦
  self._to_microseconds == other._to_microseconds

instance : BEq timedelta'rn where beq := timedelta'rn.__eq__

def timedelta'rn.__lt__ := fun (self : timedelta'rn) ↦ fun (other : timedelta'rn) ↦
  decide (self._to_microseconds < other._to_microseconds)

instance : LT timedelta'rn :=
  ⟨fun a b => timedelta'rn.__lt__ a b = true⟩

instance : DecidableRel (α := timedelta'rn) (· < ·) := fun a b =>
  inferInstanceAs (Decidable (timedelta'rn.__lt__ a b = true))

instance : Ord timedelta'rn :=
  ⟨fun a b => if timedelta'rn.__lt__ a b then .lt else if timedelta'rn.__lt__ b a then .gt else .eq⟩

def timedelta'rn.__le__ := fun (self : timedelta'rn) ↦ fun (other : timedelta'rn) ↦
  decide (self._to_microseconds ≤ other._to_microseconds)

instance : LE timedelta'rn :=
  ⟨fun a b => timedelta'rn.__le__ a b = true⟩

instance : DecidableRel (α := timedelta'rn) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (timedelta'rn.__le__ a b = true))

def timedelta'rn.__hash__ := fun (self : timedelta'rn) ↦ hash self._to_microseconds

instance : Hashable timedelta'rn :=
  ⟨fun a => hash (timedelta'rn.__hash__ a)⟩

def timedelta'rn.__bool__ := fun (self : timedelta'rn) ↦
  if PastaLean.pyTruthy (self._days != (0 : Int)) then self._days != (0 : Int)
  else
    if PastaLean.pyTruthy (self._seconds != (0 : Int)) then self._seconds != (0 : Int)
    else self._microseconds != (0 : Int)

instance : PastaLean.PyTruthy timedelta'rn :=
  ⟨timedelta'rn.__bool__⟩

instance : PastaLean.PyBool timedelta'rn :=
  ⟨timedelta'rn.__bool__⟩

instance : PastaLean.PyPrintable timedelta'rn
    where
  pyStringify := fun (self : timedelta'rn) ↦
    Id.run
      (do
        let p'_unpack_value_1 := PastaLean.pyDivmod self._seconds (60 : Int)
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut mm := Prod.fst p'_unpack_pair_1
        let mut ss := Prod.snd p'_unpack_pair_1
        let p'_unpack_value_2 := PastaLean.pyDivmod mm (60 : Int)
        let p'_unpack_pair_2 := p'_unpack_value_2
        let mut hh := Prod.fst p'_unpack_pair_2
        mm := Prod.snd p'_unpack_pair_2
        let mut s : String := PastaLean.pyStr hh +ₚ ":" +ₚ _pad'rn mm (2 : Int) +ₚ ":" +ₚ _pad'rn ss (2 : Int)
        if h_1 : PastaLean.pyTruthy self._days then 
          let mut plural : String := ""
          if h_2 : PastaLean.pyAbs self._days != (1 : Int) then 
            plural := "s"
          s := PastaLean.pyStr self._days +ₚ " day" +ₚ plural +ₚ ", " +ₚ s
        if h_2 : PastaLean.pyTruthy self._microseconds then 
          s := s +ₚ "." +ₚ _pad'rn self._microseconds (6 : Int)
        return s)
  pyReprify := fun (self : timedelta'rn) ↦
    Id.run
      (do
        let mut args : List String := []
        if h_1 : PastaLean.pyTruthy self._days then 
          args := PastaLean.pyAppend args s! "days={self._days}"
        if h_2 : PastaLean.pyTruthy self._seconds then 
          args := PastaLean.pyAppend args s! "seconds={self._seconds}"
        if h_3 : PastaLean.pyTruthy self._microseconds then 
          args := PastaLean.pyAppend args s! "microseconds={self._microseconds}"
        if h_4 : !PastaLean.pyTruthy args then 
          args := PastaLean.pyAppend args "0"
        let p'_ret_1 := "datetime.timedelta(" +ₚ PastaLean.pyStringJoin ", " args +ₚ ")"
        return p'_ret_1)

end Libraries.datetime
