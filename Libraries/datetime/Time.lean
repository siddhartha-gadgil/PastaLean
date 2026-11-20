import Libraries.datetime.Timezone
import Std.Tactic.Do

open PastaLean
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace Libraries.datetime

/-- A time of day, to the microsecond, optionally with a fixed-offset `timezone`. -/
structure time where
  _hour : Int
  _minute : Int
  _second : Int
  _microsecond : Int
  _tzinfo : Option timezone
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy time where truthy _ := true

instance : PastaLean.PyBool time where pyBool _ := true

instance : PastaLean.PyTyped time where pyTypeOf _ := TypeInfer.PyType.cls "time"

instance : Coe time (Option time) :=
  ⟨some⟩

def time.new (hour : Int := (0 : Int)) (minute : Int := (0 : Int)) (second : Int := (0 : Int))
    (microsecond : Int := (0 : Int)) (tzinfo : Option timezone := Option.none) : PastaLean.ProofMode.PyProofM time :=
  ((do
      let mut self : time := default
      let _ ← _check_time_fields hour minute second microsecond
      self := { self with _hour := hour }
      self := { self with _minute := minute }
      self := { self with _second := second }
      self := { self with _microsecond := microsecond }
      self := { self with _tzinfo := tzinfo }
      return self) :
    PastaLean.ProofMode.PyProofM time)

def time.fromisoformat := fun (s : String) ↦
  ((do
      if h_1 : PastaLean.pyLen s < (2 : Int) then 
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
      let mut hour : Int := (← _parse_digits s (0 : Int) (2 : Int))
      let mut minute : Int := (0 : Int)
      let mut second : Int := (0 : Int)
      let mut microsecond : Int := (0 : Int)
      if h_2 : PastaLean.pyLen s ≥ (5 : Int) then 
        minute := (← _parse_digits s (3 : Int) (2 : Int))
      if h_3 : PastaLean.pyLen s ≥ (8 : Int) then 
        second := (← _parse_digits s (6 : Int) (2 : Int))
      if h_4 : PastaLean.pyLen s > (9 : Int) then 
        let mut digits : Int := PastaLean.pyLen s -ₚ (9 : Int)
        if h_5 : digits ≠ (3 : Int) ∧ digits ≠ (6 : Int) then 
          throw
              (PastaLean.PyException.Raise "ValueError"
                (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
        microsecond := (← _parse_digits s (9 : Int) digits)
        if h_6 : digits = (3 : Int) then 
          microsecond := microsecond *ₚ (1000 : Int)
      let p'_ret_1 := (← time.new hour minute second microsecond)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] time.fromisoformat

def time.hour := fun (self : time) ↦ self._hour

attribute [simp, taste_ingr] time.hour

def time.minute := fun (self : time) ↦ self._minute

attribute [simp, taste_ingr] time.minute

def time.second := fun (self : time) ↦ self._second

attribute [simp, taste_ingr] time.second

def time.microsecond := fun (self : time) ↦ self._microsecond

attribute [simp, taste_ingr] time.microsecond

def time.tzinfo := fun (self : time) ↦ (show Option timezone from self._tzinfo)

attribute [simp, taste_ingr] time.tzinfo

def time.utcoffset := fun (self : time) ↦
  (show Option timedelta from
    Id.run
      (do
        let mut tz : Option timezone := self._tzinfo
        if let some tz'rb0 := tz then 
          let p'_ret_1 := tz'rb0.utcoffset
          return p'_ret_1
        return Option.none))

attribute [simp, taste_ingr] time.utcoffset

def time._to_microseconds := fun (self : time) ↦
  ((self._hour *ₚ (60 : Int) +ₚ self._minute) *ₚ (60 : Int) +ₚ self._second) *ₚ (1000000 : Int) +ₚ self._microsecond -ₚ
    _offset_of self._tzinfo

attribute [simp, taste_ingr] time._to_microseconds

def time.isoformat (self : time) (timespec : String := "auto") :=
  ((do
      let p'_ret_1 :=
        (← _format_time self._hour self._minute self._second self._microsecond timespec) +ₚ _tz_suffix self._tzinfo ":"
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] time.isoformat

def time.strftime := fun (self : time) ↦ fun (fmt : String) ↦
  _strftime fmt (1900 : Int) (1 : Int) (1 : Int) self._hour self._minute self._second self._microsecond (0 : Int)
    (1 : Int)

attribute [simp, taste_ingr] time.strftime

def time.replace (self : time) (hour : Int := -(1 : Int)) (minute : Int := -(1 : Int)) (second : Int := -(1 : Int))
    (microsecond : Int := -(1 : Int)) :=
  ((do
      if h_1 : hour = -(1 : Int) then 
        let mut hour : Int := self._hour
      if h_2 : minute = -(1 : Int) then 
        let mut minute : Int := self._minute
      if h_3 : second = -(1 : Int) then 
        let mut second : Int := self._second
      if h_4 : microsecond = -(1 : Int) then 
        let mut microsecond : Int := self._microsecond
      let p'_ret_1 := (← time.new hour minute second microsecond self._tzinfo)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] time.replace

def time.__eq__ := fun (self : time) ↦ fun (other : time) ↦
  if PastaLean.pyIsNone self._tzinfo ≠ PastaLean.pyIsNone other._tzinfo then Bool.false
  else self._to_microseconds == other._to_microseconds

attribute [simp, taste_ingr] time.__eq__

instance : BEq time where beq := time.__eq__

/-- Python refuses to order an offset-naive against an offset-aware value (`TypeError`). -/
def time.__lt__ (self other : time) : PastaLean.ProofMode.PyProofM Bool := do
  _same_awareness self._tzinfo other._tzinfo
  return decide (self._to_microseconds < other._to_microseconds)


instance : LT time :=
  ⟨fun a b => PastaLean.runPure (time.__lt__ a b) = true⟩

instance : DecidableRel (α := time) (· < ·) := fun a b => inferInstanceAs (Decidable (PastaLean.runPure (time.__lt__ a b) = true))

instance : Ord time :=
  ⟨fun a b => if PastaLean.runPure (time.__lt__ a b) then .lt
    else if PastaLean.runPure (time.__lt__ b a) then .gt else .eq⟩

/-- Python refuses to order an offset-naive against an offset-aware value (`TypeError`). -/
def time.__le__ (self other : time) : PastaLean.ProofMode.PyProofM Bool := do
  _same_awareness self._tzinfo other._tzinfo
  return decide (self._to_microseconds ≤ other._to_microseconds)


instance : LE time :=
  ⟨fun a b => PastaLean.runPure (time.__le__ a b) = true⟩

instance : DecidableRel (α := time) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (PastaLean.runPure (time.__le__ a b) = true))

def time.__hash__ := fun (self : time) ↦ hash self._to_microseconds

attribute [simp, taste_ingr] time.__hash__

instance : Hashable time :=
  ⟨fun a => hash (time.__hash__ a)⟩

def time.__bool__ := fun (self : time) ↦ Bool.true

attribute [simp, taste_ingr] time.__bool__

instance : PastaLean.PyTruthy time :=
  ⟨time.__bool__⟩

instance : PastaLean.PyBool time :=
  ⟨time.__bool__⟩

instance : PastaLean.PyPrintable time
    where
  pyStringify := fun (self : time) ↦
    _format_time_auto self._hour self._minute self._second self._microsecond +ₚ _tz_suffix self._tzinfo ":"
  pyReprify := fun (self : time) ↦
    Id.run
      (do
        let mut parts : List String := [PastaLean.pyStr self._hour, PastaLean.pyStr self._minute]
        if h_1 : PastaLean.pyTruthy self._second = true ∨ PastaLean.pyTruthy self._microsecond = true then 
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._second)
        if h_2 : PastaLean.pyTruthy self._microsecond then 
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._microsecond)
        let mut r : String := "datetime.time(" +ₚ PastaLean.pyStringJoin ", " parts
        let mut tz : Option timezone := self._tzinfo
        if let some tz'rb1 := tz then 
          r := r +ₚ ", tzinfo=" +ₚ PastaLean.PyPrintable.pyReprify tz'rb1
        let p'_ret_1 := r +ₚ ")"
        return p'_ret_1)

/-- A time of day, to the microsecond, optionally with a fixed-offset `timezone`. -/
structure time'rn where
  _hour : Int
  _minute : Int
  _second : Int
  _microsecond : Int
  _tzinfo : Option timezone'rn
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy time'rn where truthy _ := true

instance : PastaLean.PyBool time'rn where pyBool _ := true

instance : PastaLean.PyTyped time'rn where pyTypeOf _ := TypeInfer.PyType.cls "time"

instance : Coe time'rn (Option time'rn) :=
  ⟨some⟩

def time'rn.new (hour : Int := (0 : Int)) (minute : Int := (0 : Int)) (second : Int := (0 : Int))
    (microsecond : Int := (0 : Int)) (tzinfo : Option timezone'rn := Option.none) : PastaLean.PyExcept time'rn :=
  ((do
      let mut self : time'rn := default
      let _ ← _check_time_fields'rn hour minute second microsecond
      self := { self with _hour := hour }
      self := { self with _minute := minute }
      self := { self with _second := second }
      self := { self with _microsecond := microsecond }
      self := { self with _tzinfo := tzinfo }
      return self) :
    PastaLean.PyExcept time'rn)

def time'rn.fromisoformat := fun (s : String) ↦
  ((do
      if h_1 : PastaLean.pyLen s < (2 : Int) then 
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
      let mut hour : Int := (← _parse_digits'rn s (0 : Int) (2 : Int))
      let mut minute : Int := (0 : Int)
      let mut second : Int := (0 : Int)
      let mut microsecond : Int := (0 : Int)
      if h_2 : PastaLean.pyLen s ≥ (5 : Int) then 
        minute := (← _parse_digits'rn s (3 : Int) (2 : Int))
      if h_3 : PastaLean.pyLen s ≥ (8 : Int) then 
        second := (← _parse_digits'rn s (6 : Int) (2 : Int))
      if h_4 : PastaLean.pyLen s > (9 : Int) then 
        let mut digits : Int := PastaLean.pyLen s -ₚ (9 : Int)
        if h_5 : digits != (3 : Int) && digits != (6 : Int) then 
          throw
              (PastaLean.PyException.Raise "ValueError"
                (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
        microsecond := (← _parse_digits'rn s (9 : Int) digits)
        if h_6 : digits == (3 : Int) then 
          microsecond := microsecond *ₚ (1000 : Int)
      let p'_ret_1 := (← time'rn.new hour minute second microsecond)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def time'rn.hour := fun (self : time'rn) ↦ self._hour

def time'rn.minute := fun (self : time'rn) ↦ self._minute

def time'rn.second := fun (self : time'rn) ↦ self._second

def time'rn.microsecond := fun (self : time'rn) ↦ self._microsecond

def time'rn.tzinfo := fun (self : time'rn) ↦ (show Option timezone'rn from self._tzinfo)

def time'rn.utcoffset := fun (self : time'rn) ↦
  (show Option timedelta'rn from
    Id.run
      (do
        let mut tz : Option timezone'rn := self._tzinfo
        if let some tz'rb0 := tz then 
          let p'_ret_1 := tz'rb0.utcoffset
          return p'_ret_1
        return Option.none))

def time'rn._to_microseconds := fun (self : time'rn) ↦
  ((self._hour *ₚ (60 : Int) +ₚ self._minute) *ₚ (60 : Int) +ₚ self._second) *ₚ (1000000 : Int) +ₚ self._microsecond -ₚ
    _offset_of'rn self._tzinfo

def time'rn.isoformat (self : time'rn) (timespec : String := "auto") :=
  ((do
      let p'_ret_1 :=
        (← _format_time'rn self._hour self._minute self._second self._microsecond timespec) +ₚ
          _tz_suffix'rn self._tzinfo ":"
      return p'_ret_1) :
    PastaLean.PyExcept _)

def time'rn.strftime := fun (self : time'rn) ↦ fun (fmt : String) ↦
  _strftime'rn fmt (1900 : Int) (1 : Int) (1 : Int) self._hour self._minute self._second self._microsecond (0 : Int)
    (1 : Int)

def time'rn.replace (self : time'rn) (hour : Int := -(1 : Int)) (minute : Int := -(1 : Int))
    (second : Int := -(1 : Int)) (microsecond : Int := -(1 : Int)) :=
  ((do
      if h_1 : hour == -(1 : Int) then 
        let mut hour : Int := self._hour
      if h_2 : minute == -(1 : Int) then 
        let mut minute : Int := self._minute
      if h_3 : second == -(1 : Int) then 
        let mut second : Int := self._second
      if h_4 : microsecond == -(1 : Int) then 
        let mut microsecond : Int := self._microsecond
      let p'_ret_1 := (← time'rn.new hour minute second microsecond self._tzinfo)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def time'rn.__eq__ := fun (self : time'rn) ↦ fun (other : time'rn) ↦
  if PastaLean.pyIsNone self._tzinfo != PastaLean.pyIsNone other._tzinfo then Bool.false
  else self._to_microseconds == other._to_microseconds

instance : BEq time'rn where beq := time'rn.__eq__

/-- Python refuses to order an offset-naive against an offset-aware value (`TypeError`). -/
def time'rn.__lt__ (self other : time'rn) : PastaLean.PyExcept Bool := do
  _same_awareness'rn self._tzinfo other._tzinfo
  return decide (self._to_microseconds < other._to_microseconds)

instance : LT time'rn :=
  ⟨fun a b => PastaLean.runPure (time'rn.__lt__ a b) = true⟩

instance : DecidableRel (α := time'rn) (· < ·) := fun a b => inferInstanceAs (Decidable (PastaLean.runPure (time'rn.__lt__ a b) = true))

instance : Ord time'rn :=
  ⟨fun a b => if PastaLean.runPure (time'rn.__lt__ a b) then .lt
    else if PastaLean.runPure (time'rn.__lt__ b a) then .gt else .eq⟩

/-- Python refuses to order an offset-naive against an offset-aware value (`TypeError`). -/
def time'rn.__le__ (self other : time'rn) : PastaLean.PyExcept Bool := do
  _same_awareness'rn self._tzinfo other._tzinfo
  return decide (self._to_microseconds ≤ other._to_microseconds)

instance : LE time'rn :=
  ⟨fun a b => PastaLean.runPure (time'rn.__le__ a b) = true⟩

instance : DecidableRel (α := time'rn) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (PastaLean.runPure (time'rn.__le__ a b) = true))

def time'rn.__hash__ := fun (self : time'rn) ↦ hash self._to_microseconds

instance : Hashable time'rn :=
  ⟨fun a => hash (time'rn.__hash__ a)⟩

def time'rn.__bool__ := fun (self : time'rn) ↦ Bool.true

instance : PastaLean.PyTruthy time'rn :=
  ⟨time'rn.__bool__⟩

instance : PastaLean.PyBool time'rn :=
  ⟨time'rn.__bool__⟩

instance : PastaLean.PyPrintable time'rn
    where
  pyStringify := fun (self : time'rn) ↦
    _format_time_auto'rn self._hour self._minute self._second self._microsecond +ₚ _tz_suffix'rn self._tzinfo ":"
  pyReprify := fun (self : time'rn) ↦
    Id.run
      (do
        let mut parts : List String := [PastaLean.pyStr self._hour, PastaLean.pyStr self._minute]
        if h_1 : PastaLean.pyTruthy self._second || PastaLean.pyTruthy self._microsecond then 
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._second)
        if h_2 : PastaLean.pyTruthy self._microsecond then 
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._microsecond)
        let mut r : String := "datetime.time(" +ₚ PastaLean.pyStringJoin ", " parts
        let mut tz : Option timezone'rn := self._tzinfo
        if let some tz'rb1 := tz then 
          r := r +ₚ ", tzinfo=" +ₚ PastaLean.PyPrintable.pyReprify tz'rb1
        let p'_ret_1 := r +ₚ ")"
        return p'_ret_1)

end Libraries.datetime
