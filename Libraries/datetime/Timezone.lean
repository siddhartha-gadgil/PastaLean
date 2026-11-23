import Libraries.datetime.Date
import Std.Tactic.Do

open PastaLean
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace Libraries.datetime

def _format_offset := fun (off : timedelta) ↦ fun (sep : String) ↦
  Id.run
    (do
      let mut off := off
      let mut sign : String := "+"
      if h_1 : off.days < (0 : Int) then 
        sign := "-"
        off := -off
      let p'_unpack_value_1 := PastaLean.pyDivmod off.seconds (3600 : Int)
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut hh := Prod.fst p'_unpack_pair_1
      let mut rest := Prod.snd p'_unpack_pair_1
      let p'_unpack_value_2 := PastaLean.pyDivmod rest (60 : Int)
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut mm := Prod.fst p'_unpack_pair_2
      let mut ss := Prod.snd p'_unpack_pair_2
      let mut s : String := sign +ₚ _pad hh (2 : Int) +ₚ sep +ₚ _pad mm (2 : Int)
      if h_2 : PastaLean.pyTruthy ss = true ∨ PastaLean.pyTruthy off.microseconds = true then 
        s := s +ₚ sep +ₚ _pad ss (2 : Int)
        if h_3 : PastaLean.pyTruthy off.microseconds then 
          s := s +ₚ "." +ₚ _pad off.microseconds (6 : Int)
      return s)

attribute [simp, taste_ingr] _format_offset

def _format_offset'rn := fun (off : timedelta'rn) ↦ fun (sep : String) ↦
  Id.run
    (do
      let mut off := off
      let mut sign : String := "+"
      if h_1 : off.days < (0 : Int) then 
        sign := "-"
        off := -off
      let p'_unpack_value_1 := PastaLean.pyDivmod off.seconds (3600 : Int)
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut hh := Prod.fst p'_unpack_pair_1
      let mut rest := Prod.snd p'_unpack_pair_1
      let p'_unpack_value_2 := PastaLean.pyDivmod rest (60 : Int)
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut mm := Prod.fst p'_unpack_pair_2
      let mut ss := Prod.snd p'_unpack_pair_2
      let mut s : String := sign +ₚ _pad'rn hh (2 : Int) +ₚ sep +ₚ _pad'rn mm (2 : Int)
      if h_2 : PastaLean.pyTruthy ss || PastaLean.pyTruthy off.microseconds then 
        s := s +ₚ sep +ₚ _pad'rn ss (2 : Int)
        if h_3 : PastaLean.pyTruthy off.microseconds then 
          s := s +ₚ "." +ₚ _pad'rn off.microseconds (6 : Int)
      return s)

/-- A fixed UTC offset (strictly between -24h and +24h), optionally named. -/
structure timezone where
  _offset : timedelta
  _name : String
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy timezone where truthy _ := true

instance : PastaLean.PyBool timezone where pyBool _ := true

instance : PastaLean.PyTyped timezone where pyTypeOf _ := TypeInfer.PyType.cls "timezone"

instance : Coe timezone (Option timezone) :=
  ⟨some⟩

def timezone.new (offset : timedelta) (name : String := "") : PastaLean.ProofMode.PyProofM timezone :=
  ((do
      let mut self : timezone := default
      if h_1 : ¬(-timedelta.ofParts (hours := (24 : Int)) < offset ∧ offset < timedelta.ofParts (hours := (24 : Int))) then 
        throw
            (PastaLean.PyException.Raise "ValueError"
              ("offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24), not "
                ++ PastaLean.PyPrintable.pyReprify offset))
      self := { self with _offset := offset }
      self := { self with _name := name }
      return self) :
    PastaLean.ProofMode.PyProofM timezone)

def timezone.utcoffset := fun (self : timezone) ↦ self._offset

attribute [simp, taste_ingr] timezone.utcoffset

def timezone.tzname := fun (self : timezone) ↦
  if self._name ≠ "" then self._name
  else if ¬PastaLean.pyTruthy self._offset = true then "UTC" else "UTC" +ₚ _format_offset self._offset ":"

attribute [simp, taste_ingr] timezone.tzname

def timezone.__eq__ := fun (self : timezone) ↦ fun (other : timezone) ↦ self._offset == other._offset

attribute [simp, taste_ingr] timezone.__eq__

instance : BEq timezone where beq := timezone.__eq__

def timezone.__hash__ := fun (self : timezone) ↦ hash self._offset

attribute [simp, taste_ingr] timezone.__hash__

instance : Hashable timezone :=
  ⟨fun a => hash (timezone.__hash__ a)⟩

instance : PastaLean.PyPrintable timezone
    where
  pyStringify := fun (self : timezone) ↦ self.tzname
  pyReprify := fun (self : timezone) ↦
    if ¬PastaLean.pyTruthy self._offset = true ∧ self._name = "" then "datetime.timezone.utc"
    else
      if self._name = "" then s! "datetime.timezone({PastaLean.PyPrintable.pyReprify self._offset})"
      else
        s!"datetime.timezone({(PastaLean.PyPrintable.pyReprify
            self._offset)}, {PastaLean.PyPrintable.pyReprify self._name})"

/-- A fixed UTC offset (strictly between -24h and +24h), optionally named. -/
structure timezone'rn where
  _offset : timedelta'rn
  _name : String
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy timezone'rn where truthy _ := true

instance : PastaLean.PyBool timezone'rn where pyBool _ := true

instance : PastaLean.PyTyped timezone'rn where pyTypeOf _ := TypeInfer.PyType.cls "timezone"

instance : Coe timezone'rn (Option timezone'rn) :=
  ⟨some⟩

def timezone'rn.new (offset : timedelta'rn) (name : String := "") : PastaLean.PyExcept timezone'rn :=
  ((do
      let mut self : timezone'rn := default
      if h_1 :
          !(decide (-timedelta'rn.ofParts (hours := (24 : Int)) < offset) &&
              decide (offset < timedelta'rn.ofParts (hours := (24 : Int)))) then
        
        throw
            (PastaLean.PyException.Raise "ValueError"
              ("offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24), not "
                ++ PastaLean.PyPrintable.pyReprify offset))
      self := { self with _offset := offset }
      self := { self with _name := name }
      return self) :
    PastaLean.PyExcept timezone'rn)

def timezone'rn.utcoffset := fun (self : timezone'rn) ↦ self._offset

def timezone'rn.tzname := fun (self : timezone'rn) ↦
  if self._name != "" then self._name
  else if !PastaLean.pyTruthy self._offset then "UTC" else "UTC" +ₚ _format_offset'rn self._offset ":"

def timezone'rn.__eq__ := fun (self : timezone'rn) ↦ fun (other : timezone'rn) ↦ self._offset == other._offset

instance : BEq timezone'rn where beq := timezone'rn.__eq__

def timezone'rn.__hash__ := fun (self : timezone'rn) ↦ hash self._offset

instance : Hashable timezone'rn :=
  ⟨fun a => hash (timezone'rn.__hash__ a)⟩

instance : PastaLean.PyPrintable timezone'rn
    where
  pyStringify := fun (self : timezone'rn) ↦ self.tzname
  pyReprify := fun (self : timezone'rn) ↦
    if !PastaLean.pyTruthy self._offset && self._name == "" then "datetime.timezone.utc"
    else
      if self._name == "" then s! "datetime.timezone({PastaLean.PyPrintable.pyReprify self._offset})"
      else
        s!"datetime.timezone({(PastaLean.PyPrintable.pyReprify
            self._offset)}, {PastaLean.PyPrintable.pyReprify self._name})"

def _offset_of := fun (tz : Option timezone) ↦
  Id.run
    (do
      if let some tz := tz then 
        let p'_ret_1 := tz.utcoffset._to_microseconds
        return p'_ret_1
      return (0 : Int))

attribute [simp, taste_ingr] _offset_of

def _offset_of'rn := fun (tz : Option timezone'rn) ↦
  Id.run
    (do
      if let some tz := tz then 
        let p'_ret_1 := tz.utcoffset._to_microseconds
        return p'_ret_1
      return (0 : Int))

def _tz_suffix := fun (tz : Option timezone) ↦ fun (sep : String) ↦
  Id.run
    (do
      if let some tz := tz then 
        let p'_ret_1 := _format_offset tz.utcoffset sep
        return p'_ret_1
      return "")

attribute [simp, taste_ingr] _tz_suffix

def _tz_suffix'rn := fun (tz : Option timezone'rn) ↦ fun (sep : String) ↦
  Id.run
    (do
      if let some tz := tz then 
        let p'_ret_1 := _format_offset'rn tz.utcoffset sep
        return p'_ret_1
      return "")

def _same_awareness : Option timezone → Option timezone → PastaLean.ProofMode.PyProofM Unit :=
  fun (a : Option timezone) ↦ fun (b : Option timezone) ↦ do
  if h_1 : PastaLean.pyIsNone a ≠ PastaLean.pyIsNone b then 
    throw
        (PastaLean.PyException.Raise "TypeError"
          (ToString.toString "can't compare offset-naive and offset-aware datetimes"))

attribute [simp] _same_awareness

def _same_awareness'rn : Option timezone'rn → Option timezone'rn → PastaLean.PyExcept Unit :=
  fun (a : Option timezone'rn) ↦ fun (b : Option timezone'rn) ↦ do
  if h_1 : PastaLean.pyIsNone a != PastaLean.pyIsNone b then 
    throw
        (PastaLean.PyException.Raise "TypeError"
          (ToString.toString "can't compare offset-naive and offset-aware datetimes"))

end Libraries.datetime
