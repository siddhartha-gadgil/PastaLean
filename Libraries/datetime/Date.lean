import Libraries.datetime.Timedelta
import Std.Tactic.Do

open PastaLean
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace Libraries.datetime

/-- A proleptic Gregorian calendar date. -/
structure date where
  _year : Int
  _month : Int
  _day : Int
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy date where truthy _ := true

instance : PastaLean.PyBool date where pyBool _ := true

instance : PastaLean.PyTyped date where pyTypeOf _ := TypeInfer.PyType.cls "date"

instance : Coe date (Option date) :=
  ⟨some⟩

def date.new : Int → Int → Int → PastaLean.ProofMode.PyProofM date := fun (year : Int) ↦ fun (month : Int) ↦
  fun (day : Int) ↦
  ((do
      let mut self : date := default
      let _ ← _check_date_fields year month day
      self := { self with _year := year }
      self := { self with _month := month }
      self := { self with _day := day }
      return self) :
    PastaLean.ProofMode.PyProofM date)

def date.fromordinal := fun (n : Int) ↦
  ((do
      let p'_unpack_value_1 := _ord2ymd n
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut y : Int := Prod.fst p'_unpack_pair_1
      let mut m : Int := Prod.fst (Prod.snd p'_unpack_pair_1)
      let mut d : Int := Prod.snd (Prod.snd p'_unpack_pair_1)
      let p'_ret_1 := (← date.new y m d)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] date.fromordinal

def date.today :=
  ((do
      let p'_ret_1 := (← date.fromordinal (PastaLean.pyFloorDiv (← _now_local_us) (86400000000 : Int)))
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

def date.fromisoformat := fun (date_string : String) ↦
  ((do
      if h_1 :
          (PastaLean.pyLen date_string = (10 : Int) ∧ date_string⦋(4 : Int)⦌ = "-") ∧ date_string⦋(7 : Int)⦌ = "-" then 
        let p'_ret_1 :=
          (←
            date.new (← _parse_digits date_string (0 : Int) (4 : Int)) (← _parse_digits date_string (5 : Int) (2 : Int))
              (← _parse_digits date_string (8 : Int) (2 : Int)))
        return p'_ret_1
      if h_2 : PastaLean.pyLen date_string = (8 : Int) then 
        let p'_ret_1 :=
          (←
            date.new (← _parse_digits date_string (0 : Int) (4 : Int)) (← _parse_digits date_string (4 : Int) (2 : Int))
              (← _parse_digits date_string (6 : Int) (2 : Int)))
        return p'_ret_1
      throw
          (PastaLean.PyException.Raise "ValueError"
            (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify date_string}"))) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] date.fromisoformat

def date.year := fun (self : date) ↦ self._year

attribute [simp, taste_ingr] date.year

def date.month := fun (self : date) ↦ self._month

attribute [simp, taste_ingr] date.month

def date.day := fun (self : date) ↦ self._day

attribute [simp, taste_ingr] date.day

def date.toordinal := fun (self : date) ↦ _ymd2ord self._year self._month self._day

attribute [simp, taste_ingr] date.toordinal

def date.weekday := fun (self : date) ↦ (self.toordinal +ₚ (6 : Int)) %ₚ (7 : Int)

attribute [simp, taste_ingr] date.weekday

def date.isoweekday := fun (self : date) ↦
  if PastaLean.pyTruthy (self.toordinal %ₚ (7 : Int)) then self.toordinal %ₚ (7 : Int) else (7 : Int)

attribute [simp, taste_ingr] date.isoweekday

def date.isoformat := fun (self : date) ↦
  _pad self._year (4 : Int) +ₚ "-" +ₚ _pad self._month (2 : Int) +ₚ "-" +ₚ _pad self._day (2 : Int)

attribute [simp, taste_ingr] date.isoformat

def date.strftime := fun (self : date) ↦ fun (fmt : String) ↦
  let yday := (self.toordinal -ₚ _ymd2ord self._year (1 : Int) (1 : Int) +ₚ (1 : Int) : Int)
  _strftime fmt self._year self._month self._day (0 : Int) (0 : Int) (0 : Int) (0 : Int) self.weekday yday

attribute [simp, taste_ingr] date.strftime

def date.ctime := fun (self : date) ↦
  Id.run
    (do
      let mut day : String := PastaLean.pyStr self._day
      if h_1 : self._day < (10 : Int) then 
        day := " " +ₚ day
      let p'_ret_1 := self.strftime "%a %b " +ₚ day +ₚ " 00:00:00 " +ₚ _pad self._year (4 : Int)
      return p'_ret_1)

attribute [simp, taste_ingr] date.ctime

def date.replace (self : date) (year : Int := -(1 : Int)) (month : Int := -(1 : Int)) (day : Int := -(1 : Int)) :=
  ((do
      if h_1 : year = -(1 : Int) then 
        let mut year : Int := self._year
      if h_2 : month = -(1 : Int) then 
        let mut month : Int := self._month
      if h_3 : day = -(1 : Int) then 
        let mut day : Int := self._day
      let p'_ret_1 := (← date.new year month day)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] date.replace

def date.__add__ := fun (self : date) ↦ fun (other : timedelta) ↦
  ((do
      let mut o := self.toordinal +ₚ other.days
      if h_1 : (0 : Int) < o ∧ o ≤ _ymd2ord MAXYEAR (12 : Int) (31 : Int) then 
        let p'_ret_1 := (← date.fromordinal o)
        return p'_ret_1
      throw (PastaLean.PyException.Raise "OverflowError" (ToString.toString "date value out of range"))) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] date.__add__

instance : PastaLean.PyHAdd date timedelta (PastaLean.ProofMode.PyProofM date) where hAdd := date.__add__

def date.__sub__'timedelta := fun (self : date) ↦ fun (other : timedelta) ↦
  ((do
      let p'_ret_1 := (← self +ₚ timedelta.ofParts (-other.days))
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] date.__sub__'timedelta

instance : PastaLean.PyHSub date timedelta (PastaLean.ProofMode.PyProofM date) where hSub := date.__sub__'timedelta

def date.__sub__'date := fun (self : date) ↦ fun (other : date) ↦
  let days1 := (self.toordinal : Int)
  let days2 := (other.toordinal : Int)
  timedelta.ofParts (days1 -ₚ days2)

attribute [simp, taste_ingr] date.__sub__'date

instance : PastaLean.PyHSub date date timedelta where hSub := date.__sub__'date

def date.__eq__ := fun (self : date) ↦ fun (other : date) ↦ self.toordinal == other.toordinal

attribute [simp, taste_ingr] date.__eq__

instance : BEq date where beq := date.__eq__

def date.__lt__ := fun (self : date) ↦ fun (other : date) ↦ decide (self.toordinal < other.toordinal)

attribute [simp, taste_ingr] date.__lt__

instance : LT date :=
  ⟨fun a b => date.__lt__ a b = true⟩

instance : DecidableRel (α := date) (· < ·) := fun a b => inferInstanceAs (Decidable (date.__lt__ a b = true))

instance : Ord date :=
  ⟨fun a b => if date.__lt__ a b then .lt else if date.__lt__ b a then .gt else .eq⟩

def date.__le__ := fun (self : date) ↦ fun (other : date) ↦ decide (self.toordinal ≤ other.toordinal)

attribute [simp, taste_ingr] date.__le__

instance : LE date :=
  ⟨fun a b => date.__le__ a b = true⟩

instance : DecidableRel (α := date) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (date.__le__ a b = true))

def date.__hash__ := fun (self : date) ↦ hash self.toordinal

attribute [simp, taste_ingr] date.__hash__

instance : Hashable date :=
  ⟨fun a => hash (date.__hash__ a)⟩

instance : PastaLean.PyPrintable date
    where
  pyStringify := fun (self : date) ↦ self.isoformat
  pyReprify := fun (self : date) ↦ s! "datetime.date({self._year }, {self._month }, {self._day})"

/-- A proleptic Gregorian calendar date. -/
structure date'rn where
  _year : Int
  _month : Int
  _day : Int
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy date'rn where truthy _ := true

instance : PastaLean.PyBool date'rn where pyBool _ := true

instance : PastaLean.PyTyped date'rn where pyTypeOf _ := TypeInfer.PyType.cls "date"

instance : Coe date'rn (Option date'rn) :=
  ⟨some⟩

def date'rn.new : Int → Int → Int → PastaLean.PyExcept date'rn := fun (year : Int) ↦ fun (month : Int) ↦
  fun (day : Int) ↦
  ((do
      let mut self : date'rn := default
      let _ ← _check_date_fields'rn year month day
      self := { self with _year := year }
      self := { self with _month := month }
      self := { self with _day := day }
      return self) :
    PastaLean.PyExcept date'rn)

def date'rn.fromordinal := fun (n : Int) ↦
  ((do
      let p'_unpack_value_1 := _ord2ymd'rn n
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut y : Int := Prod.fst p'_unpack_pair_1
      let mut m : Int := Prod.fst (Prod.snd p'_unpack_pair_1)
      let mut d : Int := Prod.snd (Prod.snd p'_unpack_pair_1)
      let p'_ret_1 := (← date'rn.new y m d)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def date'rn.today :=
  ((do
      let p'_ret_1 := (← date'rn.fromordinal (PastaLean.pyFloorDiv (← _now_local_us'rn) (86400000000 : Int)))
      return p'_ret_1) :
    PastaLean.PyExcept _)

def date'rn.fromisoformat := fun (date_string : String) ↦
  ((do
      if h_1 :
          PastaLean.pyLen date_string == (10 : Int) && date_string⦋(4 : Int)⦌ == "-" &&
            date_string⦋(7 : Int)⦌ == "-" then
        
        let p'_ret_1 :=
          (←
            date'rn.new (← _parse_digits'rn date_string (0 : Int) (4 : Int))
              (← _parse_digits'rn date_string (5 : Int) (2 : Int)) (← _parse_digits'rn date_string (8 : Int) (2 : Int)))
        return p'_ret_1
      if h_2 : PastaLean.pyLen date_string == (8 : Int) then 
        let p'_ret_1 :=
          (←
            date'rn.new (← _parse_digits'rn date_string (0 : Int) (4 : Int))
              (← _parse_digits'rn date_string (4 : Int) (2 : Int)) (← _parse_digits'rn date_string (6 : Int) (2 : Int)))
        return p'_ret_1
      throw
          (PastaLean.PyException.Raise "ValueError"
            (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify date_string}"))) :
    PastaLean.PyExcept _)

def date'rn.year := fun (self : date'rn) ↦ self._year

def date'rn.month := fun (self : date'rn) ↦ self._month

def date'rn.day := fun (self : date'rn) ↦ self._day

def date'rn.toordinal := fun (self : date'rn) ↦ _ymd2ord'rn self._year self._month self._day

def date'rn.weekday := fun (self : date'rn) ↦ (self.toordinal +ₚ (6 : Int)) %ₚ (7 : Int)

def date'rn.isoweekday := fun (self : date'rn) ↦
  if PastaLean.pyTruthy (self.toordinal %ₚ (7 : Int)) then self.toordinal %ₚ (7 : Int) else (7 : Int)

def date'rn.isoformat := fun (self : date'rn) ↦
  _pad'rn self._year (4 : Int) +ₚ "-" +ₚ _pad'rn self._month (2 : Int) +ₚ "-" +ₚ _pad'rn self._day (2 : Int)

def date'rn.strftime := fun (self : date'rn) ↦ fun (fmt : String) ↦
  let yday := (self.toordinal -ₚ _ymd2ord'rn self._year (1 : Int) (1 : Int) +ₚ (1 : Int) : Int)
  _strftime'rn fmt self._year self._month self._day (0 : Int) (0 : Int) (0 : Int) (0 : Int) self.weekday yday

def date'rn.ctime := fun (self : date'rn) ↦
  Id.run
    (do
      let mut day : String := PastaLean.pyStr self._day
      if h_1 : self._day < (10 : Int) then 
        day := " " +ₚ day
      let p'_ret_1 := self.strftime "%a %b " +ₚ day +ₚ " 00:00:00 " +ₚ _pad'rn self._year (4 : Int)
      return p'_ret_1)

def date'rn.replace (self : date'rn) (year : Int := -(1 : Int)) (month : Int := -(1 : Int)) (day : Int := -(1 : Int)) :=
  ((do
      if h_1 : year == -(1 : Int) then 
        let mut year : Int := self._year
      if h_2 : month == -(1 : Int) then 
        let mut month : Int := self._month
      if h_3 : day == -(1 : Int) then 
        let mut day : Int := self._day
      let p'_ret_1 := (← date'rn.new year month day)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def date'rn.__add__ := fun (self : date'rn) ↦ fun (other : timedelta'rn) ↦
  ((do
      let mut o := self.toordinal +ₚ other.days
      if h_1 : decide ((0 : Int) < o) && decide (o ≤ _ymd2ord'rn MAXYEAR (12 : Int) (31 : Int)) then 
        let p'_ret_1 := (← date'rn.fromordinal o)
        return p'_ret_1
      throw (PastaLean.PyException.Raise "OverflowError" (ToString.toString "date value out of range"))) :
    PastaLean.PyExcept _)

instance : PastaLean.PyHAdd date'rn timedelta'rn (PastaLean.PyExcept date'rn) where hAdd := date'rn.__add__

def date'rn.__sub__'timedelta := fun (self : date'rn) ↦ fun (other : timedelta'rn) ↦
  ((do
      let p'_ret_1 := (← self +ₚ timedelta'rn.ofParts (-other.days))
      return p'_ret_1) :
    PastaLean.PyExcept _)

instance : PastaLean.PyHSub date'rn timedelta'rn (PastaLean.PyExcept date'rn) where hSub := date'rn.__sub__'timedelta

def date'rn.__sub__'date := fun (self : date'rn) ↦ fun (other : date'rn) ↦
  let days1 := (self.toordinal : Int)
  let days2 := (other.toordinal : Int)
  timedelta'rn.ofParts (days1 -ₚ days2)

instance : PastaLean.PyHSub date'rn date'rn timedelta'rn where hSub := date'rn.__sub__'date

def date'rn.__eq__ := fun (self : date'rn) ↦ fun (other : date'rn) ↦ self.toordinal == other.toordinal

instance : BEq date'rn where beq := date'rn.__eq__

def date'rn.__lt__ := fun (self : date'rn) ↦ fun (other : date'rn) ↦ decide (self.toordinal < other.toordinal)

instance : LT date'rn :=
  ⟨fun a b => date'rn.__lt__ a b = true⟩

instance : DecidableRel (α := date'rn) (· < ·) := fun a b => inferInstanceAs (Decidable (date'rn.__lt__ a b = true))

instance : Ord date'rn :=
  ⟨fun a b => if date'rn.__lt__ a b then .lt else if date'rn.__lt__ b a then .gt else .eq⟩

def date'rn.__le__ := fun (self : date'rn) ↦ fun (other : date'rn) ↦ decide (self.toordinal ≤ other.toordinal)

instance : LE date'rn :=
  ⟨fun a b => date'rn.__le__ a b = true⟩

instance : DecidableRel (α := date'rn) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (date'rn.__le__ a b = true))

def date'rn.__hash__ := fun (self : date'rn) ↦ hash self.toordinal

instance : Hashable date'rn :=
  ⟨fun a => hash (date'rn.__hash__ a)⟩

instance : PastaLean.PyPrintable date'rn
    where
  pyStringify := fun (self : date'rn) ↦ self.isoformat
  pyReprify := fun (self : date'rn) ↦ s! "datetime.date({self._year }, {self._month }, {self._day})"

end Libraries.datetime
