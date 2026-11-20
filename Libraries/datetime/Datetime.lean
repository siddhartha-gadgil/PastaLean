import Libraries.datetime.Time
import Std.Tactic.Do

open PastaLean
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace Libraries.datetime

/-- A date and time of day, to the microsecond, optionally with a fixed-offset `timezone`. -/
structure datetime where
  _year : Int
  _month : Int
  _day : Int
  _hour : Int
  _minute : Int
  _second : Int
  _microsecond : Int
  _tzinfo : Option timezone
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy datetime where truthy _ := true

instance : PastaLean.PyBool datetime where pyBool _ := true

instance : PastaLean.PyTyped datetime where pyTypeOf _ := TypeInfer.PyType.cls "datetime"

instance : Coe datetime (Option datetime) :=
  ⟨some⟩

def datetime.new (year : Int) (month : Int) (day : Int) (hour : Int := (0 : Int)) (minute : Int := (0 : Int))
    (second : Int := (0 : Int)) (microsecond : Int := (0 : Int)) (tzinfo : Option timezone := Option.none) :
    PastaLean.ProofMode.PyProofM datetime :=
  ((do
      let mut self : datetime := default
      let _ ← _check_date_fields year month day
      let _ ← _check_time_fields hour minute second microsecond
      self := { self with _year := year }
      self := { self with _month := month }
      self := { self with _day := day }
      self := { self with _hour := hour }
      self := { self with _minute := minute }
      self := { self with _second := second }
      self := { self with _microsecond := microsecond }
      self := { self with _tzinfo := tzinfo }
      return self) :
    PastaLean.ProofMode.PyProofM datetime)

def datetime._from_us := fun (total : Int) ↦ fun (tz : Option timezone) ↦
  ((do
      let p'_unpack_value_1 := PastaLean.pyDivmod total ((86400 : Int) *ₚ (1000000 : Int))
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut days := Prod.fst p'_unpack_pair_1
      let mut us := Prod.snd p'_unpack_pair_1
      if h_1 : ¬((0 : Int) < days ∧ days ≤ _ymd2ord MAXYEAR (12 : Int) (31 : Int)) then 
        throw (PastaLean.PyException.Raise "OverflowError" (ToString.toString "date value out of range"))
      let p'_unpack_value_2 := _ord2ymd days
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut y : Int := Prod.fst p'_unpack_pair_2
      let mut m : Int := Prod.fst (Prod.snd p'_unpack_pair_2)
      let mut d : Int := Prod.snd (Prod.snd p'_unpack_pair_2)
      let p'_unpack_value_3 := PastaLean.pyDivmod us (1000000 : Int)
      let p'_unpack_pair_3 := p'_unpack_value_3
      let mut secs := Prod.fst p'_unpack_pair_3
      let mut usec := Prod.snd p'_unpack_pair_3
      let p'_unpack_value_4 := PastaLean.pyDivmod secs (60 : Int)
      let p'_unpack_pair_4 := p'_unpack_value_4
      let mut mins := Prod.fst p'_unpack_pair_4
      let mut sec := Prod.snd p'_unpack_pair_4
      let p'_unpack_value_5 := PastaLean.pyDivmod mins (60 : Int)
      let p'_unpack_pair_5 := p'_unpack_value_5
      let mut hh := Prod.fst p'_unpack_pair_5
      let mut mi := Prod.snd p'_unpack_pair_5
      let p'_ret_1 := (← datetime.new y m d hh mi sec usec tz)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime._from_us

def datetime.combine := fun (d : date) ↦ fun (t : time) ↦
  ((do
      let p'_ret_1 := (← datetime.new d.year d.month d.day t.hour t.minute t.second t.microsecond t.tzinfo)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.combine

def datetime.now (tz : Option timezone := Option.none) :=
  ((do
      if let some tz := tz then 
        let p'_ret_1 := (← datetime._from_us ((← _now_utc_us) +ₚ tz.utcoffset._to_microseconds) tz)
        return p'_ret_1
      let p'_ret_1 := (← datetime._from_us (← _now_local_us) Option.none)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

def datetime.today :=
  ((do
      let p'_ret_1 := (← datetime._from_us (← _now_local_us) Option.none)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

def datetime.fromisoformat := fun (s : String) ↦
  ((do
      let mut d := (← date.fromisoformat (PastaLean.pySlice s (some (0 : Int)) (some (10 : Int)) none))
      if h_1 : PastaLean.pyLen s = (10 : Int) then 
        let p'_ret_1 := (← datetime.new d.year d.month d.day)
        return p'_ret_1
      if h_2 : PastaLean.pyLen s < (13 : Int) ∨ s⦋(10 : Int)⦌ ≠ "T" ∧ s⦋(10 : Int)⦌ ≠ " " then 
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
      let mut rest : String := PastaLean.pySlice s (some (11 : Int)) none none
      let mut tz : Option timezone := Option.none
      let mut cut : Int := PastaLean.pyLen rest
      for i in (PastaLean.pyRange (PastaLean.pyLen rest))do
        if h_3 : (rest⦋i⦌ = "+" ∨ rest⦋i⦌ = "-") ∨ rest⦋i⦌ = "Z" then 
          cut := i
          break
      if h_3 : cut < PastaLean.pyLen rest then 
        let mut off : String := PastaLean.pySlice rest (some cut) none none
        if h_4 : off = "Z" then 
          tz := (← timezone.new (timedelta.ofParts (0 : Int)))
        else
          if h_5 : PastaLean.pyLen off ≠ (6 : Int) ∨ off⦋(3 : Int)⦌ ≠ ":" then 
            throw
                (PastaLean.PyException.Raise "ValueError"
                  (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
          let mut minutes : Int :=
            (← _parse_digits off (1 : Int) (2 : Int)) *ₚ (60 : Int) +ₚ (← _parse_digits off (4 : Int) (2 : Int))
          if h_6 : off⦋(0 : Int)⦌ = "-" then 
            minutes := -minutes
          tz := (← timezone.new (timedelta.ofParts (minutes := minutes)))
      let mut t := (← time.fromisoformat (PastaLean.pySlice rest (some (0 : Int)) (some cut) none))
      let p'_ret_1 := (← datetime.new d.year d.month d.day t.hour t.minute t.second t.microsecond tz)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.fromisoformat

def datetime.year := fun (self : datetime) ↦ self._year

attribute [simp, taste_ingr] datetime.year

def datetime.month := fun (self : datetime) ↦ self._month

attribute [simp, taste_ingr] datetime.month

def datetime.day := fun (self : datetime) ↦ self._day

attribute [simp, taste_ingr] datetime.day

def datetime.hour := fun (self : datetime) ↦ self._hour

attribute [simp, taste_ingr] datetime.hour

def datetime.minute := fun (self : datetime) ↦ self._minute

attribute [simp, taste_ingr] datetime.minute

def datetime.second := fun (self : datetime) ↦ self._second

attribute [simp, taste_ingr] datetime.second

def datetime.microsecond := fun (self : datetime) ↦ self._microsecond

attribute [simp, taste_ingr] datetime.microsecond

def datetime.tzinfo := fun (self : datetime) ↦ (show Option timezone from self._tzinfo)

attribute [simp, taste_ingr] datetime.tzinfo

def datetime.date := fun (self : datetime) ↦
  ((do
      let p'_ret_1 := (← date.new self._year self._month self._day)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.date

def datetime.time := fun (self : datetime) ↦
  ((do
      let p'_ret_1 := (← time.new self._hour self._minute self._second self._microsecond)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.time

def datetime.timetz := fun (self : datetime) ↦
  ((do
      let p'_ret_1 := (← time.new self._hour self._minute self._second self._microsecond self._tzinfo)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.timetz

def datetime.utcoffset := fun (self : datetime) ↦
  (show Option timedelta from
    Id.run
      (do
        let mut tz : Option timezone := self._tzinfo
        if let some tz'rb0 := tz then 
          let p'_ret_1 := tz'rb0.utcoffset
          return p'_ret_1
        return Option.none))

attribute [simp, taste_ingr] datetime.utcoffset

def datetime.toordinal := fun (self : datetime) ↦ _ymd2ord self._year self._month self._day

attribute [simp, taste_ingr] datetime.toordinal

def datetime.weekday := fun (self : datetime) ↦ (self.toordinal +ₚ (6 : Int)) %ₚ (7 : Int)

attribute [simp, taste_ingr] datetime.weekday

def datetime.isoweekday := fun (self : datetime) ↦
  if PastaLean.pyTruthy (self.toordinal %ₚ (7 : Int)) then self.toordinal %ₚ (7 : Int) else (7 : Int)

attribute [simp, taste_ingr] datetime.isoweekday

def datetime._local_us := fun (self : datetime) ↦
  let secs :=
    ((self.toordinal *ₚ (24 : Int) +ₚ self._hour) *ₚ (3600 : Int) +ₚ self._minute *ₚ (60 : Int) +ₚ self._second : Int)
  secs *ₚ (1000000 : Int) +ₚ self._microsecond

attribute [simp, taste_ingr] datetime._local_us

def datetime._to_microseconds := fun (self : datetime) ↦ self._local_us -ₚ _offset_of self._tzinfo

attribute [simp, taste_ingr] datetime._to_microseconds

def datetime.timestamp := fun (self : datetime) ↦
  ((do
      let mut epoch : Int := _ymd2ord (1970 : Int) (1 : Int) (1 : Int) *ₚ (86400000000 : Int)
      let mut tz : Option timezone := self._tzinfo
      if let some tz'rb1 := tz then 
        let p'_ret_1 := (self._to_microseconds -ₚ epoch) /ₚ (1000000 : Int)
        return p'_ret_1
      let p'_ret_1 := (self._local_us -ₚ ((← _now_local_us) -ₚ (← _now_utc_us)) -ₚ epoch) /ₚ (1000000 : Int)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

def datetime.astimezone := fun (self : datetime) ↦ fun (tz : timezone) ↦
  ((do
      let p'_ret_1 := (← datetime._from_us (self._to_microseconds +ₚ tz.utcoffset._to_microseconds) tz)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.astimezone

def datetime.isoformat (self : datetime) (sep : String := "T") (timespec : String := "auto") :=
  ((do
      let p'_ret_1 :=
        _pad self._year (4 : Int) +ₚ "-" +ₚ _pad self._month (2 : Int) +ₚ "-" +ₚ _pad self._day (2 : Int) +ₚ sep +ₚ
            (← _format_time self._hour self._minute self._second self._microsecond timespec) +ₚ
          _tz_suffix self._tzinfo ":"
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.isoformat

def datetime.strftime := fun (self : datetime) ↦ fun (fmt : String) ↦
  let yday := (self.toordinal -ₚ _ymd2ord self._year (1 : Int) (1 : Int) +ₚ (1 : Int) : Int)
  _strftime fmt self._year self._month self._day self._hour self._minute self._second self._microsecond self.weekday
    yday

attribute [simp, taste_ingr] datetime.strftime

def datetime.replace (self : datetime) (year : Int := -(1 : Int)) (month : Int := -(1 : Int)) (day : Int := -(1 : Int))
    (hour : Int := -(1 : Int)) (minute : Int := -(1 : Int)) (second : Int := -(1 : Int))
    (microsecond : Int := -(1 : Int)) :=
  ((do
      if h_1 : year = -(1 : Int) then 
        let mut year : Int := self._year
      if h_2 : month = -(1 : Int) then 
        let mut month : Int := self._month
      if h_3 : day = -(1 : Int) then 
        let mut day : Int := self._day
      if h_4 : hour = -(1 : Int) then 
        let mut hour : Int := self._hour
      if h_5 : minute = -(1 : Int) then 
        let mut minute : Int := self._minute
      if h_6 : second = -(1 : Int) then 
        let mut second : Int := self._second
      if h_7 : microsecond = -(1 : Int) then 
        let mut microsecond : Int := self._microsecond
      let p'_ret_1 := (← datetime.new year month day hour minute second microsecond self._tzinfo)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.replace

def datetime.__add__ := fun (self : datetime) ↦ fun (other : timedelta) ↦
  ((do
      let p'_ret_1 := (← datetime._from_us (self._local_us +ₚ other._to_microseconds) self._tzinfo)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.__add__

instance : PastaLean.PyHAdd datetime timedelta (PastaLean.ProofMode.PyProofM datetime) where hAdd := datetime.__add__

def datetime.__sub__'timedelta := fun (self : datetime) ↦ fun (other : timedelta) ↦
  ((do
      let p'_ret_1 := (← self +ₚ -other)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.__sub__'timedelta

instance : PastaLean.PyHSub datetime timedelta (PastaLean.ProofMode.PyProofM datetime) where
  hSub := datetime.__sub__'timedelta

def datetime.__sub__'datetime := fun (self : datetime) ↦ fun (other : datetime) ↦
  ((do
      let _ ← _same_awareness self._tzinfo other._tzinfo
      let p'_ret_1 := timedelta.ofParts (0 : Int) (0 : Int) (self._to_microseconds -ₚ other._to_microseconds)
      return p'_ret_1) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] datetime.__sub__'datetime

instance : PastaLean.PyHSub datetime datetime (PastaLean.ProofMode.PyProofM timedelta) where
  hSub := datetime.__sub__'datetime

def datetime.__eq__ := fun (self : datetime) ↦ fun (other : datetime) ↦
  if PastaLean.pyIsNone self._tzinfo ≠ PastaLean.pyIsNone other._tzinfo then Bool.false
  else self._to_microseconds == other._to_microseconds

attribute [simp, taste_ingr] datetime.__eq__

instance : BEq datetime where beq := datetime.__eq__

/-- Python refuses to order an offset-naive against an offset-aware value (`TypeError`). -/
def datetime.__lt__ (self other : datetime) : PastaLean.ProofMode.PyProofM Bool := do
  _same_awareness self._tzinfo other._tzinfo
  return decide (self._to_microseconds < other._to_microseconds)


instance : LT datetime :=
  ⟨fun a b => PastaLean.runPure (datetime.__lt__ a b) = true⟩

instance : DecidableRel (α := datetime) (· < ·) := fun a b =>
  inferInstanceAs (Decidable (PastaLean.runPure (datetime.__lt__ a b) = true))

instance : Ord datetime :=
  ⟨fun a b => if PastaLean.runPure (datetime.__lt__ a b) then .lt
    else if PastaLean.runPure (datetime.__lt__ b a) then .gt else .eq⟩

/-- Python refuses to order an offset-naive against an offset-aware value (`TypeError`). -/
def datetime.__le__ (self other : datetime) : PastaLean.ProofMode.PyProofM Bool := do
  _same_awareness self._tzinfo other._tzinfo
  return decide (self._to_microseconds ≤ other._to_microseconds)


instance : LE datetime :=
  ⟨fun a b => PastaLean.runPure (datetime.__le__ a b) = true⟩

instance : DecidableRel (α := datetime) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (PastaLean.runPure (datetime.__le__ a b) = true))

def datetime.__hash__ := fun (self : datetime) ↦ hash self._to_microseconds

attribute [simp, taste_ingr] datetime.__hash__

instance : Hashable datetime :=
  ⟨fun a => hash (datetime.__hash__ a)⟩

instance : PastaLean.PyPrintable datetime
    where
  pyStringify := fun (self : datetime) ↦
    _pad self._year (4 : Int) +ₚ "-" +ₚ _pad self._month (2 : Int) +ₚ "-" +ₚ _pad self._day (2 : Int) +ₚ " " +ₚ
        _format_time_auto self._hour self._minute self._second self._microsecond +ₚ
      _tz_suffix self._tzinfo ":"
  pyReprify := fun (self : datetime) ↦
    Id.run
      (do
        let mut parts : List String :=
          [PastaLean.pyStr self._year, PastaLean.pyStr self._month, PastaLean.pyStr self._day]
        if h_1 :
            ((PastaLean.pyTruthy self._hour = true ∨ PastaLean.pyTruthy self._minute = true) ∨
                PastaLean.pyTruthy self._second = true) ∨
              PastaLean.pyTruthy self._microsecond = true then
          
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._hour)
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._minute)
        if h_2 : PastaLean.pyTruthy self._second = true ∨ PastaLean.pyTruthy self._microsecond = true then 
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._second)
        if h_3 : PastaLean.pyTruthy self._microsecond then 
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._microsecond)
        let mut r : String := "datetime.datetime(" +ₚ PastaLean.pyStringJoin ", " parts
        let mut tz : Option timezone := self._tzinfo
        if let some tz'rb2 := tz then 
          r := r +ₚ ", tzinfo=" +ₚ PastaLean.PyPrintable.pyReprify tz'rb2
        let p'_ret_1 := r +ₚ ")"
        return p'_ret_1)

/-- A date and time of day, to the microsecond, optionally with a fixed-offset `timezone`. -/
structure datetime'rn where
  _year : Int
  _month : Int
  _day : Int
  _hour : Int
  _minute : Int
  _second : Int
  _microsecond : Int
  _tzinfo : Option timezone'rn
  deriving Inhabited, Repr

instance : PastaLean.PyTruthy datetime'rn where truthy _ := true

instance : PastaLean.PyBool datetime'rn where pyBool _ := true

instance : PastaLean.PyTyped datetime'rn where pyTypeOf _ := TypeInfer.PyType.cls "datetime"

instance : Coe datetime'rn (Option datetime'rn) :=
  ⟨some⟩

def datetime'rn.new (year : Int) (month : Int) (day : Int) (hour : Int := (0 : Int)) (minute : Int := (0 : Int))
    (second : Int := (0 : Int)) (microsecond : Int := (0 : Int)) (tzinfo : Option timezone'rn := Option.none) :
    PastaLean.PyExcept datetime'rn :=
  ((do
      let mut self : datetime'rn := default
      let _ ← _check_date_fields'rn year month day
      let _ ← _check_time_fields'rn hour minute second microsecond
      self := { self with _year := year }
      self := { self with _month := month }
      self := { self with _day := day }
      self := { self with _hour := hour }
      self := { self with _minute := minute }
      self := { self with _second := second }
      self := { self with _microsecond := microsecond }
      self := { self with _tzinfo := tzinfo }
      return self) :
    PastaLean.PyExcept datetime'rn)

def datetime'rn._from_us := fun (total : Int) ↦ fun (tz : Option timezone'rn) ↦
  ((do
      let p'_unpack_value_1 := PastaLean.pyDivmod total ((86400 : Int) *ₚ (1000000 : Int))
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut days := Prod.fst p'_unpack_pair_1
      let mut us := Prod.snd p'_unpack_pair_1
      if h_1 : !(decide ((0 : Int) < days) && decide (days ≤ _ymd2ord'rn MAXYEAR (12 : Int) (31 : Int))) then 
        throw (PastaLean.PyException.Raise "OverflowError" (ToString.toString "date value out of range"))
      let p'_unpack_value_2 := _ord2ymd'rn days
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut y : Int := Prod.fst p'_unpack_pair_2
      let mut m : Int := Prod.fst (Prod.snd p'_unpack_pair_2)
      let mut d : Int := Prod.snd (Prod.snd p'_unpack_pair_2)
      let p'_unpack_value_3 := PastaLean.pyDivmod us (1000000 : Int)
      let p'_unpack_pair_3 := p'_unpack_value_3
      let mut secs := Prod.fst p'_unpack_pair_3
      let mut usec := Prod.snd p'_unpack_pair_3
      let p'_unpack_value_4 := PastaLean.pyDivmod secs (60 : Int)
      let p'_unpack_pair_4 := p'_unpack_value_4
      let mut mins := Prod.fst p'_unpack_pair_4
      let mut sec := Prod.snd p'_unpack_pair_4
      let p'_unpack_value_5 := PastaLean.pyDivmod mins (60 : Int)
      let p'_unpack_pair_5 := p'_unpack_value_5
      let mut hh := Prod.fst p'_unpack_pair_5
      let mut mi := Prod.snd p'_unpack_pair_5
      let p'_ret_1 := (← datetime'rn.new y m d hh mi sec usec tz)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.combine := fun (d : date'rn) ↦ fun (t : time'rn) ↦
  ((do
      let p'_ret_1 := (← datetime'rn.new d.year d.month d.day t.hour t.minute t.second t.microsecond t.tzinfo)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.now (tz : Option timezone'rn := Option.none) :=
  ((do
      if let some tz := tz then 
        let p'_ret_1 := (← datetime'rn._from_us ((← _now_utc_us'rn) +ₚ tz.utcoffset._to_microseconds) tz)
        return p'_ret_1
      let p'_ret_1 := (← datetime'rn._from_us (← _now_local_us'rn) Option.none)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.today :=
  ((do
      let p'_ret_1 := (← datetime'rn._from_us (← _now_local_us'rn) Option.none)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.fromisoformat := fun (s : String) ↦
  ((do
      let mut d := (← date'rn.fromisoformat (PastaLean.pySlice s (some (0 : Int)) (some (10 : Int)) none))
      if h_1 : PastaLean.pyLen s == (10 : Int) then 
        let p'_ret_1 := (← datetime'rn.new d.year d.month d.day)
        return p'_ret_1
      if h_2 : decide (PastaLean.pyLen s < (13 : Int)) || s⦋(10 : Int)⦌ != "T" && s⦋(10 : Int)⦌ != " " then 
        throw
            (PastaLean.PyException.Raise "ValueError"
              (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
      let mut rest : String := PastaLean.pySlice s (some (11 : Int)) none none
      let mut tz : Option timezone'rn := Option.none
      let mut cut : Int := PastaLean.pyLen rest
      for i in (PastaLean.pyRange (PastaLean.pyLen rest))do
        if h_3 : rest⦋i⦌ == "+" || rest⦋i⦌ == "-" || rest⦋i⦌ == "Z" then 
          cut := i
          break
      if h_3 : cut < PastaLean.pyLen rest then 
        let mut off : String := PastaLean.pySlice rest (some cut) none none
        if h_4 : off == "Z" then 
          tz := (← timezone'rn.new (timedelta'rn.ofParts (0 : Int)))
        else
          if h_5 : PastaLean.pyLen off != (6 : Int) || off⦋(3 : Int)⦌ != ":" then 
            throw
                (PastaLean.PyException.Raise "ValueError"
                  (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
          let mut minutes : Int :=
            (← _parse_digits'rn off (1 : Int) (2 : Int)) *ₚ (60 : Int) +ₚ (← _parse_digits'rn off (4 : Int) (2 : Int))
          if h_6 : off⦋(0 : Int)⦌ == "-" then 
            minutes := -minutes
          tz := (← timezone'rn.new (timedelta'rn.ofParts (minutes := minutes)))
      let mut t := (← time'rn.fromisoformat (PastaLean.pySlice rest (some (0 : Int)) (some cut) none))
      let p'_ret_1 := (← datetime'rn.new d.year d.month d.day t.hour t.minute t.second t.microsecond tz)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.year := fun (self : datetime'rn) ↦ self._year

def datetime'rn.month := fun (self : datetime'rn) ↦ self._month

def datetime'rn.day := fun (self : datetime'rn) ↦ self._day

def datetime'rn.hour := fun (self : datetime'rn) ↦ self._hour

def datetime'rn.minute := fun (self : datetime'rn) ↦ self._minute

def datetime'rn.second := fun (self : datetime'rn) ↦ self._second

def datetime'rn.microsecond := fun (self : datetime'rn) ↦ self._microsecond

def datetime'rn.tzinfo := fun (self : datetime'rn) ↦ (show Option timezone'rn from self._tzinfo)

def datetime'rn.date := fun (self : datetime'rn) ↦
  ((do
      let p'_ret_1 := (← date'rn.new self._year self._month self._day)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.time := fun (self : datetime'rn) ↦
  ((do
      let p'_ret_1 := (← time'rn.new self._hour self._minute self._second self._microsecond)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.timetz := fun (self : datetime'rn) ↦
  ((do
      let p'_ret_1 := (← time'rn.new self._hour self._minute self._second self._microsecond self._tzinfo)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.utcoffset := fun (self : datetime'rn) ↦
  (show Option timedelta'rn from
    Id.run
      (do
        let mut tz : Option timezone'rn := self._tzinfo
        if let some tz'rb0 := tz then 
          let p'_ret_1 := tz'rb0.utcoffset
          return p'_ret_1
        return Option.none))

def datetime'rn.toordinal := fun (self : datetime'rn) ↦ _ymd2ord'rn self._year self._month self._day

def datetime'rn.weekday := fun (self : datetime'rn) ↦ (self.toordinal +ₚ (6 : Int)) %ₚ (7 : Int)

def datetime'rn.isoweekday := fun (self : datetime'rn) ↦
  if PastaLean.pyTruthy (self.toordinal %ₚ (7 : Int)) then self.toordinal %ₚ (7 : Int) else (7 : Int)

def datetime'rn._local_us := fun (self : datetime'rn) ↦
  let secs :=
    ((self.toordinal *ₚ (24 : Int) +ₚ self._hour) *ₚ (3600 : Int) +ₚ self._minute *ₚ (60 : Int) +ₚ self._second : Int)
  secs *ₚ (1000000 : Int) +ₚ self._microsecond

def datetime'rn._to_microseconds := fun (self : datetime'rn) ↦ self._local_us -ₚ _offset_of'rn self._tzinfo

def datetime'rn.timestamp := fun (self : datetime'rn) ↦
  ((do
      let mut epoch : Int := _ymd2ord'rn (1970 : Int) (1 : Int) (1 : Int) *ₚ (86400000000 : Int)
      let mut tz : Option timezone'rn := self._tzinfo
      if let some tz'rb1 := tz then 
        let p'_ret_1 := PastaLean.pyTrueDiv (self._to_microseconds -ₚ epoch) (1000000 : Int)
        return p'_ret_1
      let p'_ret_1 :=
        PastaLean.pyTrueDiv (self._local_us -ₚ ((← _now_local_us'rn) -ₚ (← _now_utc_us'rn)) -ₚ epoch) (1000000 : Int)
      return p'_ret_1) :
    IO _)

def datetime'rn.astimezone := fun (self : datetime'rn) ↦ fun (tz : timezone'rn) ↦
  ((do
      let p'_ret_1 := (← datetime'rn._from_us (self._to_microseconds +ₚ tz.utcoffset._to_microseconds) tz)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.isoformat (self : datetime'rn) (sep : String := "T") (timespec : String := "auto") :=
  ((do
      let p'_ret_1 :=
        _pad'rn self._year (4 : Int) +ₚ "-" +ₚ _pad'rn self._month (2 : Int) +ₚ "-" +ₚ _pad'rn self._day (2 : Int) +ₚ
              sep +ₚ
            (← _format_time'rn self._hour self._minute self._second self._microsecond timespec) +ₚ
          _tz_suffix'rn self._tzinfo ":"
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.strftime := fun (self : datetime'rn) ↦ fun (fmt : String) ↦
  let yday := (self.toordinal -ₚ _ymd2ord'rn self._year (1 : Int) (1 : Int) +ₚ (1 : Int) : Int)
  _strftime'rn fmt self._year self._month self._day self._hour self._minute self._second self._microsecond self.weekday
    yday

def datetime'rn.replace (self : datetime'rn) (year : Int := -(1 : Int)) (month : Int := -(1 : Int))
    (day : Int := -(1 : Int)) (hour : Int := -(1 : Int)) (minute : Int := -(1 : Int)) (second : Int := -(1 : Int))
    (microsecond : Int := -(1 : Int)) :=
  ((do
      if h_1 : year == -(1 : Int) then 
        let mut year : Int := self._year
      if h_2 : month == -(1 : Int) then 
        let mut month : Int := self._month
      if h_3 : day == -(1 : Int) then 
        let mut day : Int := self._day
      if h_4 : hour == -(1 : Int) then 
        let mut hour : Int := self._hour
      if h_5 : minute == -(1 : Int) then 
        let mut minute : Int := self._minute
      if h_6 : second == -(1 : Int) then 
        let mut second : Int := self._second
      if h_7 : microsecond == -(1 : Int) then 
        let mut microsecond : Int := self._microsecond
      let p'_ret_1 := (← datetime'rn.new year month day hour minute second microsecond self._tzinfo)
      return p'_ret_1) :
    PastaLean.PyExcept _)

def datetime'rn.__add__ := fun (self : datetime'rn) ↦ fun (other : timedelta'rn) ↦
  ((do
      let p'_ret_1 := (← datetime'rn._from_us (self._local_us +ₚ other._to_microseconds) self._tzinfo)
      return p'_ret_1) :
    PastaLean.PyExcept _)

instance : PastaLean.PyHAdd datetime'rn timedelta'rn (PastaLean.PyExcept datetime'rn) where hAdd := datetime'rn.__add__

def datetime'rn.__sub__'timedelta := fun (self : datetime'rn) ↦ fun (other : timedelta'rn) ↦
  ((do
      let p'_ret_1 := (← self +ₚ -other)
      return p'_ret_1) :
    PastaLean.PyExcept _)

instance : PastaLean.PyHSub datetime'rn timedelta'rn (PastaLean.PyExcept datetime'rn) where
  hSub := datetime'rn.__sub__'timedelta

def datetime'rn.__sub__'datetime := fun (self : datetime'rn) ↦ fun (other : datetime'rn) ↦
  ((do
      let _ ← _same_awareness'rn self._tzinfo other._tzinfo
      let p'_ret_1 := timedelta'rn.ofParts (0 : Int) (0 : Int) (self._to_microseconds -ₚ other._to_microseconds)
      return p'_ret_1) :
    PastaLean.PyExcept _)

instance : PastaLean.PyHSub datetime'rn datetime'rn (PastaLean.PyExcept timedelta'rn) where
  hSub := datetime'rn.__sub__'datetime

def datetime'rn.__eq__ := fun (self : datetime'rn) ↦ fun (other : datetime'rn) ↦
  if PastaLean.pyIsNone self._tzinfo != PastaLean.pyIsNone other._tzinfo then Bool.false
  else self._to_microseconds == other._to_microseconds

instance : BEq datetime'rn where beq := datetime'rn.__eq__

/-- Python refuses to order an offset-naive against an offset-aware value (`TypeError`). -/
def datetime'rn.__lt__ (self other : datetime'rn) : PastaLean.PyExcept Bool := do
  _same_awareness'rn self._tzinfo other._tzinfo
  return decide (self._to_microseconds < other._to_microseconds)

instance : LT datetime'rn :=
  ⟨fun a b => PastaLean.runPure (datetime'rn.__lt__ a b) = true⟩

instance : DecidableRel (α := datetime'rn) (· < ·) := fun a b =>
  inferInstanceAs (Decidable (PastaLean.runPure (datetime'rn.__lt__ a b) = true))

instance : Ord datetime'rn :=
  ⟨fun a b => if PastaLean.runPure (datetime'rn.__lt__ a b) then .lt
    else if PastaLean.runPure (datetime'rn.__lt__ b a) then .gt else .eq⟩

/-- Python refuses to order an offset-naive against an offset-aware value (`TypeError`). -/
def datetime'rn.__le__ (self other : datetime'rn) : PastaLean.PyExcept Bool := do
  _same_awareness'rn self._tzinfo other._tzinfo
  return decide (self._to_microseconds ≤ other._to_microseconds)

instance : LE datetime'rn :=
  ⟨fun a b => PastaLean.runPure (datetime'rn.__le__ a b) = true⟩

instance : DecidableRel (α := datetime'rn) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (PastaLean.runPure (datetime'rn.__le__ a b) = true))

def datetime'rn.__hash__ := fun (self : datetime'rn) ↦ hash self._to_microseconds

instance : Hashable datetime'rn :=
  ⟨fun a => hash (datetime'rn.__hash__ a)⟩

instance : PastaLean.PyPrintable datetime'rn
    where
  pyStringify := fun (self : datetime'rn) ↦
    _pad'rn self._year (4 : Int) +ₚ "-" +ₚ _pad'rn self._month (2 : Int) +ₚ "-" +ₚ _pad'rn self._day (2 : Int) +ₚ " " +ₚ
        _format_time_auto'rn self._hour self._minute self._second self._microsecond +ₚ
      _tz_suffix'rn self._tzinfo ":"
  pyReprify := fun (self : datetime'rn) ↦
    Id.run
      (do
        let mut parts : List String :=
          [PastaLean.pyStr self._year, PastaLean.pyStr self._month, PastaLean.pyStr self._day]
        if h_1 :
            PastaLean.pyTruthy self._hour || PastaLean.pyTruthy self._minute || PastaLean.pyTruthy self._second ||
              PastaLean.pyTruthy self._microsecond then
          
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._hour)
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._minute)
        if h_2 : PastaLean.pyTruthy self._second || PastaLean.pyTruthy self._microsecond then 
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._second)
        if h_3 : PastaLean.pyTruthy self._microsecond then 
          parts := PastaLean.pyAppend parts (PastaLean.pyStr self._microsecond)
        let mut r : String := "datetime.datetime(" +ₚ PastaLean.pyStringJoin ", " parts
        let mut tz : Option timezone'rn := self._tzinfo
        if let some tz'rb2 := tz then 
          r := r +ₚ ", tzinfo=" +ₚ PastaLean.PyPrintable.pyReprify tz'rb2
        let p'_ret_1 := r +ₚ ")"
        return p'_ret_1)

/-- `datetime.UTC` / `timezone.utc`: the zero offset (in range, so built without the validating
constructor). -/
def UTC : timezone := { _offset := timedelta.ofParts, _name := "" }

def UTC'rn : timezone'rn := { _offset := timedelta'rn.ofParts, _name := "" }

def timezone.utc : timezone := UTC

def timezone'rn.utc : timezone'rn := UTC'rn

end Libraries.datetime
