import PastaLean.PyAPI
import Std.Time
import Std.Tactic.Do

open PastaLean
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace Libraries.datetime

/-!
# Python's `datetime` module

`timedelta`, `date`, `time`, `datetime` and fixed-offset `timezone` (`UTC`, `timezone.utc`), with both
twins. Derived from CPython 3.14 `Lib/_pydatetime.py` (Copyright (c) 2001-2025 Python Software
Foundation, PSF License Version 2), first translated from Python by PastaLean: the proleptic Gregorian
ordinal arithmetic, field validation, normalisation and ISO formatting/parsing are CPython's.
The module is split as CPython's `_pydatetime.py` is laid out: `Basic` (ordinals, validation,
formatting, the clock), `Timedelta`, `Date`, `Timezone`, `Time`, `Datetime`. The clock
(`today()`, `now()`, naive `timestamp()`) is the system's in the runnable twin and the fixed unspecified
`nowUtcUs`/`localOffsetUs` in the provable one.

A program importing this library gets its class declarations from `Libraries/datetime/Mapping.lean`.
-/

def MINYEAR :=
  (1 : Int)

def MAXYEAR :=
  (9999 : Int)

def _DAYS_IN_MONTH :=
  [-(1 : Int), (31 : Int), (28 : Int), (31 : Int), (30 : Int), (31 : Int), (30 : Int), (31 : Int), (31 : Int),
    (30 : Int), (31 : Int), (30 : Int), (31 : Int)]

def _DAYS_BEFORE_MONTH :=
  [-(1 : Int), (0 : Int), (31 : Int), (59 : Int), (90 : Int), (120 : Int), (151 : Int), (181 : Int), (212 : Int),
    (243 : Int), (273 : Int), (304 : Int), (334 : Int)]

def _MONTHNAMES :=
  ["", "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

def _DAYNAMES :=
  ["", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

def _FULL_MONTHNAMES :=
  ["", "January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November",
    "December"]

def _FULL_DAYNAMES :=
  ["", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]

def _DI400Y :=
  (146097 : Int)

def _DI100Y :=
  (36524 : Int)

def _DI4Y :=
  (1461 : Int)

def _is_leap := fun (year : Int) ↦
  if PastaLean.pyTruthy (year %ₚ (4 : Int) == (0 : Int)) then
    year %ₚ (100 : Int) != (0 : Int) || year %ₚ (400 : Int) == (0 : Int)
  else year %ₚ (4 : Int) == (0 : Int)

attribute [simp, taste_ingr] _is_leap

def _is_leap'rn := fun (year : Int) ↦
  if PastaLean.pyTruthy (year %ₚ (4 : Int) == (0 : Int)) then
    year %ₚ (100 : Int) != (0 : Int) || year %ₚ (400 : Int) == (0 : Int)
  else year %ₚ (4 : Int) == (0 : Int)

def _days_before_year := fun (year : Int) ↦
  let y := (year -ₚ (1 : Int) : Int)
  y *ₚ (365 : Int) +ₚ PastaLean.pyFloorDiv y (4 : Int) -ₚ PastaLean.pyFloorDiv y (100 : Int) +ₚ
    PastaLean.pyFloorDiv y (400 : Int)

attribute [simp, taste_ingr] _days_before_year

def _days_before_year'rn := fun (year : Int) ↦
  let y := (year -ₚ (1 : Int) : Int)
  y *ₚ (365 : Int) +ₚ PastaLean.pyFloorDiv y (4 : Int) -ₚ PastaLean.pyFloorDiv y (100 : Int) +ₚ
    PastaLean.pyFloorDiv y (400 : Int)

def _days_in_month := fun (year : Int) ↦ fun (month : Int) ↦
  if month = (2 : Int) ∧ PastaLean.pyTruthy (_is_leap year) = true then (29 : Int) else _DAYS_IN_MONTH⦋month⦌

attribute [simp, taste_ingr] _days_in_month

def _days_in_month'rn := fun (year : Int) ↦ fun (month : Int) ↦
  if month == (2 : Int) && PastaLean.pyTruthy (_is_leap'rn year) then (29 : Int) else _DAYS_IN_MONTH⦋month⦌

def _days_before_month := fun (year : Int) ↦ fun (month : Int) ↦
  Id.run
    (do
      let mut extra : Int := (0 : Int)
      if h_1 : month > (2 : Int) ∧ PastaLean.pyTruthy (_is_leap year) = true then 
        extra := (1 : Int)
      let p'_ret_1 := _DAYS_BEFORE_MONTH⦋month⦌ +ₚ extra
      return p'_ret_1)

attribute [simp, taste_ingr] _days_before_month

def _days_before_month'rn := fun (year : Int) ↦ fun (month : Int) ↦
  Id.run
    (do
      let mut extra : Int := (0 : Int)
      if h_1 : decide (month > (2 : Int)) && PastaLean.pyTruthy (_is_leap'rn year) then 
        extra := (1 : Int)
      let p'_ret_1 := _DAYS_BEFORE_MONTH⦋month⦌ +ₚ extra
      return p'_ret_1)

def _ymd2ord := fun (year : Int) ↦ fun (month : Int) ↦ fun (day : Int) ↦
  _days_before_year year +ₚ _days_before_month year month +ₚ day

attribute [simp, taste_ingr] _ymd2ord

def _ymd2ord'rn := fun (year : Int) ↦ fun (month : Int) ↦ fun (day : Int) ↦
  _days_before_year'rn year +ₚ _days_before_month'rn year month +ₚ day

def _ord2ymd := fun (n : Int) ↦
  Id.run
    (do
      let mut n := n
      n := n -ₚ (1 : Int)
      let p'_unpack_value_1 := PastaLean.pyDivmod n _DI400Y
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut n400 := Prod.fst p'_unpack_pair_1
      n := Prod.snd p'_unpack_pair_1
      let mut year := n400 *ₚ (400 : Int) +ₚ (1 : Int)
      let p'_unpack_value_2 := PastaLean.pyDivmod n _DI100Y
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut n100 := Prod.fst p'_unpack_pair_2
      n := Prod.snd p'_unpack_pair_2
      let p'_unpack_value_3 := PastaLean.pyDivmod n _DI4Y
      let p'_unpack_pair_3 := p'_unpack_value_3
      let mut n4 := Prod.fst p'_unpack_pair_3
      n := Prod.snd p'_unpack_pair_3
      let p'_unpack_value_4 := PastaLean.pyDivmod n (365 : Int)
      let p'_unpack_pair_4 := p'_unpack_value_4
      let mut n1 := Prod.fst p'_unpack_pair_4
      n := Prod.snd p'_unpack_pair_4
      year := year +ₚ (n100 *ₚ (100 : Int) +ₚ n4 *ₚ (4 : Int) +ₚ n1)
      if h_1 : n1 = (4 : Int) ∨ n100 = (4 : Int) then 
        let p'_ret_1 := (year -ₚ (1 : Int), ((12 : Int), (31 : Int)))
        return p'_ret_1
      let mut leapyear : Bool :=
        if PastaLean.pyTruthy (n1 == (3 : Int)) then n4 != (24 : Int) || n100 == (3 : Int) else n1 == (3 : Int)
      let mut month : Int := PastaLean.pyShiftRight (n +ₚ (50 : Int)) (5 : Int)
      let mut preceding : Int := _DAYS_BEFORE_MONTH⦋month⦌
      if h_2 : month > (2 : Int) ∧ PastaLean.pyTruthy leapyear = true then 
        preceding := preceding +ₚ (1 : Int)
      if h_3 : preceding > n then 
        month := month -ₚ (1 : Int)
        preceding := preceding -ₚ _DAYS_IN_MONTH⦋month⦌
        if h_4 : month = (2 : Int) ∧ PastaLean.pyTruthy leapyear = true then 
          preceding := preceding -ₚ (1 : Int)
      n := n -ₚ preceding
      let p'_ret_1 := (year, (month, n +ₚ (1 : Int)))
      return p'_ret_1)

attribute [simp, taste_ingr] _ord2ymd

def _ord2ymd'rn := fun (n : Int) ↦
  Id.run
    (do
      let mut n := n
      n := n -ₚ (1 : Int)
      let p'_unpack_value_1 := PastaLean.pyDivmod n _DI400Y
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut n400 := Prod.fst p'_unpack_pair_1
      n := Prod.snd p'_unpack_pair_1
      let mut year := n400 *ₚ (400 : Int) +ₚ (1 : Int)
      let p'_unpack_value_2 := PastaLean.pyDivmod n _DI100Y
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut n100 := Prod.fst p'_unpack_pair_2
      n := Prod.snd p'_unpack_pair_2
      let p'_unpack_value_3 := PastaLean.pyDivmod n _DI4Y
      let p'_unpack_pair_3 := p'_unpack_value_3
      let mut n4 := Prod.fst p'_unpack_pair_3
      n := Prod.snd p'_unpack_pair_3
      let p'_unpack_value_4 := PastaLean.pyDivmod n (365 : Int)
      let p'_unpack_pair_4 := p'_unpack_value_4
      let mut n1 := Prod.fst p'_unpack_pair_4
      n := Prod.snd p'_unpack_pair_4
      year := year +ₚ (n100 *ₚ (100 : Int) +ₚ n4 *ₚ (4 : Int) +ₚ n1)
      if h_1 : n1 == (4 : Int) || n100 == (4 : Int) then 
        let p'_ret_1 := (year -ₚ (1 : Int), ((12 : Int), (31 : Int)))
        return p'_ret_1
      let mut leapyear : Bool :=
        if PastaLean.pyTruthy (n1 == (3 : Int)) then n4 != (24 : Int) || n100 == (3 : Int) else n1 == (3 : Int)
      let mut month : Int := PastaLean.pyShiftRight (n +ₚ (50 : Int)) (5 : Int)
      let mut preceding : Int := _DAYS_BEFORE_MONTH⦋month⦌
      if h_2 : decide (month > (2 : Int)) && PastaLean.pyTruthy leapyear then 
        preceding := preceding +ₚ (1 : Int)
      if h_3 : preceding > n then 
        month := month -ₚ (1 : Int)
        preceding := preceding -ₚ _DAYS_IN_MONTH⦋month⦌
        if h_4 : month == (2 : Int) && PastaLean.pyTruthy leapyear then 
          preceding := preceding -ₚ (1 : Int)
      n := n -ₚ preceding
      let p'_ret_1 := (year, (month, n +ₚ (1 : Int)))
      return p'_ret_1)

/-- The provable twin's clock: one fixed but unspecified instant, as `ordinal * 86400000000 + µs of day`
(UTC), so a proof can rely on nothing about `today()`/`now()` beyond their types. -/
opaque nowUtcUs : Int

/-- The provable twin's local UTC offset (µs): fixed but unspecified. -/
opaque localOffsetUs : Int

def _now_utc_us : PastaLean.ProofMode.PyProofM Int := pure nowUtcUs

def _now_local_us : PastaLean.ProofMode.PyProofM Int := pure (nowUtcUs + localOffsetUs)

/-- µs from 0001-01-01 (ordinal 1) back to the ordinal origin, plus the Unix epoch's ordinal 719163. -/
def unixEpochUs : Int := 719163 * 86400000000

def _now_utc_us'rn : IO Int := do
  let t ← Std.Time.Timestamp.now
  return t.toNanosecondsSinceUnixEpoch.val / 1000 + unixEpochUs

def _now_local_us'rn : IO Int := do
  let t ← Std.Time.Timestamp.now
  let rules ← Std.Time.Database.defaultGetLocalZoneRules
  let offset := (rules.timezoneAt t).offset.second.val
  return t.toNanosecondsSinceUnixEpoch.val / 1000 + unixEpochUs + offset * 1000000

def _check_date_fields : Int → Int → Int → PastaLean.ProofMode.PyProofM Unit := fun (year : Int) ↦
  fun (month : Int) ↦ fun (day : Int) ↦ do
  if h_1 : ¬(MINYEAR ≤ year ∧ year ≤ MAXYEAR) then 
    throw
        (PastaLean.PyException.Raise "ValueError"
          (ToString.toString s! "year must be in {MINYEAR }..{MAXYEAR }, not {year}"))
  if h_2 : ¬((1 : Int) ≤ month ∧ month ≤ (12 : Int)) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString s! "month must be in 1..12, not {month}"))
  let mut dim : Int := _days_in_month year month
  if h_3 : ¬((1 : Int) ≤ day ∧ day ≤ dim) then 
    throw
        (PastaLean.PyException.Raise "ValueError"
          (ToString.toString s! "day {day } must be in range 1..{dim } for month {month } in year {year}"))

attribute [simp] _check_date_fields

def _check_date_fields'rn : Int → Int → Int → PastaLean.PyExcept Unit := fun (year : Int) ↦ fun (month : Int) ↦
  fun (day : Int) ↦ do
  if h_1 : !(decide (MINYEAR ≤ year) && decide (year ≤ MAXYEAR)) then 
    throw
        (PastaLean.PyException.Raise "ValueError"
          (ToString.toString s! "year must be in {MINYEAR }..{MAXYEAR }, not {year}"))
  if h_2 : !(decide ((1 : Int) ≤ month) && decide (month ≤ (12 : Int))) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString s! "month must be in 1..12, not {month}"))
  let mut dim : Int := _days_in_month'rn year month
  if h_3 : !(decide ((1 : Int) ≤ day) && decide (day ≤ dim)) then 
    throw
        (PastaLean.PyException.Raise "ValueError"
          (ToString.toString s! "day {day } must be in range 1..{dim } for month {month } in year {year}"))

def _check_time_fields : Int → Int → Int → Int → PastaLean.ProofMode.PyProofM Unit := fun (hour : Int) ↦
  fun (minute : Int) ↦ fun (second : Int) ↦ fun (microsecond : Int) ↦ do
  if h_1 : ¬((0 : Int) ≤ hour ∧ hour ≤ (23 : Int)) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString s! "hour must be in 0..23, not {hour}"))
  if h_2 : ¬((0 : Int) ≤ minute ∧ minute ≤ (59 : Int)) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString s! "minute must be in 0..59, not {minute}"))
  if h_3 : ¬((0 : Int) ≤ second ∧ second ≤ (59 : Int)) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString s! "second must be in 0..59, not {second}"))
  if h_4 : ¬((0 : Int) ≤ microsecond ∧ microsecond ≤ (999999 : Int)) then 
    throw
        (PastaLean.PyException.Raise "ValueError"
          (ToString.toString s! "microsecond must be in 0..999999, not {microsecond}"))

attribute [simp] _check_time_fields

def _check_time_fields'rn : Int → Int → Int → Int → PastaLean.PyExcept Unit := fun (hour : Int) ↦
  fun (minute : Int) ↦ fun (second : Int) ↦ fun (microsecond : Int) ↦ do
  if h_1 : !(decide ((0 : Int) ≤ hour) && decide (hour ≤ (23 : Int))) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString s! "hour must be in 0..23, not {hour}"))
  if h_2 : !(decide ((0 : Int) ≤ minute) && decide (minute ≤ (59 : Int))) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString s! "minute must be in 0..59, not {minute}"))
  if h_3 : !(decide ((0 : Int) ≤ second) && decide (second ≤ (59 : Int))) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString s! "second must be in 0..59, not {second}"))
  if h_4 : !(decide ((0 : Int) ≤ microsecond) && decide (microsecond ≤ (999999 : Int))) then 
    throw
        (PastaLean.PyException.Raise "ValueError"
          (ToString.toString s! "microsecond must be in 0..999999, not {microsecond}"))

def _pad := fun (n : Int) ↦ fun (width : Int) ↦
  Id.run
    (do
      let mut s : String := PastaLean.pyStr (PastaLean.pyAbs n)
      while (PastaLean.pyLen s < width) do
        s := "0" +ₚ s
      if h_1 : n < (0 : Int) then 
        let p'_ret_1 := "-" +ₚ s
        return p'_ret_1
      return s)

attribute [simp, taste_ingr] _pad

def _pad'rn := fun (n : Int) ↦ fun (width : Int) ↦
  Id.run
    (do
      let mut s : String := PastaLean.pyStr (PastaLean.pyAbs n)
      while (PastaLean.pyLen s < width) do
        s := "0" +ₚ s
      if h_1 : n < (0 : Int) then 
        let p'_ret_1 := "-" +ₚ s
        return p'_ret_1
      return s)

def _format_time_auto := fun (hh : Int) ↦ fun (mm : Int) ↦ fun (ss : Int) ↦ fun (us : Int) ↦
  Id.run
    (do
      let mut s : String := _pad hh (2 : Int) +ₚ ":" +ₚ _pad mm (2 : Int) +ₚ ":" +ₚ _pad ss (2 : Int)
      if h_1 : PastaLean.pyTruthy us then 
        s := s +ₚ "." +ₚ _pad us (6 : Int)
      return s)

attribute [simp, taste_ingr] _format_time_auto

def _format_time_auto'rn := fun (hh : Int) ↦ fun (mm : Int) ↦ fun (ss : Int) ↦ fun (us : Int) ↦
  Id.run
    (do
      let mut s : String := _pad'rn hh (2 : Int) +ₚ ":" +ₚ _pad'rn mm (2 : Int) +ₚ ":" +ₚ _pad'rn ss (2 : Int)
      if h_1 : PastaLean.pyTruthy us then 
        s := s +ₚ "." +ₚ _pad'rn us (6 : Int)
      return s)

def _format_time : Int → Int → Int → Int → String → PastaLean.ProofMode.PyProofM String := fun (hh : Int) ↦
  fun (mm : Int) ↦ fun (ss : Int) ↦ fun (us : Int) ↦ fun (timespec : String) ↦ do
  let mut timespec := timespec
  if h_1 : timespec = "auto" then 
    if h_2 : PastaLean.pyTruthy us then 
      timespec := "microseconds"
    else
      timespec := "seconds"
  if h_2 : timespec = "hours" then 
    let p'_ret_1 := _pad hh (2 : Int)
    return p'_ret_1
  if h_3 : timespec = "minutes" then 
    let p'_ret_1 := _pad hh (2 : Int) +ₚ ":" +ₚ _pad mm (2 : Int)
    return p'_ret_1
  if h_4 : timespec = "seconds" then 
    let p'_ret_1 := _pad hh (2 : Int) +ₚ ":" +ₚ _pad mm (2 : Int) +ₚ ":" +ₚ _pad ss (2 : Int)
    return p'_ret_1
  if h_5 : timespec = "milliseconds" then 
    let p'_ret_1 :=
      _pad hh (2 : Int) +ₚ ":" +ₚ _pad mm (2 : Int) +ₚ ":" +ₚ _pad ss (2 : Int) +ₚ "." +ₚ
        _pad (PastaLean.pyFloorDiv us (1000 : Int)) (3 : Int)
    return p'_ret_1
  if h_6 : timespec = "microseconds" then 
    let p'_ret_1 :=
      _pad hh (2 : Int) +ₚ ":" +ₚ _pad mm (2 : Int) +ₚ ":" +ₚ _pad ss (2 : Int) +ₚ "." +ₚ _pad us (6 : Int)
    return p'_ret_1
  throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "Unknown timespec value"))

attribute [simp] _format_time

def _format_time'rn : Int → Int → Int → Int → String → PastaLean.PyExcept String := fun (hh : Int) ↦
  fun (mm : Int) ↦ fun (ss : Int) ↦ fun (us : Int) ↦ fun (timespec : String) ↦ do
  let mut timespec := timespec
  if h_1 : timespec == "auto" then 
    if h_2 : PastaLean.pyTruthy us then 
      timespec := "microseconds"
    else
      timespec := "seconds"
  if h_2 : timespec == "hours" then 
    let p'_ret_1 := _pad'rn hh (2 : Int)
    return p'_ret_1
  if h_3 : timespec == "minutes" then 
    let p'_ret_1 := _pad'rn hh (2 : Int) +ₚ ":" +ₚ _pad'rn mm (2 : Int)
    return p'_ret_1
  if h_4 : timespec == "seconds" then 
    let p'_ret_1 := _pad'rn hh (2 : Int) +ₚ ":" +ₚ _pad'rn mm (2 : Int) +ₚ ":" +ₚ _pad'rn ss (2 : Int)
    return p'_ret_1
  if h_5 : timespec == "milliseconds" then 
    let p'_ret_1 :=
      _pad'rn hh (2 : Int) +ₚ ":" +ₚ _pad'rn mm (2 : Int) +ₚ ":" +ₚ _pad'rn ss (2 : Int) +ₚ "." +ₚ
        _pad'rn (PastaLean.pyFloorDiv us (1000 : Int)) (3 : Int)
    return p'_ret_1
  if h_6 : timespec == "microseconds" then 
    let p'_ret_1 :=
      _pad'rn hh (2 : Int) +ₚ ":" +ₚ _pad'rn mm (2 : Int) +ₚ ":" +ₚ _pad'rn ss (2 : Int) +ₚ "." +ₚ _pad'rn us (6 : Int)
    return p'_ret_1
  throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "Unknown timespec value"))

def _parse_digits : String → Int → Int → PastaLean.ProofMode.PyProofM Int := fun (s : String) ↦
  fun (start : Int) ↦ fun (count : Int) ↦ do
  if h_1 : start +ₚ count > PastaLean.pyLen s then 
    throw
        (PastaLean.PyException.Raise "ValueError"
          (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
  let mut value : Int := (0 : Int)
  for i in (PastaLean.pyRange (start +ₚ count) start)do
    let mut c : String := s⦋i⦌
    if h_2 : c < "0" ∨ c > "9" then 
      throw
          (PastaLean.PyException.Raise "ValueError"
            (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
    value := value *ₚ (10 : Int) +ₚ PastaLean.pyOrd c -ₚ (48 : Int)
  return value

attribute [simp] _parse_digits

def _parse_digits'rn : String → Int → Int → PastaLean.PyExcept Int := fun (s : String) ↦ fun (start : Int) ↦
  fun (count : Int) ↦ do
  if h_1 : start +ₚ count > PastaLean.pyLen s then 
    throw
        (PastaLean.PyException.Raise "ValueError"
          (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
  let mut value : Int := (0 : Int)
  for i in (PastaLean.pyRange (start +ₚ count) start)do
    let mut c : String := s⦋i⦌
    if h_2 : decide (c < "0") || decide (c > "9") then 
      throw
          (PastaLean.PyException.Raise "ValueError"
            (ToString.toString s! "Invalid isoformat string: {PastaLean.PyPrintable.pyReprify s}"))
    value := value *ₚ (10 : Int) +ₚ PastaLean.pyOrd c -ₚ (48 : Int)
  return value

def _strftime := fun (fmt : String) ↦ fun (year : Int) ↦ fun (month : Int) ↦ fun (day : Int) ↦
  fun (hour : Int) ↦ fun (minute : Int) ↦ fun (second : Int) ↦ fun (microsecond : Int) ↦ fun (weekday : Int) ↦
  fun (yday : Int) ↦
  Id.run
    (do
      let mut out : List String := []
      let mut i : Int := (0 : Int)
      let mut n : Int := PastaLean.pyLen fmt
      while (i < n) do
        let mut ch : String := fmt⦋i⦌
        i := i +ₚ (1 : Int)
        if h_1 : ch ≠ "%" ∨ i ≥ n then 
          out := PastaLean.pyAppend out ch
          continue
        ch := fmt⦋i⦌
        i := i +ₚ (1 : Int)
        if h_2 : ch = "Y" then 
          out := PastaLean.pyAppend out (_pad year (4 : Int))
        else
          if h_3 : ch = "y" then 
            out := PastaLean.pyAppend out (_pad (year %ₚ (100 : Int)) (2 : Int))
          else
            if h_4 : ch = "m" then 
              out := PastaLean.pyAppend out (_pad month (2 : Int))
            else
              if h_5 : ch = "d" then 
                out := PastaLean.pyAppend out (_pad day (2 : Int))
              else
                if h_6 : ch = "H" then 
                  out := PastaLean.pyAppend out (_pad hour (2 : Int))
                else
                  if h_7 : ch = "I" then 
                    let mut h12 : Int := hour %ₚ (12 : Int)
                    if h_8 : h12 = (0 : Int) then 
                      h12 := (12 : Int)
                    out := PastaLean.pyAppend out (_pad h12 (2 : Int))
                  else
                    if h_8 : ch = "p" then 
                      if h_9 : hour < (12 : Int) then 
                        out := PastaLean.pyAppend out "AM"
                      else
                        out := PastaLean.pyAppend out "PM"
                    else
                      if h_9 : ch = "M" then 
                        out := PastaLean.pyAppend out (_pad minute (2 : Int))
                      else
                        if h_10 : ch = "S" then 
                          out := PastaLean.pyAppend out (_pad second (2 : Int))
                        else
                          if h_11 : ch = "f" then 
                            out := PastaLean.pyAppend out (_pad microsecond (6 : Int))
                          else
                            if h_12 : ch = "j" then 
                              out := PastaLean.pyAppend out (_pad yday (3 : Int))
                            else
                              if h_13 : ch = "a" then 
                                out := PastaLean.pyAppend out _DAYNAMES⦋weekday +ₚ (1 : Int)⦌
                              else
                                if h_14 : ch = "A" then 
                                  out := PastaLean.pyAppend out _FULL_DAYNAMES⦋weekday +ₚ (1 : Int)⦌
                                else
                                  if h_15 : ch = "b" then 
                                    out := PastaLean.pyAppend out _MONTHNAMES⦋month⦌
                                  else
                                    if h_16 : ch = "B" then 
                                      out := PastaLean.pyAppend out _FULL_MONTHNAMES⦋month⦌
                                    else
                                      if h_17 : ch = "w" then 
                                        out :=
                                          PastaLean.pyAppend out (PastaLean.pyStr ((weekday +ₚ (1 : Int)) %ₚ (7 : Int)))
                                      else
                                        if h_18 : ch = "u" then 
                                          out := PastaLean.pyAppend out (PastaLean.pyStr (weekday +ₚ (1 : Int)))
                                        else
                                          if h_19 : ch = "%" then 
                                            out := PastaLean.pyAppend out "%"
                                          else
                                            out := PastaLean.pyAppend out ("%" +ₚ ch)
      let p'_ret_1 := PastaLean.pyStringJoin "" out
      return p'_ret_1)

attribute [simp, taste_ingr] _strftime

def _strftime'rn := fun (fmt : String) ↦ fun (year : Int) ↦ fun (month : Int) ↦ fun (day : Int) ↦
  fun (hour : Int) ↦ fun (minute : Int) ↦ fun (second : Int) ↦ fun (microsecond : Int) ↦ fun (weekday : Int) ↦
  fun (yday : Int) ↦
  Id.run
    (do
      let mut out : List String := []
      let mut i : Int := (0 : Int)
      let mut n : Int := PastaLean.pyLen fmt
      while (i < n) do
        let mut ch : String := fmt⦋i⦌
        i := i +ₚ (1 : Int)
        if h_1 : ch != "%" || decide (i ≥ n) then 
          out := PastaLean.pyAppend out ch
          continue
        ch := fmt⦋i⦌
        i := i +ₚ (1 : Int)
        if h_2 : ch == "Y" then 
          out := PastaLean.pyAppend out (_pad'rn year (4 : Int))
        else
          if h_3 : ch == "y" then 
            out := PastaLean.pyAppend out (_pad'rn (year %ₚ (100 : Int)) (2 : Int))
          else
            if h_4 : ch == "m" then 
              out := PastaLean.pyAppend out (_pad'rn month (2 : Int))
            else
              if h_5 : ch == "d" then 
                out := PastaLean.pyAppend out (_pad'rn day (2 : Int))
              else
                if h_6 : ch == "H" then 
                  out := PastaLean.pyAppend out (_pad'rn hour (2 : Int))
                else
                  if h_7 : ch == "I" then 
                    let mut h12 : Int := hour %ₚ (12 : Int)
                    if h_8 : h12 == (0 : Int) then 
                      h12 := (12 : Int)
                    out := PastaLean.pyAppend out (_pad'rn h12 (2 : Int))
                  else
                    if h_8 : ch == "p" then 
                      if h_9 : hour < (12 : Int) then 
                        out := PastaLean.pyAppend out "AM"
                      else
                        out := PastaLean.pyAppend out "PM"
                    else
                      if h_9 : ch == "M" then 
                        out := PastaLean.pyAppend out (_pad'rn minute (2 : Int))
                      else
                        if h_10 : ch == "S" then 
                          out := PastaLean.pyAppend out (_pad'rn second (2 : Int))
                        else
                          if h_11 : ch == "f" then 
                            out := PastaLean.pyAppend out (_pad'rn microsecond (6 : Int))
                          else
                            if h_12 : ch == "j" then 
                              out := PastaLean.pyAppend out (_pad'rn yday (3 : Int))
                            else
                              if h_13 : ch == "a" then 
                                out := PastaLean.pyAppend out _DAYNAMES⦋weekday +ₚ (1 : Int)⦌
                              else
                                if h_14 : ch == "A" then 
                                  out := PastaLean.pyAppend out _FULL_DAYNAMES⦋weekday +ₚ (1 : Int)⦌
                                else
                                  if h_15 : ch == "b" then 
                                    out := PastaLean.pyAppend out _MONTHNAMES⦋month⦌
                                  else
                                    if h_16 : ch == "B" then 
                                      out := PastaLean.pyAppend out _FULL_MONTHNAMES⦋month⦌
                                    else
                                      if h_17 : ch == "w" then 
                                        out :=
                                          PastaLean.pyAppend out (PastaLean.pyStr ((weekday +ₚ (1 : Int)) %ₚ (7 : Int)))
                                      else
                                        if h_18 : ch == "u" then 
                                          out := PastaLean.pyAppend out (PastaLean.pyStr (weekday +ₚ (1 : Int)))
                                        else
                                          if h_19 : ch == "%" then 
                                            out := PastaLean.pyAppend out "%"
                                          else
                                            out := PastaLean.pyAppend out ("%" +ₚ ch)
      let p'_ret_1 := PastaLean.pyStringJoin "" out
      return p'_ret_1)

end Libraries.datetime
