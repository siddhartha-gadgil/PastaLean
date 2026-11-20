import PastaLean.PyVerify.Refute.Arb
import Libraries.datetime.Datetime

/-!
# Generators for the `datetime` library's classes

Values are built valid by construction (a day within its month, normalised `timedelta` fields), the
year biased to the calendar's edges (1, leap years, 9999) and both pools of the search: the program's
integer literals feed `timedelta` days, so `date + timedelta(days=8314)`-style targets are reachable.
A witness reads back as `date(year=…, month=…, day=…)`, which CPython rebuilds through its own
`datetime` module.
-/

namespace PastaLean.Refute

open Plausible Libraries.datetime

private def genYear : Gen Int := do
  match (← Gen.choose Nat 0 5 (by omega)).val with
  | 0 => return #[1, 2, 1999, 2000, 2020, 2022, 2024, 9998, 9999][(← Gen.choose Nat 0 8 (by omega)).val]!
  | 1 => return 2000 + ((← Gen.choose Nat 0 60 (by omega)).val : Int)
  | _ => return ((← Gen.choose Nat 1 9999 (by omega)).val : Int)

/-- The `date(…)`/`datetime(…)` literals among constructor literals, as (ordinal, microseconds into the day). -/
def momentsOf (cs : Array (Lean.Name × Array Int)) : Array (Int × Int) :=
  cs.filterMap fun (c, a) =>
    if c != `Libraries.datetime.date && c != `Libraries.datetime.datetime then none else
    let (y, m, d) := (a[0]!, a[1]!, a.getD 2 1)
    if y < 1 || y > 9999 || m < 1 || m > 12 || d < 1 || d > _days_in_month'rn y m then none else
    let us := ((a.getD 3 0 * 60 + a.getD 4 0) * 60 + a.getD 5 0) * 1000000 + a.getD 6 0
    some (_ymd2ord'rn y m d, us)

@[never_extract, noinline]
unsafe def minedMomentsImpl (_ : Unit) : Array (Int × Int) := unsafeBaseIO do return momentsOf (← ctorPool.get)

/-- The program's `date(…)`/`datetime(…)` literals, read from the pool at draw time (never cached: the
pool is set per search, after this code is compiled). -/
@[never_extract, implemented_by minedMomentsImpl]
opaque minedMoments : Unit → Array (Int × Int)

/-- A mined moment, a third of the time shifted by a pool-biased number of days
(`base + timedelta(days=8314) == datetime(2022, …)` needs the target minus 8314 days). -/
def genMinedMoment : Gen (Option (Int × Int)) := do
  let ms := minedMoments ()
  if ms.isEmpty || (← Gen.choose Nat 0 2 (by omega)).val != 0 then return none
  let (o, us) := ms[(← Gen.choose Nat 0 (ms.size - 1) (by omega)).val]!
  let ints := (pool ()).2
  let shift ← match (← Gen.choose Nat 0 2 (by omega)).val with
    | 0 => if ints.isEmpty then genInt else pure ints[(← Gen.choose Nat 0 (ints.size - 1) (by omega)).val]!
    | 1 => genInt
    | _ => pure 0
  let o' := o - shift
  return if 1 ≤ o' && o' ≤ 3652059 then some (o', us) else some (o, us)

private def genYmd : Gen (Int × Int × Int) := do
  -- a third of the time, by ordinal from the program's integer literals (`d1 - d2 == 8314`)
  if (← Gen.choose Nat 0 2 (by omega)).val == 0 then
    let n ← genInt
    return _ord2ymd'rn (max 1 (min 3652059 n.natAbs))
  let y ← genYear
  let m : Int := (← Gen.choose Nat 1 12 (by omega)).val
  let dim := (_days_in_month'rn y m).toNat
  let dayPick := (← Gen.choose Nat 0 3 (by omega)).val
  let mid := (← Gen.choose Nat 1 (max dim 1) (by omega)).val
  let d : Int := if dayPick == 0 then 1 else if dayPick == 1 then dim else mid
  return (y, m, d)

private def genClock : Gen (Int × Int × Int × Int) := do
  let edge := (← Gen.choose Nat 0 3 (by omega)).val == 0
  if edge then return (0, 0, 0, 0)
  let hh := (← Gen.choose Nat 0 23 (by omega)).val
  let mi := (← Gen.choose Nat 0 59 (by omega)).val
  let ss := (← Gen.choose Nat 0 59 (by omega)).val
  let withUs := (← Gen.choose Nat 0 2 (by omega)).val == 0
  let us := (← Gen.choose Nat 0 999999 (by omega)).val
  return (hh, mi, ss, if withUs then us else 0)

private def tdLit (d s us : Int) : PyLit :=
  .obj "timedelta" [("days", .int d), ("seconds", .int s), ("microseconds", .int us)]

/-- A `timedelta` nudged: days by a pool-biased amount, or seconds. -/
def mutateTimedelta (t : timedelta) : Gen timedelta := do
  if ← Gen.chooseAny Bool then return timedelta.ofParts (← mutateInt t._days) t._seconds t._microseconds
  return timedelta.ofParts t._days (← mutateInt t._seconds) t._microseconds

instance : PyArb timedelta where
  toLit t := tdLit t._days t._seconds t._microseconds
  arb := do
    -- the gap between two mined moments (`date(2000, 1, 1) + delta == date(2022, 10, 6)`)
    let ms := minedMoments ()
    if ms.size > 0 && (← Gen.choose Nat 0 2 (by omega)).val == 0 then
      let (oa, ua) := ms[(← Gen.choose Nat 0 (ms.size - 1) (by omega)).val]!
      let (ob, ub) := ms[(← Gen.choose Nat 0 (ms.size - 1) (by omega)).val]!
      return timedelta.ofParts (ob - oa) 0 (ub - ua)
    let days ← genInt
    let whole := (← Gen.choose Nat 0 2 (by omega)).val == 0
    let secs : Int := (← Gen.choose Nat 0 86399 (by omega)).val
    return timedelta.ofParts days (if whole then 0 else secs)
  mutate := mutateTimedelta

instance : PyArb timedelta'rn where
  toLit t := tdLit t._days t._seconds t._microseconds
  arb := do
    let t : timedelta ← PyArb.arb
    return timedelta'rn.ofParts t._days t._seconds t._microseconds
  mutate t := do
    let t' ← mutateTimedelta (timedelta.ofParts t._days t._seconds t._microseconds)
    return timedelta'rn.ofParts t'._days t'._seconds t'._microseconds

private def dateLit (y m d : Int) : PyLit := .obj "date" [("year", .int y), ("month", .int m), ("day", .int d)]

/-- `(y, m, d)` moved by a pool-biased number of days, staying in range. -/
def shiftYmd (y m d : Int) : Gen (Int × Int × Int) := do
  let o := _ymd2ord'rn y m d - (← mutateInt 0)
  return _ord2ymd'rn (max 1 (min 3652059 o))

private def genDateYmd : Gen (Int × Int × Int) := do
  match ← genMinedMoment with
  | some (o, _) => return _ord2ymd'rn o
  | none => genYmd

instance : PyArb date where
  toLit d := dateLit d._year d._month d._day
  arb := do let (y, m, d) ← genDateYmd; return { _year := y, _month := m, _day := d }
  mutate x := do let (y, m, d) ← shiftYmd x._year x._month x._day; return { _year := y, _month := m, _day := d }

instance : PyArb date'rn where
  toLit d := dateLit d._year d._month d._day
  arb := do let (y, m, d) ← genDateYmd; return { _year := y, _month := m, _day := d }
  mutate x := do let (y, m, d) ← shiftYmd x._year x._month x._day; return { _year := y, _month := m, _day := d }

private def genDatetimeFields : Gen ((Int × Int × Int) × (Int × Int × Int × Int)) := do
  match ← genMinedMoment with
  | some (o, us) =>
      let s := us / 1000000
      return (_ord2ymd'rn o, (s / 3600, s / 60 % 60, s % 60, us % 1000000))
  | none => return (← genYmd, ← genClock)

private def datetimeLit (y m d hh mi ss us : Int) : PyLit :=
  .obj "datetime" [("year", .int y), ("month", .int m), ("day", .int d), ("hour", .int hh),
    ("minute", .int mi), ("second", .int ss), ("microsecond", .int us)]

instance : PyArb datetime where
  toLit t := datetimeLit t._year t._month t._day t._hour t._minute t._second t._microsecond
  arb := do
    let ((y, m, d), (hh, mi, ss, us)) ← genDatetimeFields
    return { _year := y, _month := m, _day := d, _hour := hh, _minute := mi, _second := ss,
             _microsecond := us, _tzinfo := none }
  -- the day moved, or one clock field nudged within its range
  mutate t := do
    match (← Gen.choose Nat 0 2 (by omega)).val with
    | 0 => let (y, m, d) ← shiftYmd t._year t._month t._day; return { t with _year := y, _month := m, _day := d }
    | 1 => return { t with _hour := (← mutateInt t._hour) % 24, _minute := (← mutateInt t._minute) % 60 }
    | _ => return { t with _second := (← mutateInt t._second) % 60, _microsecond := 0 }

instance : PyArb datetime'rn where
  toLit t := datetimeLit t._year t._month t._day t._hour t._minute t._second t._microsecond
  arb := do
    let ((y, m, d), (hh, mi, ss, us)) ← genDatetimeFields
    return { _year := y, _month := m, _day := d, _hour := hh, _minute := mi, _second := ss,
             _microsecond := us, _tzinfo := none }
  -- the day moved, or one clock field nudged within its range
  mutate t := do
    match (← Gen.choose Nat 0 2 (by omega)).val with
    | 0 => let (y, m, d) ← shiftYmd t._year t._month t._day; return { t with _year := y, _month := m, _day := d }
    | 1 => return { t with _hour := (← mutateInt t._hour) % 24, _minute := (← mutateInt t._minute) % 60 }
    | _ => return { t with _second := (← mutateInt t._second) % 60, _microsecond := 0 }

end PastaLean.Refute
