import PastaLean.Imports
import PastaLean.PyAPI.PyPanic

/-!
# Python's float operations, bit for bit

The runnable twin computes in Lean's `Float` (IEEE binary64, like a CPython `float`), and IEEE
`+ - * / sqrt` are already exact matches. What differs is everything Python builds *on top of* IEEE:
`//` and `%` (CPython's `fmod`-based `float_divmod`), `int()`/`round()`/`math.floor` (exact big
integers, `OverflowError` on `inf`), correctly rounded int→float and int `/` int, `round(x, n)`,
`hypot`, `float(str)`, and `**`'s error rules. Each is reproduced here from an exact decoding of the
double (`floatDecode`) and one correctly rounded conversion back (`roundToFloat`).
-/

namespace PastaLean

/-- The value `v`; at run time also records the Python error `msg` (`"ZeroDivisionError: …"`) in
`pyErrorLog`. For an operation whose total model keeps a value (e.g. `a % 0 = a`) while Python raises:
proofs see `v`, `pastalean refute` sees the raise. -/
@[never_extract, noinline]
unsafe def pyRaiseOrImpl {α : Type} (msg : String) (v : α) : α :=
  -- The value comes out of the IO action, so the write cannot be dropped as dead code.
  unsafeBaseIO (do pyErrorLog.set (some ((msg.splitOn ":").headD msg)); pure v)

@[never_extract, implemented_by pyRaiseOrImpl]
def pyRaiseOr {α : Type} (_msg : String) (v : α) : α := v

@[simp] theorem pyRaiseOr_eq {α : Type} (msg : String) (v : α) : pyRaiseOr msg v = v := rfl

/-- `|x| = m · 2^e` for a finite double, with its sign. -/
def floatDecode (x : Float) : Bool × Nat × Int :=
  let bits := x.toBits
  let neg := bits >>> 63 == 1
  let ex := ((bits >>> 52) &&& 0x7FF).toNat
  let f := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if ex == 0 then (neg, f, -1074) else (neg, f + 2 ^ 52, (ex : Int) - 1075)

def floatSignBit (x : Float) : Bool := x.toBits >>> 63 == 1

/-- `|x|` with the sign of `y` (C `copysign`). -/
def floatCopySign (x y : Float) : Float :=
  Float.ofBits ((x.toBits &&& 0x7FFFFFFFFFFFFFFF) ||| (y.toBits &&& 0x8000000000000000))

/-- The double nearest `±(m + δ) · 2^e` (ties to even), where `δ ∈ (0, 1)` when `sticky` and `0`
otherwise; `±inf` past the largest double. With `sticky`, `m` must carry at least 54 bits. -/
def roundToFloat (neg : Bool) (m : Nat) (e : Int) (sticky : Bool := false) : Float :=
  let r : Float :=
    if m == 0 then 0.0 else
    let top : Int := m.log2
    -- Bits to drop: down to 53 significant bits, but never below the subnormal unit 2^-1074.
    let s : Int := max (top - 52) (-1074 - e)
    let (q, e') :=
      if s ≤ 0 then (m * 2 ^ (-s).toNat, e + s)
      else
        let k := s.toNat
        let q := m >>> k
        let rem := m % 2 ^ k
        let half := 2 ^ (k - 1)
        let up := rem > half || (rem == half && (sticky || q % 2 == 1))
        (if up then q + 1 else q, e + s)
    if q == 0 then 0.0
    else if (q.log2 : Int) + e' ≥ 1024 then (1.0 : Float) / 0.0
    else Float.scaleB (Float.ofNat q) e'
  if neg then -r else r

/-- The double nearest a rational (ties to even). -/
def ratToFloatRound (q : ℚ) : Float :=
  let num := q.num.natAbs
  let den := q.den
  if num == 0 then 0.0 else
  -- At least 55 quotient bits, so the remainder only needs to say "above or below".
  let s : Int := 55 + (den.log2 : Int) - (num.log2 : Int)
  let (m, sticky) :=
    if s ≥ 0 then ((num <<< s.toNat) / den, (num <<< s.toNat) % den != 0)
    else (num / (den <<< (-s).toNat), num % (den <<< (-s).toNat) != 0)
  roundToFloat (q < 0) m (-s) sticky

/-- Python `float(n)` for an int: correctly rounded; `OverflowError` past the largest double. -/
def pyIntToFloat (n : Int) : Float :=
  let r := roundToFloat (n < 0) n.natAbs 0
  if r.isInf then pyPanic "OverflowError: int too large to convert to float" else r

/-- Python `a / b` for ints: the exact quotient, rounded once. -/
def pyIntTrueDiv (a b : Int) : Float :=
  if b == 0 then pyPanic "ZeroDivisionError: division by zero"
  else if a == 0 then (if b < 0 then -0.0 else 0.0)
  else
    let r := ratToFloatRound ((a : ℚ) / b)
    if r.isInf then pyPanic "OverflowError: integer division result too large for a float" else r

/-- The exact value of a finite double. -/
def floatExactRat (x : Float) : ℚ :=
  let (neg, m, e) := floatDecode x
  let v : ℚ := if e ≥ 0 then ((m * 2 ^ e.toNat : Nat) : ℚ) else (m : ℚ) / ((2 ^ (-e).toNat : Nat) : ℚ)
  if neg then -v else v

private def nonFiniteToInt (x : Float) : Int :=
  if x.isNaN then pyPanic "ValueError: cannot convert float NaN to integer"
  else pyPanic "OverflowError: cannot convert float infinity to integer"

/-- Python `int(x)`: truncation toward zero, exact for any magnitude. -/
def pyFloatToInt (x : Float) : Int :=
  if !x.isFinite then nonFiniteToInt x else
  let (neg, m, e) := floatDecode x
  let n : Nat := if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
  if neg then -(n : Int) else n

/-- Python `math.floor(x)`. -/
def pyFloatFloorInt (x : Float) : Int :=
  if !x.isFinite then nonFiniteToInt x else
  let q := floatExactRat x
  ⌊q⌋

/-- Python `math.ceil(x)`. -/
def pyFloatCeilInt (x : Float) : Int :=
  if !x.isFinite then nonFiniteToInt x else ⌈floatExactRat x⌉

/-- `q` rounded to an integer, ties to even. -/
def ratRoundHalfEvenInt (q : ℚ) : Int :=
  let fl := ⌊q⌋
  let d := q - fl
  if d < 1/2 then fl else if d > 1/2 then fl + 1 else if fl % 2 == 0 then fl else fl + 1

/-- Python `round(x)` (an int, ties to even). -/
def pyFloatRoundInt (x : Float) : Int :=
  if !x.isFinite then nonFiniteToInt x else ratRoundHalfEvenInt (floatExactRat x)

/-- Python `round(x, n)`: the exact value rounded half-even at `n` decimals, then the nearest double. -/
def pyFloatRoundDigits (x : Float) (n : Int) : Float :=
  if !x.isFinite || x == 0.0 || n > 323 then x
  else if n < -308 then floatCopySign 0.0 x
  else
    let p : ℚ := if n ≥ 0 then ((10 ^ n.toNat : Nat) : ℚ) else 1 / ((10 ^ (-n).toNat : Nat) : ℚ)
    let k := ratRoundHalfEvenInt (floatExactRat x * p)
    let r := ratToFloatRound ((k : ℚ) / p)
    if r.isInf then pyPanic "OverflowError: rounded value too large to represent"
    else if r == 0.0 then floatCopySign 0.0 x else r

/-- C `fmod`: `x - n·y` with `n = trunc(x / y)`, computed exactly (the result is always a double). -/
def floatFmod (x y : Float) : Float :=
  if x.isNaN || y.isNaN || x.isInf || y == 0.0 then (0.0 : Float) / 0.0
  else if y.isInf then x
  else
    let (nx, mx, ex) := floatDecode x
    let (_, my, ey) := floatDecode y
    let e := min ex ey
    let a := mx * 2 ^ (ex - e).toNat
    let b := my * 2 ^ (ey - e).toNat
    let r := roundToFloat nx (a % b) e
    if r == 0.0 then floatCopySign 0.0 x else r

/-- CPython `float_divmod`: `(a // b, a % b)`. -/
def pyFloatDivmod (a b : Float) : Float × Float :=
  let m := floatFmod a b
  let d := (a - m) / b
  let (m, d) :=
    if m != 0.0 then (if (b < 0.0) != (m < 0.0) then (m + b, d - 1.0) else (m, d))
    else (floatCopySign 0.0 b, d)
  let fd :=
    if d != 0.0 then (let f := d.floor; if d - f > 0.5 then f + 1.0 else f)
    else floatCopySign 0.0 (a / b)
  (fd, m)

/-- Python `a // b` on floats. -/
def pyFloatFloorDivPy (a b : Float) : Float :=
  if b == 0.0 then pyPanic "ZeroDivisionError: float floor division by zero" else (pyFloatDivmod a b).1

/-- Python `a % b` on floats. -/
def pyFloatModPy (a b : Float) : Float :=
  if b == 0.0 then pyPanic "ZeroDivisionError: float modulo by zero"
  else
    let m := floatFmod a b
    if m != 0.0 then (if (b < 0.0) != (m < 0.0) then m + b else m) else floatCopySign 0.0 b

/-- Python `math.hypot(x, y)`, correctly rounded from the exact `√(x² + y²)`. -/
def pyFloatHypot (x y : Float) : Float :=
  if x.isInf || y.isInf then (1.0 : Float) / 0.0
  else if x.isNaN || y.isNaN then (0.0 : Float) / 0.0
  else
    let (_, m1, e1) := floatDecode x
    let (_, m2, e2) := floatDecode y
    let e := min e1 e2
    let a := m1 * 2 ^ (e1 - e).toNat
    let b := m2 * 2 ^ (e2 - e).toNat
    let s := a * a + b * b
    if s == 0 then 0.0 else
    let t := if s.log2 ≥ 112 then 0 else (112 - s.log2) / 2 + 1
    let n := s * 4 ^ t
    let r := n.sqrt
    roundToFloat false r (e - t) (r * r != n)

private def isOddInteger (x : Float) : Bool :=
  x.isFinite && x.floor == x && x.abs < 9007199254740992.0 * 2.0 && floatFmod x 2.0 != 0.0

/-- Python `a ** b` on floats (CPython `float_pow`): `ZeroDivisionError` for `0.0 ** negative`,
`OverflowError` when a finite power overflows. A negative base with a non-integer exponent is a
*complex* number in Python, which has no `Float` value: `nan`. -/
def pyFloatPow (a b : Float) : Float :=
  if b == 0.0 then 1.0
  else if a.isNaN then a
  else if b.isNaN then (if a == 1.0 then 1.0 else b)
  else if b.isInf then
    let av := a.abs
    if av == 1.0 then 1.0 else if (b > 0.0) == (av > 1.0) then b.abs else 0.0
  else if a.isInf then
    if b > 0.0 then (if isOddInteger b then a else a.abs)
    else (if isOddInteger b then floatCopySign 0.0 a else 0.0)
  else if a == 0.0 then
    if b < 0.0 then pyPanic "ZeroDivisionError: 0.0 cannot be raised to a negative power"
    else if isOddInteger b then a else 0.0
  else
    let neg := a < 0.0 && isOddInteger b
    if a < 0.0 && b.floor != b then
      -- Python computes this power in the complex plane; it still overflows like a real one.
      if (Float.pow a.abs b).isInf then pyPanic "OverflowError: complex exponentiation" else (0.0 : Float) / 0.0
    else
      let v := Float.pow a.abs b
      let v := if neg then -v else v
      if v.isInf then pyPanic "OverflowError: (34, 'Numerical result out of range')" else v

/-- Python `float(s)`: decimal syntax (underscores between digits, `inf`/`infinity`/`nan` in any case,
optional sign and surrounding whitespace), correctly rounded; `ValueError` otherwise. -/
def pyParseFloat (s : String) : Float :=
  let t := s.trimAscii.toString
  let (neg, body) :=
    if t.startsWith "-" then (true, (t.drop 1).toString)
    else if t.startsWith "+" then (false, (t.drop 1).toString) else (false, t)
  let lower := body.toLower
  if lower == "inf" || lower == "infinity" then (if neg then -1.0 else 1.0) / 0.0
  else if lower == "nan" then (0.0 : Float) / 0.0
  else
    let digitsOk (u : String) : Bool :=
      !u.isEmpty && !u.startsWith "_" && !u.endsWith "_" && (u.splitOn "__").length == 1
        && u.all (fun c => c.isDigit || c == '_')
    let clean (u : String) : String := String.ofList (u.toList.filter (· != '_'))
    let (mant, ex) := match lower.splitOn "e" with
      | [m] => (m, some "0")
      | [m, x] => (m, some x)
      | _ => (lower, none)
    let (ip, fp) := match mant.splitOn "." with
      | [i] => (i, "")
      | [i, f] => (i, f)
      | _ => ("", "")
    let exOk := match ex with
      | some x =>
        let x' := if x.startsWith "-" || x.startsWith "+" then (x.drop 1).toString else x
        digitsOk x'
      | none => false
    if !exOk || (ip.isEmpty && fp.isEmpty) || (!ip.isEmpty && !digitsOk ip) || (!fp.isEmpty && !digitsOk fp)
    then pyPanic s!"ValueError: could not convert string to float: '{s}'"
    else
      let digits := clean ip ++ clean fp
      let exDigits := clean (ex.getD "0")
      let exDigits := if exDigits.startsWith "+" then (exDigits.drop 1).toString else exDigits
      let e10 : Int := (exDigits.toInt?.getD 0) - (clean fp).length
      let m := digits.toNat?.getD 0
      let mag : Int := e10 + (toString m).length
      let r : Float :=
        if m == 0 then 0.0
        else if mag > 330 then (1.0 : Float) / 0.0
        else if mag < -345 then 0.0
        else ratToFloatRound (if e10 ≥ 0 then ((m * 10 ^ e10.toNat : Nat) : ℚ) else (m : ℚ) / ((10 ^ (-e10).toNat : Nat) : ℚ))
      if neg then -r else r

end PastaLean
