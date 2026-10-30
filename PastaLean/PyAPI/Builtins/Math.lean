import PastaLean.Imports
import PastaLean.PyAPI.FloatOps

namespace PastaLean

/-!
Python's builtin `pow`.

`pow(b, e)` is the same as `b ** e`; `pow(b, e, m)` is *modular* exponentiation,
`(b ** e) % m`, computed with fast (square-and-multiply) exponentiation so that the
competitive-programming idiom `pow(k, p, 1000000007)` with a huge exponent stays cheap
instead of materializing the astronomically large `b ** e` first.
-/

/-- Square-and-multiply helper: `(b ^ e * acc) % m`, halving `e` each step. -/
private partial def pyPowModGo (m b e acc : Nat) : Nat :=
  if e == 0 then acc
  else
    let acc := if e % 2 == 1 then (acc * b) % m else acc
    pyPowModGo m ((b * b) % m) (e / 2) acc

/-- Fast modular exponentiation over the naturals: `(base ^ exp) % m` (with `m = 0` meaning
"no modulus", i.e. plain `base ^ exp`). -/
def pyPowModNat (base exp m : Nat) : Nat :=
  if m == 0 then base ^ exp
  else pyPowModGo m (base % m) exp (1 % m)

/-- Python `pow(base, exp, m)` modular exponentiation on integers, normalizing the result into
`[0, m)` like Python. A zero modulus falls back to plain `base ^ exp` (the 2-arg form passes
`m = 0`). Negative exponents are not supported (Python would return a float / modular inverse);
they are clamped via `toNat`, matching competitive-programming use. -/
def pyPow (base exp : Int) (m : Int := 0) : Int :=
  if m == 0 then
    base ^ exp.toNat
  else
    let mn := m.natAbs
    -- reduce the base into [0, m) first so `toNat` is faithful for negative bases
    let b := ((base % m) + m) % m
    (pyPowModNat b.toNat exp.toNat mn : Int)

/-! ### `abs` -/

/-- Python's builtin `abs`, kept polymorphic over the numeric types via a small protocol so the
result type matches the argument (`abs(-3) : Int`, `abs(-2.5) : Float`). -/
class PyAbs (α : Type) where
  pyAbs : α → α

/-- Dispatch Python `abs` through the `PyAbs` protocol. -/
def pyAbs {α : Type} [PyAbs α] (x : α) : α := PyAbs.pyAbs x

instance : PyAbs Int where pyAbs x := if x < 0 then -x else x
instance : PyAbs Nat where pyAbs x := x
instance : PyAbs Float where pyAbs x := x.abs
instance : PyAbs Rat where pyAbs x := if x < 0 then -x else x

/-! ### `divmod` -/

/-- Python `divmod(a, b) = (a // b, a % b)`, flooring quotient (`Int.fdiv`, matching `pyFloorDiv`)
so the remainder `a - b*q` carries the divisor's sign, like Python. `divmod(-21, 10) = (-3, 9)`. -/
def pyDivmod (a b : Int) : Int × Int :=
  let q := Int.fdiv a b
  (q, a - b * q)

/-! ### `round` -/

/-- Python `round(x)` on a float: an int, ties to even, exact for any magnitude. -/
def pyRound (x : Float) : Int := pyFloatRoundInt x

/-- Python `round(x, ndigits)`: round to `ndigits` decimal places, staying in the same numeric type.
Polymorphic so the exact/real twin (`x : ℝ`, e.g. `round(area ** 0.5, 2)` where a root is irrational)
rounds in `ℝ`, while the run twin rounds in `Float`. -/
class PyRoundDigitsC (α : Type) where
  pyRoundDigits : α → Int → α

def pyRoundDigitsFloat (x : Float) (ndigits : Int) : Float := pyFloatRoundDigits x ndigits

/-- Round `x` to the nearest integer, ties to even (Python's `round`). Mathlib's `round` is
half-*up*, so ties like `round(0.5)`/`round(2.5)` diverge from Python; this reproduces the
banker's rounding CPython uses for both `round(x)` and `round(x, n)`. -/
def ratRoundHalfEven (x : ℚ) : ℤ :=
  let fl := ⌊x⌋
  let diff := x - (fl : ℚ)
  if diff < 1/2 then fl
  else if diff > 1/2 then fl + 1
  else if fl % 2 == 0 then fl else fl + 1

noncomputable def realRoundHalfEven (x : ℝ) : ℤ :=
  let fl := ⌊x⌋
  let diff := x - (fl : ℝ)
  if diff < 1/2 then fl
  else if diff > 1/2 then fl + 1
  else if fl % 2 == 0 then fl else fl + 1

noncomputable def pyRoundDigitsReal (x : ℝ) (ndigits : Int) : ℝ :=
  let p : ℝ := (10 : ℝ) ^ ndigits
  ((realRoundHalfEven (x * p) : ℤ) : ℝ) / p

/-- Exact-mode `round(x, n)` on a `ℚ` (`round(sum(t)/len(t), 5)` — `sum/len` is `ℚ`). Computable. -/
def pyRoundDigitsRat (x : ℚ) (ndigits : Int) : ℚ :=
  let p : ℚ := (10 : ℚ) ^ ndigits
  ((ratRoundHalfEven (x * p) : ℤ) : ℚ) / p

instance : PyRoundDigitsC Float := ⟨pyRoundDigitsFloat⟩
instance : PyRoundDigitsC ℚ := ⟨pyRoundDigitsRat⟩
noncomputable instance : PyRoundDigitsC ℝ := ⟨pyRoundDigitsReal⟩

export PyRoundDigitsC (pyRoundDigits)

/-- `int.bit_length()`: bits needed to represent `|n|`, and `0` for `0`. `pyBitLength 5 = 3`. -/
def pyBitLength (n : Int) : Int :=
  let m := n.natAbs
  if m == 0 then 0 else Int.ofNat (Nat.toDigits 2 m).length

/-- `int.bit_count()`: number of one-bits in `|n|`. `pyBitCount 5 = 2`. -/
def pyBitCount (n : Int) : Int :=
  Int.ofNat ((Nat.toDigits 2 n.natAbs).count '1')

/-- Python's `bin`/`hex`/`oct` prefixed radix strings; the sign leads, as in CPython.
`pyBin 5 = "0b101"`, `pyBin (-5) = "-0b101"`, `pyHex 255 = "0xff"`, `pyOct 8 = "0o10"`. -/
private def pyRadixString (tag : String) (base : Nat) (n : Int) : String :=
  (if n < 0 then "-" else "") ++ tag ++ String.ofList (Nat.toDigits base n.natAbs)

def pyBin (n : Int) : String := pyRadixString "0b" 2 n
def pyHex (n : Int) : String := pyRadixString "0x" 16 n
def pyOct (n : Int) : String := pyRadixString "0o" 8 n

end PastaLean
