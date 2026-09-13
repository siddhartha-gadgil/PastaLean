import PastaLean.Imports
import PastaLean.PyAPI.CommonProtocols.Iterable
import PastaLean.PyAPI.PyPrint

namespace PastaLean

/--
Typeclass for Python-style `int(...)` coercions used by translated code.

This intentionally keeps the current CP-oriented behavior forgiving: invalid strings
become `0` instead of raising, so `int(input())` stays simple in the current subset.
-/
class PyIntCast (α : Type) where
  pyInt : α → Int

/-- Dispatch Python-style integer coercions. -/
def pyInt {α : Type} [PyIntCast α] (x : α) : Int :=
  PyIntCast.pyInt x

instance : PyIntCast Int where
  pyInt x := x

/-- `int(x)` on an exact-mode real number (a transcendental result). `ℝ` is noncomputable, so this
is `noncomputable` and only lets the program elaborate. -/
noncomputable instance : PyIntCast ℝ where
  pyInt x := ⌊x⌋

/-- `int(q)` on an exact-mode rational truncates toward the floor (`⌊q⌋`), computable. -/
instance : PyIntCast Rat where
  pyInt q := ⌊q⌋

instance : PyIntCast Nat where
  pyInt x := x

instance : PyIntCast Bool where
  pyInt
    | true => 1
    | false => 0

instance : PyIntCast String where
  pyInt s := s.trimAscii.toString.toInt? |>.getD 0

/-- Python `int(x)` on a float truncates toward zero (e.g. `int(n ** 0.5)`). -/
instance : PyIntCast Float where
  pyInt x := if x ≥ 0 then (x.toUInt64.toNat : Int) else -((-x).toUInt64.toNat : Int)

/-- Python `int(s, base)`: parse the string `s` as an integer in `base` (2–36), with an optional
sign and the usual `0x`/`0b`/`0o` prefix for base 16/2/8. Malformed input yields `0`. -/
def pyIntBase (s : String) (base : Int) : Int := Id.run do
  let b := base.toNat
  if b < 2 then return 0
  let mut chars := s.trimAscii.toString.toList
  let mut neg := false
  match chars with
  | '-' :: rest => neg := true; chars := rest
  | '+' :: rest => chars := rest
  | _ => pure ()
  match b, chars with
  | 16, '0' :: c :: rest => if c == 'x' || c == 'X' then chars := rest
  | 2,  '0' :: c :: rest => if c == 'b' || c == 'B' then chars := rest
  | 8,  '0' :: c :: rest => if c == 'o' || c == 'O' then chars := rest
  | _, _ => pure ()
  if chars.isEmpty then return 0
  let digit? (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if c.isAlpha then some (c.toLower.toNat - 'a'.toNat + 10)
    else none
  let mut acc : Nat := 0
  for c in chars do
    match digit? c with
    | some d => if d < b then acc := acc * b + d else return 0
    | none => return 0
  return if neg then -(acc : Int) else (acc : Int)

/--
Python-style `str(...)` coercion.

This reuses the printing runtime so values render with the same Python-like surface as
they would inside `print(...)`.
-/
def pyStr {α : Type} [PyPrintable α] (x : α) : String :=
  pyStringify x

/--
Python-style eager `list(...)` coercion.

This currently follows the iterable protocol, so strings become character lists,
lists stay lists, and dictionaries become their key lists.
-/
def pyList {α β : Type} [PyIterable α β] (x : α) : List β :=
  pyIter x

/-- Convert an `Int` to a `Float` (no `Float.ofInt` in core; build from the magnitude). -/
def floatOfInt (x : Int) : Float :=
  if x ≥ 0 then Float.ofNat x.toNat else - Float.ofNat (-x).toNat

/-- Python widens `int` to `float` implicitly (`xs[i] = 0` into a float list, `f = g[i]` from an int
matrix into a float one). Mirror it so an `Int` value flows into a `Float` slot. Only relevant in
`--approx` (Float) mode; exact mode uses `ℚ`, which already has `IntCast`. -/
instance : Coe Int Float := ⟨floatOfInt⟩
instance : Coe Nat Float := ⟨Float.ofNat⟩

/-- Python's numeric tower bottoms out at `bool ⊆ int` (`True == 1`), which widens on up
(`sum([True, False, True]) == 2`, a `bool` flowing into an int/float/ℚ slot). `int → ℚ`/`float`/`ℝ`
and `ℚ`/`int → ℝ` already come from Mathlib / the `Coe Int Float` above, completing the tower
`bool < int < {float, ℚ} < ℝ`. -/
instance : Coe Bool Int   := ⟨fun b => if b then 1 else 0⟩
instance : Coe Bool Float := ⟨fun b => if b then 1.0 else 0.0⟩
instance : Coe Bool Rat   := ⟨fun b => if b then 1 else 0⟩

/--
Typeclass for Python-style `float(...)` coercions.

Numeric inputs convert directly. Strings recognise the `inf`/`-inf`/`nan` sentinels
(common in competitive programming as comparison bounds); other strings currently fall back
to `0.0` since the runtime has no general float parser yet.
-/
class PyFloatCast (α : Type) where
  pyFloat : α → Float

/-- Dispatch Python-style float coercions. -/
def pyFloat {α : Type} [PyFloatCast α] (x : α) : Float :=
  PyFloatCast.pyFloat x

instance : PyFloatCast Float where pyFloat x := x
-- `@[default_instance]` pins an otherwise-unconstrained `pyFloat x` (e.g. the run twin of
-- `a / b` with untyped params, emitted as `pyFloat a /ₚ b`) to `Int`.
@[default_instance]
instance : PyFloatCast Int where pyFloat x := floatOfInt x
instance : PyFloatCast Nat where pyFloat x := Float.ofNat x
instance : PyFloatCast Bool where
  pyFloat | true => 1.0 | false => 0.0
-- `float(q)` on a rational (`float(float('inf'))`, or a run twin whose value stayed `ℚ`): its `Float`.
instance : PyFloatCast Rat where pyFloat x := x.toFloat
/-- `10.0 ^ n` built by repeated multiplication (avoids `Nat` overflow for the exponent). -/
private def tenPowNat : Nat → Float
  | 0 => 1.0
  | n + 1 => 10.0 * tenPowNat n

/--
Parse a Python-style decimal float literal: optional sign, integer and/or fractional part,
and an optional `e`/`E` exponent (e.g. `"2.75"`, `"-.5"`, `"1.5e-3"`). Anything unparseable
in a part contributes `0`, matching the forgiving `int(...)` cast above.
-/
private def parseFloatString (s : String) : Float :=
  let t := s.trimAscii.toString
  if t == "inf" || t == "+inf" || t == "Infinity" then (1.0 : Float) / 0.0
  else if t == "-inf" || t == "-Infinity" then (-1.0 : Float) / 0.0
  else if t == "nan" then (0.0 : Float) / 0.0
  else
    let (neg, body) :=
      if t.startsWith "-" then (true, (t.drop 1).toString)
      else if t.startsWith "+" then (false, (t.drop 1).toString)
      else (false, t)
    -- normalise the exponent marker so the split below catches both `e` and `E`
    let lower := body.map (fun c => if c == 'E' then 'e' else c)
    let (mant, exp) :=
      match lower.splitOn "e" with
      | [m] => (m, (0 : Int))
      | [m, e] => (m, e.toInt?.getD 0)
      | _ => (lower, 0)
    let (ip, fp) :=
      match mant.splitOn "." with
      | [i] => (i, "")
      | [i, f] => (i, f)
      | _ => (mant, "")
    let intVal : Nat := ip.toNat?.getD 0
    let fracVal : Nat := fp.toNat?.getD 0
    let base := Float.ofNat intVal + Float.ofNat fracVal / tenPowNat fp.length
    let scale := if exp ≥ 0 then tenPowNat exp.toNat else 1.0 / tenPowNat (-exp).toNat
    let v := base * scale
    if neg then -v else v

instance : PyFloatCast String where
  pyFloat s := parseFloatString s

/-! ## Exact-mode `float(...)` → `ℚ`

In the default (exact) numeric mode `float(x)` lowers to `pyRat`, producing an exact rational.
Notably a decimal string parses *exactly* (`float("0.1") = 1/10`), and `int`/`bool`/`Rat` inputs
coerce losslessly. A non-finite string (`float("inf")`) routes through `pyRatNonFinite`, so a
runtime-computed string gives the SAME result as the *literal* `float('inf')`. -/

/-- Exact-mode stand-in for a non-finite float, which `ℚ` cannot represent. `inf`/`-inf` become a
sentinel far outside any competitive value range (so the `ans = -inf; ans = max(ans, …)` /
`best = inf; best = min(best, …)` initializer idiom behaves). `nan` has NO honest `ℚ` value — `0`
would be silently wrong (real `nan` propagates through arithmetic and compares `False` against
everything, itself included), so it **panics loudly** instead; use `--approx` (Float) mode for genuine
NaN semantics. The `inf` sentinel is NOT a true infinity — returning it verbatim still mismatches. -/
def pyRatNonFinite (literal : String) : Rat :=
  let s := literal.toLower
  if s.endsWith "nan" then
    -- `nan` has NO exact-`ℚ` value, and `0` is silently wrong (real `nan` propagates through
    -- arithmetic and compares `False` against everything, including itself — `0` does neither). Fail
    -- loudly rather than lie; use `--approx` (Float) mode for genuine NaN semantics.
    panic! "float('nan') is unrepresentable in exact (ℚ) mode — run with --approx for real NaN"
  else
    let big : Rat := (10 : Rat) ^ (30 : Nat)
    if s.startsWith "-" then -big else big

/-- `ℤ` form of the same sentinel, for an integer DP (`ans = -inf; ans = max(ans, …)` where the
function is annotated `-> int`). Python compares `-inf` against ints happily; Lean needs one type. -/
def pyIntNonFinite (literal : String) : Int :=
  let s := literal.toLower
  if s.endsWith "nan" then
    panic! "float('nan') is unrepresentable in exact (ℤ) mode — run with --approx for real NaN"
  else
    let big : Int := (10 : Int) ^ (30 : Nat)
    if s.startsWith "-" then -big else big

/-- A non-finite float literal takes its type from the slot it lands in, so one `float('inf')`
serves an `ℚ` table and an `ℤ` one. `ℚ` is the default when the context leaves it open. -/
class PyNonFinite (α : Type) where
  nonFinite : String → α

@[default_instance] instance : PyNonFinite Rat where nonFinite := pyRatNonFinite
instance : PyNonFinite Int where nonFinite := pyIntNonFinite
instance : PyNonFinite Float where
  nonFinite s :=
    let t := s.toLower
    if t.endsWith "nan" then 0.0
    else if t.startsWith "-" then -(1.0 / 0.0) else 1.0 / 0.0

/-- Codegen target for a literal `float('inf')` / `float('nan')`. -/
def pyNonFinite {α : Type} [PyNonFinite α] (literal : String) : α :=
  PyNonFinite.nonFinite literal

/-- Typeclass for exact-mode `float(...)` coercions producing `ℚ`. -/
class PyRatCast (α : Type) where
  pyRat : α → Rat

/-- Dispatch exact-mode float coercions to `ℚ`. -/
def pyRat {α : Type} [PyRatCast α] (x : α) : Rat :=
  PyRatCast.pyRat x

instance : PyRatCast Rat where pyRat x := x
instance : PyRatCast Int where pyRat x := (x : Rat)
instance : PyRatCast Nat where pyRat x := (x : Rat)
instance : PyRatCast Bool where
  pyRat | true => 1 | false => 0

/-- `10 ^ n` as a `ℚ` via repeated multiplication. -/
private def tenPowNatRat : Nat → Rat
  | 0 => 1
  | n + 1 => 10 * tenPowNatRat n

/-- Parse a Python-style decimal float literal into an *exact* `ℚ` (sign, integer/fractional
parts, optional `e`/`E` exponent). `inf`/`nan` are not representable in `ℚ` and degrade to `0`. -/
private def parseRatString (s : String) : Rat :=
  let t := s.trimAscii.toString
  let tl := t.toLower
  -- A runtime-computed non-finite string (`float(x)` with `x == "inf"`) must give the SAME result as
  -- the literal `float('inf')`, which lowers to `pyRatNonFinite`. Routing through it keeps them
  -- consistent (and makes `nan` fail loudly there rather than silently becoming `0`).
  if tl == "inf" || tl == "+inf" || tl == "infinity" || tl == "-inf" || tl == "-infinity"
     || tl == "+infinity" || tl == "nan" || tl == "-nan" then pyRatNonFinite t
  else
    let (neg, body) :=
      if t.startsWith "-" then (true, (t.drop 1).toString)
      else if t.startsWith "+" then (false, (t.drop 1).toString)
      else (false, t)
    let lower := body.map (fun c => if c == 'E' then 'e' else c)
    let (mant, exp) :=
      match lower.splitOn "e" with
      | [m] => (m, (0 : Int))
      | [m, e] => (m, e.toInt?.getD 0)
      | _ => (lower, 0)
    let (ip, fp) :=
      match mant.splitOn "." with
      | [i] => (i, "")
      | [i, f] => (i, f)
      | _ => (mant, "")
    let intVal : Nat := ip.toNat?.getD 0
    let fracVal : Nat := fp.toNat?.getD 0
    let base : Rat := (intVal : Rat) + (fracVal : Rat) / tenPowNatRat fp.length
    let scale : Rat := if exp ≥ 0 then tenPowNatRat exp.toNat else 1 / tenPowNatRat (-exp).toNat
    let v := base * scale
    if neg then -v else v

instance : PyRatCast String where pyRat s := parseRatString s

end PastaLean
