import PastaLean.Imports

/-!
# Python-style `repr` for `Float`

Lean's `Float.toString` is a fixed 6-digit `%f` — it both pads (`3.000000`) and *truncates*
(`0.285714`, losing precision). Python prints the **shortest decimal string that round-trips** to
the same double (`3.0`, `0.2857142857142857`, `3.141592653589793`). This file reproduces that:
recover the double's exact rational value from its IEEE-754 bits, then search for the fewest
significant digits whose decimal rounds back to the same float — checked *exactly* against the
float's neighbours (no lossy re-parse).
-/

namespace PastaLean

/-- Exact rational value of a finite IEEE-754 double, from its bits. -/
def floatToRat (x : Float) : Rat :=
  let bits := x.toBits
  let sign := (bits >>> 63) == 1
  let expBits := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  let (mant, e2) : Int × Int :=
    if expBits == 0 then (Int.ofNat frac, -1074)                                  -- subnormal
    else (Int.ofNat (frac + 0x10000000000000), (Int.ofNat expBits) - 1075)        -- 2^52 + frac
  let magnitude : Rat := (mant : Rat) * (2 : Rat) ^ e2
  if sign then -magnitude else magnitude

private def numDigits (n : Nat) : Nat := (toString n).length

/-- `⌊log₁₀ q⌋` for `q > 0` (its most-significant decimal position). `digits(num) − digits(den)` is
always the true exponent or one above it, so a single downward check settles it. -/
private def decExp (q : Rat) : Int :=
  let n := q.num.natAbs
  let d := q.den
  let est : Int := (numDigits n : Int) - (numDigits d : Int)
  let geEst : Bool :=
    if est ≥ 0 then (n : Int) ≥ (d : Int) * 10 ^ est.toNat
    else (n : Int) * 10 ^ (-est).toNat ≥ (d : Int)
  if geEst then est else est - 1

private def strTake (s : String) (n : Nat) : String := String.ofList (s.toList.take n)
private def strDrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
private def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- Place the `p`-digit significand `R` at decimal exponent `E` (Python's `%g` layout: plain decimal
for `-4 ≤ E < 16`, scientific otherwise). Integers keep a trailing `.0`. -/
private def layout (R : Nat) (p : Nat) (E : Int) : String :=
  let raw := toString R
  let ds := if raw.length < p then zeros (p - raw.length) ++ raw else raw
  if E < -4 || E ≥ 16 then
    let tail := strDrop ds 1
    let mant := if tail.isEmpty then strTake ds 1 else strTake ds 1 ++ "." ++ tail
    let eabs := (if E ≥ 0 then E else -E).toNat
    mant ++ "e" ++ (if E ≥ 0 then "+" else "-") ++ (if eabs < 10 then "0" ++ toString eabs else toString eabs)
  else
    let pointPos : Int := E + 1
    if pointPos ≤ 0 then "0." ++ zeros (-pointPos).toNat ++ ds
    else if pointPos ≥ (p : Int) then ds ++ zeros (pointPos.toNat - p) ++ ".0"
    else strTake ds pointPos.toNat ++ "." ++ strDrop ds pointPos.toNat

/-- `|q|` rounded to `p` significant digits: the exact decimal value it denotes, and its string. -/
private def sigRepr (q : Rat) (p : Nat) : Rat × String :=
  let E := decExp q
  let s : Int := (p : Int) - 1 - E
  let (num, den) : Int × Int :=
    if s ≥ 0 then (q.num * 10 ^ s.toNat, (q.den : Int))
    else (q.num, (q.den : Int) * 10 ^ (-s).toNat)
  let R0 : Int := (2 * num + den) / (2 * den)              -- round half up (num, den > 0)
  let (R, E') : Int × Int := if R0 ≥ 10 ^ p then (R0 / 10, E + 1) else (R0, E)
  ((R : Rat) * (10 : Rat) ^ (E' - (p : Int) + 1), layout R.natAbs p E')

/-- Does the decimal value `r` round to the positive float `x`? Exact: `r` lies within the midpoints
to `x`'s two IEEE neighbours (obtained by bumping the bit pattern). -/
private def roundsToPos (r : Rat) (x : Float) : Bool :=
  let q := floatToRat x
  let midHi := (q + floatToRat (Float.ofBits (x.toBits + 1))) / 2
  let midLo := (q + floatToRat (Float.ofBits (x.toBits - 1))) / 2
  midLo ≤ r && r ≤ midHi

/-- The shortest `p ∈ [1,17]` significant digits of a positive finite `x` that round-trips. -/
private def shortestPos (x : Float) : String := Id.run do
  let q := floatToRat x
  for p in [1:18] do
    let (v, str) := sigRepr q p
    if roundsToPos v x then return str
  return (sigRepr q 17).2

/-- Python `repr(float)`: shortest round-tripping decimal, with `.0` on integers. -/
def pyFloatRepr (x : Float) : String :=
  if x.isNaN then "nan"
  else if x == (1.0 / 0.0) then "inf"
  else if x == -(1.0 / 0.0) then "-inf"
  else if x == 0.0 then (if x.toBits >>> 63 == 1 then "-0.0" else "0.0")
  else if x < 0.0 then "-" ++ shortestPos (-x)
  else shortestPos x

end PastaLean
