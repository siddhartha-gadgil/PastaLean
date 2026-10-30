import PastaLean.Imports
import PastaLean.PyAPI.PyPanic
import PastaLean.PyAPI.FloatOps
import PastaLean.PyAPI.TasteIngr

namespace PastaLean

@[grind]
class PyHAdd (α β : Type) (γ : outParam Type) where
  hAdd : α → β → γ

infixl:65 " +ₚ " => PyHAdd.hAdd

@[default_instance]
instance {α β γ} [HAdd α β γ] : PyHAdd α β γ where
  hAdd := HAdd.hAdd

@[default_instance]
instance (priority := high) : PyHAdd Rat Rat Rat where
  hAdd := fun a b => (a : Rat) + (b : Rat)

-- Keep `Int + Int = Int` (Python semantics) even when the operands are still metavariables at
-- elaboration (e.g. `[x + y for x in xs for y in ys]` over `List Int`). Without this, the
-- `Rat` defaulting above coerces both operands to `ℚ`, which then forces the iterable's element
-- type to `ℚ` and fails (the rat-default-instance hazard). A higher *defaulting* priority on the
-- concrete `Int` instance wins the tie. Mirrors the existing `Int`-preserving behavior of `-ₚ`.
@[default_instance 10001]
instance (priority := high) : PyHAdd Int Int Int where
  hAdd := fun a b => a + b

/-- Python's `bool` is an `int`: `True + 1 = 2`. Lets the common `cnt += a > b` idiom lower. -/
def pyBoolToInt (b : Bool) : Int := if b then 1 else 0

instance (priority := high) : PyHAdd Int Bool Int where hAdd a b := a + pyBoolToInt b
instance (priority := high) : PyHAdd Bool Int Int where hAdd a b := pyBoolToInt a + b
instance (priority := high) : PyHAdd Bool Bool Int where hAdd a b := pyBoolToInt a + pyBoolToInt b

instance : PyHAdd String String String where
  hAdd := String.append

/-- String building by appending a single character, e.g. `s + word[i]`. -/
instance : PyHAdd String Char String where
  hAdd := fun s c => s ++ c.toString

-- String indexing yields a `Char` here, so `word[i] + word[j]` / `word[i] + rest` concat as strings.
instance : PyHAdd Char Char String where hAdd := fun a b => a.toString ++ b.toString
instance : PyHAdd Char String String where hAdd := fun c s => c.toString ++ s

/-- Python list `+` CONCATENATES. Without this, the generic `[HAdd α β γ]` instance resolves to
Mathlib's *pointwise* `Add (List α)` (`[1,2]+[3,4] = [4,6]`) — silently wrong; hence high priority. -/
instance (priority := high) {α : Type} : PyHAdd (List α) (List α) (List α) where
  hAdd := (· ++ ·)

/-! Mixed-numeric list concatenation: `[0] + [inf]*n` puts an `int` list beside a `float`/`ℚ` list;
Python makes one list of the widened element, so we coerce the `int` side and concatenate. -/
instance (priority := high) : PyHAdd (List Int) (List Rat)   (List Rat)   where hAdd xs ys := xs.map (Int.cast) ++ ys
instance (priority := high) : PyHAdd (List Rat) (List Int)   (List Rat)   where hAdd xs ys := xs ++ ys.map (Int.cast)
instance (priority := high) : PyHAdd (List Int) (List Float) (List Float) where hAdd xs ys := xs.map pyIntToFloat ++ ys
instance (priority := high) : PyHAdd (List Float) (List Int) (List Float) where hAdd xs ys := xs ++ ys.map pyIntToFloat

/-- Array concatenation, so an array-backed `[base] + [x]*n` DP-init (`f = [1] + [0]*n`) stays an
`Array` — keeping the loop's `f[i] = v` O(1) instead of the `List` O(n) that turns the DP O(n²). -/
instance (priority := high) {α : Type} : PyHAdd (Array α) (Array α) (Array α) where
  hAdd := (· ++ ·)

/-! Mixed numeric `+`. Lean has no heterogeneous `HAdd Nat Int` / `HAdd Rat Int`, so the
generic `[HAdd α β γ]` instance does not cover these mixed-type sums that arise when one
operand came from integer division (`Rat`) or a length/count (`Nat`). The result widens to
the more general type. -/
instance (priority := high) : PyHAdd Rat Int Rat where
  hAdd := fun a b => a + (b : Rat)

instance (priority := high) : PyHAdd Int Rat Rat where
  hAdd := fun a b => (a : Rat) + b

instance (priority := high) : PyHAdd Nat Int Int where
  hAdd := fun a b => (a : Int) + b

instance (priority := high) : PyHAdd Int Nat Int where
  hAdd := fun a b => a + (b : Int)

-- `Nat` (e.g. a raw length) meeting a `bool` predicate, mirroring the `Int`/`Bool` mixes above.
instance (priority := high) : PyHAdd Nat Bool Int where hAdd a b := (a : Int) + pyBoolToInt b
instance (priority := high) : PyHAdd Bool Nat Int where hAdd a b := pyBoolToInt a + (b : Int)

class PyHSub (α β : Type) (γ : outParam Type) where
  hSub : α → β → γ

infixl:65 " -ₚ " => PyHSub.hSub

@[default_instance]
instance (priority := low) {α β γ} [HSub α β γ] : PyHSub α β γ where
  hSub := HSub.hSub

instance (priority := high) : PyHSub Int Bool Int where hSub a b := a - pyBoolToInt b
instance (priority := high) : PyHSub Bool Int Int where hSub a b := pyBoolToInt a - b

instance (priority := high) : PyHSub Nat Nat Int where
  hSub := fun a b => (a : Int) - (b : Int)

-- Not a `default_instance`: this instance must remain available for a genuine `Rat - Int`,
-- but it must NOT be used to *default* an unconstrained left operand to `Rat`. Marking it
-- default made `ok -ₚ ng` (with `ng : Int` and `ok` a yet-unconstrained parameter) pin
-- `ok := Rat`, which then forced integer-only follow-ups like `pyFloorDiv (ok +ₚ ng)` to fail.
instance (priority := high) : PyHSub Rat Int Rat where
  hSub := fun a b => (a : Rat) - (b : Int)

-- Symmetric `Int - Rat` (e.g. `1 - g/k` in a logistic term where `g/k : ℚ`). Plain instance, NOT
-- `@[default_instance]` (same rat-default-instance hazard note as above).
instance (priority := high) : PyHSub Int Rat Rat where
  hSub := fun a b => (a : Rat) - b

@[grind]
class PyHMul (α β : Type) (γ : outParam Type) where
  hMul : α → β → γ

infixl:70 " *ₚ " => PyHMul.hMul

@[default_instance]
instance {α β γ} [HMul α β γ] : PyHMul α β γ where
  hMul := HMul.hMul

instance (priority := high) : PyHMul Int Bool Int where hMul a b := a * pyBoolToInt b
instance (priority := high) : PyHMul Bool Int Int where hMul a b := pyBoolToInt a * b
instance (priority := high) : PyHMul Nat Bool Int where hMul a b := (a : Int) * pyBoolToInt b
instance (priority := high) : PyHMul Bool Nat Int where hMul a b := pyBoolToInt a * (b : Int)

instance : PyHMul String Nat String where
  hMul := fun s n => String.intercalate "" (List.replicate n s)

instance : PyHMul String Int String where
  hMul := fun s n =>
    if n < 0 then
      ""
    else
      String.intercalate "" (List.replicate n.toNat s)

/-! Symmetric string repetition `n * s` (Python allows the count on either side). -/
instance : PyHMul Nat String String where
  hMul := fun n s => String.intercalate "" (List.replicate n s)

instance : PyHMul Int String String where
  hMul := fun n s => if n < 0 then "" else String.intercalate "" (List.replicate n.toNat s)

/-- Python list repetition `xs * n` as an ordinary function (not the `outParam`-result `*ₚ`
operator). Codegen targets this for a *list-literal* operand (`[None] * n`, `[0] * n`) so the
result type is concretely `List α` even when `α` is still an unresolved metavariable — the
`outParam` operator would leave the whole list type postponed, which then stalls later
`pyIter`/`pyGetItem`/`pySetItem` on a `[None] * n` placeholder whose element type only gets
pinned by a later assignment. A non-positive count yields `[]`, matching Python. -/
def pyListRepeat {α : Type} (xs : List α) (n : Int) : List α :=
  if n ≤ 0 then [] else (List.replicate n.toNat xs).flatten

/-- Python list repetition `xs * n` (and the symmetric `n * xs`): repeats the list `n` times,
matching `[0] * n` style array initialization. A non-positive count yields `[]`. -/
instance {α : Type} : PyHMul (List α) Int (List α) where
  hMul := fun xs n => pyListRepeat xs n

instance {α : Type} : PyHMul Int (List α) (List α) where
  hMul := fun n xs => pyListRepeat xs n

@[default_instance]
instance (priority := high) : PyHMul Rat Rat Rat where
  hMul := fun a b => (a : Rat) * (b : Rat)

-- Mixed `Rat * Int` / `Rat * Nat` (and symmetric). Plain instances, NOT `@[default_instance]`:
-- a default here would pin an unconstrained operand to `Rat` (the rat-default-instance hazard).
instance (priority := high) : PyHMul Rat Int Rat where hMul := fun a b => a * (b : Rat)
instance (priority := high) : PyHMul Int Rat Rat where hMul := fun a b => (a : Rat) * b
instance (priority := high) : PyHMul Rat Nat Rat where hMul := fun a b => a * (b : Rat)
instance (priority := high) : PyHMul Nat Rat Rat where hMul := fun a b => (a : Rat) * b

-- Keep `Int * Int = Int` (Python semantics) even with still-metavariable operands — see the
-- `PyHAdd Int Int Int` note above (the rat-default-instance hazard, here for `*ₚ`).
@[default_instance 10001]
instance (priority := high) : PyHMul Int Int Int where hMul := fun a b => a * b

@[grind]
class PyHPow (α β : Type) (γ : outParam Type) where
  hPow : α → β → γ

infixr:80 " ^ₚ " => PyHPow.hPow

@[grind]
class PyModulo (α β : Type) (γ : outParam Type) where
  hMod : α → β → γ

infixl:70 " %ₚ " => PyModulo.hMod

def pyMod (a b : Int) : Int :=
  if b == 0 then
    pyRaiseOr "ZeroDivisionError: integer modulo by zero" a
  else
    let r := a % b
    if (r < 0 && b > 0) || (r > 0 && b < 0) then
      r + b
    else
      r

@[default_instance]
instance (priority := high) : PyModulo Int Int Int where
  hMod := pyMod

instance : PyModulo Nat Nat Nat where
  hMod := fun a b => a % b

-- Integer `%` mixing `Nat` and `Int` (`n % len(xs)`), floored via `pyMod`, result `Int`.
instance (priority := high) : PyModulo Nat Int Int where hMod a b := pyMod (a : Int) b
instance (priority := high) : PyModulo Int Nat Int where hMod a b := pyMod a (b : Int)

/-- Python `%` on rationals: the result takes the *divisor's* sign (`a - b·⌊a/b⌋`), unlike Lean's
truncating `%`. So `(-5.5 : ℚ) % 2 = 0.5`. -/
def pyRatMod (a b : Rat) : Rat := if b == 0 then a else a - b * ((⌊a / b⌋ : Int) : Rat)

/-- Python `%` on floats (floored, divisor-signed) — see `pyRatMod`. -/
def pyFloatMod (a b : Float) : Float := pyFloatModPy a b

instance : PyModulo Rat Rat Rat where hMod := pyRatMod
instance : PyModulo Float Float Float where hMod := pyFloatMod

-- Mixed `%` promotes to the wider computable type (as `/ₚ` does), keeping Python's floor semantics.
instance (priority := high) : PyModulo Float Int Float where hMod a b := pyFloatMod a (pyIntToFloat b)
instance (priority := high) : PyModulo Int Float Float where hMod a b := pyFloatMod (pyIntToFloat a) b
instance (priority := high) : PyModulo Float Nat Float where hMod a b := pyFloatMod a (pyIntToFloat (b : Int))
instance (priority := high) : PyModulo Nat Float Float where hMod a b := pyFloatMod (pyIntToFloat (a : Int)) b
instance (priority := high) : PyModulo Rat Int Rat where hMod a b := pyRatMod a (b : Rat)
instance (priority := high) : PyModulo Int Rat Rat where hMod a b := pyRatMod (a : Rat) b
instance (priority := high) : PyModulo Rat Nat Rat where hMod a b := pyRatMod a (b : Rat)
instance (priority := high) : PyModulo Nat Rat Rat where hMod a b := pyRatMod (a : Rat) b

-- `%` with a `bool` operand (bool coerces to int: `x % 2` where `x` is a predicate) and the mixed
-- `Rat`/`Float` cases (`PyNumJoin` does not cover `%`), following Python's floor/divisor-sign result.
instance (priority := high) : PyModulo Bool Int Int where hMod a b := pyMod (pyBoolToInt a) b
instance (priority := high) : PyModulo Int Bool Int where hMod a b := pyMod a (pyBoolToInt b)
instance : PyModulo Bool Bool Int where hMod a b := pyMod (pyBoolToInt a) (pyBoolToInt b)
instance (priority := high) : PyModulo Nat Bool Int where hMod a b := pyMod (a : Int) (pyBoolToInt b)
instance (priority := high) : PyModulo Bool Nat Int where hMod a b := pyMod (pyBoolToInt a) (b : Int)
instance (priority := high) : PyModulo Rat Float Float where hMod a b := pyFloatMod (ratToFloatRound a) b
instance (priority := high) : PyModulo Float Rat Float where hMod a b := pyFloatMod a (ratToFloatRound b)

@[default_instance]
instance {α β γ} [HPow α β γ] : PyHPow α β γ where
  hPow := HPow.hPow

@[default_instance]
instance (priority := high) {α β} [Pow α β] : PyHPow α β α where
  hPow := Pow.pow

@[default_instance]
instance (priority := high) : PyHPow Rat Int Rat where
  hPow := fun a b => (a : Rat) ^ (b : Int)

/-- Python `a ** b` on integers, e.g. `2 ** n`. Lean has no `HPow Int Int Int` (a negative
exponent would be a rational), so we raise to `b.toNat`; this matches competitive-programming
use, where exponents are non-negative. -/
@[default_instance]
instance (priority := high) : PyHPow Int Int Int where
  hPow := fun a b => a ^ b.toNat

instance : PyHPow Nat Nat Nat where
  hPow := fun a b => a ^ b

/-- Python `a ** b` with a float exponent (e.g. `n ** 0.5` for a square root) yields a float.
The base is widened to `Float`; the common idiom is `int(n ** 0.5)`. -/
instance (priority := high) : PyHPow Int Float Float where
  hPow := fun a b => pyFloatPow (pyIntToFloat a) b

-- In exact mode a literal like `0.5` is a `Rat`, so `n ** 0.5` is `Int ^ Rat` — a root, which is
-- irrational, so the provable type is noncomputable `ℝ` (via `rpow`), NOT `Float`. The approx twin
-- never hits this: there `0.5` is already a `Float`, matching `PyHPow Int Float Float` above.
noncomputable instance (priority := high) : PyHPow Int Rat Real where
  hPow := fun a b => Real.rpow (a : ℝ) (b : ℝ)

instance (priority := high) : PyHPow Float Float Float where
  hPow := pyFloatPow

-- Float base with an integer exponent (`x ** 2`); `Nat ** Int` takes the exponent non-negative.
instance (priority := high) : PyHPow Float Int Float where hPow a b := pyFloatPow a (pyIntToFloat b)
instance (priority := high) : PyHPow Float Nat Float where hPow a b := pyFloatPow a (pyIntToFloat (b : Int))
instance (priority := high) : PyHPow Nat Int Nat where hPow a b := a ^ b.toNat

-- `**` mixes missing from the tower. A rational/`Nat` base with a rational exponent is generally
-- irrational → noncomputable `ℝ` (via `rpow`), matching `Int ** Rat` above; a `Float` operand keeps
-- the result `Float`. (`Rat ** Nat` / `Rat ** Int` are already covered by the generic `Pow`/explicit
-- instances above.)
noncomputable instance (priority := high) : PyHPow Rat Rat Real where hPow a b := Real.rpow (a : ℝ) (b : ℝ)
noncomputable instance (priority := high) : PyHPow Nat Rat Real where hPow a b := Real.rpow (a : ℝ) (b : ℝ)
instance (priority := high) : PyHPow Nat Float Float where hPow a b := pyFloatPow (pyIntToFloat (a : Int)) b
instance (priority := high) : PyHPow Rat Float Float where hPow a b := pyFloatPow (ratToFloatRound a) b
instance (priority := high) : PyHPow Float Rat Float where hPow a b := pyFloatPow a (ratToFloatRound b)

@[default_instance]
instance (priority := high) : Neg Rat where
  neg := fun a => - (a : Rat)

class PyHDiv (α β : Type) (γ : outParam Type) where
  hDiv : α → β → γ

infixl:70 " /ₚ " => PyHDiv.hDiv

@[default_instance]
instance {α β γ} [HDiv α β γ] : PyHDiv α β γ where
  hDiv := HDiv.hDiv

-- `@[default_instance 10001]` (as with `PyHAdd Int Int Int`) pins untyped division operands
-- (`def divide(a, b): return a / b`) to `Int /ₚ Int : Rat` — Python `/` always yields a float.
@[default_instance 10001]
instance (priority := high) : PyHDiv Int Int Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

-- Mixed `Rat / Int` / `Rat / Nat` (and symmetric). The common case is `total / len(xs)` where
-- `total : Rat` and `len(xs) : Int`. Plain instances (no `@[default_instance]`) — see the mul note.
instance (priority := high) : PyHDiv Rat Int Rat where hDiv := fun a b => a / (b : Rat)
instance (priority := high) : PyHDiv Int Rat Rat where hDiv := fun a b => (a : Rat) / b
instance (priority := high) : PyHDiv Rat Nat Rat where hDiv := fun a b => a / (b : Rat)
instance (priority := high) : PyHDiv Nat Rat Rat where hDiv := fun a b => (a : Rat) / b

instance (priority := high) : PyHDiv Nat Nat Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

@[default_instance]
instance (priority := high) : PyHDiv Rat Rat Rat where
  hDiv := fun a b => (a : Rat) / (b : Rat)

/-- Python float `/`: a zero divisor raises `ZeroDivisionError` (IEEE would give `±inf`/`nan`). -/
def pyFloatDiv (a b : Float) : Float :=
  if b == 0.0 then pyPanic "ZeroDivisionError: float division by zero" else a / b

instance (priority := high) : PyHDiv Float Float Float where hDiv := pyFloatDiv

-- Python true division `/` always yields a float when a float is involved. `pyLen`/`int` operands
-- are `Int`, so e.g. `total / len(xs)` is `Float / Int`; these instances cover the mixed cases.
instance (priority := high) : PyHDiv Float Int Float where
  hDiv := fun a b => pyFloatDiv a (pyIntToFloat (b : Int))

instance (priority := high) : PyHDiv Int Float Float where
  hDiv := fun a b => pyFloatDiv (pyIntToFloat (a : Int)) b

instance (priority := high) : PyHDiv Float Nat Float where
  hDiv := fun a b => pyFloatDiv a (pyIntToFloat (b : Int))

instance (priority := high) : PyHDiv Nat Float Float where
  hDiv := fun a b => pyFloatDiv (pyIntToFloat (a : Int)) b

instance (priority := high) : PyHDiv Rat Float Float where hDiv a b := pyFloatDiv (ratToFloatRound a) b
instance (priority := high) : PyHDiv Float Rat Float where hDiv a b := pyFloatDiv a (ratToFloatRound b)

/-! Mixed `Float`/`Int` and `Float`/`Nat` `+`/`-`/`*` (Python promotes the integer to float).
Lean has no heterogeneous `HAdd Float Int` etc., so these are needed whenever an integer literal
or a `len()`/`int()` result meets a float — e.g. `1 - g / k`, `grass[i] + 1`, `2 * x`. -/
instance (priority := high) : PyHAdd Float Int Float where hAdd a b := a + pyIntToFloat (b : Int)
instance (priority := high) : PyHAdd Int Float Float where hAdd a b := pyIntToFloat (a : Int) + b
instance (priority := high) : PyHAdd Float Nat Float where hAdd a b := a + pyIntToFloat (b : Int)
instance (priority := high) : PyHAdd Nat Float Float where hAdd a b := pyIntToFloat (a : Int) + b

instance (priority := high) : PyHSub Float Int Float where hSub a b := a - pyIntToFloat (b : Int)
instance (priority := high) : PyHSub Int Float Float where hSub a b := pyIntToFloat (a : Int) - b
instance (priority := high) : PyHSub Float Nat Float where hSub a b := a - pyIntToFloat (b : Int)
instance (priority := high) : PyHSub Nat Float Float where hSub a b := pyIntToFloat (a : Int) - b

instance (priority := high) : PyHMul Float Int Float where hMul a b := a * pyIntToFloat (b : Int)
instance (priority := high) : PyHMul Int Float Float where hMul a b := pyIntToFloat (a : Int) * b
instance (priority := high) : PyHMul Float Nat Float where hMul a b := a * pyIntToFloat (b : Int)
instance (priority := high) : PyHMul Nat Float Float where hMul a b := pyIntToFloat (a : Int) * b

/-! ## Mixed `ℚ`/`ℝ` (and `ℤ`/`ℕ` with `ℝ`) arithmetic — exact mode

In exact mode a transcendental yields `ℝ` while the surrounding rational/integer values are `ℚ`/`ℤ`,
e.g. `g *ₚ math.log (g +ₚ 1)` with `g : ℚ`. Lean has no heterogeneous `HMul ℚ ℝ`, so these promote
the rational/integer operand into `ℝ` and produce `ℝ`. (`ℝ×ℝ` already works via the generic
`[HMul α β γ]` instance.) `noncomputable`, since the `ℚ ↪ ℝ` / `ℤ ↪ ℝ` casts are. -/
noncomputable instance (priority := high) : PyHMul Real Real Real where hMul a b := (a : ℝ) * b
noncomputable instance (priority := high) : PyHMul Rat Real Real where hMul a b := (a : ℝ) * b
noncomputable instance (priority := high) : PyHMul Real Rat Real where hMul a b := a * (b : ℝ)
noncomputable instance (priority := high) : PyHMul Int Real Real where hMul a b := (a : ℝ) * b
noncomputable instance (priority := high) : PyHMul Real Int Real where hMul a b := a * (b : ℝ)
noncomputable instance (priority := high) : PyHMul Nat Real Real where hMul a b := (a : ℝ) * b
noncomputable instance (priority := high) : PyHMul Real Nat Real where hMul a b := a * (b : ℝ)

noncomputable instance (priority := high) : PyHAdd Real Real Real where hAdd a b := (a : ℝ) + b
noncomputable instance (priority := high) : PyHAdd Rat Real Real where hAdd a b := (a : ℝ) + b
noncomputable instance (priority := high) : PyHAdd Real Rat Real where hAdd a b := a + (b : ℝ)
noncomputable instance (priority := high) : PyHAdd Int Real Real where hAdd a b := (a : ℝ) + b
noncomputable instance (priority := high) : PyHAdd Real Int Real where hAdd a b := a + (b : ℝ)
noncomputable instance (priority := high) : PyHAdd Nat Real Real where hAdd a b := (a : ℝ) + b
noncomputable instance (priority := high) : PyHAdd Real Nat Real where hAdd a b := a + (b : ℝ)

noncomputable instance (priority := high) : PyHSub Real Real Real where hSub a b := (a : ℝ) - b
noncomputable instance (priority := high) : PyHSub Rat Real Real where hSub a b := (a : ℝ) - b
noncomputable instance (priority := high) : PyHSub Real Rat Real where hSub a b := a - (b : ℝ)
noncomputable instance (priority := high) : PyHSub Int Real Real where hSub a b := (a : ℝ) - b
noncomputable instance (priority := high) : PyHSub Real Int Real where hSub a b := a - (b : ℝ)
noncomputable instance (priority := high) : PyHSub Nat Real Real where hSub a b := (a : ℝ) - b
noncomputable instance (priority := high) : PyHSub Real Nat Real where hSub a b := a - (b : ℝ)

noncomputable instance (priority := high) : PyHDiv Real Real Real where hDiv a b := (a : ℝ) / b
noncomputable instance (priority := high) : PyHDiv Rat Real Real where hDiv a b := (a : ℝ) / b
noncomputable instance (priority := high) : PyHDiv Real Rat Real where hDiv a b := a / (b : ℝ)
noncomputable instance (priority := high) : PyHDiv Int Real Real where hDiv a b := (a : ℝ) / b
noncomputable instance (priority := high) : PyHDiv Real Int Real where hDiv a b := a / (b : ℝ)
noncomputable instance (priority := high) : PyHDiv Nat Real Real where hDiv a b := (a : ℝ) / b
noncomputable instance (priority := high) : PyHDiv Real Nat Real where hDiv a b := a / (b : ℝ)


/-! ## Auto-derived mixed numeric arithmetic — `PyNumJoin`

Rather than writing every mixed pair out four times (once per `+ - * /`), `PyNumJoin α β γ` names the
common result type `γ` of mixing `α` and `β` **once**, together with the two coercions into it. A
*single* generic instance per operator then derives all four. Adding a new numeric type later means
adding its coercion pairs here once — not `4 ×` new operator instances.

These are LOW priority and NOT `@[default_instance]`: the carefully-tuned homogeneous defaults above
(`Rat`/`Int` `@[default_instance]`, the `@[simp] rfl` lemmas) still win for same-type and
unconstrained-operand resolution; `PyNumJoin` only fires for a genuinely-mixed *concrete* pair that
no higher-priority instance already covers (e.g. `ℚ × Float`, which arises when a run-twin function
multiplies a shared `ℚ` constant by a `Float` local). The `ℝ` mixes stay explicit (`noncomputable`)
just above; this covers the computable tower `ℕ ⊂ ℤ ⊂ ℚ` and `Float`. -/
class PyNumJoin (α β : Type) (γ : outParam Type) where
  coeL : α → γ
  coeR : β → γ

namespace PyNumJoin
/-- `α` mixed with itself does not need a join (the homogeneous `[HAdd α α α]` instance handles it);
`mk2 f g` builds the two-coercion record for a genuinely mixed pair. -/
abbrev mk2 {α β γ} (f : α → γ) (g : β → γ) : PyNumJoin α β γ := ⟨f, g⟩
end PyNumJoin

-- ℕ ⊂ ℤ
instance : PyNumJoin Nat Int Int := .mk2 (Int.ofNat) id
instance : PyNumJoin Int Nat Int := .mk2 id (Int.ofNat)
-- · ⊂ ℚ
instance : PyNumJoin Nat Rat Rat := .mk2 (fun n => (n : ℚ)) id
instance : PyNumJoin Rat Nat Rat := .mk2 id (fun n => (n : ℚ))
instance : PyNumJoin Int Rat Rat := .mk2 (fun n => (n : ℚ)) id
instance : PyNumJoin Rat Int Rat := .mk2 id (fun n => (n : ℚ))
-- · ⊂ Float  (ℚ → Float is `Rat.toFloat`; this is the pair the prove/run twin split needs)
instance : PyNumJoin Nat Float Float := .mk2 (fun n => pyIntToFloat (n : Int)) id
instance : PyNumJoin Float Nat Float := .mk2 id (fun n => pyIntToFloat (n : Int))
instance : PyNumJoin Int Float Float := .mk2 (fun n => pyIntToFloat n) id
instance : PyNumJoin Float Int Float := .mk2 id (fun n => pyIntToFloat n)
instance : PyNumJoin Rat Float Float := .mk2 ratToFloatRound id
instance : PyNumJoin Float Rat Float := .mk2 id ratToFloatRound

-- One generic instance per operator derives `+ - * /` for every `PyNumJoin` pair. Project through
-- the named `j` (its `β` is fixed) — a bare `PyNumJoin.coeL a` would leave `β` a metavar.
instance (priority := low) {α β γ} [j : PyNumJoin α β γ] [Add γ] : PyHAdd α β γ where
  hAdd a b := j.coeL a + j.coeR b
instance (priority := low) {α β γ} [j : PyNumJoin α β γ] [Sub γ] : PyHSub α β γ where
  hSub a b := j.coeL a - j.coeR b
instance (priority := low) {α β γ} [j : PyNumJoin α β γ] [Mul γ] : PyHMul α β γ where
  hMul a b := j.coeL a * j.coeR b
instance (priority := low) {α β γ} [j : PyNumJoin α β γ] [Div γ] : PyHDiv α β γ where
  hDiv a b := j.coeL a / j.coeR b


/-- Python-style floor division: `a // b` truncates toward negative infinity. -/
class PyFloorDiv (α β : Type) (γ : outParam Type) where floorDiv : α → β → γ
/-- Python `a // b`. -/
def pyFloorDiv {α β γ : Type} [PyFloorDiv α β γ] (a : α) (b : β) : γ := PyFloorDiv.floorDiv a b

instance : PyFloorDiv Int Int Int where
  floorDiv a b := if b == 0 then PastaLean.pyPanic "ZeroDivisionError: integer division or modulo by zero" else Int.fdiv a b

/-! Python `//` is floor division for EVERY numeric type, not just `int`: `7.0 // 2 = 3.0` (float),
`len(a) // len(b)` (the operands are `Nat`), and the exact-mode rational/mixed cases. `PyNumJoin`
only auto-derives `+ - * /`, so each `//` pair is spelled out. Result type follows Python: a float
operand keeps the result float, otherwise it stays in the integer/rational domain. -/
instance : PyFloorDiv Float Float Float where floorDiv := pyFloatFloorDivPy
instance : PyFloorDiv Rat Rat Rat where floorDiv a b := if b == 0 then a else ((⌊a / b⌋ : Int) : Rat)
instance : PyFloorDiv Nat Nat Nat where floorDiv a b := a / b
-- Float with an integer operand → Float (Python promotes).
instance : PyFloorDiv Float Int Float where floorDiv a b := pyFloatFloorDivPy a (pyIntToFloat b)
instance : PyFloorDiv Int Float Float where floorDiv a b := pyFloatFloorDivPy (pyIntToFloat a) b
instance : PyFloorDiv Float Nat Float where floorDiv a b := pyFloatFloorDivPy a (pyIntToFloat (b : Int))
instance : PyFloorDiv Nat Float Float where floorDiv a b := pyFloatFloorDivPy (pyIntToFloat (a : Int)) b
-- Rat with an integer operand → Rat (exact mode).
instance : PyFloorDiv Rat Int Rat where floorDiv a b := if b == 0 then a else ((⌊a / (b : Rat)⌋ : Int) : Rat)
instance : PyFloorDiv Int Rat Rat where floorDiv a b := if b == 0 then (a : Rat) else ((⌊(a : Rat) / b⌋ : Int) : Rat)
instance : PyFloorDiv Rat Nat Rat where floorDiv a b := if b == 0 then a else ((⌊a / (b : Rat)⌋ : Int) : Rat)
instance : PyFloorDiv Nat Rat Rat where floorDiv a b := if b == 0 then (a : Rat) else ((⌊(a : Rat) / b⌋ : Int) : Rat)
-- Nat/Int mixes → Int (floored).
instance : PyFloorDiv Nat Int Int where floorDiv a b := if b == 0 then (a : Int) else Int.fdiv (a : Int) b
instance : PyFloorDiv Int Nat Int where floorDiv a b := if b == 0 then a else Int.fdiv a (b : Int)
-- Bool coerces to int (`True // 2 = 0`).
instance : PyFloorDiv Bool Int Int where floorDiv a b := if b == 0 then pyBoolToInt a else Int.fdiv (pyBoolToInt a) b
instance : PyFloorDiv Int Bool Int where floorDiv a b := if pyBoolToInt b == 0 then a else Int.fdiv a (pyBoolToInt b)

/-!
Python-style integer bitwise operators, modelling Python's infinite two's-complement (`-1 & 15 = 15`,
`x & 1` for a negative `x`) at a fixed 64-bit width — ample for competitive-programming values (which
fit in 63 bits). A negative operand becomes its unsigned 64-bit representative, the `Nat` bitwise op
runs, and the result is re-signed (negative iff the top bit is set).
-/

/-- Apply a `Nat` bitwise op with Python's arbitrary-precision two's-complement semantics. Python
integers are unbounded, so a FIXED width is wrong: a non-negative result ≥ 2^63 would be re-signed to a
negative (`reduce(or_, big)` → `-1`) and anything wider than the width truncates. Instead pick a width
`w` STRICTLY larger than either operand's magnitude — then a non-negative result never sets the sign bit
(no spurious negative), a negative operand still round-trips (`-1 & 5 = 5`), and nothing truncates. -/
private def pyTwosComp (f : Nat → Nat → Nat) (a b : Int) : Int :=
  let w := (max a.natAbs b.natAbs).log2 + 2      -- 2^(w-1) > max magnitude
  let width : Int := 2 ^ w
  let r := f (a % width).toNat (b % width).toNat  -- `Int.emod` is non-negative for width > 0
  if r ≥ 2 ^ (w - 1) then (r : Int) - width else (r : Int)

/-- Python `a & b`. -/
-- `&`, `|`, `^` are bitwise on integers *and* the binary set operations (intersection, union,
-- symmetric difference) on Python sets. They are typeclasses (Int instances here; the
-- list-backed set instances live in `Sets.lean`) so codegen emits one stable name per operator
-- and the operand type selects the meaning.
class PyBitAnd (α β : Type) (γ : outParam Type) where bitAnd : α → β → γ
class PyBitOr (α β : Type) (γ : outParam Type) where bitOr : α → β → γ
class PyBitXor (α β : Type) (γ : outParam Type) where bitXor : α → β → γ

/-- Python `a & b` (integer bitwise-and, or set intersection). -/
def pyBitAnd {α β γ : Type} [PyBitAnd α β γ] (a : α) (b : β) : γ := PyBitAnd.bitAnd a b
/-- Python `a | b` (integer bitwise-or, or set union). -/
def pyBitOr {α β γ : Type} [PyBitOr α β γ] (a : α) (b : β) : γ := PyBitOr.bitOr a b
/-- Python `a ^ b` (integer bitwise-xor, or set symmetric difference). -/
def pyBitXor {α β γ : Type} [PyBitXor α β γ] (a : α) (b : β) : γ := PyBitXor.bitXor a b

instance : PyBitAnd Int Int Int where bitAnd := pyTwosComp Nat.land
instance : PyBitOr Int Int Int where bitOr := pyTwosComp Nat.lor
instance : PyBitXor Int Int Int where bitXor := pyTwosComp Nat.xor

-- Bitwise on `Nat` operands (a length/`range` index): non-negative, so the plain `Nat` bit ops apply.
instance : PyBitAnd Nat Nat Nat where bitAnd := Nat.land
instance : PyBitOr Nat Nat Nat where bitOr := Nat.lor
instance : PyBitXor Nat Nat Nat where bitXor := Nat.xor

/-- On two `bool`s Python's `&`/`|`/`^` are the boolean connectives (returning `bool`), e.g.
`flag |= cond`, `parity ^= bit`. Mixed `bool`/`int` goes through the `Int` instances (bool coerces). -/
instance : PyBitAnd Bool Bool Bool where bitAnd a b := a && b
instance : PyBitOr Bool Bool Bool where bitOr a b := a || b
instance : PyBitXor Bool Bool Bool where bitXor a b := xor a b

/-- Mixed `bool`/`int` bitwise: the `bool` coerces to `int` (Python `True & 6 = 0`, `flag |= cond`,
`parity ^= bit`). The comment above promised these "go through the Int instances", but there was no
`Bool→Int` coercion for these classes — these instances supply it. -/
instance : PyBitAnd Bool Int Int where bitAnd a b := pyTwosComp Nat.land (pyBoolToInt a) b
instance : PyBitAnd Int Bool Int where bitAnd a b := pyTwosComp Nat.land a (pyBoolToInt b)
instance : PyBitOr Bool Int Int where bitOr a b := pyTwosComp Nat.lor (pyBoolToInt a) b
instance : PyBitOr Int Bool Int where bitOr a b := pyTwosComp Nat.lor a (pyBoolToInt b)
instance : PyBitXor Bool Int Int where bitXor a b := pyTwosComp Nat.xor (pyBoolToInt a) b
instance : PyBitXor Int Bool Int where bitXor a b := pyTwosComp Nat.xor a (pyBoolToInt b)

class PyShiftLeft (α β : Type) (γ : outParam Type) where shiftLeft : α → β → γ
class PyShiftRight (α β : Type) (γ : outParam Type) where shiftRight : α → β → γ
/-- Python `a << b`. -/
def pyShiftLeft {α β γ : Type} [PyShiftLeft α β γ] (a : α) (b : β) : γ := PyShiftLeft.shiftLeft a b
/-- Python `a >> b` (floor division by `2 ^ b`). -/
def pyShiftRight {α β γ : Type} [PyShiftRight α β γ] (a : α) (b : β) : γ := PyShiftRight.shiftRight a b

instance : PyShiftLeft Int Int Int where shiftLeft a b := a * (2 ^ b.toNat)
instance : PyShiftRight Int Int Int where shiftRight a b := Int.fdiv a (2 ^ b.toNat)

-- Shifts with a `Nat` or `bool` operand (bool coerces to int: `flag << 1`, `1 << n` with `n : Nat`).
instance : PyShiftLeft Nat Nat Nat where shiftLeft a b := a * (2 ^ b)
instance : PyShiftRight Nat Nat Nat where shiftRight a b := a / (2 ^ b)
instance : PyShiftLeft Int Nat Int where shiftLeft a b := a * (2 ^ b)
instance : PyShiftRight Int Nat Int where shiftRight a b := Int.fdiv a (2 ^ b)
instance : PyShiftLeft Bool Int Int where shiftLeft a b := (pyBoolToInt a) * (2 ^ b.toNat)
instance : PyShiftRight Bool Int Int where shiftRight a b := Int.fdiv (pyBoolToInt a) (2 ^ b.toNat)

/-!
## Reduction lemmas — `simp` rewrites the Python operators to the standard ones

Generated code uses `+ₚ -ₚ *ₚ /ₚ` (the `PyH*` typeclasses). They are *definitionally* the
ordinary `ℚ`/`ℤ` operators, but `ring`/`nlinarith`/`linarith` don't see through the notation.
These `@[simp]` lemmas (all `rfl`) let a proof do `simp [myFunc]` to expose plain `+ - * /`, after
which `ring`/`nlinarith` close the goal. So theorems can be proved directly on the generated
`ℚ` definitions (no re-statement over `ℝ`). -/

-- Also in the `taste_ingr` set, so `taste?`'s `simp only [taste_ingr]` clears the `*ₚ` operators
-- (turning them into plain `+ - * /`) without naming each lemma in the tactic.
@[simp, taste_ingr] theorem pyAdd_rat (a b : ℚ) : a +ₚ b = a + b := rfl
@[simp, taste_ingr] theorem pySub_rat (a b : ℚ) : a -ₚ b = a - b := rfl
@[simp, taste_ingr] theorem pyMul_rat (a b : ℚ) : a *ₚ b = a * b := rfl
@[simp, taste_ingr] theorem pyDiv_rat (a b : ℚ) : a /ₚ b = a / b := rfl

@[simp, taste_ingr] theorem pyAdd_int (a b : ℤ) : a +ₚ b = a + b := rfl
@[simp, taste_ingr] theorem pySub_int (a b : ℤ) : a -ₚ b = a - b := rfl
@[simp, taste_ingr] theorem pyMul_int (a b : ℤ) : a *ₚ b = a * b := rfl

end PastaLean
