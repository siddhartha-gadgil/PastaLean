import PastaLean.Imports
import PastaLean.PyAPI.Core
import PastaLean.PyAPI.Builtins.FloatRepr

namespace PastaLean

universe u v

/--
Python-style value formatting used by the printing runtime.

This is intentionally separate from Lean's `ToString` / `Repr` so we can make common
runtime values look more like Python when printed.
-/
class PyPrintable (α : Type u) where
  pyStringify : α → String
  /-- Python's `repr`: how the value renders *inside* a container. `print(x)` uses `str(x)`, but a
  container's own `str` renders its elements with `repr`, so `print("a")` is `a` while
  `print(["a"])` is `['a']`. Only `String`/`Char` differ; everything else defaults to `pyStringify`. -/
  pyReprify : α → String := pyStringify

export PyPrintable (pyStringify pyReprify)

/-- Python's `repr` of a string: single quotes, switching to double when the text contains a `'`
and no `"`, with the backslash, the active quote and the usual control characters escaped. -/
def pyReprString (s : String) : String :=
  let useDouble := s.contains '\'' && !s.contains '"'
  let quote := if useDouble then '"' else '\''
  let escaped := s.toList.foldl (init := "") fun acc c =>
    acc ++
      if c == '\\' then "\\\\"
      else if c == quote then "\\" ++ String.singleton c
      else if c == '\n' then "\\n"
      else if c == '\r' then "\\r"
      else if c == '\t' then "\\t"
      else String.singleton c
  String.singleton quote ++ escaped ++ String.singleton quote

/--
One printable argument in a Python-style `print(...)` call.

This wrapper lets Lean accept heterogeneous argument lists like
`["sum", (3 : Int), true]` while still routing each element through the
`PyPrintable` typeclass.
-/
structure PyPrintArg where
  rendered : String

/-- Any printable Lean value can be used directly as a Python print argument. -/
instance {α : Type u} [PyPrintable α] : CoeOut α PyPrintArg where
  coe x := ⟨pyStringify x⟩

/--
Wrap one printable value as a `print(...)` argument (the lowercase smart constructor for
`PyPrintArg`).

Generated `print(...)` code emits `pyPrintArg x` per argument — far tidier than the explicit
`PyPrintArg.mk (pyStringify x)` it replaces — while still applying `pyStringify` eagerly, so each
argument elaborates at its own type before the heterogeneous `List PyPrintArg` is assembled (the
reason codegen can't just lean on the `CoeOut` coercion, which would force `PyPrintArg` onto
polymorphic argument terms).
-/
@[inline] def pyPrintArg {α : Type u} [PyPrintable α] (x : α) : PyPrintArg :=
  ⟨pyStringify x⟩

/-- Join already-formatted pieces with the separator Python's `print` commonly uses. -/
private def pyJoinPrinted (parts : List String) : String :=
  String.intercalate ", " parts

/-- Render a Python-style `print(...)` call from already-formatted argument strings. -/
def pyPrintRendered (parts : List String) (sep : String := " ") (ending : String := "\n") : String :=
  String.intercalate sep parts ++ ending

/-- Render a Python-style `print(...)` call from heterogeneous printable arguments. -/
def pyPrintArgsRendered (parts : List PyPrintArg) (sep : String := " ") (ending : String := "\n") : String :=
  pyPrintRendered (parts.map PyPrintArg.rendered) sep ending

/-- Strings print as themselves, without Lean quotes — but gain Python's quotes inside a container. -/
instance : PyPrintable String where
  pyStringify s := s
  pyReprify := pyReprString

/-- Booleans use Python casing. -/
instance : PyPrintable Bool where
  pyStringify b := if b then "True" else "False"

/-- Lean's unit values line up with Python `None` when printed. -/
instance : PyPrintable Unit where
  pyStringify _ := "None"

/-- Lean's pretty-printed `PUnit` also behaves like Python `None`. -/
instance : PyPrintable PUnit where
  pyStringify _ := "None"

/-- Characters print as one-character strings, quoted inside a container like any other string. -/
instance : PyPrintable Char where
  pyStringify c := String.singleton c
  pyReprify c := pyReprString (String.singleton c)

/-- Numeric values can use Lean's ordinary string form. -/
instance : PyPrintable Int where
  pyStringify n := toString n

instance : PyPrintable Nat where
  pyStringify n := toString n

/-- Floats print with Python's `repr`: the shortest decimal that round-trips (`3.0`, not
`3.000000`; `0.2857142857142857`, not the 6-digit `0.285714`). See `Builtins/FloatRepr.lean`. -/
instance : PyPrintable Float where
  pyStringify := pyFloatRepr

/-- Rationals print as a Python-style **decimal** (`3/2` → `1.5`), not the fraction `n/d` — matching
`print` output when `float` lowers to `ℚ` (exact mode). Uses the same shortest-round-trip repr. -/
instance : PyPrintable Rat where
  pyStringify q := pyFloatRepr (Rat.toFloat q)


/-- Python exceptions print with their existing `ToString` rendering. -/
instance : PyPrintable PyException where
  pyStringify exc := toString exc

/-- `None` stays visible; present values print as the value itself. -/
instance [PyPrintable α] : PyPrintable (Option α) where
  pyStringify
    | none => "None"
    | some value => pyStringify value
  pyReprify
    | none => "None"
    | some value => pyReprify value

/-- Lists print with Python-style brackets and comma separation, their elements rendered with
`repr` as Python's own list formatting does. -/
instance [PyPrintable α] : PyPrintable (List α) where
  pyStringify xs :=
    "[" ++ pyJoinPrinted (xs.map pyReprify) ++ "]"

/-- The comma-joined inside of a tuple (no surrounding parens), flattening the right-nested product an
n-tuple `(a, b, c)` = `(a, (b, c))` is. A genuine 2-tuple-of-a-pair `(a, (b, c))` is the same product
at runtime, so it flattens too — flat n-tuples are far more common, so this is the better default. -/
class PyTupleBody (α : Type) where
  body : α → String

instance (priority := 1100) [PyPrintable α] [PyTupleBody β] : PyTupleBody (α × β) where
  body p := pyReprify p.1 ++ ", " ++ PyTupleBody.body p.2

instance [PyPrintable α] : PyTupleBody α where
  body a := pyReprify a

/-- Tuples print as Python tuples, flattening the nesting so `(25, 9, 1)` is not `(25, (9, 1))`.
Elements render with `repr`, as inside any Python container. -/
instance [PyPrintable α] [PyTupleBody β] : PyPrintable (α × β) where
  pyStringify p := "(" ++ pyReprify p.1 ++ ", " ++ PyTupleBody.body p.2 ++ ")"

/--
Hash maps print as Python-style dictionaries.

The underlying runtime type does not preserve Python insertion order, so we sort by
the printed key to keep the rendered output deterministic in tests.
-/
instance [PyPrintable α] [PyPrintable β] [BEq α] [Hashable α] :
    PyPrintable (Std.HashMap α β) where
  pyStringify m :=
    let rendered :=
      m.toList.map fun (k, v) =>
        let keyText := pyReprify k
        (keyText, keyText ++ ": " ++ pyReprify v)
    let sorted := rendered.mergeSort (fun a b => compare a.1 b.1 != Ordering.gt)
    "{" ++ pyJoinPrinted (sorted.map Prod.snd) ++ "}"

/-- Function values do not have a good runtime textual form, so use a Python-style placeholder. -/
instance {α : Type u} {β : Type v} : PyPrintable (α → β) where
  pyStringify _ := "<function>"

/-- Functions have no `Repr`, so a generated `Val` universe carrying a function-typed cell (a heap
`list` of closures) cannot `deriving Repr`. Give function types the same placeholder `Repr` so the
derive succeeds; nothing inspects the stored closure's text. -/
instance (priority := low) {α : Type u} {β : Type v} : Repr (α → β) where
  reprPrec _ _ := "<function>"

/--
Fallback printer for any value that already has a `Repr`.

This keeps the printing surface extensible without forcing every new runtime type to
add a custom `PyPrintable` instance on day one.
-/
@[default_instance low]
instance [Repr α] : PyPrintable α where
  pyStringify x := reprStr x

/-- Public helper returning the Python-style printable text for a value. -/
def pyPrintStr {α : Type u} [PyPrintable α] (x : α) : String :=
  pyStringify x

/--
Real console-printing helper using Python-style `print(...)` semantics.

The input is a heterogeneous list of printable arguments, so both single-value and
multi-value calls go through the same user-facing API:

`pyPrintIO ["sum", (3 : Int), true]`
-/
def pyPrintIO (parts : List PyPrintArg) (sep : String := " ") (ending : String := "\n") : IO Unit :=
  IO.print (pyPrintArgsRendered parts sep ending)

/-- No-op `print` used by the `prove` (exact) semantics: that version exists to state and prove
theorems, not to produce output. It takes the SAME arguments as `pyPrintIO` — so the generated code
keeps the full `print(...)` line, readable and type-checked — but discards them and produces no
output (a noncomputable `ℝ` has no real printable form; see the placeholder `PyPrintable ℝ` below).
Any `input()` side effect in the arguments is still hoisted and run before this; only the output is
dropped. The runnable `'rn` / `--mode run` twin keeps the real `pyPrintIO`.
Polymorphic in the monad - works in IO, PyExcept, PyExceptId, Id, etc. -/
def pyPrintNoop [Monad m] (_parts : List PyPrintArg) (_sep : String := " ") (_ending : String := "\n") :
    m Unit := pure ()

/-- Placeholder renderers for `ℝ`, so a `prove`-mode `print(...)` line that embeds a real value can
still be *written* and type-checked — via `pyPrintArg` (`PyPrintable`), string interpolation `s!"…
{realExpr}"` (`ToString`), or a format spec `pyFormatSpec realExpr ".2f"` (`PyFmtNum`). None of these
is ever actually rendered: only `pyPrintNoop` consumes the real arguments and it discards them, so
the placeholder content (`{ℝ}` / `0.0`) is irrelevant — the *expression* stays visible in the source
line regardless. `ℝ`'s true string form is noncomputable; these exist only to keep the line. -/
instance : PyPrintable ℝ where
  pyStringify _ := "{ℝ}"

instance : ToString ℝ where
  toString _ := "{ℝ}"

/--
Pure compatibility surface mirroring `pyPrintIO`.

This preserves Python formatting semantics without attempting visible console output
inside non-`IO` translated code paths.
-/
def pyPrint (parts : List PyPrintArg) (sep : String := " ") (ending : String := "\n") : Unit :=
  let _ := pyPrintArgsRendered parts sep ending
  ()

/-! ## f-string format specifiers (`{x:.2f}`) -/

/-- Numeric values an f-string format spec can apply to (`Float`/`Int`/`Nat`/`Rat`). -/
class PyFmtNum (α : Type) where
  toFmtFloat : α → Float

instance : PyFmtNum Float := ⟨id⟩
instance : PyFmtNum Nat := ⟨Float.ofNat⟩
instance : PyFmtNum Int := ⟨fun n => if n ≥ 0 then Float.ofNat n.toNat else - Float.ofNat (-n).toNat⟩
instance : PyFmtNum Rat := ⟨Rat.toFloat⟩
-- Placeholder for `ℝ`: lets a `prove`-mode `print(f"{realExpr:.2f}")` line keep its format spec.
-- Never rendered (only `pyPrintNoop` consumes it, discarding), so the `0.0` stand-in is irrelevant.
instance : PyFmtNum ℝ := ⟨fun _ => 0.0⟩

/-- The exact truncated integer of a non-negative `Float`, via IEEE-754 bit decode, so a value beyond
`UInt64`'s range (`toUInt64` saturates there) still converts faithfully. A `Float` ≥ 2^52 is already an
integer, so this is exact for the large magnitudes where `pyFixedFloat`'s scaled `toUInt64` overflows. -/
def floatToExactNat (x : Float) : Nat :=
  let bits := x.toBits
  let exp := ((bits >>> 52) &&& 0x7FF).toNat
  let mant := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if exp == 0 then 0                        -- zero / subnormal (|x| < 1)
  else
    let m := mant + 0x10000000000000        -- restore the implicit leading 1 (2^52)
    let e : Int := (exp : Int) - 1023 - 52
    if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat

/-- Format a `Float` with exactly `prec` digits after the decimal point (Python `:.Nf`). Rounds the
`Float`'s exact IEEE-754 value with round-half-to-even, matching CPython: `2.675` (stored as
`2.6749999…`) → `2.67`, exact ties like `0.125`/`2.5` → even. Sign follows the sign bit, so a negative
value rounding to zero still prints `-0` as Python does. -/
def pyFixedFloat (x : Float) (prec : Nat) : String :=
  let neg := (x.toBits >>> 63) == 1
  let bits := x.toBits
  let exp := ((bits >>> 52) &&& 0x7FF).toNat
  let mant := (bits &&& 0xFFFFFFFFFFFFF).toNat
  let pow := 10 ^ prec
  -- `|x| = m * 2^e`, exactly (subnormal ⇒ no implicit leading 1). `e = exp - 1023 - 52`.
  let (m, e) :=
    if exp == 0 then (mant, (-1074 : Int))
    else (mant + 0x10000000000000, (exp : Int) - 1075)
  -- Exact round-half-to-even of `|x| * 10^prec`.
  let r : Nat :=
    if e ≥ 0 then m * pow * 2 ^ e.toNat
    else
      let den := 2 ^ (-e).toNat
      let num := m * pow
      let q := num / den
      let rem := num % den
      if 2 * rem < den then q
      else if 2 * rem > den then q + 1
      else if q % 2 == 0 then q else q + 1
  let intPart := r / pow
  let fracPart := r % pow
  let body :=
    if prec == 0 then toString intPart
    else
      let fracStr := toString fracPart
      let pad := String.ofList (List.replicate (prec - fracStr.length) '0')
      s!"{intPart}.{pad}{fracStr}"
  if neg then "-" ++ body else body

/-- The precision (digits after `.`) requested by a format spec, defaulting to Python's 6. -/
private def pyFmtPrecision (spec : String) : Nat :=
  match spec.toList.dropWhile (· != '.') with
  | '.' :: rest => (String.ofList (rest.takeWhile Char.isDigit)).toNat?.getD 6
  | _ => 6

/-- Integer string of a `Float` that holds a whole number (`{:d}`/width specs), sign-aware. -/
private def pyFmtIntStr (f : Float) : String :=
  let n := (Float.abs f).toUInt64.toNat
  if f < 0.0 && n != 0 then "-" ++ toString n else toString n

/-- Apply a Python f-string format spec to a numeric value. `.Nf` → fixed decimals; a `d`/plain/width
spec formats as an integer; then fill/align/zero-pad/width (`{:02d}`, `{:>5}`) are applied. -/
def pyFormatSpec {α : Type} [PyFmtNum α] (x : α) (spec : String) : String :=
  let f := PyFmtNum.toFmtFloat x
  let base := if spec.endsWith "f" then pyFixedFloat f (pyFmtPrecision spec) else pyFmtIntStr f
  pyFmtApply spec base

end PastaLean
