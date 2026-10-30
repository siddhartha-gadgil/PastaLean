import PastaLean.Imports
import PastaLean.PyAPI.PyPanic

namespace PastaLean

/-! ### Seeing through `Id`

A loop+`Invariant` function is emitted `Id`-typed (`String → Id ℤ`) so it can carry an `mvcgen`
Hoare-triple spec. When such a function is then used as a first-class value or in a value comparison
by another function (`max(map(strength, xs))`, `strength(e) == m`), the `Id` wrapper leaks into the
element/operand type. `Id α` is *definitionally* `α`, but instance synthesis does not unfold `Id`, so
`Ord (Id ℤ)` / `BEq (Id ℤ)` / `DecidableEq (Id ℤ)` go stuck. These forwarding instances close that gap
(each is `inferInstanceAs` on the reduced `α`); they only ever *add* resolutions, never change one. -/
instance {α : Type u} [Ord α] : Ord (Id α) := inferInstanceAs (Ord α)
instance {α : Type u} [BEq α] : BEq (Id α) := inferInstanceAs (BEq α)
instance {α : Type u} [DecidableEq α] : DecidableEq (Id α) := inferInstanceAs (DecidableEq α)
instance {α : Type u} [LT α] : LT (Id α) := inferInstanceAs (LT α)
instance {α : Type u} [LE α] : LE (Id α) := inferInstanceAs (LE α)

/-- Minimal runtime value for translated Python exceptions. -/
structure PyException where
  kind : String
  msg : String
  deriving Inhabited, Repr, BEq

namespace PyException

/-- Smart constructor used by codegen so generated Lean does not need to expose `.mk`. -/
def Raise (kind : String) (msg : String := "") : PyException :=
  .mk kind msg

/-- Accessor used by generated code when matching caught exceptions by kind. -/
def OfKind (exc : PyException) : String :=
  exc.kind

end PyException

/-- Concrete exception monad used for translated Python code that can raise (with IO). -/
abbrev PyExcept (α : Type) := ExceptT PyException IO α

/-- Pure exception monad for translated Python code that can raise but does no IO. -/
abbrev PyExceptId (α : Type) := ExceptT PyException Id α

instance : ToString PyException where
  toString exc :=
    if exc.msg.isEmpty then
      exc.kind
    else
      s!"{exc.kind}: {exc.msg}"

/-- Run `body`, converting any underlying `IO` error into a `PyException` raise (leaving an
already-raised `PyException` untouched). A bare Python `except:` catches *everything*, including
the `EOFError`/`OSError` that `input()` raises at end of input — but those surface as `IO` errors
below the `ExceptT` layer, invisible to a `try … catch` over `PyExcept` (which only sees
`PyException`). Wrapping the `try` body in this turns such errors into `PyException`s, so the
translated `catch` (which keeps a real `try … catch`, so `break`/`continue` in the handler still
work) catches them — matching Python. -/
def PyExcept.captureIOErrors {α : Type} (body : PyExcept α) : PyExcept α :=
  ExceptT.mk
    (try body.run
     catch e : IO.Error => pure (Except.error (PyException.Raise "Exception" (toString e))))

/-- Python-style `range` supporting positive and negative steps. -/
def pyRange (stop : Int) (start : Int := 0) (step : Int := 1) : List Int := do
  if step > 0 then
    -- Element count is ⌈(stop-start)/step⌉ (0 when stop ≤ start). `(d + step - 1)/step` is that ceil.
    List.map (fun i => start + i) (List.range' 0 ((stop - start + step - 1) / step).toNat step.toNat)
  else if step < 0 then
    List.map (fun i => start - i) (List.range' 0 ((start - stop + (-step) - 1) / (-step)).toNat (-step).toNat)
  else
    []

/-- Pad `s` to `width` with `fill`, honouring alignment (`<` left, `>` right, `^` centre). -/
def pyFmtPad (s : String) (width : Nat) (fill : Char) (align : Char) : String :=
  let n := s.length
  if n ≥ width then s
  else
    let total := width - n
    match align with
    | '<' => s ++ String.ofList (List.replicate total fill)
    | '^' => let l := total / 2
             String.ofList (List.replicate l fill) ++ s ++ String.ofList (List.replicate (total - l) fill)
    | _   => String.ofList (List.replicate total fill) ++ s   -- '>' (default for a numeric field)

/-- `|n|` in `radix` (2/8/16), Python `format`-style: no `0x` prefix, sign kept, `x`/`X` case. -/
def pyIntToRadix (radix : Nat) (upper : Bool) (n : Int) : String :=
  let digits := (Nat.toDigits radix n.natAbs).map (if upper then Char.toUpper else id)
  let s := String.ofList digits
  if n < 0 then "-" ++ s else s

/-- Apply one Python format spec (the part after `:`) to an already-stringified argument. Handles
the common `[fill][align][0]width` forms — `{:02d}`, `{:>5}`, `{:<10}`, `{:5d}` — plus a radix type
char (`{:02x}`/`{:o}`/`{:b}`) on an integer arg. Other type chars and any `.precision` are ignored:
the argument is already rendered. -/
def pyFmtApply (spec : String) (arg : String) : String :=
  let cs := spec.toList
  -- optional `[fill]align`: an explicit align, possibly preceded by a fill char.
  let (fill, align, cs) :=
    match cs with
    | f :: a :: rest =>
        if a == '<' || a == '>' || a == '^' then (f, a, rest)
        else if f == '<' || f == '>' || f == '^' then (' ', f, a :: rest)
        else (' ', ' ', cs)
    | [a] => if a == '<' || a == '>' || a == '^' then (' ', a, []) else (' ', ' ', cs)
    | [] => (' ', ' ', cs)
  -- `0` before the width zero-fills and right-aligns.
  let (fill, align, cs) :=
    match cs with
    | '0' :: rest => ('0', (if align == ' ' then '>' else align), rest)
    | _ => (fill, align, cs)
  let width := (String.ofList (cs.takeWhile Char.isDigit)).toNat?.getD 0
  -- A radix type char after the width (`{:02x}` → hex, `{:o}`/`{:b}`) converts an integer arg. Both
  -- `str.format` (pre-renders args to decimal) and f-strings route here, so the base conversion lives
  -- here rather than in each formatter.
  let arg := match (cs.dropWhile Char.isDigit).head?, arg.toInt? with
    | some 'x', some n => pyIntToRadix 16 false n
    | some 'X', some n => pyIntToRadix 16 true n
    | some 'o', some n => pyIntToRadix 8 false n
    | some 'b', some n => pyIntToRadix 2 false n
    | _, _ => arg
  pyFmtPad arg width fill align

/-- Python-style list indexing with negative indices and runtime failure on out-of-bounds access. -/
def pyListGetItem {α : Type} [Inhabited α] (xs : List α) (idx : Int) : α :=
  let len := xs.length
  if len == 0 then
    PastaLean.pyPanic "IndexError: list index out of range"
  else
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then
      PastaLean.pyPanic "IndexError: list index out of range"
    else
      match xs[trueIdx.toNat]? with
      | some value => value
      | none => PastaLean.pyPanic "IndexError: list index out of range"

/-- Python-style slicing for lists. -/
def pyListSlice {α : Type} (xs : List α) (start : Option Int) (stop : Option Int) : List α :=
  let len := xs.length
  let start : Nat := match start with
    | some i => if i < 0 then (max 0 (len + i)).toNat else (min len i.toNat)
    | none => 0
  let stop : Nat := match stop with
    | some i => if i < 0 then (max 0 (len + i)).toNat else (min len i.toNat)
    | none => len
  xs.take stop |> List.drop start

/-- Full Python list slicing `xs[start:stop:step]`, including a negative `step` (e.g. `xs[::-1]`
reverses; `xs[::2]` takes every other element). Implements CPython's index clamping: with a
positive step the bounds clamp into `[0, len]`, with a negative step into `[-1, len-1]`, then it
walks `start, start+step, …` while still on the correct side of `stop`. A `step` of `0` (a Python
`ValueError`) yields `[]`. -/
def pyListSliceStep {α : Type} (xs : List α) (start stop step : Option Int) : List α :=
  let len : Int := xs.length
  let s : Int := step.getD 1
  if s == 0 then []
  else
    let arr := xs.toArray
    let clampPos (i : Int) : Int := if i < 0 then max 0 (len + i) else min i len
    let clampNeg (i : Int) : Int := if i < 0 then max (-1) (len + i) else min i (len - 1)
    let lo : Int := if s > 0 then (match start with | none => 0 | some i => clampPos i)
                    else (match start with | none => len - 1 | some i => clampNeg i)
    let hi : Int := if s > 0 then (match stop with | none => len | some i => clampPos i)
                    else (match stop with | none => -1 | some i => clampNeg i)
    let rec go (idx : Int) (fuel : Nat) (acc : List α) : List α :=
      match fuel with
      | 0 => acc.reverse
      | fuel + 1 =>
        let onSide := if s > 0 then idx < hi else idx > hi
        if onSide && idx ≥ 0 && idx < len then
          match arr[idx.toNat]? with
          | some x => go (idx + s) fuel (x :: acc)
          | none => acc.reverse
        else acc.reverse
    go lo (xs.length + 1) []

/-- Python-style indexing/slicing for strings. -/
def pyStringGetItem (s : String) (idx : Int) : Option Char :=
  let lst := s.toList
  let len := lst.length
  if len == 0 then
    none
  else
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then
      none
    else
      lst[trueIdx.toNat]?

/-- Python-style string indexing, returning a one-character string. Python has no separate
character type — `s[i]` is a length-1 `str` — so string element access yields `String`, keeping
it interoperable with string literals (`s[i] == 'x'`), `ord`, and string methods. An
out-of-range index yields the empty string. -/
def pyStringGetItemStr (s : String) (idx : Int) : String :=
  match pyStringGetItem s idx with
  | some c => c.toString
  | none => ""

/-- Python-style slicing for strings. -/
def pyStringSlice (s : String) (start : Option Int) (stop : Option Int) : String :=
  let lst := s.toList
  let sliced := pyListSlice lst start stop
  String.ofList sliced

/-- Full Python string slicing `s[start:stop:step]` (negative step reverses, etc.). -/
def pyStringSliceStep (s : String) (start stop step : Option Int) : String :=
  String.ofList (pyListSliceStep s.toList start stop step)

/-- Python slicing `c[lo:hi:step]` over the types that support it. Both lists and strings slice,
and codegen cannot tell which a value is (e.g. `a[1:]` where `a` is a parameter), so it targets
the single name `pySlice` and the instance is chosen by the value's type — a `String` slices to a
`String`, a `List` to a `List`. The `step` is carried so `a[::-1]`/`a[::2]` work. -/
class PySlice (α : Type) where
  slice : α → Option Int → Option Int → Option Int → α

/-- Dispatch Python slicing `c[lo:hi:step]` through the `PySlice` typeclass. -/
def pySlice {α : Type} [PySlice α] (c : α) (lo hi step : Option Int) : α :=
  PySlice.slice c lo hi step

instance {β : Type} : PySlice (List β) where
  slice xs lo hi step := pyListSliceStep xs lo hi step

instance : PySlice String where
  slice s lo hi step := pyStringSliceStep s lo hi step

/--
Concrete carrier for a Python construct the transpiler does not support (foreign libraries like
`logging`/`requests`, unhandled syntax, ...). It carries the original source and prints as its
`Repr`.
-/
structure PyUnsupportedValue where
  source : String
  deriving Inhabited, Repr, BEq

/--
Best-effort fallback sink. Codegen emits `pyUnsupported "<original source>"` in
every position a dropped statement appears — bare statement (`let _ := …`), assignment
(`let x := …`), or top-level (`def … := …`). Because it returns a concrete type, the binding
always elaborates and keeps the variable **declared** (no unconstrained `Inhabited ?m`); the
[`PastaLean.Linter`] flags each use with a yellow "not supported" warning.
-/
@[inline] def pyUnsupported (source : String) : PyUnsupportedValue := ⟨source⟩

end PastaLean
