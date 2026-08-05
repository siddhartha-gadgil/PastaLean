import Mathlib
import PastaLean.PyAPI.Core
import PastaLean.PyAPI.CommonProtocols.Iterable

namespace PastaLean

/-- Treat the most common Python whitespace characters as separators/strip chars. -/
private def isPyWhitespace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

/-- Helper used by `strip` to remove matching characters from the left. -/
private def stripLeftBy (p : Char → Bool) : List Char → List Char
  | c :: cs =>
      if p c then
        stripLeftBy p cs
      else
        c :: cs
  | [] => []

/-- Helper used by `strip` to remove matching characters from both ends. -/
private def stripBy (p : Char → Bool) (s : String) : String :=
  let leftTrimmed := stripLeftBy p s.toList
  let rightTrimmedRev := stripLeftBy p leftTrimmed.reverse
  String.ofList rightTrimmedRev.reverse

/--
Python-style `split()` with no explicit separator.

This collapses repeated whitespace and discards empty chunks, which matches the usual
Python behavior more closely than `splitOn " "`.
-/
private def splitOnPyWhitespace (s : String) : List String :=
  let rec go (rest : List Char) (currentRev : List Char) (accRev : List String) : List String :=
    match rest with
    | [] =>
        let accRev :=
          if currentRev.isEmpty then
            accRev
          else
            String.ofList currentRev.reverse :: accRev
        accRev.reverse
    | c :: cs =>
        if isPyWhitespace c then
          let accRev :=
            if currentRev.isEmpty then
              accRev
            else
              String.ofList currentRev.reverse :: accRev
          go cs [] accRev
        else
          go cs (c :: currentRev) accRev
  go s.toList [] []

/--
Elements accepted by Python-style `str.join`.

Python requires the iterable items to behave like strings. We support the two common
runtime cases here:
- `List String`-style inputs join directly
- a `String` input iterates by `Char`, and each character becomes a one-character string
-/
class PyStringJoin (α : Type) where
  toJoinString : α → String

/-- Strings already have the right representation for `str.join`. -/
instance : PyStringJoin String where
  toJoinString := id

/-- Joining over a string should treat each character as a one-character string. -/
instance : PyStringJoin Char where
  toJoinString c := String.singleton c

/--
Concrete string implementation for Python `join`.

Python `str.join` takes any iterable whose items behave like strings. In Lean, that means
the argument is any `α` with a `PyIterable α β` instance, together with a way to convert
each iterated item into the joined string fragment.
-/
def pyStringJoin {α β : Type} [PyIterable α β] [PyStringJoin β] (sep : String) (xs : α) : String :=
  String.intercalate sep <| (pyIter xs).map PyStringJoin.toJoinString

/-- Public runtime surface for Python `join`. -/
def pyJoin {α β : Type} [PyIterable α β] [PyStringJoin β] (sep : String) (xs : α) : String :=
  pyStringJoin sep xs

/-- Concrete string implementation for Python `replace`. -/
def pyStringReplace : String → (old : String) → (new : String) → String
  | s, old, new => s.replace old new

/-- Pad `s` to `width` with `fill`, honouring alignment (`<` left, `>` right, `^` centre). -/
private partial def pyStrFormatGo (argv : Array String) : List Char → Nat → String → String
  | [], _, acc => acc
  | '{' :: '{' :: rest, next, acc => pyStrFormatGo argv rest next (acc ++ "{")
  | '}' :: '}' :: rest, next, acc => pyStrFormatGo argv rest next (acc ++ "}")
  | '{' :: rest, next, acc =>
      let field := rest.takeWhile (· != '}')
      let rest := (rest.dropWhile (· != '}')).drop 1
      let (idxStr, spec) :=
        match (String.ofList field).splitOn ":" with
        | [i] => (i, "")
        | i :: s => (i, String.intercalate ":" s)
        | [] => ("", "")
      let (i, next) := match idxStr.toNat? with
        | some k => (k, next)
        | none => (next, next + 1)
      pyStrFormatGo argv rest next (acc ++ pyFmtApply spec (argv[i]?.getD ""))
  | c :: rest, next, acc => pyStrFormatGo argv rest next (acc.push c)

/-- Python `str.format`. Replaces each `{...}` placeholder with an (already-stringified) argument:
`{}` / `{:spec}` consume positionally, `{n}` / `{n:spec}` index explicitly. `{{`/`}}` are literal
braces. `spec` supports fill/align/zero-pad/width (`"{:02d}".format(7) = "07"`); the type char and
precision are ignored since the argument is pre-rendered. -/
def pyStrFormat (fmt : String) (args : List String) : String :=
  pyStrFormatGo args.toArray fmt.toList 0 ""

/-- Python `str.zfill(width)`: left-pad with `'0'` to `width`, keeping any leading sign first
(`"42".zfill(5) = "00042"`, `"-42".zfill(5) = "-0042"`). -/
def pyStringZfill (s : String) (width : Int) : String :=
  let w := width.toNat
  if s.length ≥ w then s
  else
    let zeros := String.ofList (List.replicate (w - s.length) '0')
    match s.toList with
    | '-' :: rest => "-" ++ zeros ++ String.ofList rest
    | '+' :: rest => "+" ++ zeros ++ String.ofList rest
    | _ => zeros ++ s

/--
Concrete string implementation for Python `strip`.

When `chars` is omitted, Python strips surrounding whitespace. When `chars` is given,
Python treats it as a set of characters to trim from both ends.
-/
def pyStringStrip : String → (chars : String := " ") → String
  | s, chars =>
      if chars = " " then
        stripBy isPyWhitespace s
      else
        let stripCharSet := chars.toList
        stripBy (fun c => stripCharSet.contains c) s

/-- Python `lstrip`: drop leading whitespace, or leading characters from `chars`. -/
def pyStringLstrip : String → (chars : String := " ") → String
  | s, chars =>
      let p := if chars = " " then isPyWhitespace else (fun c => chars.toList.contains c)
      String.ofList (stripLeftBy p s.toList)

/-- Python `rstrip`: drop trailing whitespace, or trailing characters from `chars`. -/
def pyStringRstrip : String → (chars : String := " ") → String
  | s, chars =>
      let p := if chars = " " then isPyWhitespace else (fun c => chars.toList.contains c)
      String.ofList (stripLeftBy p s.toList.reverse).reverse

/-- Python `rfind`: index of the LAST occurrence of `sub`, or `-1`. -/
def pyStringRfind (s sub : String) : Int :=
  let n := s.length
  let m := sub.length
  let rec go (i : Nat) : Int :=
    if i = 0 then (if (s.toList.take m) = sub.toList then 0 else -1)
    else if (s.toList.drop i).take m = sub.toList then (i : Int)
    else go (i - 1)
  if m = 0 then (n : Int) else if m > n then -1 else go (n - m)

/--
Concrete string implementation for Python `find`.

Returns `-1` when the substring is missing, matching Python's `str.find`.
-/
def pyStringFind : String → (sub : String) → Int
  | s, sub =>
      match s.find? sub with
      | some idx => idx.offset.byteIdx
      | none => -1

/--
Concrete string implementation for Python `index`.

Raises at runtime when the substring is missing, matching Python's `str.index`.
-/
def pyStringIndex : String → (sub : String) → Int
  | s, sub =>
      match s.find? sub with
      | some idx => idx.offset.byteIdx
      | none => panic! "ValueError: substring not found"

/-- Concrete string implementation for Python `startswith`. -/
def pyStringStartswith : String → (pfx : String) → Bool
  | s, pfx => s.startsWith pfx

/-- Concrete string implementation for Python `endswith`. -/
def pyStringEndswith : String → (sfx : String) → Bool
  | s, sfx => s.endsWith sfx

/-- Concrete string implementation for Python `lower`. -/
def pyStringLower : String → String
  | s => s.toList.map Char.toLower |> String.ofList

/-- Concrete string implementation for Python `upper`. -/
def pyStringUpper : String → String
  | s => s.toList.map Char.toUpper |> String.ofList

def pyStringCapitalize : String → String
  | s => match s.toList with
    | [] => ""
    -- Python lowercases the tail, unlike Lean's `String.capitalize` which leaves it unchanged.
    | c :: rest => String.ofList (c.toUpper :: rest.map Char.toLower)

/-- Python `title`: uppercase the first letter of each word, lowercase the rest. A "word" starts
after any non-alphabetic character (`"ab c'd" → "Ab C'D"`). -/
def pyStringTitle (s : String) : String :=
  let step : (List Char × Bool) → Char → (List Char × Bool) := fun (acc, prevAlpha) c =>
    let c' := if prevAlpha then c.toLower else c.toUpper
    (c' :: acc, c.isAlpha)
  String.ofList (s.toList.foldl step ([], false) |>.1).reverse

/-- Python `swapcase`: lowercase becomes uppercase and vice versa. -/
def pyStringSwapcase (s : String) : String :=
  String.ofList (s.toList.map fun c => if c.isUpper then c.toLower else c.toUpper)

/-- Python `casefold`: like `lower` for the ASCII range. -/
def pyStringCasefold : String → String := pyStringLower

/-- Python `removeprefix`: drop `pfx` from the front if present, else return `s` unchanged. -/
def pyStringRemovePrefix (s pfx : String) : String :=
  if pfx ≠ "" ∧ s.startsWith pfx then String.ofList (s.toList.drop pfx.length) else s

/-- Python `removesuffix`: drop `sfx` from the end if present, else return `s` unchanged. -/
def pyStringRemoveSuffix (s sfx : String) : String :=
  if sfx ≠ "" ∧ s.endsWith sfx then String.ofList (s.toList.take (s.length - sfx.length)) else s

/-- Python `rjust`: right-justify in a field of `width`, padding on the left with `fill`. -/
def pyStringRjust (s : String) (width : Int) (fill : String := " ") : String :=
  let pad := width - s.length
  let ch := fill.toList.head?.getD ' '
  if pad ≤ 0 then s else String.ofList (List.replicate pad.toNat ch) ++ s

/-- Python `ljust`: left-justify in a field of `width`, padding on the right with `fill`. -/
def pyStringLjust (s : String) (width : Int) (fill : String := " ") : String :=
  let pad := width - s.length
  let ch := fill.toList.head?.getD ' '
  if pad ≤ 0 then s else s ++ String.ofList (List.replicate pad.toNat ch)

/-- Python `center`: center in a field of `width`; the extra pad char (odd gap) goes on the right. -/
def pyStringCenter (s : String) (width : Int) (fill : String := " ") : String :=
  let pad := width - s.length
  let ch := fill.toList.head?.getD ' '
  if pad ≤ 0 then s
  else
    let left := pad.toNat / 2
    let right := pad.toNat - left
    String.ofList (List.replicate left ch) ++ s ++ String.ofList (List.replicate right ch)

/--
Concrete string implementation for Python `split`.

With an explicit separator, this uses `splitOn`. With no explicit separator, it uses
Python-like whitespace splitting.
-/
def pyStringSplit : String → (sep : String := " ") → List String
  | s, sep =>
      if sep = " " then
        splitOnPyWhitespace s
      else
        if sep = "" then
          panic! "ValueError: empty separator"
        else
          s.splitOn sep

/-- Concrete string implementation for Python `splitlines()`. -/
def pyStringSplitLines : String → List String
  | s => s.splitOn "\n"

/-- Public runtime surface for Python `split`. -/
def pySplit : String → (sep : String := " ") → List String
  | s, sep => pyStringSplit s sep

/-- Public runtime surface for Python `replace`. -/
def pyReplace : String → (old : String) → (new : String) → String :=
  pyStringReplace

/-- Public runtime surface for Python `strip`. -/
def pyStrip : String → (chars : String := " ") → String
  | s, chars => pyStringStrip s chars

def pyStringCount : String → (sub : String) → Int
   | s, "" => s.length + 1
   | s, sub => (s.splitOn sub |>.length) - 1

-- #check String.count
/-- Python `islower`: every cased character is lowercase AND there is at least one of them, so
`"".islower()` and `"123".islower()` are both `False`. Cased = alphabetic in the ASCII range. -/
def pyIsLower : String → Bool
  | s =>
      let cased := s.toList.filter Char.isAlpha
      !cased.isEmpty && cased.all Char.isLower

/-- Python `isupper`: the `pyIsLower` rule with `isUpper`. -/
def pyIsUpper : String → Bool
  | s =>
      let cased := s.toList.filter Char.isAlpha
      !cased.isEmpty && cased.all Char.isUpper

-- Python's `str.isX()` predicates are all `False` on the empty string.
def pyIsAlpha : String → Bool
  | s => !s.isEmpty && s.toList.all Char.isAlpha

def pyIsDecimal : String → Bool
  | s => !s.isEmpty && s.toList.all Char.isDigit

def pyIsAlphanum : String → Bool
  | s => !s.isEmpty && s.toList.all Char.isAlphanum

def pyIsWhitespace : String → Bool
  | s => !s.isEmpty && s.toList.all isPyWhitespace


def pyPartition : String → (sep : String) → (String × String × String)
  | s, sep =>
    match sep with
    | "" => panic! "ValueError: empty separator"
    | _ =>
      match s.find? sep with
      | some idx =>
          -- let idx := idx.offset.byteIdx
          let chars := s.toList
          let pfx := String.ofList (chars.take idx.offset.byteIdx)
          let suffix := String.ofList (chars.drop (idx.offset.byteIdx + sep.length))
          (pfx, sep, suffix)
      | none => (s, "", "")

theorem pyLower_is_lower (s : String) : pyIsLower s = true → pyStringLower s = s := by
  intro h
  unfold pyIsLower at h
  unfold pyStringLower
  simp_all only [List.all_filter]
  have eq : List.map Char.toLower s.toList = s.toList := by
    have h'' : (List.map Char.toLower s.toList).length = s.toList.length := by grind
    apply List.ext_getElem!
    · exact h''
    · intro n
      by_cases h' : n < s.toList.length
      · simp_all only [List.length_map, String.length_toList, getElem!_pos, List.getElem_map]
        have g : s.toList[n] ∈ s.toList := List.getElem_mem (by get_elem_tactic)
        have g' : s.toList[n].isAlpha = false ∨ s.toList[n].isLower = true := by grind only [=
            List.all_eq]
        by_cases sc : s.toList[n].isLower
        · grind only [Char.not_isLower_of_isUpper, Char.toLower_eq_of_not_isUpper]
        · grind only [Char.isAlpha, Char.toLower_eq_of_not_isUpper]
      · grind only [= getElem!_neg]
  simp [eq]


theorem pyUpper_is_upper (s : String) : pyIsUpper s = true → pyStringUpper s = s := by
  intro h
  unfold pyIsUpper at h
  unfold pyStringUpper
  simp_all only [List.all_filter]
  have eq : List.map Char.toUpper s.toList = s.toList := by
    have h'' : (List.map Char.toUpper s.toList).length = s.toList.length := by grind
    apply List.ext_getElem!
    · exact h''
    · intro n
      by_cases h' : n < s.toList.length
      · simp_all only [List.length_map, String.length_toList, getElem!_pos, List.getElem_map]
        have g : s.toList[n] ∈ s.toList := List.getElem_mem (by get_elem_tactic)
        have g' : s.toList[n].isAlpha = false ∨ s.toList[n].isUpper = true := by grind only [= List.all_eq]
        by_cases sc : s.toList[n].isUpper
        · grind only [Char.toUpper_eq_of_not_isLower, Char.not_isLower_of_isUpper]
        · grind only [Char.isAlpha, Char.toUpper_eq_of_not_isLower]
      · grind only [= getElem!_neg]
  simp [eq]

theorem pyLower_length_invariant (s : String) : (pyStringLower s).length = s.length := by
  unfold pyStringLower
  grind only [String.length_eq_list_length, = List.length_map, String.length_toList]

theorem pyUpper_length_invariant (s : String) : (pyStringUpper s).length = s.length := by
  unfold pyStringUpper
  grind only [String.length_eq_list_length, = List.length_map, String.length_toList]

theorem pyFind_eq_pyIndex (s sub : String) : pyStringFind s sub ≠ -1 → pyStringFind s sub = pyStringIndex s sub := by
  intro h
  match eq : s.find? sub with
  | some idx =>
      simp [pyStringFind, pyStringIndex,eq]
  | none => simp [pyStringFind, eq] at h

-- #check String.split
end PastaLean
