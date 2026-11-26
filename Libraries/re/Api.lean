import Libraries.re.Matcher

namespace Libraries.re

open PastaLean

/-- `pattern.match(s)`: a match anchored at the start of `s`. -/
def Pattern.match (p : Pattern) (s : String) : Option Match :=
  (runAt p s.toList.toArray 0 false).map (toMatch p s 0)

/-- `pattern.fullmatch(s)`: a match of the whole of `s`. -/
def Pattern.fullmatch (p : Pattern) (s : String) : Option Match :=
  (runAt p s.toList.toArray 0 true).map (toMatch p s 0)

/-- `pattern.search(s)`: the leftmost match anywhere in `s`. -/
def Pattern.search (p : Pattern) (s : String) : Option Match :=
  let cs := s.toList.toArray
  (List.range (cs.size + 1)).findSome? fun i => (runAt p cs i false).map (toMatch p s i)

/-- Non-overlapping matches, left to right (an empty match advances one character). -/
def allMatches (p : Pattern) (s : String) : List Match := Id.run do
  let cs := s.toList.toArray
  let mut out : List Match := []
  let mut i := 0
  let mut fuel := cs.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    match (List.range (cs.size + 1 - i)).findSome? (fun d => (runAt p cs (i + d) false).map fun r => (i + d, r)) with
    | some (st, (j, caps)) =>
        out := out ++ [toMatch p s st (j, caps)]
        i := if j == st then j + 1 else j
        if i > cs.size then break
    | none => break
  return out

def substr (s : String) (a b : Nat) : String := String.ofList ((s.toList.drop a).take (b - a))

/-- What `m.group(n)` returns: the matched text, or `None` for a group that did not participate. It
stands in for a `str` where Python code uses it as one (it coerces, concatenates, converts); using a
`None` group that way is Python's `TypeError`/`AttributeError`, raised through `pyPanic`. -/
structure Group where
  val : Option String
  deriving Inhabited, BEq, Repr

def Group.str (g : Group) : String :=
  g.val.getD (pyPanic "AttributeError: 'NoneType' object has no attribute (the group did not match)")

instance : Coe Group String := ⟨Group.str⟩
instance : PyPrintable Group where
  pyStringify g := match g.val with | some s => s | none => "None"
  pyReprify g := match g.val with | some s => pyReprString s | none => "None"
instance : PyIsNone Group := ⟨fun g => g.val.isNone⟩
instance : PyTruthy Group := ⟨fun g => match g.val with | some s => !s.isEmpty | none => false⟩
instance : PyLen Group := ⟨fun g => g.str.length⟩
instance : PyIntCast Group := ⟨fun g => pyInt g.str⟩
instance : PyRatCast Group := ⟨fun g => pyRat g.str⟩
instance : PyFloatCast Group := ⟨fun g => pyFloat g.str⟩
instance : PyHAdd Group String String := ⟨fun g s => g.str ++ s⟩
instance : PyHAdd String Group String := ⟨fun s g => s ++ g.str⟩
instance : PyHAdd Group Group String := ⟨fun g h => g.str ++ h.str⟩
instance : PyIterable Group String := ⟨fun g => g.str.toList.map String.singleton⟩
instance : PyContains Group String := ⟨fun g t => pyContains g.str t⟩

/-- The text of group `n`, `""` when it did not participate (`sub`'s and `findall`'s convention). -/
def Match.text (m : Match) (n : Int) : String :=
  match m.spans[n.toNat]? with
  | some (some (a, b)) => substr m.string a b
  | some none => ""
  | none => pyPanic "IndexError: no such group"

/-- `m.group(n)` (0: the whole match); `None` for a group that did not participate. -/
def Match.group (m : Match) (n : Int := 0) : Group :=
  match m.spans[n.toNat]? with
  | some (some (a, b)) => ⟨some (substr m.string a b)⟩
  | some none => ⟨none⟩
  | none => pyPanic "IndexError: no such group"

/-- A tuple of group strings (`None` for a group that did not participate): what `m.groups()` and a
multi-group `findall` return. A one-element `findall` result is a bare string (`tuple := false`). -/
structure Groups where
  items : List (Option String)
  tuple : Bool := true
  deriving Inhabited, BEq

instance : PyPrintable Groups where
  pyStringify g :=
    let parts := g.items.map fun | some x => pyReprString x | none => "None"
    if !g.tuple then parts.headD "''"
    else if parts.length == 1 then s!"({parts.head!},)" else "(" ++ ", ".intercalate parts ++ ")"

instance : PyLen Groups := ⟨fun g => g.items.length⟩
instance : PyIterable Groups (Option String) := ⟨fun g => g.items⟩
instance : PyGetItem Groups Int (Option String) := ⟨fun g i => pyListGetItem g.items i⟩

/-- `m.groups()`: every capturing group, `None` for one that did not participate. -/
def Match.groups (m : Match) : Groups :=
  { items := (List.range (m.spans.size - 1)).map fun i =>
      match m.spans[i + 1]? with | some (some (a, b)) => some (substr m.string a b) | _ => none }

def Match.start (m : Match) (n : Int := 0) : Int :=
  match m.spans[n.toNat]? with | some (some (a, _)) => a | _ => -1

def Match.«end» (m : Match) (n : Int := 0) : Int :=
  match m.spans[n.toNat]? with | some (some (_, b)) => b | _ => -1

def Match.span (m : Match) (n : Int := 0) : Int × Int := (m.start n, m.«end» n)

/-- `pattern.findall(s)`: the whole matches, group 1 when the pattern has exactly one group, else the
groups as tuples. -/
def Pattern.findall (p : Pattern) (s : String) : List Groups :=
  (allMatches p s).map fun m =>
    if p.groupCount == 0 then { items := [some (m.text 0)], tuple := false }
    else if p.groupCount == 1 then { items := [some (m.text 1)], tuple := false }
    else { (m.groups) with items := m.groups.items.map (some ∘ (·.getD "")) }

def expandRepl (m : Match) (repl : String) : String := Id.run do
  let cs := repl.toList.toArray
  let mut out := ""
  let mut i := 0
  while h : i < cs.size do
    let c := cs[i]
    if c == '\\' && i + 1 < cs.size then
      let d := cs[i + 1]!
      if d.isDigit then out := out ++ m.text (d.toNat - '0'.toNat); i := i + 2
      else if d == 'g' && cs[i + 2]? == some '<' then
        let name := String.ofList ((cs.toList.drop (i + 3)).takeWhile (· != '>'))
        let idx := (m.groupNames.lookup name).getD (name.toNat?.getD 0)
        out := out ++ m.text idx
        i := i + 4 + name.length
      else if d == 'n' then out := out.push '\n'; i := i + 2
      else if d == 't' then out := out.push '\t'; i := i + 2
      else if d == '\\' then out := out.push '\\'; i := i + 2
      else out := out.push c; i := i + 1
    else out := out.push c; i := i + 1
  return out

/-- `pattern.sub(repl, s, count=0)` with a string replacement (`\1`, `\g<name>`). -/
def Pattern.sub (p : Pattern) (repl : String) (s : String) (count : Int := 0) : String := Id.run do
  let ms := allMatches p s
  let ms := if count > 0 then ms.take count.toNat else ms
  let mut out := ""
  let mut last := 0
  for m in ms do
    let a := (m.start 0).toNat
    out := out ++ substr s last a ++ expandRepl m repl
    last := (m.«end» 0).toNat
  return out ++ substr s last s.length

/-- `pattern.split(s, maxsplit=0)`: pieces between matches, with any groups interleaved. -/
def Pattern.split (p : Pattern) (s : String) (maxsplit : Int := 0) : List String := Id.run do
  let ms := allMatches p s
  let ms := if maxsplit > 0 then ms.take maxsplit.toNat else ms
  let mut out : List String := []
  let mut last := 0
  for m in ms do
    out := out ++ [substr s last (m.start 0).toNat] ++ m.groups.items.map (·.getD "")
    last := (m.«end» 0).toNat
  return out ++ [substr s last s.length]

/-! ### Module-level functions (compile, then use the pattern) -/

def «match» (pattern s : String) (flags : Int := 0) : Option Match := (compile pattern flags).match s
def fullmatch (pattern s : String) (flags : Int := 0) : Option Match := (compile pattern flags).fullmatch s
def search (pattern s : String) (flags : Int := 0) : Option Match := (compile pattern flags).search s
def findall (pattern s : String) (flags : Int := 0) : List Groups := (compile pattern flags).findall s
def sub (pattern repl s : String) (count : Int := 0) (flags : Int := 0) : String :=
  (compile pattern flags).sub repl s count
def split (pattern s : String) (maxsplit : Int := 0) (flags : Int := 0) : List String :=
  (compile pattern flags).split s maxsplit
def escape (s : String) : String :=
  s.foldl (fun acc c => if c.isAlphanum || c == '_' then acc.push c else (acc.push '\\').push c) ""

/-! ### Python views -/

instance : PyPrintable Pattern where
  pyStringify p := s!"re.compile({pyReprString p.pattern})"

instance : PyPrintable Match where
  pyStringify m :=
    let (a, b) := m.span 0
    s!"<re.Match object; span=({a}, {b}), match={pyReprString (m.text 0)}>"

instance : PyTruthy Match := ⟨fun _ => true⟩
instance : PyBool Match := ⟨fun _ => true⟩

/-- `m.group(…)` etc. on the `Optional[Match]` a match returns: Python raises `AttributeError` on
`None`, so these unwrap (code calls them after testing the match). -/
def _root_.Option.group (m : Option Match) (n : Int := 0) : Group :=
  match m with | some m => m.group n | none => pyPanic "AttributeError: 'NoneType' object has no attribute 'group'"
def _root_.Option.groups (m : Option Match) : Groups :=
  match m with | some m => m.groups | none => pyPanic "AttributeError: 'NoneType' object has no attribute 'groups'"
def _root_.Option.span (m : Option Match) (n : Int := 0) : Int × Int :=
  match m with | some m => m.span n | none => pyPanic "AttributeError: 'NoneType' object has no attribute 'span'"

end Libraries.re
