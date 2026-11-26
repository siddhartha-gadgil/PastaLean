import PastaLean.PyAPI

/-!
# Python's `re` module

A backtracking matcher for Python's regular-expression syntax: literals and escapes (`\d \w \s \D \W \S
\b \B \A \Z`, `\.` …), `.`, classes `[a-z_]` / `[^…]`, groups `(…)` / `(?:…)` / `(?P<name>…)`,
backreferences `\1`, alternation, greedy and lazy quantifiers `* + ? {m,n}`, anchors `^ $`, and the
flags `IGNORECASE`, `MULTILINE`, `DOTALL`, `VERBOSE` (with `#` comments). Matching follows Python's
leftmost, priority-ordered backtracking semantics. A malformed pattern raises `re.error`
(`PatternError`, a `ValueError`) through `pyPanic`.

`compile`, `fullmatch`/`match`/`search`, `findall`, `sub` (string replacement with `\1`/`\g<name>`),
`split`, and `Match.group`/`groups`/`start`/`end`/`span`; lookarounds `(?=…)`/`(?!…)`/`(?<=…)`/`(?<!…)`,
inline flags `(?imsx)`, `(?#…)` and `(?P=name)`. Possessive quantifiers, atomic groups and Unicode
classes beyond ASCII are not modelled.

Files: `Syntax` (flags, the pattern AST, `Pattern`/`Match`), `Parser`, `Matcher` (backtracking),
`Api` (pattern and match methods, module-level functions).
-/
namespace Libraries.re

open PastaLean

def IGNORECASE : Int := 2
def I : Int := 2
def MULTILINE : Int := 8
def M : Int := 8
def DOTALL : Int := 16
def S : Int := 16
def VERBOSE : Int := 64
def X : Int := 64
def ASCII : Int := 256
def A : Int := 256

/-- The union of two flag sets (`re` flags are disjoint bits). -/
def orFlags (a b : Int) : Int :=
  [2, 8, 16, 64, 256].foldl (fun acc f => if (a / f) % 2 == 1 || (b / f) % 2 == 1 then acc + f else acc) 0

inductive ClassItem where
  | single (c : Char)
  | range (lo hi : Char)
  | digit (neg : Bool)
  | space (neg : Bool)
  | word (neg : Bool)
  deriving Inhabited, Repr, BEq

inductive Node where
  | char (c : Char)
  | any
  | cls (items : List ClassItem) (neg : Bool)
  | lineStart | lineEnd | strStart | strEnd
  | wordBoundary (neg : Bool)
  | group (idx : Option Nat) (alts : List (List Node))
  | rep (n : Node) (min : Nat) (max : Option Nat) (greedy : Bool)
  | backref (idx : Nat)
  /-- `(?=…)` / `(?!…)` (`behind := false`), `(?<=…)` / `(?<!…)` (`behind := true`). -/
  | look (behind neg : Bool) (alts : List (List Node))
  deriving Inhabited, Repr

/-- A compiled pattern: the source, its flags, the parsed alternatives and its group names. -/
structure Pattern where
  pattern : String
  flags : Int
  prog : List (List Node)
  groupCount : Nat
  groupNames : List (String × Nat)
  deriving Inhabited

/-- A successful match: the subject and each group's span (group 0 is the whole match). -/
structure Match where
  string : String
  spans : Array (Option (Nat × Nat))
  groupNames : List (String × Nat)
  deriving Inhabited

def hasFlag (flags : Int) (f : Int) : Bool := (flags / f) % 2 == 1

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

def isSpaceChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

def patternError (msg : String) {α : Type} [Inhabited α] : α :=
  pyPanic s!"PatternError: {msg}"

end Libraries.re
