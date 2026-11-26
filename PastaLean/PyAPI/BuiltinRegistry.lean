import PastaLean.PyAPI

namespace PastaLean

/-!
Registry for Python builtins that lower to ordinary Lean runtime names.

Special builtins such as `print` and `input` still need custom call lowering
because they affect evaluation order, effects, or argument interpretation.
-/

/-- Direct builtin mapping for plain function calls that need no special syntax handling. -/
def pythonBuiltinMap? (name : String) : Option Lean.Name :=
  match name with
  | "len" => some ``pyLen
  | "sorted" => some ``pySort
  | "zip" => some ``pyZip
  | "enumerate" => some ``pyEnumerate
  | "sum" => some ``pySum
  | "min" => some ``pyMin
  | "max" => some ``pyMax
  | "bool" => some ``pyBool
  | "any" => some ``pyStdAny
  | "all" => some ``pyAll
  | "abs" => some ``pyAbs
  | "bin" => some ``pyBin
  | "hex" => some ``pyHex
  | "oct" => some ``pyOct
  | "divmod" => some ``pyDivmod
  | "reversed" => some ``pyReversed
  | "chr" => some ``pyChr
  | "ord" => some ``pyOrd
  -- `pow(b, e)` ≡ `b ** e`; `pow(b, e, m)` is modular exponentiation. `pyPow`'s modulus
  -- argument defaults to `0` ("no modulus"), so both arities lower to the same name.
  | "pow" => some ``pyPow
  | "set" => some ``pySet
  -- `dict(pairs)` (e.g. `dict(zip(keys, vals))`) builds a hash map from an iterable of pairs.
  | "dict" => some ``pyDict
  -- `int`/`str` have dedicated special-case lowering for *direct* calls (`int(x)`); the
  -- registry entries make them usable as first-class callables, e.g. `map(int, xs)`.
  | "int" => some ``pyInt
  | "str" => some ``pyStr
  | "repr" => some ``PyPrintable.pyReprify
  | "float" => some ``pyFloat
  -- We have no real tuple-from-iterable runtime; `tuple(xs)` is treated as a list, which is
  -- adequate for the membership/comparison/iteration uses that appear in this subset.
  | "tuple" => some ``pyList
  -- `map`/`filter`/`list` also have dedicated special-case lowering for direct calls (which
  -- wins, being matched first). The registry entries are the fallback used when the call is
  -- IO-effectful and routed through `inlineEffectfulTerm`, e.g. `map(int, input().split())`.
  | "map" => some ``pyMap
  | "filter" => some ``pyFilter
  | "list" => some ``pyList
  | "type" => some ``pyType
  | "eval" => some ``pyEval
  -- `next(iter(e))` / `next(iter(e), d)`, rewritten by the driver (general iterators are stateful)
  | "__pl_first" => some ``pyFirst
  | "__pl_first_or" => some ``pyFirstOr
  | _ => none

/-- Exact-mode overrides for builtins whose numeric result type changes when `float` lowers to
`ℚ`. Consulted *before* `pythonBuiltinMap?` in the default mode; `none` falls through to it. -/
def pythonBuiltinMapExact? (name : String) : Option Lean.Name :=
  match name with
  | "float" => some ``pyRat
  | _ => none

/-- Associativity for folding a binary runtime function over a variadic builtin's arguments. -/
inductive BuiltinFoldDir where
  | left
  | right
  deriving Repr, DecidableEq

/--
Registry for *variadic* builtins that lower by folding one binary runtime function over their
(two-or-more) arguments. This is the general, data-driven home for "n-ary" builtins: a single
generic handler in the call lowering reads this table, so adding such a builtin is one row here
rather than a new branch in the call generator.

`zip(x₁, …, xₙ)` is `pyZip x₁ (pyZip x₂ (… (pyZip xₙ₋₁ xₙ)))` — a *right* fold of the 2-way
`pyZip`. That yields the right-nested n-tuple `(a₁, (a₂, …, aₙ))` that tuple unpacking projects
through, and `pyZip`'s shortest-wins truncation composes to "truncate to the shortest input".
-/
def variadicFoldBuiltin? (name : String) : Option (Lean.Name × BuiltinFoldDir) :=
  match name with
  | "zip" => some (``pyZip, BuiltinFoldDir.right)
  | _ => none

end PastaLean
