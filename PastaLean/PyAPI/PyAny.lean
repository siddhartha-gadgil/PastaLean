import PastaLean.PyAPI.PyPrint
import PastaLean.PyAPI.CommonProtocols.Truthy
import PastaLean.PyAPI.CommonProtocols.GetItem
import PastaLean.PyAPI.CommonProtocols.SetItem
import PastaLean.PyAPI.CommonProtocols.Length
import PastaLean.PyAPI.CommonProtocols.Iterable
import PastaLean.PyAPI.CommonProtocols.IsNone
import PastaLean.PyAPI.Operators
import PastaLean.PyAPI.Builtins.Casting
import PastaLean.PyAPI.Builtins.Math
import PastaLean.PyAPI.Builtins.Functional
import PastaLean.PyAPI.Strings
import PastaLean.PyAPI.Lists
import PastaLean.PyAPI.CommonProtocols.Membership
import PastaLean.PyAPI.CommonProtocols.Count
import PastaLean.PyAPI.CommonProtocols.Sorting

/-!
# `PyAny` — the dynamic-value fallback

When type inference cannot give a value a single Lean type — a variable that is an `int` on one path
and a `str` on another, a function that returns different types per branch — the value is boxed as a
`PyAny`. Every Python value maps into `PyAny`, so a boxed slot always type-checks; the cost is
that a boxed value is not provable (it is not a commutative ring), which is why boxing is a last
resort the code generator warns about.

Boxing is automatic at the boundary: a `CoeTail` instance means `return 1` and `return "neg"` in the
same function both coerce to `PyAny` with no explicit wrapper.
-/

namespace PastaLean

/-- A boxed Python value: whatever a slot could not be given a single static type. -/
inductive PyAny where
  | int   (n : Int)
  | bool  (b : Bool)
  | str   (s : String)
  | float (q : Rat)
  | list  (xs : List PyAny)
  | none
  deriving Repr

/-- The canonical empty/default boxed value. Used to initialize a hoisted `let mut` binding for a
variable Python assigns only inside a block (`if`/`try`) — Lean has no such leak-out, so codegen
pre-declares the variable before the block. `none` (Python `None`) is the honest empty; it does not
faithfully model `UnboundLocalError`, which the linter flags separately. -/
def emptyPyAny : PyAny := .none

/- Structural decidable equality on the boxed value (`=`), distinct from the numeric `BEq` below
(`==`, which makes `5 == 5.0` true). `deriving DecidableEq` fails on the nested `List PyAny`, so this
is a hand-written *mutual* recursion over `PyAny` and `List PyAny`. It lets a boxed comparison against a
literal — `s = PyAny.str ""` — resolve when `s` could not be un-boxed to a concrete type. -/
mutual
def PyAny.decEq : (a b : PyAny) → Decidable (a = b)
  | .int x,   .int y   => if h : x = y then .isTrue (by subst h; rfl) else .isFalse (by intro he; injection he; exact h ‹_›)
  | .bool x,  .bool y  => if h : x = y then .isTrue (by subst h; rfl) else .isFalse (by intro he; injection he; exact h ‹_›)
  | .str x,   .str y   => if h : x = y then .isTrue (by subst h; rfl) else .isFalse (by intro he; injection he; exact h ‹_›)
  | .float x, .float y => if h : x = y then .isTrue (by subst h; rfl) else .isFalse (by intro he; injection he; exact h ‹_›)
  | .none,    .none    => .isTrue rfl
  | .list x,  .list y  => match PyAny.decEqList x y with
      | .isTrue h  => .isTrue (by subst h; rfl)
      | .isFalse h => .isFalse (by intro he; injection he; exact h ‹_›)
  | .int _,.bool _ | .int _,.str _ | .int _,.float _ | .int _,.list _ | .int _,.none
  | .bool _,.int _ | .bool _,.str _ | .bool _,.float _ | .bool _,.list _ | .bool _,.none
  | .str _,.int _ | .str _,.bool _ | .str _,.float _ | .str _,.list _ | .str _,.none
  | .float _,.int _ | .float _,.bool _ | .float _,.str _ | .float _,.list _ | .float _,.none
  | .list _,.int _ | .list _,.bool _ | .list _,.str _ | .list _,.float _ | .list _,.none
  | .none,.int _ | .none,.bool _ | .none,.str _ | .none,.float _ | .none,.list _ =>
      .isFalse (by intro h; injection h)
def PyAny.decEqList : (a b : List PyAny) → Decidable (a = b)
  | [], []       => .isTrue rfl
  | [], _::_     => .isFalse (by intro h; injection h)
  | _::_, []     => .isFalse (by intro h; injection h)
  | x::xs, y::ys => match PyAny.decEq x y, PyAny.decEqList xs ys with
      | .isTrue h1, .isTrue h2 => .isTrue (by subst h1; subst h2; rfl)
      | .isFalse h1, _         => .isFalse (by intro he; injection he with a b; exact h1 a)
      | _, .isFalse h2         => .isFalse (by intro he; injection he with a b; exact h2 b)
end
instance : DecidableEq PyAny := PyAny.decEq

/-- Default a `PyAny` to `emptyPyAny` (Python `None`), not `int 0` (the derived first-constructor
default), so a hoisted dynamic binding reads as "unset" rather than a spurious zero. -/
instance : Inhabited PyAny := ⟨emptyPyAny⟩

namespace PyAny

/-- Python `str()` of a boxed value; `repr` is the form shown *inside* a container (strings quoted). -/
partial def toStr (repr : Bool) : PyAny → String
  | .int n   => toString n
  | .bool b  => if b then "True" else "False"
  | .str s   => if repr then pyReprString s else s
  | .float q => toString (Rat.toFloat q)
  | .none    => "None"
  | .list xs => "[" ++ String.intercalate ", " (xs.map (toStr true)) ++ "]"

end PyAny

/-- Box a value of a known type into `PyAny`. -/
class PyToValue (α : Type) where
  toValue : α → PyAny

export PyToValue (toValue)

instance : PyToValue PyAny where toValue := id
instance : PyToValue Int     where toValue := .int
instance : PyToValue Nat     where toValue n := .int n
instance : PyToValue Bool    where toValue := .bool
instance : PyToValue String  where toValue := .str
instance : PyToValue Char    where toValue c := .str (String.singleton c)
instance : PyToValue Rat     where toValue := .float
-- `Float` is the run-twin's `float`; box it via its exact rational value so a dynamic (`PyAny`) slot
-- can hold a `Float` (`PyAny.float` carries a `Rat`). This is the one tower type that could not
-- previously enter `PyAny`, so `x + f` / a boxed return of `pyFloat …` (approx-mode division) failed.
instance : PyToValue Float   where toValue f := .float f.toRat0
instance : PyToValue Unit    where toValue _ := .none
instance {α : Type} [PyToValue α] : PyToValue (List α)   where toValue xs := .list (xs.map toValue)
instance {α : Type} [PyToValue α] : PyToValue (Option α) where
  toValue | some x => toValue x | none => .none

/-- Automatic boxing at a boundary: a branch of a known type coerces to `PyAny`, so the two arms
of `if c then 1 else "neg"` unify at `PyAny` with no explicit wrapper. Concrete source types only —
a generic `CoeTail α PyAny` has no synthesization order (the source `α` is unconstrained). -/
instance : CoeTail Int PyAny    where coe := .int
instance : CoeTail Nat PyAny    where coe n := .int n
instance : CoeTail Bool PyAny   where coe := .bool
instance : CoeTail Float PyAny  where coe f := .float f.toRat0
instance : CoeTail String PyAny where coe := .str
instance : CoeTail Char PyAny   where coe c := .str (String.singleton c)
instance : CoeTail Rat PyAny    where coe := .float
instance : CoeTail (List PyAny) PyAny where coe := .list
instance : CoeTail (List Int) PyAny     where coe xs := .list (xs.map .int)
instance : CoeTail (List String) PyAny  where coe xs := .list (xs.map .str)

-- Element-wise boxing INTO a dynamic list (`List α → List PyAny`, not `→ PyAny`): lets a `List PyAny`
-- slot accept a concrete list — the Option-A case where a var reassigned at conflicting element types
-- is typed `List PyAny`, so `l = list(str(x))` (List String) and `l = list(map(int, l))` (List Int)
-- coerce here. Enumerated by element type for the same reason as the scalar coes above (a generic
-- `CoeTail (List α) (List PyAny)` has no synthesization order).
instance : CoeTail (List Int) (List PyAny)    where coe xs := xs.map .int
instance : CoeTail (List Nat) (List PyAny)    where coe xs := xs.map (.int ·)
-- Int/Nat element list widening into a rational/float list (numeric tower `int ⊂ ℚ`/`Float`): a
-- function mixing `list[int]` and `list[float]` returns ascribes the codomain to `List ℚ`/`List Float`,
-- and the `list[int]` returns coerce here (Tri: `return [1]` into a `List ℚ` codomain).
instance : CoeTail (List Int) (List Rat)   where coe xs := xs.map (· : Int → Rat)
instance : CoeTail (List Nat) (List Rat)   where coe xs := xs.map (· : Nat → Rat)
instance : CoeTail (List Int) (List Float) where coe xs := xs.map Float.ofInt
instance : CoeTail (List Nat) (List Float) where coe xs := xs.map Float.ofNat
instance : CoeTail (List String) (List PyAny) where coe xs := xs.map .str
instance : CoeTail (List Bool) (List PyAny)   where coe xs := xs.map .bool
instance : CoeTail (List Float) (List PyAny)  where coe xs := xs.map (.float ·.toRat0)
instance : CoeTail (List Rat) (List PyAny)    where coe xs := xs.map .float

-- Numerals are polymorphic via `OfNat`, not coercion, so a bare `0`/`5` in a boxed position needs
-- these (codegen usually emits typed literals like `(0 : Int)`, which coerce, but not always).
instance (n : Nat) : OfNat PyAny n where ofNat := .int n
instance : Neg PyAny where neg | .int n => .int (-n) | .float q => .float (-q) | v => v

/-! ### Dynamic arithmetic — dispatch on the runtime tag

This is what makes a boxed polymorphic function like `def add(a, b): return a + b` run at *both* `int`
and `str`: `a +ₚ b` is one definition that inspects the constructors at runtime. Same-type operands
combine as Python does (`int+int`, `str++str`, `list++list`); numeric operands promote to `float`;
`bool` counts as `0`/`1`. A genuine mismatch (`1 + "a"`) yields `none` rather than raising — a soft
failure that keeps the operation total. -/

namespace PyAny

def asNum : PyAny → Option (Sum Int Rat)
  | .int n => some (.inl n)
  | .bool b => some (.inl (if b then 1 else 0))
  | .float q => some (.inr q)
  | _ => .none

/-- Apply integer/rational ops to two numeric boxes, promoting to `float` if either is a float. -/
def numBinop (fi : Int → Int → Int) (fq : Rat → Rat → Rat) (a b : PyAny) : Option PyAny :=
  match asNum a, asNum b with
  | some (.inl x), some (.inl y) => some (.int (fi x y))
  | some x, some y =>
      let toRat : Sum Int Rat → Rat := fun | .inl n => (n : Rat) | .inr q => q
      some (.float (fq (toRat x) (toRat y)))
  | _, _ => .none

def add : PyAny → PyAny → PyAny
  | .str a, .str b => .str (a ++ b)
  | .list a, .list b => .list (a ++ b)
  | a, b => (numBinop (· + ·) (· + ·) a b).getD .none

def sub (a b : PyAny) : PyAny := (numBinop (· - ·) (· - ·) a b).getD .none
def mul : PyAny → PyAny → PyAny
  | .str a, .int n => .str (String.join (List.replicate n.toNat a))
  | .int n, .str a => .str (String.join (List.replicate n.toNat a))
  | a, b => (numBinop (· * ·) (· * ·) a b).getD .none

private def toRat : Sum Int Rat → Rat := fun | .inl n => (n : Rat) | .inr q => q

/-- Python `/` is always true division → `float`. -/
def div (a b : PyAny) : PyAny :=
  match asNum a, asNum b with
  | some x, some y => let d := toRat y; if d == 0 then .none else .float (toRat x / d)
  | _, _ => .none

/-- Python `//`: `int//int` stays `int` (floored), else a floored `float`. -/
def floordiv (a b : PyAny) : PyAny :=
  match asNum a, asNum b with
  | some (.inl x), some (.inl y) => if y == 0 then .none else .int (pyFloorDiv x y)
  | some x, some y => let d := toRat y; if d == 0 then .none else .float ((Rat.floor (toRat x / d) : Int) : Rat)
  | _, _ => .none

/-- Python `%`: `int%int` stays `int`, else float modulo `a - b*⌊a/b⌋`. -/
def mod (a b : PyAny) : PyAny :=
  match asNum a, asNum b with
  | some (.inl x), some (.inl y) => if y == 0 then .none else .int (pyMod x y)
  | some x, some y =>
      let xr := toRat x; let yr := toRat y
      if yr == 0 then .none else .float (xr - yr * ((Rat.floor (xr / yr) : Int) : Rat))
  | _, _ => .none

/-- Python `**`: `int**(≥0)` stays `int`; an integer exponent otherwise gives a `float`; a fractional
exponent is transcendental (soft-`none`). -/
def pow (a b : PyAny) : PyAny :=
  match asNum a, asNum b with
  | some (.inl x), some (.inl y) => if y ≥ 0 then .int (x ^ y.toNat) else .float ((toRat (.inl x)) ^ y)
  | some x, some (.inl y) => .float ((toRat x) ^ y)
  -- FRACTIONAL exponent (`4 ** 0.5`): a Rat base to a Rat power is generally irrational, so compute it
  -- as a `Float` (like Python) and box the result — `int(4 ** 0.5)` = 2 only if `2.0` comes back
  -- exact, so this must go through `Float.pow` (correctly rounded), not a stuck `.none`.
  | some x, some (.inr q) => .float (floatToRat (Float.pow (Rat.toFloat (toRat x)) (Rat.toFloat q)))
  | _, _ => .none

/-- The integer value of a boxed `int`/`bool`, for the integer-only bitwise/shift operators. -/
def asInt : PyAny → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

def bitOp (f : Int → Int → Int) (a b : PyAny) : PyAny :=
  match asInt a, asInt b with | some x, some y => .int (f x y) | _, _ => .none
def shl (a b : PyAny) : PyAny := match asInt a, asInt b with | some x, some y => .int (pyShiftLeft x y) | _, _ => .none
def shr (a b : PyAny) : PyAny := match asInt a, asInt b with | some x, some y => .int (pyShiftRight x y) | _, _ => .none

/-- Numeric/string comparison, `none` when the operands are incomparable (as Python raises). -/
def cmp (a b : PyAny) : Option Ordering :=
  match a, b with
  | .str x, .str y => some (compare x y)
  | .list x, .list y => some (compare (x.map (·.toStr false)) (y.map (·.toStr false)))
  | _, _ => match asNum a, asNum b with
      | some x, some y => some (compare (toRat x) (toRat y))
      | _, _ => Option.none

def blt (a b : PyAny) : Bool := a.cmp b == some .lt
def ble (a b : PyAny) : Bool := a.cmp b == some .lt || a.cmp b == some .eq

/-- Python `==`: numeric across the tower (`5 == 5.0`), else structural (`5 == "5"` is `False`). -/
partial def beq (a b : PyAny) : Bool :=
  match asNum a, asNum b with
  | some x, some y => toRat x == toRat y
  | _, _ => match a, b with
      | .str x, .str y => x == y
      | .none, .none => true
      | .list x, .list y => x.length == y.length && (x.zip y).all fun (p, q) => beq p q
      | _, _ => false

end PyAny

instance : PyHAdd PyAny PyAny PyAny where hAdd := PyAny.add
instance : PyHSub PyAny PyAny PyAny where hSub := PyAny.sub
instance : PyHMul PyAny PyAny PyAny where hMul := PyAny.mul

/-- Mixed `PyAny op scalar` / `scalar op PyAny`: box the scalar and dispatch on the tags, so
arithmetic on an un-inferred (boxed) value against an `Int`/`ℚ` literal works (`x * 2` where `x` is a
`PyAny` element of an untyped param). Low priority so the exact `PyAny × PyAny` instances win. -/
instance (priority := low) {α} [PyToValue α] : PyHAdd PyAny α PyAny where hAdd a b := PyAny.add a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyHAdd α PyAny PyAny where hAdd a b := PyAny.add (PyToValue.toValue a) b
instance (priority := low) {α} [PyToValue α] : PyHSub PyAny α PyAny where hSub a b := PyAny.sub a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyHSub α PyAny PyAny where hSub a b := PyAny.sub (PyToValue.toValue a) b
instance (priority := low) {α} [PyToValue α] : PyHMul PyAny α PyAny where hMul a b := PyAny.mul a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyHMul α PyAny PyAny where hMul a b := PyAny.mul (PyToValue.toValue a) b

instance : PyHDiv PyAny PyAny PyAny where hDiv := PyAny.div
instance : PyModulo PyAny PyAny PyAny where hMod := PyAny.mod
instance : PyHPow PyAny PyAny PyAny where hPow := PyAny.pow
instance (priority := low) {α} [PyToValue α] : PyHDiv PyAny α PyAny where hDiv a b := PyAny.div a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyHDiv α PyAny PyAny where hDiv a b := PyAny.div (PyToValue.toValue a) b
instance (priority := low) {α} [PyToValue α] : PyModulo PyAny α PyAny where hMod a b := PyAny.mod a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyModulo α PyAny PyAny where hMod a b := PyAny.mod (PyToValue.toValue a) b
instance (priority := low) {α} [PyToValue α] : PyHPow PyAny α PyAny where hPow a b := PyAny.pow a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyHPow α PyAny PyAny where hPow a b := PyAny.pow (PyToValue.toValue a) b

/-- `==` on `PyAny` is numeric across the tower (`5 == 5.0`), replacing the structural derived `BEq`. -/
instance : BEq PyAny := ⟨PyAny.beq⟩

instance : LT PyAny := ⟨fun a b => PyAny.blt a b = true⟩
instance : LE PyAny := ⟨fun a b => PyAny.ble a b = true⟩
instance (a b : PyAny) : Decidable (a < b) := inferInstanceAs (Decidable (PyAny.blt a b = true))
instance (a b : PyAny) : Decidable (a ≤ b) := inferInstanceAs (Decidable (PyAny.ble a b = true))

instance : PyFloorDiv PyAny PyAny PyAny where floorDiv := PyAny.floordiv
instance : PyBitAnd PyAny PyAny PyAny where bitAnd := PyAny.bitOp (fun x y => pyBitAnd x y)
instance : PyBitOr PyAny PyAny PyAny where bitOr := PyAny.bitOp (fun x y => pyBitOr x y)
instance : PyBitXor PyAny PyAny PyAny where bitXor := PyAny.bitOp (fun x y => pyBitXor x y)
instance : PyShiftLeft PyAny PyAny PyAny where shiftLeft := PyAny.shl
instance : PyShiftRight PyAny PyAny PyAny where shiftRight := PyAny.shr
instance (priority := low) {α} [PyToValue α] : PyFloorDiv PyAny α PyAny where floorDiv a b := PyAny.floordiv a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyFloorDiv α PyAny PyAny where floorDiv a b := PyAny.floordiv (PyToValue.toValue a) b
instance (priority := low) {α} [PyToValue α] : PyBitAnd PyAny α PyAny where bitAnd a b := PyAny.bitOp (fun x y => pyBitAnd x y) a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyBitAnd α PyAny PyAny where bitAnd a b := PyAny.bitOp (fun x y => pyBitAnd x y) (PyToValue.toValue a) b
instance (priority := low) {α} [PyToValue α] : PyBitOr PyAny α PyAny where bitOr a b := PyAny.bitOp (fun x y => pyBitOr x y) a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyBitOr α PyAny PyAny where bitOr a b := PyAny.bitOp (fun x y => pyBitOr x y) (PyToValue.toValue a) b
instance (priority := low) {α} [PyToValue α] : PyBitXor PyAny α PyAny where bitXor a b := PyAny.bitOp (fun x y => pyBitXor x y) a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyBitXor α PyAny PyAny where bitXor a b := PyAny.bitOp (fun x y => pyBitXor x y) (PyToValue.toValue a) b
instance (priority := low) {α} [PyToValue α] : PyShiftLeft PyAny α PyAny where shiftLeft a b := PyAny.shl a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyShiftLeft α PyAny PyAny where shiftLeft a b := PyAny.shl (PyToValue.toValue a) b
instance (priority := low) {α} [PyToValue α] : PyShiftRight PyAny α PyAny where shiftRight a b := PyAny.shr a (PyToValue.toValue b)
instance (priority := low) {α} [PyToValue α] : PyShiftRight α PyAny PyAny where shiftRight a b := PyAny.shr (PyToValue.toValue a) b

/-- `float(x)` / the `/`-in-run-twin cast on a boxed value: read its numeric tag as a `Float`. -/
instance : PyFloatCast PyAny where
  pyFloat v := match PyAny.asNum v with
    | some (.inl n) => Float.ofInt n
    | some (.inr q) => q.toFloat
    | Option.none => 0.0

/-! ### Container protocols — delegate to the boxed value's own instance

A boxed slot that is indexed, iterated, or `len`-ed dispatches on the runtime tag and reuses the
concrete `List`/`String` instance (no reimplementation); the element is reboxed as `PyAny`. This
is why an un-inferred parameter can still be subscripted (`x[i]`, `x[i]=v`), looped, or measured. -/

instance : PyGetItem PyAny Int PyAny where
  getItem v i :=
    match v with
    | .list xs => pyListGetItem xs i
    | .str s => .str (pyStringGetItemStr s i)
    | _ => .none

/-- A *typed* list indexed by a *boxed* index (`xs[k]` where `k` is dynamic, e.g. a loop variable
that stayed `PyAny`) — unbox an integer index and delegate to the list instance. -/
instance {α : Type} [Inhabited α] : PyGetItem (List α) PyAny α where
  getItem xs i := match i with | .int n => pyListGetItem xs n | _ => default

/-- A boxed value indexed by a *boxed* index (`x[k]` where `k` is also dynamic) — unbox an integer
index and delegate; any other index yields `None`. -/
instance : PyGetItem PyAny PyAny PyAny where
  getItem v i :=
    match i with
    | .int n => match v with
        | .list xs => pyListGetItem xs n
        | .str s => .str (pyStringGetItemStr s n)
        | _ => .none
    | _ => .none

/-- `s[k]` on a concrete `String` indexed by a *boxed* index (`k` is a dynamic value that stayed
`PyAny`, e.g. an un-inferred loop variable) — unbox an integer index and delegate to the string
instance; any other index yields the empty string. -/
instance : PyGetItem String PyAny String where
  getItem s i := match i with | .int n => pyStringGetItemStr s n | _ => ""

instance : PySetItem PyAny Int PyAny where
  setItem v i x :=
    match v with
    | .list xs => .list (pySetItem xs i x)
    | _ => v

instance : PyLen PyAny where
  pyLen
    | .list xs => xs.length
    | .str s => s.length
    | _ => 0

instance : PyIterable PyAny PyAny where
  toPyList
    | .list xs => xs
    | .str s => s.toList.map (fun c => .str c.toString)
    | _ => []

instance : PyPrintable PyAny where
  pyStringify := PyAny.toStr false
  pyReprify := PyAny.toStr true
/-- `"".join(xs)` where `xs`'s elements are boxed (an un-inferred `str`/`list[str]` param filtered to
`List PyAny`): a boxed `str` joins as itself, anything else stringifies (Python would `TypeError`, but
the faithful case only ever holds boxed `str`s). -/
instance : PyStringJoin PyAny where
  toJoinString | .str s => s | v => PyAny.toStr false v
/-- A `PyAny` is `None` exactly when it carries the `none` tag. -/
instance : PyIsNone PyAny where isNoneVal | .none => true | _ => false
instance : PyTruthy PyAny where
  truthy
    | .int n => n != 0
    | .bool b => b
    | .str s => !s.isEmpty
    | .float q => q != 0
    | .none => false
    | .list xs => !xs.isEmpty

/-- Total ordering for `sorted`/`min`/`max`/`Ord`-keyed containers over boxed values. Reuses the
numeric/string/list comparison in `PyAny.cmp`; incomparable tags compare equal (a stable no-op). -/
instance : Ord PyAny := ⟨fun a b => (a.cmp b).getD .eq⟩

/-- Python `abs` on a boxed number; non-numbers pass through. -/
instance : PyAbs PyAny where
  pyAbs
    | .int n => .int (if n < 0 then -n else n)
    | .float q => .float (if q < 0 then -q else q)
    | v => v

/-- Hash a boxed value by tag + payload, so a `PyAny` can key a dict / enter a set. -/
partial def PyAny.pyHash : PyAny → UInt64
  | .int n => mixHash 3 (hash n)
  | .bool b => mixHash 5 (hash b)
  | .str s => mixHash 7 (hash s)
  | .float q => mixHash 11 (mixHash (hash q.num) (hash q.den))
  | .none => 13
  | .list xs => xs.foldl (fun h x => mixHash h x.pyHash) 17
instance : Hashable PyAny := ⟨PyAny.pyHash⟩

/-- `sep.join(xs)` where each boxed item stringifies (Python str-joins any iterable of str-likes). -/
instance : PyStringJoin PyAny where toJoinString := PyAny.toStr false

/-- `float('inf')`/`float('nan')` in a boxed slot becomes a boxed float. -/
instance : PyNonFinite PyAny where nonFinite s := .float (PyNonFinite.nonFinite s)

/-! ### More container/value protocols on a boxed value — same delegate-by-tag design as above.
These let an un-inferred (`PyAny`) parameter be `int()`-cast, membership-tested, `count`-ed, sliced,
sorted, and summed, reusing the concrete `List`/`String` runtime and reboxing results. -/

/-- `int(x)` on a boxed value: numeric tags read directly (float truncates toward zero, matching
Python `int()`); a numeric string parses; everything else is `0`. -/
instance : PyIntCast PyAny where
  pyInt
    | .int n => n
    | .bool b => if b then 1 else 0
    | .float q => q.num.tdiv (q.den : Int)
    | .str s => (s.trimAscii.toInt?).getD 0
    | _ => 0

/-- `needle in x` on a boxed container: list membership (element equality) or substring test.
`β` is an `outParam`, so a concrete needle (e.g. `ℤ`) coerces to `PyAny` via `CoeTail`; only this
single `PyAny PyAny` instance may exist for the boxed container (extra ones break resolution). -/
instance : PyContains PyAny PyAny where
  contains
    | .list xs, v => xs.contains v
    | .str s, .str t => pyStrContainsSubstr s t
    | _, _ => false

/-- `x.count(v)` on a boxed list (occurrence count) or string (substring count). -/
instance : PyCount PyAny PyAny where
  pyCount
    | .list xs, v => pyListCount xs v
    | .str s, .str t => pyStringCount s t
    | _, _ => 0
instance : PyCount PyAny Int where
  pyCount
    | .list xs, x => pyListCount xs (PyAny.int x)
    | _, _ => 0
instance : PyCount PyAny String where
  pyCount
    | .list xs, x => pyListCount xs (PyAny.str x)
    | .str s, t => pyStringCount s t
    | _, _ => 0

/-- `sum(x)` over a boxed iterable: each element is already a `PyAny`, folded with boxed `+`. -/
instance : PySummand PyAny PyAny := ⟨id⟩

/-- `x[lo:hi:step]` on a boxed list/string; other tags pass through unchanged. -/
instance : PySlice PyAny where
  slice v lo hi step := match v with
    | .list xs => .list (pyListSliceStep xs lo hi step)
    | .str s => .str (pyStringSliceStep s lo hi step)
    | _ => v

/-- `sorted(x)` on a boxed list (or string → sorted chars); reuses `Ord PyAny`. -/
instance : PySort PyAny PyAny where
  pySort
    | .list xs => PySort.pySort xs
    | .str s => PySort.pySort (s.toList.map (fun c => PyAny.str c.toString))
    | _ => []

/-- Decode a JSON value into `PyAny`, PRESERVING Python's int-vs-float distinction (a JSON number with
no fractional part is `.int`, otherwise `.float`). Used by the test harness to feed a `PyAny`-typed
parameter (e.g. `any_int`, which does `type(x) == int`) without collapsing every number to `Float`. -/
partial def PyAny.ofJson? : Lean.Json → Except String PyAny
  | .null   => .ok .none
  | .bool b => .ok (.bool b)
  | .str s  => .ok (.str s)
  | .num n  => .ok (if n.exponent == 0 then .int n.mantissa
                    else .float ((n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat)))
  | .arr xs => do let l ← xs.toList.mapM PyAny.ofJson?; .ok (.list l)
  | .obj _  => .error "PyAny.ofJson?: JSON objects (dict) are not supported"

instance : Lean.FromJson PyAny := ⟨PyAny.ofJson?⟩

end PastaLean
