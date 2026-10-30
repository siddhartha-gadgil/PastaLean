import Plausible
import PastaLean.PyVerify.Refute.PyLit

/-!
# Generators for Python-visible values

`PyArb α` is how the search draws and shrinks a value of a binder's type. It reuses Plausible's `Gen`
(size-indexed randomness) and keeps its own instances, because the values must be *Python* values:
ASCII strings, dyadic floats, and the same draw for `ℚ` (provable twin) and `Float` (runnable twin).
-/

namespace PastaLean.Refute

open Plausible

class PyArb (α : Type) extends ToPyLit α where
  arb : Gen α
  shrink : α → List α := fun _ => []
  /-- Values up to depth `d` (SmallCheck-style), smallest first, at most `lim` of them; `[]` when not
  enumerable. The cap matters: products grow exponentially and lists are strict. -/
  enum : Nat → Nat → List α := fun _ _ => []

/-- Exponent bound for dyadic floats `k / 2^e`; small, so values stay readable and exact. -/
def floatExpMax : Nat := 4

def genInt : Gen Int := do
  let s ← Gen.getSize
  let pick ← Gen.choose Nat 0 9 (by omega)
  match pick.val with
  | 0 => pure 0
  | 1 => pure 1
  | 2 => pure (-1)
  | 3 => do
      -- Powers of two stay within reach of the size: a huge one sent to a counting loop never returns.
      let k ← Gen.choose Nat 1 (min 62 (2 * s + 2)) (by omega)
      let sgn ← Gen.chooseAny Bool
      pure (if sgn then (2 : Int) ^ k.val else -((2 : Int) ^ k.val))
  | _ => do
      let v ← Gen.choose Int (-(s : Int)) (s : Int) (by omega)
      pure v.val

def shrinkInt (n : Int) : List Int :=
  if n == 0 then [] else
  let s := n.sign
  ([0, s, 2 * s, n / 4, n / 2, n - s, n - 2 * s, n - 3 * s] ++ (if n < 0 then [-n] else [])).eraseDups.filter
    (fun m => m.natAbs < n.natAbs || (m == -n && n < 0))

/-- A dyadic `k / 2^e`: the one draw both float carriers share. -/
def genDyadic : Gen (Int × Nat) := do
  let s ← Gen.getSize
  let e ← Gen.choose Nat 0 floatExpMax (by omega)
  let bound : Nat := s * 2 ^ e.val + 1
  let k ← Gen.choose Int (-(bound : Int)) (bound : Int) (by omega)
  pure (normDyadic k.val e.val)

def shrinkDyadic : Int × Nat → List (Int × Nat)
  | (k, e) =>
    let toward := if e > 0 then [normDyadic (k / 2) (e - 1), (k / 2 ^ e, 0)] else (shrinkInt k).map (·, 0)
    (if k == 0 then [] else (0, 0) :: toward).eraseDups.filter (· != (k, e))

def ratOfDyadic : Int × Nat → Rat
  | (k, e) => mkRat k (2 ^ e)

def dyadicOfRat? (q : Rat) : Option (Int × Nat) :=
  if q.den.isPowerOfTwo then some (normDyadic q.num (Nat.log2 q.den)) else none

instance : ToPyLit Int := ⟨.int⟩
/-- Pairs from `as` and `bs`, diagonal by index sum (small with small first), at most `lim`. -/
def diagonal (as : List α) (bs : List β) (lim : Nat) : List (α × β) := Id.run do
  let aa := as.toArray
  let bb := bs.toArray
  let mut out : Array (α × β) := #[]
  for s in [0:aa.size + bb.size] do
    if out.size ≥ lim then break
    for i in [0:s + 1] do
      if out.size ≥ lim then break
      if h₁ : i < aa.size then
        if h₂ : s - i < bb.size then
          out := out.push (aa[i], bb[s - i])
  return out.toList

/-- Tuples of length `n` over `es`, diagonal-ordered, at most `lim`. -/
def tuplesOf (es : List α) : Nat → Nat → List (List α)
  | 0, _ => [[]]
  | n + 1, lim => (diagonal es (tuplesOf es n lim) lim).map fun (e, rest) => e :: rest

/-- `0, 1, -1, 2, -2, …, d, -d`. -/
def enumInt (d : Nat) : List Int :=
  0 :: (List.range d).flatMap fun i => [((i + 1 : Nat) : Int), -((i + 1 : Nat) : Int)]

instance : PyArb Int where
  arb := genInt
  shrink := shrinkInt
  enum d lim := (enumInt d).take lim

instance : ToPyLit Nat := ⟨fun n => .int n⟩
instance : PyArb Nat where
  arb := do pure (← genInt).natAbs
  shrink n := (shrinkInt n).filterMap fun m => if m ≥ 0 then some m.toNat else none
  enum d lim := (List.range (d + 1)).take lim

instance : ToPyLit Bool := ⟨.bool⟩
instance : PyArb Bool where
  arb := Gen.chooseAny Bool
  shrink b := if b then [false] else []
  enum _ lim := [false, true].take lim

instance : ToPyLit Unit := ⟨fun _ => .none⟩
instance : PyArb Unit where
  arb := pure ()
  enum _ _ := [()]

/-- Characters a generated string is drawn from: a small biased alphabet that collides often (so
`==`, `in` and dedup logic get exercised), widened to all of printable ASCII. -/
def strAlphabet : List Char := ['a', 'b', 'a', 'b', 'c', '0', '1', ' ']

def genChar : Gen Char := do
  let wide ← Gen.choose Nat 0 4 (by omega)
  if wide.val == 0 then
    let c ← Gen.choose Nat 32 126 (by omega)
    pure (Char.ofNat c.val)
  else
    let i ← Gen.choose Nat 0 (strAlphabet.length - 1) (by decide)
    pure (strAlphabet.getD i.val 'a')

instance : ToPyLit String := ⟨.str⟩
instance : PyArb String where
  arb := do
    let s ← Gen.getSize
    let n ← Gen.choose Nat 0 (s / 2) (by omega)
    let cs ← (List.range n.val).mapM fun _ => genChar
    pure (String.ofList cs)
  shrink s :=
    if s.isEmpty then [] else
    let cs := s.toList
    ["", String.ofList (cs.take (cs.length / 2)), String.ofList cs.tail, String.ofList cs.dropLast].eraseDups.filter (· != s)
  -- Words over a two-letter alphabet (plus a space) up to length `d / 2`: enough to make strings equal,
  -- differ, repeat and contain each other.
  enum d lim := ((List.range (d / 2 + 1)).flatMap fun n =>
    (tuplesOf ['a', 'b', ' '] n lim).map String.ofList).take lim

instance : ToPyLit Rat where
  toLit q := match dyadicOfRat? q with
    | some (k, e) => .float k e
    | Option.none => .rat q.num q.den
/-- Integers and halves up to `d` in magnitude: the small dyadics. -/
def enumDyadic (d : Nat) : List (Int × Nat) :=
  (enumInt d).map (·, 0) ++ ((enumInt (2 * d)).filter (· % 2 != 0)).map (·, 1)

instance : PyArb Rat where
  arb := do pure (ratOfDyadic (← genDyadic))
  shrink q := match dyadicOfRat? q with
    | some d => (shrinkDyadic d).map ratOfDyadic
    | Option.none => []
  enum d lim := ((enumDyadic d).map ratOfDyadic).take lim

/-- The exact dyadic value of a finite double: `f = m·2^e` with `|m| ∈ [½, 1)`, so `m·2^53` is an integer. -/
def dyadicOfFloat? (f : Float) : Option (Int × Nat) :=
  if !f.isFinite then none else
  -- `-0.0` is not a dyadic rational; it travels as raw bits so its sign survives.
  if f == 0 then (if f.toBits >>> 63 == 1 then none else some (0, 0)) else
  let (m, e) := f.frExp
  let k : Int := (m * (2 : Float) ^ (53 : Float)).toInt64.toInt
  let sh : Int := e - 53
  if sh ≥ 0 then some (k * 2 ^ sh.toNat, 0) else some (normDyadic k (-sh).toNat)

instance : ToPyLit Float where
  toLit f := match dyadicOfFloat? f with
    | some (k, e) => .float k e
    | Option.none => .double f.toBits
def floatOfDyadic : Int × Nat → Float
  | (k, e) => Float.ofInt k / (2 ^ e : Nat).toFloat

instance : PyArb Float where
  arb := do pure (floatOfDyadic (← genDyadic))
  enum d lim := ((enumDyadic d).map floatOfDyadic).take lim

instance [ToPyLit α] : ToPyLit (List α) := ⟨fun xs => .list (xs.map ToPyLit.toLit)⟩
instance [PyArb α] : PyArb (List α) where
  arb := do
    let s ← Gen.getSize
    let n ← Gen.choose Nat 0 (s / 3 + 1) (by omega)
    (List.range n.val).mapM fun _ => Gen.resize (fun s => s * 2 / 3) PyArb.arb
  shrink xs :=
    if xs.isEmpty then [] else
    let n := xs.length
    let drops := (List.range n).map fun i => xs.eraseIdx i
    let halves := [xs.take (n / 2), xs.drop (n / 2)]
    let elems := xs.zipIdx.flatMap fun (x, i) => (PyArb.shrink x).map fun y => xs.set i y
    [[]] ++ halves ++ drops ++ elems
  -- Lists of length ≤ d whose elements have depth d - 1.
  enum d lim :=
    let elems := PyArb.enum (d - 1) lim
    ((List.range (d + 1)).flatMap fun n => tuplesOf elems n lim).take lim

instance [ToPyLit α] : ToPyLit (Array α) := ⟨fun xs => .list (xs.toList.map ToPyLit.toLit)⟩
instance [PyArb α] : PyArb (Array α) where
  arb := do pure (← (PyArb.arb : Gen (List α))).toArray
  shrink xs := (PyArb.shrink xs.toList).map List.toArray
  enum d lim := (PyArb.enum d lim : List (List α)).map List.toArray

instance [ToPyLit α] : ToPyLit (Option α) := ⟨fun | some a => ToPyLit.toLit a | Option.none => .none⟩
instance [PyArb α] : PyArb (Option α) where
  arb := do
    let k ← Gen.choose Nat 0 3 (by omega)
    if k.val == 0 then pure Option.none else pure (some (← PyArb.arb))
  shrink
    | some a => Option.none :: (PyArb.shrink a).map some
    | Option.none => []
  enum d lim := (Option.none :: (PyArb.enum d lim).map some).take lim

/-- Python tuples. A binder tuple is terminated by `Unit`, so `α × Unit` reads back as one value. -/
partial def tupleItems : PyLit → List PyLit
  | .tuple xs => xs
  | x => [x]

instance [ToPyLit α] [ToPyLit β] : ToPyLit (α × β) where
  toLit p := .tuple (ToPyLit.toLit p.1 :: tupleItems (ToPyLit.toLit p.2))
instance [PyArb α] [PyArb β] : PyArb (α × β) where
  arb := do pure ((← PyArb.arb), (← PyArb.arb))
  shrink p := (PyArb.shrink p.1).map (·, p.2) ++ (PyArb.shrink p.2).map (p.1, ·)
  enum d lim := diagonal (PyArb.enum d lim) (PyArb.enum d lim) lim

end PastaLean.Refute
