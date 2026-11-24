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

/-- The two operands of one comparison the program evaluated (`s[k] == "-"`, `n == 8314`): usually one
comes from the input and the other is what it must become to flip the branch. -/
inductive CmpPair where
  | str (a b : String)
  | int (a b : Int)
  deriving BEq, Hashable, Inhabited, Repr

class PyArb (α : Type) extends ToPyLit α where
  arb : Gen α
  shrink : α → List α := fun _ => []
  /-- Values up to depth `d` (SmallCheck-style), smallest first, at most `lim` of them; `[]` when not
  enumerable. The cap matters: products grow exponentially and lists are strict. -/
  enum : Nat → Nat → List α := fun _ _ => []
  /-- The program's literals of this type (read at draw time): a dict draws its keys from them. -/
  fromPool : Unit → List α := fun _ => []
  /-- A small change to a value, for the coverage-guided search (a fresh draw by default). -/
  mutate : α → Gen α := fun _ => arb
  /-- Parts of two values in one (crossover): inputs that each reached a different goal, combined
  (`"111"` and `"x.txt"` → `"x111.txt"`). The first value by default. -/
  crossover : α → α → Gen α := fun a _ => pure a
  /-- A move toward a goal `d` away (branch distance): steps scaled to `d`, so climbing `|n² − 1764|`
  takes a few dozen moves rather than a random walk. A mutation by default. -/
  climb : α → Nat → Gen α := fun x _ => mutate x
  /-- Input-to-state (as in RedQueen): where the value holds one operand of a comparison that steers a
  branch, put the other (`"0e0"` compared at `s[2] == "-"` → `"0e-0"`). A mutation by default. -/
  splice : α → CmpPair → Gen α := fun x _ => mutate x

/-- `PyArb.arb` / `PyArb.mutate` for the fields of a generated class instance: not inlined, or compiling
a class of ten `Option (List C)` fields takes ~25 s. -/
@[noinline] def PyArb.arbField {α : Type} [PyArb α] : Gen α := PyArb.arb
@[noinline] def PyArb.mutateField {α : Type} [PyArb α] (a : α) : Gen α := PyArb.mutate a

/-- Literals of the program under test (strings, integers), set before each search: generated values
aim at them, as a fuzzer's dictionary does (`"sx250ab" in s` needs that substring). -/
initialize literalPool : IO.Ref (Array String × Array Int) ← IO.mkRef (#[], #[])

@[never_extract, noinline]
unsafe def poolImpl (_ : Unit) : Array String × Array Int := unsafeBaseIO literalPool.get

/-- The current literal pool (read at draw time, never cached). -/
@[never_extract, implemented_by poolImpl]
opaque pool : Unit → Array String × Array Int

/-- Magnitude bound on generated integers (`0`: none), set per search from `RefuteConfig.intCap`: the
retry after a draw like `n = 10**9 + 7` made `[0] * n` exhaust memory. -/
initialize intCapRef : IO.Ref Nat ← IO.mkRef 0

@[never_extract, noinline]
unsafe def intCapImpl (_ : Unit) : Nat := unsafeBaseIO intCapRef.get

@[never_extract, implemented_by intCapImpl]
opaque intCap : Unit → Nat

/-- `n` within the integer cap, if there is one. -/
def capInt (n : Int) : Int :=
  match intCap () with
  | 0 => n
  | c => max (-(c : Int)) (min c n)

/-- Operands the instrumented program compared against during this search (`x == 8314`,
`s == "age"`). Kept apart from `literalPool`: deep instrumentation (a library's parser) logs many, and
they would crowd the program's own literals out of fresh draws; mutation splices them in. -/
initialize cmpPool : IO.Ref (Array String × Array Int) ← IO.mkRef (#[], #[])

@[never_extract, noinline]
unsafe def cmpsImpl (_ : Unit) : Array String × Array Int := unsafeBaseIO cmpPool.get

@[never_extract, implemented_by cmpsImpl]
opaque cmps : Unit → Array String × Array Int

/-- Library constructor calls of the program with integer-literal arguments, by class
(`date(2022, 10, 6)` ↦ ``(`Libraries.datetime.date, #[2022, 10, 6])``): a library's generator derives
values related to them (a `timedelta` between two mined dates). -/
initialize ctorPool : IO.Ref (Array (Lean.Name × Array Int)) ← IO.mkRef #[]

/-- Exponent bound for dyadic floats `k / 2^e`; small, so values stay readable and exact. -/
def floatExpMax : Nat := 4

def genInt : Gen Int := do return capInt (← genIntRaw)
where genIntRaw : Gen Int := do
  let s ← Gen.getSize
  let ints := (pool ()).2
  if ints.size > 0 then
    if (← Gen.choose Nat 0 9 (by omega)).val == 0 then
      let i ← Gen.choose Nat 0 (ints.size - 1) (by omega)
      let d ← Gen.choose Nat 0 2 (by omega)
      return ints.getD i.val 0 + (d.val : Int) - 1
  let pick ← Gen.choose Nat 0 9 (by omega)
  match pick.val with
  | 0 => pure 0
  | 1 => pure 1
  | 2 => pure (-1)
  | 3 => do
      -- Powers of two stay within reach of the size: a huge one sent to a counting loop never returns.
      let k ← Gen.choose Nat 1 (min 62 (s / 2 + 2)) (by omega)
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

/-- An element of a non-empty list, uniformly. -/
def pickFrom {α : Type} [Inhabited α] (xs : List α) : Gen α := do
  let i ← Gen.choose Nat 0 (xs.length - 1) (by omega)
  return xs.getD i.val default

def mutateInt (n : Int) : Gen Int := do return capInt (← mutateIntRaw n)
where mutateIntRaw (n : Int) : Gen Int := do
  let ints := if ← Gen.chooseAny Bool then (pool ()).2 else (cmps ()).2
  let ints := if ints.isEmpty then (pool ()).2 else ints
  match (← Gen.choose Nat 0 6 (by omega)).val with
  | 0 => return n + 1
  | 1 => return n - 1
  | 2 => return n + ((← Gen.choose Nat 2 16 (by omega)).val : Int) * (if ← Gen.chooseAny Bool then 1 else -1)
  | 3 =>
      if ints.isEmpty then return -n
      let i ← Gen.choose Nat 0 (ints.size - 1) (by omega)
      return ints[i.val]!
  | 4 => return n * 2
  | 5 => return n / 2
  | _ => genInt

/-- `⌊√d⌋`, by Newton's method. -/
def natSqrt (d : Nat) : Nat := Id.run do
  if d < 2 then return d
  let mut x := d
  for _ in [0:64] do
    let y := (x + d / x) / 2
    if y ≥ x then break
    x := y
  return x

/-- `n` moved by a step scaled to the distance `d` still to cover: `d`, `d / 2`, `√d`, … or 1. -/
def climbInt (n : Int) (d : Nat) : Gen Int := do
  let r := natSqrt d
  let steps := [1, d, d / 2, r, r / 2 + 1, d / 4 + 1].filter (· > 0)
  let step ← pickFrom steps
  return capInt (if ← Gen.chooseAny Bool then n + step else n - step)

/-- `n` shifted by the gap between two compared integers (exactly onto the other one when `n` is the
first), or one off it, for the strict side of `<`. -/
def spliceInt (n : Int) : CmpPair → Gen Int
  | .int a b => do
      let (a, b) := if n == b then (b, a) else (a, b)
      return capInt (n + (b - a) + (← pickFrom [0, 0, 1, -1]))
  | .str .. => mutateInt n

instance : PyArb Int where
  arb := genInt
  shrink := shrinkInt
  enum d lim := (enumInt d).take lim
  fromPool _ := (pool ()).2.toList
  mutate := mutateInt
  climb := climbInt
  splice := spliceInt

instance : ToPyLit Nat := ⟨fun n => .int n⟩
instance : PyArb Nat where
  arb := do pure (← genInt).natAbs
  shrink n := (shrinkInt n).filterMap fun m => if m ≥ 0 then some m.toNat else none
  enum d lim := (List.range (d + 1)).take lim
  mutate n := do return (← mutateInt n).toNat
  climb n d := do return (← climbInt n d).toNat
  splice n p := do return (← spliceInt n p).toNat

instance : ToPyLit Bool := ⟨.bool⟩
instance : PyArb Bool where
  arb := Gen.chooseAny Bool
  shrink b := if b then [false] else []
  mutate b := pure !b
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
/-- A length up to `s / 2`, a quarter of the time one of the program's integers (`len(v) == 3`). -/
def genLen (s : Nat) : Gen Nat := do
  let lens := (pool ()).2.filter fun n => 0 ≤ n && n ≤ 64
  if lens.size > 0 && (← Gen.choose Nat 0 3 (by omega)).val == 0 then
    return (lens.getD (← Gen.choose Nat 0 (lens.size - 1) (by omega)).val 0).toNat
  return (← Gen.choose Nat 0 (s / 2) (by omega)).val

/-- One to three character edits (insert, replace, delete), with characters from the program's short
literals and the generator's alphabet; or a mined string spliced in. -/
def mutateString (str : String) : Gen String := do
  let strs := if ← Gen.chooseAny Bool then (pool ()).1 else (cmps ()).1
  let strs := if strs.isEmpty then (pool ()).1 else strs
  if !strs.isEmpty && (← Gen.choose Nat 0 4 (by omega)).val == 0 then
    let w := strs[(← Gen.choose Nat 0 (strs.size - 1) (by omega)).val]!
    if ← Gen.chooseAny Bool then return w
    let k := (← Gen.choose Nat 0 str.length (by omega)).val
    return String.ofList (str.toList.take k ++ w.toList ++ str.toList.drop k)
  let short := strs.foldl (fun acc w => if w.length ≤ 2 then acc ++ w.toList else acc) []
  let mut cs := str.toList
  for _ in [0:(← Gen.choose Nat 1 3 (by omega)).val] do
    let c ← if !short.isEmpty && (← Gen.chooseAny Bool) then pickFrom short else genChar
    let k := (← Gen.choose Nat 0 cs.length (by omega)).val
    cs := match (← Gen.choose Nat 0 3 (by omega)).val with
      | 0 => cs.eraseIdx k
      | 1 => cs.set k c
      | _ => cs.take k ++ c :: cs.drop k
  return String.ofList cs

/-- Where `w` occurs in `cs`, by start index. -/
def occurrences (cs w : List Char) : List Nat :=
  if w.isEmpty then [] else (List.range (cs.length + 1 - w.length)).filter fun i => (cs.drop i).take w.length == w

/-- One operand of a comparison put where the other occurs in `str` — in its place, or just before or
after it (`s[k] == "-"` read the `"0"` at `k`, and the sign belongs in front of it); anywhere when
neither occurs. An integer comparison is read as one over the numeral (`int(s) == 42`). -/
def spliceString (str : String) (p : CmpPair) : Gen String := do
  let (a, b) := match p with
    | .str a b => (a.toList, b.toList)
    | .int a b => ((toString a).toList, (toString b).toList)
  let cs := str.toList
  let (a, b) := if (occurrences cs a).isEmpty && !(occurrences cs b).isEmpty then (b, a) else (a, b)
  match occurrences cs a with
  | [] =>
      if b.isEmpty then mutateString str else
      let k := (← Gen.choose Nat 0 cs.length (by omega)).val
      return String.ofList (cs.take k ++ b ++ cs.drop k)
  | occ =>
      let i ← pickFrom occ
      return String.ofList <| match (← Gen.choose Nat 0 2 (by omega)).val with
        | 0 => cs.take i ++ b ++ cs.drop (i + a.length)
        | 1 => cs.take i ++ b ++ cs.drop i
        | _ => cs.take (i + a.length) ++ b ++ cs.drop (i + a.length)

instance : PyArb String where
  arb := do
    let s ← Gen.getSize
    let strs := (pool ()).1
    -- a numeral, sometimes with a `.` (`int(s)`, `float(s)`, `s.split(".")`)
    if (← Gen.choose Nat 0 9 (by omega)).val == 0 then
      let n ← genLen s
      let cs ← (List.range n).mapM fun _ => do
        let d ← Gen.choose Nat 0 10 (by omega)
        pure (if d.val == 10 then '.' else Char.ofNat (48 + d.val))
      return String.ofList cs
    if strs.size > 0 then
      let r ← Gen.choose Nat 0 9 (by omega)
      let pick : Gen String := do
        let i ← Gen.choose Nat 0 (strs.size - 1) (by omega)
        pure (strs.getD i.val "")
      if r.val < 2 then return ← pick
      if r.val < 4 then
        -- A mined string edited one to three times, with characters from the short literals (a
        -- regex's members and class characters): `"0"` → `"0.0"`, `"0e5"` → `"0e-5"`.
        let short := strs.foldl (fun acc w => if w.length ≤ 2 then acc ++ w.toList else acc) []
        let alpha := if short.isEmpty then strs.foldl (fun acc w => acc ++ w.toList) [] else short
        if alpha.length > 0 then
          let mut cs := (← pick).toList
          for _ in [0:(← Gen.choose Nat 1 3 (by omega)).val] do
            let c := alpha.getD (← Gen.choose Nat 0 (alpha.length - 1) (by omega)).val 'a'
            let k := (← Gen.choose Nat 0 cs.length (by omega)).val
            cs := match (← Gen.choose Nat 0 3 (by omega)).val with
              | 0 => cs.eraseIdx k
              | 1 => cs.set k c
              | _ => cs.take k ++ c :: cs.drop k
          return String.ofList cs
      if r.val < 5 then
        if ← Gen.chooseAny Bool then
          -- One mined string spliced into another (`"py"` + `"./"` → `"p./y"`).
          let a ← pick
          let b ← pick
          let k ← Gen.choose Nat 0 a.length (by omega)
          return String.ofList (a.toList.take k.val ++ b.toList ++ a.toList.drop k.val)
        -- Mined words joined by a mined separator: what `s.split(" ")` / `s.split(",")` reads back
        -- (`"two one"` from the words of a lookup table and the `" "` of a split).
        let seps := strs.filter (fun w => w.length == 1 && !w.front.isAlphanum)
        let sep ← if seps.isEmpty then pure " " else pickFrom seps.toList
        let words ← (List.range (← Gen.choose Nat 1 4 (by omega)).val).mapM fun _ => pick
        return sep.intercalate words
      if r.val < 7 then
        let chars := strs.foldl (fun acc w => acc ++ w.toList) []
        if chars.length > 0 then
          let n ← genLen s
          let cs ← (List.range n).mapM fun _ => do
            let i ← Gen.choose Nat 0 (chars.length - 1) (by omega)
            pure (chars.getD i.val 'a')
          return String.ofList cs
    let n ← genLen s
    let cs ← (List.range n).mapM fun _ => genChar
    pure (String.ofList cs)
  shrink s :=
    if s.isEmpty then [] else
    let cs := s.toList
    ["", String.ofList (cs.take (cs.length / 2)), String.ofList cs.tail, String.ofList cs.dropLast].eraseDups.filter (· != s)
  fromPool _ := (pool ()).1.toList
  mutate := mutateString
  splice := spliceString
  crossover a b := do
    let k := (← Gen.choose Nat 0 a.length (by omega)).val
    if ← Gen.chooseAny Bool then return String.ofList (a.toList.take k ++ b.toList ++ a.toList.drop k)
    let j := (← Gen.choose Nat 0 b.length (by omega)).val
    return String.ofList (a.toList.take k ++ b.toList.drop j)
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
  mutate q := do match (← Gen.choose Nat 0 3 (by omega)).val with
    | 0 => pure (q + 1)
    | 1 => pure (q - 1)
    | 2 => pure (q / 2)
    | _ => do pure (ratOfDyadic (← genDyadic))

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
  mutate f := do match (← Gen.choose Nat 0 3 (by omega)).val with
    | 0 => pure (f + 1)
    | 1 => pure (f - 1)
    | 2 => pure (f / 2)
    | _ => do pure (floatOfDyadic (← genDyadic))

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
  mutate xs := do
    let k := (← Gen.choose Nat 0 xs.length (by omega)).val
    match (← Gen.choose Nat 0 4 (by omega)).val, xs[k]? with
    | 0, some x => return xs.set k (← PyArb.mutate x)
    | 1, _ => return xs.take k ++ (← PyArb.arb) :: xs.drop k
    | 2, some _ => return xs.eraseIdx k
    | 3, some x => return xs.take k ++ x :: xs.drop k
    | _, _ => return xs ++ [← PyArb.arb]
  crossover xs ys := do
    let k := (← Gen.choose Nat 0 xs.length (by omega)).val
    let j := (← Gen.choose Nat 0 ys.length (by omega)).val
    return xs.take k ++ ys.drop j
  climb xs d := do
    let k := (← Gen.choose Nat 0 (xs.length - 1) (by omega)).val
    match xs[k]? with
    | some x => return xs.set k (← PyArb.climb x d)
    | none => pure xs
  splice xs p := do
    let k := (← Gen.choose Nat 0 (xs.length - 1) (by omega)).val
    match xs[k]? with
    | some x => return xs.set k (← PyArb.splice x p)
    | none => return [← PyArb.arb]

instance [ToPyLit α] : ToPyLit (Array α) := ⟨fun xs => .list (xs.toList.map ToPyLit.toLit)⟩
instance [PyArb α] : PyArb (Array α) where
  arb := do pure (← (PyArb.arb : Gen (List α))).toArray
  shrink xs := (PyArb.shrink xs.toList).map List.toArray
  mutate xs := do pure (← PyArb.mutate xs.toList).toArray
  climb xs d := do pure (← PyArb.climb xs.toList d).toArray
  splice xs p := do pure (← PyArb.splice xs.toList p).toArray
  enum d lim := (PyArb.enum d lim : List (List α)).map List.toArray

instance [ToPyLit α] : ToPyLit (Option α) := ⟨fun | some a => ToPyLit.toLit a | Option.none => .none⟩
instance [PyArb α] : PyArb (Option α) where
  arb := do
    let k ← Gen.choose Nat 0 3 (by omega)
    if k.val == 0 then pure Option.none else pure (some (← PyArb.arb))
  shrink
    | some a => Option.none :: (PyArb.shrink a).map some
    | Option.none => []
  mutate
    | some a => do if (← Gen.choose Nat 0 4 (by omega)).val == 0 then pure Option.none else pure (some (← PyArb.mutate a))
    | Option.none => do pure (some (← PyArb.arb))
  climb
    | some a, d => do pure (some (← PyArb.climb a d))
    | Option.none, _ => do pure (some (← PyArb.arb))
  splice
    | some a, p => do pure (some (← PyArb.splice a p))
    | Option.none, _ => do pure (some (← PyArb.arb))
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
  mutate p := do match (← Gen.choose Nat 0 2 (by omega)).val with
    | 0 => do pure (← PyArb.mutate p.1, p.2)
    | 1 => do pure (p.1, ← PyArb.mutate p.2)
    | _ => do pure (← PyArb.mutate p.1, ← PyArb.mutate p.2)
  crossover p q := do
    match (← Gen.choose Nat 0 2 (by omega)).val with
    | 0 => pure (p.1, q.2)
    | 1 => pure (q.1, p.2)
    | _ => pure (← PyArb.crossover p.1 q.1, ← PyArb.crossover p.2 q.2)
  climb p d := do
    if ← Gen.chooseAny Bool then pure (← PyArb.climb p.1 d, p.2) else pure (p.1, ← PyArb.climb p.2 d)
  splice p c := do
    if ← Gen.chooseAny Bool then pure (← PyArb.splice p.1 c, p.2) else pure (p.1, ← PyArb.splice p.2 c)
  enum d lim := diagonal (PyArb.enum d lim) (PyArb.enum d lim) lim

/-- A Python callable the search can print and CPython can rebuild: a finite table and a default.
A function-typed input is searched as one of these (`higher_order(fn)` needs `fn(100) == 7`, `fn(7) == 42`). -/
structure PyFn (α β : Type) where
  table : List (α × β)
  dflt : β

def PyFn.apply {α β : Type} [BEq α] (f : PyFn α β) (a : α) : β :=
  ((f.table.find? (·.1 == a)).map (·.2)).getD f.dflt

instance [ToPyLit α] [ToPyLit β] : ToPyLit (PyFn α β) where
  toLit f := .fn (f.table.map fun (a, b) => (ToPyLit.toLit a, ToPyLit.toLit b)) (ToPyLit.toLit f.dflt)

instance [PyArb α] [PyArb β] : PyArb (PyFn α β) where
  arb := do
    let n ← Gen.choose Nat 0 3 (by omega)
    let table ← (List.range n.val).mapM fun _ => do return ((← PyArb.arb), (← PyArb.arb))
    return ⟨table, ← PyArb.arb⟩
  shrink f := (List.range f.table.length).map (fun i => { f with table := f.table.eraseIdx i })
    ++ (PyArb.shrink f.dflt).map ({ f with dflt := · })
  mutate f := do
    match (← Gen.choose Nat 0 2 (by omega)).val with
    | 0 => return { f with dflt := ← PyArb.mutate f.dflt }
    | 1 => return { f with table := ((← PyArb.arb), (← PyArb.arb)) :: f.table }
    | _ => return { f with table := ← PyArb.mutate f.table }

end PastaLean.Refute
