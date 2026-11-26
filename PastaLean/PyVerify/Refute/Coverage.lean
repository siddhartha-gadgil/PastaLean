import Lean
import PastaLean.PyAPI.Sets
import PastaLean.PyVerify.Refute.Arb

/-!
# Branch coverage and branch distance for the coverage-guided search

`Instrument.lean` copies the definitions a property reaches and wraps every decision in them — the
`Decidable` instance of an `if`/`decide`, a Bool comparison — in a probe. A probe returns the decision
unchanged and logs `(branch, direction, distance)`: the distance says how far the evaluation was from
taking the other direction (`|a - b|` for `a = b`, an edit distance for strings, as in search-based
testing). A probe on a comparison also logs its operands, which the search adds to the literal pool so
a needle compared against (`x == 8314`, `s == "age"`) can be spliced into an input.
-/

namespace PastaLean.Refute

/-- `c` without a `private` prefix: the program's own `private def`s are `_private.….PastaLean.User.…`. -/
def publicName (c : Lean.Name) : Lean.Name := (Lean.privateToUserName? c).getD c

/-- A constant of the program under test (`PastaLean.User`) or, with `libraries`, of the Python-module
libraries it calls (`Libraries`): never the runtime or Mathlib. -/
def isProgramConst (c : Lean.Name) (libraries := true) : Bool :=
  (`PastaLean.User).isPrefixOf (publicName c) || libraries && (`Libraries).isPrefixOf c

/-- The code of `c`: its definition, or for a `partial def` (an opaque constant) that of `c._unsafe_rec`. -/
def defBody? (env : Lean.Environment) (c : Lean.Name) : Option Lean.DefinitionVal :=
  match env.find? c, env.find? (c ++ `_unsafe_rec) with
  | some (.defnInfo d), _ => some d
  | some (.opaqueInfo _), some (.defnInfo d) => some d
  | _, _ => none

/-- A decision's distances: to making it true, and to making it false (one of them is `0`). -/
abbrev Dist := Nat × Nat

/-- `(branch, direction taken, distance to the other direction)` per probe hit, in order. -/
initialize covLog : IO.Ref (Array (Nat × Bool × Nat)) ← IO.mkRef #[]

/-- Operands of the comparisons evaluated since the last read (strings, integers). -/
initialize covOperands : IO.Ref (Array String × Array Int) ← IO.mkRef (#[], #[])

/-- The same operands paired, by the branch whose distance compared them (`covProbe`). -/
initialize covPairs : IO.Ref (Array (Nat × CmpPair)) ← IO.mkRef #[]

/-- The branch whose distance is being computed. -/
initialize covProbe : IO.Ref Nat ← IO.mkRef 0

/-- Log a probe hit: branch `id` went `dir`, with distances `d ()`. -/
@[noinline]
def logProbe (id : Nat) (dir : Bool) (d : Unit → Dist) : BaseIO Unit := do
  -- the distance may evaluate what the program short-circuits (`b` in `a and b`): whatever runtime
  -- error that records is not the program's, so the error log is restored around it
  let saved ← PastaLean.pyErrorLog.get
  let outer ← covProbe.swap id
  let dist ← match ← (IO.lazyPure d).toBaseIO with | .ok v => pure v | .error _ => pure ((1, 1) : Dist)
  covProbe.set outer
  PastaLean.pyErrorLog.set saved
  covLog.modify (·.push (id, dir, if dir then dist.2 else dist.1))

@[never_extract, noinline]
unsafe def covDecImpl {p : Prop} (id : Nat) (d : Unit → Dist) (inst : Decidable p) : Decidable p :=
  unsafeBaseIO do logProbe id (@decide p inst) d; pure inst

/-- The decision `inst`, logged as branch `id` with distances `d ()`. -/
@[never_extract, implemented_by covDecImpl]
def covDec {p : Prop} (_id : Nat) (_d : Unit → Dist) (inst : Decidable p) : Decidable p := inst

@[never_extract, noinline]
unsafe def covBoolImpl (id : Nat) (d : Unit → Dist) (b : Bool) : Bool :=
  unsafeBaseIO do logProbe id b d; pure b

/-- The Bool `b`, logged as branch `id` with distances `d ()`. -/
@[never_extract, implemented_by covBoolImpl]
def covBool (_id : Nat) (_d : Unit → Dist) (b : Bool) : Bool := b

@[never_extract, noinline]
unsafe def withIntsImpl (a b : Int) (r : Dist) : Dist :=
  unsafeBaseIO do
    covOperands.modify fun (s, i) => (s, if i.size < 256 then i.push a |>.push b else i)
    let id ← covProbe.get
    covPairs.modify fun ps => if ps.size < 512 then ps.push (id, .int a b) else ps
    pure r

/-- `r`, with `a` and `b` logged as compared operands. -/
@[never_extract, implemented_by withIntsImpl]
def withInts (_a _b : Int) (r : Dist) : Dist := r

@[never_extract, noinline]
unsafe def withStrsImpl (a b : String) (r : Dist) : Dist :=
  unsafeBaseIO do
    covOperands.modify fun (s, i) =>
      (if s.size < 256 && a.length ≤ 64 && b.length ≤ 64 then s.push a |>.push b else s, i)
    if a.length ≤ 64 && b.length ≤ 64 then
      let id ← covProbe.get
      covPairs.modify fun ps => if ps.size < 512 then ps.push (id, .str a b) else ps
    pure r

@[never_extract, implemented_by withStrsImpl]
def withStrs (_a _b : String) (r : Dist) : Dist := r

def distEqInt (a b : Int) : Dist :=
  withInts a b (if a == b then (0, 1) else ((a - b).natAbs, 0))

def distLtInt (a b : Int) : Dist :=
  withInts a b (if a < b then (0, (b - a).toNat) else ((a - b).toNat + 1, 0))

def distLeInt (a b : Int) : Dist :=
  withInts a b (if a ≤ b then (0, (b - a).toNat + 1) else ((a - b).toNat, 0))

/-- Levenshtein distance, capped: long strings are compared by length only. -/
def editDistance (a b : String) : Nat :=
  if a.length > 64 || b.length > 64 then (Int.ofNat a.length - b.length).natAbs + 1 else Id.run do
    let bs := b.toList.toArray
    let mut prev : Array Nat := (List.range (bs.size + 1)).toArray
    for ca in a.toList do
      let mut cur : Array Nat := #[prev[0]! + 1]
      for j in [0:bs.size] do
        let sub := prev[j]! + (if ca == bs[j]! then 0 else 1)
        cur := cur.push (min sub (min (prev[j + 1]! + 1) (cur[j]! + 1)))
      prev := cur
    return prev[bs.size]!

def distEqStr (a b : String) : Dist :=
  withStrs a b (if a == b then (0, 1) else (editDistance a b, 0))

def distEqChar (a b : Char) : Dist :=
  if a == b then (0, 1) else ((Int.ofNat a.toNat - b.toNat).natAbs, 0)

/-- `|a - b|` rounded up, for a float comparison's distance (non-finite gaps count as far). -/
def floatGap (a b : Float) : Nat :=
  let d := Float.abs (a - b)
  if d.isNaN || d.isInf then 1000000000 else d.ceil.toUInt64.toNat

def distEqFloat (a b : Float) : Dist := if a == b then (0, 1) else (floatGap a b + 1, 0)
def distLtFloat (a b : Float) : Dist := if a < b then (0, floatGap a b) else (floatGap a b + 1, 0)
def distLeFloat (a b : Float) : Dist := if a ≤ b then (0, floatGap a b + 1) else (floatGap a b, 0)

/-- Lists: the length difference plus the positions that differ. -/
def distEqList {α : Type} [BEq α] (a b : List α) : Dist :=
  if a == b then (0, 1) else
    ((Int.ofNat a.length - b.length).natAbs + ((a.zip b).filter fun (x, y) => !(x == y)).length, 0)

/-- Sets: the size of the symmetric difference. -/
def distSetEq {α : Type} [BEq α] [Hashable α] (a b : PastaLean.PySet α) : Dist :=
  let n := (a.toList.filter (!b.contains ·)).length + (b.toList.filter (!a.contains ·)).length
  if n == 0 then (0, 1) else (n, 0)

/-- `x in xs` for scalars: the distance to the nearest element. -/
def distInListInt (xs : List Int) (x : Int) : Dist :=
  if xs.contains x then (0, 1) else ((xs.map fun y => (x - y).natAbs).foldl min 1000000000 |>.max 1, 0)
def distInListStr (xs : List String) (x : String) : Dist :=
  if xs.contains x then (0, 1) else ((xs.map (editDistance x)).foldl min 1000000000 |>.max 1, 0)

/-- Unknown shape: only whether the decision holds. -/
def distBool (b : Bool) : Dist := if b then (0, 1) else (1, 0)

def distNot (d : Dist) : Dist := (d.2, d.1)
/-- `a and b` / `a or b` short-circuit: `b`'s distance is computed only when the program evaluates `b`
(when `a` does not decide), so a probe never runs code the program skips (it may not terminate). -/
def distAnd (p : Dist) (q : Unit → Dist) : Dist :=
  if p.1 != 0 then (p.1 + 1, 0) else let q := q (); (q.1, min p.2 q.2)
def distOr (p : Dist) (q : Unit → Dist) : Dist :=
  if p.1 == 0 then (0, p.2 + 1) else let q := q (); (min p.1 q.1, q.2)

/-- Read and clear the coverage log, the logged operands, and the operand pairs by branch. -/
def takeCoverage : IO (Array (Nat × Bool × Nat) × (Array String × Array Int) × Array (Nat × CmpPair)) := do
  return (← covLog.swap #[], ← covOperands.swap (#[], #[]), ← covPairs.swap #[])

end PastaLean.Refute
