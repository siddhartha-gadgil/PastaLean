import PastaLean.PyVerify.Twin

/-! `#twin_check` and `twin_tac` on hand-written twin pairs shaped like generated code: an
`Array`-state loop, Bool vs Prop tests, a list of `Array` rows, a class, a `partial` callee. -/

open PastaLean

namespace PastaLean.TwinTest

def acc := fun (n : Int) ↦ Id.run do
  let mut st : List Int := []
  let mut t : Int := 0
  for i in pyRange n do
    st := pyAppend st i
    t := t +ₚ i
  return (st, t)
def acc'rn := fun (n : Int) ↦ Id.run do
  let mut st : Array Int := #[]
  let mut t : Int := 0
  for i in pyRange n do
    st := pyArrayAppend st i
    t := t +ₚ i
  return (st, t)

def small (x y : Int) : Bool := if x = y ∧ x < 3 then true else false
def small'rn (x y : Int) : Bool := if x == y && x < 3 then true else false

def sumSmall (xs : List Int) : Int := Id.run do
  let mut s := 0
  for x in xs do
    if small x 2 then s := s + x
  return s + pyLen xs
def sumSmall'rn (xs : Array Int) : Int := Id.run do
  let mut s := 0
  for x in xs do
    if small'rn x 2 then s := s + x
  return s + pyLen xs

def grid (n : Int) : Int := Id.run do
  let mut g := (pyRange n).map fun _ => pyListRepeat [(0 : Int)] n
  for i in pyRange n do
    g := pyModifyItem g i (fun row => pySetItem row i 1)
  return g⦋0⦌⦋0⦌
def grid'rn (n : Int) : Int := Id.run do
  let mut g := (pyRange n).map fun _ => (pyListRepeat [(0 : Int)] n).toArray
  for i in pyRange n do
    g := pyModifyItem g i (fun row => pySetItem row i 1)
  return g⦋0⦌⦋0⦌

structure Bag where
  items : List Int
  n : Int
structure Bag'rn where
  items : List Int
  n : Int
def Bag.add (b : Bag) (x : Int) : Bag := { b with items := pyAppend b.items x, n := b.n + 1 }
def Bag'rn.add (b : Bag'rn) (x : Int) : Bag'rn := { b with items := pyAppend b.items x, n := b.n + 1 }

partial def down (n : Int) : Int := if n ≤ 0 then 0 else down (n - 1) + 1
partial def down'rn (n : Int) : Int := if n ≤ 0 then 0 else down'rn (n - 1) + 1
def useDown (n : Int) : Int := down n + 1
def useDown'rn (n : Int) : Int := down'rn n + 1

def withFloat (x : Rat) : Rat := x + 1
def withFloat'rn (x : Float) : Float := x + 1

/--
info: twin-report: {"pairs":[{"decl":"PastaLean.TwinTest.Bag.add","detail":"","f":"add","verdict":"proved"},{"decl":"PastaLean.TwinTest.acc","detail":"","f":"acc","verdict":"proved"},{"decl":"PastaLean.TwinTest.down","detail":"","f":"down","verdict":"partial_step_equiv"},{"decl":"PastaLean.TwinTest.grid","detail":"","f":"grid","verdict":"proved"},{"decl":"PastaLean.TwinTest.small","detail":"","f":"small","verdict":"proved"},{"decl":"PastaLean.TwinTest.sumSmall","detail":"","f":"sumSmall","verdict":"proved"},{"decl":"PastaLean.TwinTest.useDown","detail":"[PastaLean.TwinTest.down]","f":"useDown","verdict":"proved_mod_partial"},{"decl":"PastaLean.TwinTest.withFloat","detail":"","f":"withFloat","verdict":"float"}]}
-/
#guard_msgs in
#twin_check

/-- info: PastaLean.TwinTest.sumSmall._twin_eq (xs : Array ℤ) : sumSmall'rn xs = sumSmall (Twin.down xs) -/
#guard_msgs in
#check sumSmall._twin_eq

-- `twin_tac` by hand, on a pair before `#twin_check` has seen it.
def tail3 (xs : List Int) : Int := pyLen xs +ₚ (if pyTruthy xs then 1 else 0)
def tail3'rn (xs : Array Int) : Int := pyLen xs +ₚ (if pyTruthy xs then 1 else 0)
example : ∀ xs, tail3'rn (Twin.up xs) = tail3 xs := by twin_tac [tail3, tail3'rn]

end PastaLean.TwinTest
