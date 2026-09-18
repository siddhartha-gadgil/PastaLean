import PastaLean.PyAPI.Refinement

open PastaLean

/-! Proof-carrying indexing (`PastaLean.PyAPI.Refinement`), the lowering of
`for i in range(len(xs)): … xs[i] …`. -/

/-- info: 30 -/
#guard_msgs in
#eval pyListGetProof [10, 20, 30, 40] 2 (by simp)

/-- The loop hypothesis `for h : i in pyRange (pyLen xs)` alone discharges every access. -/
example (xs : List Int) : Int := Id.run do
  let mut s : Int := 0
  for h : i in pyRange (pyLen xs) do
    s := s + pyListGetProof xs i (pyRange_len_bound h)
  return s

/-- info: 100 -/
#guard_msgs in
#eval Id.run do
  let xs : List Int := [10, 20, 30, 40]
  let mut s : Int := 0
  for h : i in pyRange (pyLen xs) do
    s := s + pyListGetProof xs i (pyRange_len_bound h)
  return s

-- The proved access agrees with the defaulting one on every in-range index.
#guard pyListGetProof [10, 20, 30, 40] 0 (by simp) == pyGetItem [10, 20, 30, 40] (0 : Int)
#guard pyListGetProof [10, 20, 30, 40] 3 (by simp) == pyGetItem [10, 20, 30, 40] (3 : Int)

/-- A length ALIAS (`n = len(xs)`, then `range(n)`) discharges the same way, with `rfl` for the
defining equation — the shape the generator emits for the aliased loop. -/
example (xs : List Int) : Int := Id.run do
  let n : Int := pyLen xs
  let mut s : Int := 0
  for h : i in pyRange n do
    s := s + pyListGetProof xs i (pyRange_len_bound_of_eq rfl h)
  return s

/-- info: 7 -/
#guard_msgs in
#eval pyArrayGetProof #[5, 6, 7] 2 (by simp)

-- `pyRange n` really does bound its elements, so the refinement never over-claims.
#guard (pyRange 5).all fun i => decide (0 ≤ i) && decide (i < 5)
