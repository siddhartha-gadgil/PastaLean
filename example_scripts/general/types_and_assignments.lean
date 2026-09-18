import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def inf {α : Type} [PastaLean.PyNonFinite α] : α :=
  PastaLean.pyNonFinite "inf"

def basic_types :=
  Id.run do
    let mut a : Int := (1 : Int)
    let mut b := (2.5 : Rat)
    let mut c : String := "hello"
    let mut d : Bool := Bool.true
    let mut e : List Int := [(1 : Int), (2 : Int)]
    let mut f : Int × String := ((1 : Int), "a")
    let mut g : Int := (3 : Int)
    let mut h := (4.5 : Rat)
    let mut m : Int := (5 : Int)
    let mut n : String := "world"
    let mut p : Bool := Bool.false
    let mut tup1 : String × Int := ("foo", (42 : Int))
    let mut tup2 := (g, h)

attribute [simp, taste_ingr] basic_types

def basic_types'rn :=
  Id.run do
    let mut a : Int := (1 : Int)
    let mut b := (2.5 : Float)
    let mut c : String := "hello"
    let mut d : Bool := Bool.true
    let mut e : Array Int := #[(1 : Int), (2 : Int)]
    let mut f : Int × String := ((1 : Int), "a")
    let mut g : Int := (3 : Int)
    let mut h := (4.5 : Float)
    let mut m : Int := (5 : Int)
    let mut n : String := "world"
    let mut p : Bool := Bool.false
    let mut tup1 : String × Int := ("foo", (42 : Int))
    let mut tup2 := (g, h)

def starred_unpacking := fun (lst : List Int) ↦
  Id.run
    (do
      -- `*` collects the middle into a list; elements after the star read from the end, so `last` is
      -- always `lst[-1]` regardless of length. `head, *body, last = [1,2,3,4]` → (1, [2,3], 4).
      let p'_unpack_value_1 := lst
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut head : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (0 : Int)
      let mut body := PastaLean.pyListSlice p'_unpack_pair_1 (some (1 : Int)) (some (-1 : Int))
      let mut last : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (-1 : Int)
      let p'_unpack_value_2 := lst
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut first : Int := PastaLean.pyListGetItem p'_unpack_pair_2 (0 : Int)
      let mut rest := PastaLean.pyListSlice p'_unpack_pair_2 (some (1 : Int)) (none : Option Int)
      let p'_unpack_value_3 := lst
      let p'_unpack_pair_3 := p'_unpack_value_3
      let mut init := PastaLean.pyListSlice p'_unpack_pair_3 (some (0 : Int)) (some (-1 : Int))
      let mut tail : Int := PastaLean.pyListGetItem p'_unpack_pair_3 (-1 : Int)
      let p'_ret_1 := (head, (body, (last, (rest, init))))
      return p'_ret_1)

attribute [simp, taste_ingr] starred_unpacking

def starred_unpacking'rn := fun (lst : List Int) ↦
  Id.run
    (do
      -- `*` collects the middle into a list; elements after the star read from the end, so `last` is
      -- always `lst[-1]` regardless of length. `head, *body, last = [1,2,3,4]` → (1, [2,3], 4).
      let p'_unpack_value_1 := lst
      let p'_unpack_pair_1 := p'_unpack_value_1
      let mut head : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (0 : Int)
      let mut body := PastaLean.pyListSlice p'_unpack_pair_1 (some (1 : Int)) (some (-1 : Int))
      let mut last : Int := PastaLean.pyListGetItem p'_unpack_pair_1 (-1 : Int)
      let p'_unpack_value_2 := lst
      let p'_unpack_pair_2 := p'_unpack_value_2
      let mut first : Int := PastaLean.pyListGetItem p'_unpack_pair_2 (0 : Int)
      let mut rest := PastaLean.pyListSlice p'_unpack_pair_2 (some (1 : Int)) (none : Option Int)
      let p'_unpack_value_3 := lst
      let p'_unpack_pair_3 := p'_unpack_value_3
      let mut init := PastaLean.pyListSlice p'_unpack_pair_3 (some (0 : Int)) (some (-1 : Int))
      let mut tail : Int := PastaLean.pyListGetItem p'_unpack_pair_3 (-1 : Int)
      let p'_ret_1 := (head, (body, (last, (rest, init))))
      return p'_ret_1)

def fstring :=
  let s1 := ("Hello" : String)
  let s2 := ("World" : String)
  let s3 := (s1 +ₚ ", " +ₚ s2 +ₚ "!" : String)
  s! "This is a string: {s3} and this is a number: {(1 : Int) +ₚ (2 : Int)}"

attribute [simp, taste_ingr] fstring

def fstring'rn :=
  let s1 := ("Hello" : String)
  let s2 := ("World" : String)
  let s3 := (s1 +ₚ ", " +ₚ s2 +ₚ "!" : String)
  s! "This is a string: {s3} and this is a number: {(1 : Int) +ₚ (2 : Int)}"

def annotated_vars :=
  let x := (10 : Int)
  let y := (20 : Int)
  x +ₚ y

attribute [simp, taste_ingr] annotated_vars

def annotated_vars'rn :=
  let x := (10 : Int)
  let y := (20 : Int)
  x +ₚ y

-- Python's numeric tower: int values coerce up to float. These guard the T1 mixed int/float codegen
-- coercions the leetcode DP corpus depends on — regressions here are otherwise only caught by rerunning
-- the corpus.
def numeric_tower_widening := fun (flags : List Bool) ↦ fun (a : Int) ↦ fun (b : Int) ↦
  Id.run
    (do
      -- Python's numeric tower `bool < int < float < ℚ`: a `bool` widens into an int accumulator, and
      -- bool comparison results take part in arithmetic. `sum` of bools counts them.
      let mut total : Int := (0 : Int)
      for f in (PastaLean.pyIter flags)do
        total := total +ₚ f
      let p'_ret_1 := total +ₚ decide (a > b) +ₚ (a == b) *ₚ (2 : Int)
      return p'_ret_1)

attribute [simp, taste_ingr] numeric_tower_widening

def numeric_tower_widening'rn := fun (flags : List Bool) ↦ fun (a : Int) ↦ fun (b : Int) ↦
  Id.run
    (do
      -- Python's numeric tower `bool < int < float < ℚ`: a `bool` widens into an int accumulator, and
      -- bool comparison results take part in arithmetic. `sum` of bools counts them.
      let mut total : Int := (0 : Int)
      for f in (PastaLean.pyIter flags)do
        total := total +ₚ f
      let p'_ret_1 := total +ₚ decide (a > b) +ₚ (a == b) *ₚ (2 : Int)
      return p'_ret_1)

def mixed_scalar_accumulator := fun (xs : List Int) ↦
  (show Rat from
    Id.run
      (do
        -- int-seeded `ans` joins a float (`x / 2`) → must become float; the `0` seed coerces to `(0 : ℚ)`.
        let mut ans := (0 : Rat)
        for x in (PastaLean.pyIter xs)do
          ans := PastaLean.pyMax [ans, x /ₚ (2 : Int)]
        return ans))

attribute [simp, taste_ingr] mixed_scalar_accumulator

def mixed_scalar_accumulator'rn := fun (xs : List Int) ↦
  (show Float from
    Id.run
      (do
        -- int-seeded `ans` joins a float (`x / 2`) → must become float; the `0` seed coerces to `(0 : ℚ)`.
        let mut ans := (0 : Float)
        for x in (PastaLean.pyIter xs)do
          ans := PastaLean.pyMax [ans, PastaLean.pyFloat x /ₚ (2 : Int)]
        return ans))

def int_init_float_container := fun (nums : List Int) ↦
  (show List Rat from
    Id.run
      (do
        -- `dp = [0]*n` later holds floats (`/ 2`) → `List float`, with the `0` element coerced.
        let mut n : Int := PastaLean.pyLen nums
        let mut dp := (PastaLean.pyListRepeat [(0 : Rat)] n : List Rat)
        for i in (PastaLean.pyRange n (1 : Int))do
          dp := PastaLean.pySetItem dp i (dp⦋i -ₚ (1 : Int)⦌ /ₚ (2 : Int) +ₚ nums⦋i⦌ : Rat)
        return dp))

attribute [simp, taste_ingr] int_init_float_container

def int_init_float_container'rn := fun (nums : List Int) ↦
  (show List Float from
    Id.run
      (do
        -- `dp = [0]*n` later holds floats (`/ 2`) → `List float`, with the `0` element coerced.
        let mut n : Int := PastaLean.pyLen nums
        let mut dp := (PastaLean.pyListRepeat [(0 : Float)] n : List Float)
        for i in (PastaLean.pyRange n (1 : Int))do
          dp := PastaLean.pySetItem dp i (PastaLean.pyFloat dp⦋i -ₚ (1 : Int)⦌ /ₚ (2 : Int) +ₚ nums⦋i⦌ : Float)
        return dp))

def inf_dp := fun (cost : List Int) ↦
  Id.run
    (do
      -- Canonical `[inf]*n` DP: `inf` adapts to the container's float type across both twins.
      let mut n : Int := PastaLean.pyLen cost
      let mut dp : List Int := PastaLean.pyListRepeat [inf] (n +ₚ (1 : Int))
      dp := PastaLean.pySetItem dp (0 : Int) (0 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        dp := PastaLean.pySetItem dp i (PastaLean.pyMin [dp⦋i -ₚ (1 : Int)⦌ +ₚ cost⦋i -ₚ (1 : Int)⦌, dp⦋i⦌])
      let p'_ret_1 := dp⦋n⦌
      return p'_ret_1)

attribute [simp, taste_ingr] inf_dp

def inf_dp'rn := fun (cost : List Int) ↦
  Id.run
    (do
      -- Canonical `[inf]*n` DP: `inf` adapts to the container's float type across both twins.
      let mut n : Int := PastaLean.pyLen cost
      let mut dp : Array Int := PastaLean.pyArrayRepeat #[inf] (n +ₚ (1 : Int))
      dp := PastaLean.pySetItem dp (0 : Int) (0 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        dp := PastaLean.pySetItem dp i (PastaLean.pyMin [dp⦋i -ₚ (1 : Int)⦌ +ₚ cost⦋i -ₚ (1 : Int)⦌, dp⦋i⦌])
      let p'_ret_1 := dp⦋n⦌
      return p'_ret_1)

def grid_inf_dp := fun (houses : List Int) ↦
  Id.run
    (do
      -- A 2-D `[[inf]*k for _ in …]` DP: the comprehension is a nested list-container seeded by the
      -- polymorphic `inf`, so it must be ascribed the twin's float type (`List (List ℚ)` / `Float`) —
      -- otherwise `inf` defaults to ℚ while the run twin's values are `Float` (a `PySetItem (List ℚ) ℤ
      -- Float` clash). Mirrors the allocate-mailboxes shape.
      let mut n : Int := PastaLean.pyLen houses
      let mut f : List (List Int) :=
        (PastaLean.pyRange n).map fun (_ : Int) => PastaLean.pyListRepeat [inf] (n +ₚ (1 : Int))
      for hb'i : i in (PastaLean.pyRange n)do
        let p'_setval_1 := PastaLean.pyListGetProof houses i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
        f := PastaLean.pyModifyItem f i (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (1 : Int) p'_setval_1)
        for j in (PastaLean.pyRange (i +ₚ (2 : Int)) (2 : Int))do
          for p in (PastaLean.pyRange i)do
            let p'_setval_2 :=
              PastaLean.pyMin
                [f⦋i⦌⦋j⦌,
                  f⦋p⦌⦋j -ₚ (1 : Int)⦌ +ₚ
                    PastaLean.pyListGetProof houses i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)]
            f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
      let p'_ret_1 := f⦋n -ₚ (1 : Int)⦌⦋n⦌
      return p'_ret_1)

attribute [simp, taste_ingr] grid_inf_dp

def grid_inf_dp'rn := fun (houses : List Int) ↦
  Id.run
    (do
      -- A 2-D `[[inf]*k for _ in …]` DP: the comprehension is a nested list-container seeded by the
      -- polymorphic `inf`, so it must be ascribed the twin's float type (`List (List ℚ)` / `Float`) —
      -- otherwise `inf` defaults to ℚ while the run twin's values are `Float` (a `PySetItem (List ℚ) ℤ
      -- Float` clash). Mirrors the allocate-mailboxes shape.
      let mut n : Int := PastaLean.pyLen houses
      let mut f : Array (Array Int) :=
        ((PastaLean.pyRange n).map fun (_ : Int) => PastaLean.pyArrayRepeat #[inf] (n +ₚ (1 : Int))) |>.toArray
      for hb'i : i in (PastaLean.pyRange n)do
        let p'_setval_1 := PastaLean.pyListGetProof houses i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
        f := PastaLean.pyModifyItem f i (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (1 : Int) p'_setval_1)
        for j in (PastaLean.pyRange (i +ₚ (2 : Int)) (2 : Int))do
          for p in (PastaLean.pyRange i)do
            let p'_setval_2 :=
              PastaLean.pyMin
                [f⦋i⦌⦋j⦌,
                  f⦋p⦌⦋j -ₚ (1 : Int)⦌ +ₚ
                    PastaLean.pyListGetProof houses i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)]
            f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
      let p'_ret_1 := f⦋n -ₚ (1 : Int)⦌⦋n⦌
      return p'_ret_1)

def dp_sentinel_return := fun (cost : List Int) ↦
  Id.run
    (do
      -- The canonical inf-DP ending: `return -1 if unreachable else value`. The single ternary return
      -- mixes `int` (`-1`) with the `float` DP value, so both branches are elaborated at the mode float
      -- (`ℚ`/`Float`) — the `-1` coerces up (int→ℚ / int→Float) instead of pinning the result to `ℤ`.
      let mut n : Int := PastaLean.pyLen cost
      let mut dp : List Int := PastaLean.pyListRepeat [inf] (n +ₚ (1 : Int))
      dp := PastaLean.pySetItem dp (0 : Int) (0 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        dp := PastaLean.pySetItem dp i (PastaLean.pyMin [dp⦋i -ₚ (1 : Int)⦌ +ₚ cost⦋i -ₚ (1 : Int)⦌, dp⦋i⦌])
      let p'_ret_1 := if dp⦋n⦌ ≥ inf then -(1 : Int) else dp⦋n⦌
      return p'_ret_1)

attribute [simp, taste_ingr] dp_sentinel_return

def dp_sentinel_return'rn := fun (cost : List Int) ↦
  Id.run
    (do
      -- The canonical inf-DP ending: `return -1 if unreachable else value`. The single ternary return
      -- mixes `int` (`-1`) with the `float` DP value, so both branches are elaborated at the mode float
      -- (`ℚ`/`Float`) — the `-1` coerces up (int→ℚ / int→Float) instead of pinning the result to `ℤ`.
      let mut n : Int := PastaLean.pyLen cost
      let mut dp : Array Int := PastaLean.pyArrayRepeat #[inf] (n +ₚ (1 : Int))
      dp := PastaLean.pySetItem dp (0 : Int) (0 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int))do
        dp := PastaLean.pySetItem dp i (PastaLean.pyMin [dp⦋i -ₚ (1 : Int)⦌ +ₚ cost⦋i -ₚ (1 : Int)⦌, dp⦋i⦌])
      let p'_ret_1 := if dp⦋n⦌ ≥ inf then -(1 : Int) else dp⦋n⦌
      return p'_ret_1)

def heterogeneous_pyany :=
  (show PastaLean.PyAny from
    -- `[1, "hi", 3]` is `List PyAny`; arithmetic on a boxed element (`* 2`, `+`) dispatches on the tag.
    let xs := ([(1 : Int), "hi", (3 : Int)] : List PyAny)
    let total := (0 : Int)
    let total := total +ₚ xs⦋(0 : Int)⦌ *ₚ (2 : Int)
    total)

attribute [simp] heterogeneous_pyany

def heterogeneous_pyany'rn :=
  (show PastaLean.PyAny from
    -- `[1, "hi", 3]` is `List PyAny`; arithmetic on a boxed element (`* 2`, `+`) dispatches on the tag.
    let xs := ([(1 : Int), "hi", (3 : Int)] : List PyAny)
    let total := (0 : Int)
    let total := total +ₚ xs⦋(0 : Int)⦌ *ₚ (2 : Int)
    total)

def untyped_param_arithmetic := fun (nums : List Int) ↦
  Id.run
    (do
      -- `nums` is un-inferred → boxed `PyAny`; the two-pass seed propagates `PyAny` to the accumulator so
      -- `total` is `PyAny` (not `Int`), matching the boxed element arithmetic.
      let mut total : Int := (0 : Int)
      for x in (PastaLean.pyIter nums)do
        total := total +ₚ x *ₚ (2 : Int)
      return total)

attribute [simp, taste_ingr] untyped_param_arithmetic

def untyped_param_arithmetic'rn := fun (nums : List Int) ↦
  Id.run
    (do
      -- `nums` is un-inferred → boxed `PyAny`; the two-pass seed propagates `PyAny` to the accumulator so
      -- `total` is `PyAny` (not `Int`), matching the boxed element arithmetic.
      let mut total : Int := (0 : Int)
      for x in (PastaLean.pyIter nums)do
        total := total +ₚ x *ₚ (2 : Int)
      return total)

def untyped_param_compare_and_div := fun (nums : List Int) ↦
  (show Rat from
    Id.run
      (do
        -- Comparison, `%` and `/` on boxed (`PyAny`) values; `best` is a `let mut PyAny` slot reassigned
        -- across the loop (not shadowed).
        let mut best : Int := (0 : Int)
        for x in (PastaLean.pyIter nums)do
          if h_1 : x > best then 
            best := x +ₚ x %ₚ (3 : Int)
        let p'_ret_1 := best /ₚ (2 : Int)
        return p'_ret_1))

attribute [simp, taste_ingr] untyped_param_compare_and_div

def untyped_param_compare_and_div'rn := fun (nums : List Int) ↦
  (show Float from
    Id.run
      (do
        -- Comparison, `%` and `/` on boxed (`PyAny`) values; `best` is a `let mut PyAny` slot reassigned
        -- across the loop (not shadowed).
        let mut best : Int := (0 : Int)
        for x in (PastaLean.pyIter nums)do
          if h_1 : x > best then 
            best := x +ₚ x %ₚ (3 : Int)
        let p'_ret_1 := PastaLean.pyFloat best /ₚ (2 : Int)
        return p'_ret_1))

def untyped_param_bitwise := fun (nums : List Int) ↦
  Id.run
    (do
      -- Bitwise (`| & `), floor-div (`//`) and shift on boxed (`PyAny`) values.
      let mut r : Int := (0 : Int)
      for x in (PastaLean.pyIter nums)do
        r := PastaLean.pyBitOr r (PastaLean.pyBitAnd x (1 : Int)) +ₚ PastaLean.pyFloorDiv x (2 : Int)
      let p'_ret_1 := PastaLean.pyShiftLeft r (1 : Int)
      return p'_ret_1)

attribute [simp, taste_ingr] untyped_param_bitwise

def untyped_param_bitwise'rn := fun (nums : List Int) ↦
  Id.run
    (do
      -- Bitwise (`| & `), floor-div (`//`) and shift on boxed (`PyAny`) values.
      let mut r : Int := (0 : Int)
      for x in (PastaLean.pyIter nums)do
        r := PastaLean.pyBitOr r (PastaLean.pyBitAnd x (1 : Int)) +ₚ PastaLean.pyFloorDiv x (2 : Int)
      let p'_ret_1 := PastaLean.pyShiftLeft r (1 : Int)
      return p'_ret_1)

def grid_float_dp := fun (m : Int) ↦ fun (n : Int) ↦
  (show Rat from
    Id.run
      (do
        -- 2D grid DP initialised int (`[[0]*n ...]`) that becomes float via `/ 2` — the nested
        -- `f[i][j] = ...` teaches `f : list[list[float]]`, coercing the innermost `0`.
        let mut f :=
          ((PastaLean.pyRange m).map fun (_ : Int) => PastaLean.pyListRepeat [(0 : Rat)] n : List (List Rat))
        let p'_setval_1 := (1 : Rat)
        f := PastaLean.pyModifyItem f (0 : Int) (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (0 : Int) p'_setval_1)
        for i in (PastaLean.pyRange m)do
          for j in (PastaLean.pyRange n)do
            if h_1 : i > (0 : Int) then 
              let p'_setval_2 := f⦋i⦌⦋j⦌ +ₚ f⦋i -ₚ (1 : Int)⦌⦋j⦌ /ₚ (2 : Int)
              f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
        let p'_ret_1 := f⦋m -ₚ (1 : Int)⦌⦋n -ₚ (1 : Int)⦌
        return p'_ret_1))

attribute [simp, taste_ingr] grid_float_dp

def grid_float_dp'rn := fun (m : Int) ↦ fun (n : Int) ↦
  (show Float from
    Id.run
      (do
        -- 2D grid DP initialised int (`[[0]*n ...]`) that becomes float via `/ 2` — the nested
        -- `f[i][j] = ...` teaches `f : list[list[float]]`, coercing the innermost `0`.
        let mut f :=
          (((PastaLean.pyRange m).map fun (_ : Int) => PastaLean.pyArrayRepeat #[(0 : Float)] n) |>.toArray :
            Array (Array Float))
        let p'_setval_1 := (1 : Float)
        f := PastaLean.pyModifyItem f (0 : Int) (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (0 : Int) p'_setval_1)
        for i in (PastaLean.pyRange m)do
          for j in (PastaLean.pyRange n)do
            if h_1 : i > (0 : Int) then 
              let p'_setval_2 := f⦋i⦌⦋j⦌ +ₚ PastaLean.pyFloat f⦋i -ₚ (1 : Int)⦌⦋j⦌ /ₚ (2 : Int)
              f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
        let p'_ret_1 := f⦋m -ₚ (1 : Int)⦌⦋n -ₚ (1 : Int)⦌
        return p'_ret_1))

-- --- Back-inference from comparisons (unannotated params pinned by `== <literal>` / `in`) ---
-- Each param below is UN-annotated; its type is recovered from a comparison against a literal, so the
-- body type-checks WITHOUT boxing to PyAny. If the inference regressed, `PyAny == <literal>` would not
-- compile — so these compiling IS the regression test, one per PyAny subtype.
def eq_pins_str := fun (s : String) ↦
  -- `s == "hello"` ⇒ s : str, so `.upper()` (a str-only method) resolves.
  if s = "hello" then PastaLean.pyStringUpper s else s

attribute [simp, taste_ingr] eq_pins_str

def eq_pins_str'rn := fun (s : String) ↦
  -- `s == "hello"` ⇒ s : str, so `.upper()` (a str-only method) resolves.
  if s == "hello" then PastaLean.pyStringUpper s else s

def eq_pins_int := fun (x : Int) ↦
  -- `x == 42` ⇒ x : int, so the int-only shift `x << 1` type-checks.
  if x = (42 : Int) then PastaLean.pyShiftLeft x (1 : Int) else x

attribute [simp, taste_ingr] eq_pins_int

def eq_pins_int'rn := fun (x : Int) ↦
  -- `x == 42` ⇒ x : int, so the int-only shift `x << 1` type-checks.
  if x == (42 : Int) then PastaLean.pyShiftLeft x (1 : Int) else x

def eq_pins_float := fun (v : Rat) ↦
  (show Rat from
    -- `v == 3.14` ⇒ v : float.
    if v = (3.14 : Rat) then v *ₚ (2.0 : Rat) else v)

attribute [simp, taste_ingr] eq_pins_float

def eq_pins_float'rn := fun (v : Float) ↦
  (show Float from
    -- `v == 3.14` ⇒ v : float.
    if v == (3.14 : Float) then v *ₚ (2.0 : Float) else v)

def eq_pins_list_elem := fun (xs : List Int) ↦
  -- `xs == []` ⇒ xs : list; `xs[0] + 1` pins the ELEMENT to int ⇒ xs : list[int] (no PyAny box).
  if xs = [] then (0 : Int) else xs⦋(0 : Int)⦌ +ₚ (1 : Int)

attribute [simp, taste_ingr] eq_pins_list_elem

def eq_pins_list_elem'rn := fun (xs : List Int) ↦
  -- `xs == []` ⇒ xs : list; `xs[0] + 1` pins the ELEMENT to int ⇒ xs : list[int] (no PyAny box).
  if xs == [] then (0 : Int) else xs⦋(0 : Int)⦌ +ₚ (1 : Int)

def eq_pins_list_nested := fun (a : List Int) ↦
  -- Element int recovered from a NESTED int-forcing op: `(a[0] + a[-1]) % 2` (the SortArray pattern).
  if a ≠ [] then (a⦋(0 : Int)⦌ +ₚ a⦋(-1 : Int)⦌) %ₚ (2 : Int) else (0 : Int)

attribute [simp, taste_ingr] eq_pins_list_nested

def eq_pins_list_nested'rn := fun (a : List Int) ↦
  -- Element int recovered from a NESTED int-forcing op: `(a[0] + a[-1]) % 2` (the SortArray pattern).
  if a != [] then (a⦋(0 : Int)⦌ +ₚ a⦋(-1 : Int)⦌) %ₚ (2 : Int) else (0 : Int)

def eq_pins_list_method := fun (words : List String) ↦
  -- `words[0].upper()` — a str-only method on an element ⇒ words : list[str].
  if words ≠ [] then PastaLean.pyStringUpper words⦋(0 : Int)⦌ else ""

attribute [simp, taste_ingr] eq_pins_list_method

def eq_pins_list_method'rn := fun (words : List String) ↦
  -- `words[0].upper()` — a str-only method on an element ⇒ words : list[str].
  if words != [] then PastaLean.pyStringUpper words⦋(0 : Int)⦌ else ""

def membership_pins_str := fun ch ↦
  -- `ch in "aeiou"` ⇒ ch is an element of a str literal ⇒ ch : str.
  if PastaLean.pyContains "aeiou" ch then (1 : Int) else (0 : Int)

attribute [simp, taste_ingr] membership_pins_str

def membership_pins_str'rn := fun ch ↦
  -- `ch in "aeiou"` ⇒ ch is an element of a str literal ⇒ ch : str.
  if PastaLean.pyContains "aeiou" ch then (1 : Int) else (0 : Int)

def reassign_type_change_still_ok :=
  -- SAFETY: a type-CHANGING reassignment must keep working — `m` is str then int. Back-inference must
  -- not clobber it (codegen's rebind-shadow re-types the post-`int(m)` segment).
  let m := ("1" : String)
  let m'v1 := (PastaLean.pyInt m : Int)
  m'v1 ^ₚ (2 : Int)

attribute [simp, taste_ingr] reassign_type_change_still_ok

def reassign_type_change_still_ok'rn :=
  -- SAFETY: a type-CHANGING reassignment must keep working — `m` is str then int. Back-inference must
  -- not clobber it (codegen's rebind-shadow re-types the post-`int(m)` segment).
  let m := ("1" : String)
  let m'v1 := (PastaLean.pyInt m : Int)
  m'v1 ^ₚ (2 : Int)

end PastaLean.User.Root
