import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- type: ignore
/-
Annotations that are WRONG as Python typing but common in real (LeetCode) code. PastaLean must
still translate them; the `# type: ignore` header marks the file unchecked, so type-checking
benchmarks skip it.
-/
def inf {α : Type} [PastaLean.PyNonFinite α] : α :=
  PastaLean.pyNonFinite "inf"

structure ListNode where
  val : Int
  next : Option ListNode
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy ListNode where truthy _ := true

instance : PastaLean.PyBool ListNode where pyBool _ := true

instance : PastaLean.PyTyped ListNode where pyTypeOf _ := TypeInfer.PyType.cls "ListNode"

instance : Coe ListNode (Option ListNode) :=
  ⟨some⟩

def ListNode.new (val : Int := (0 : Int)) (next : Option ListNode := Option.none) : ListNode :=
  ({ val := val, next := next } : ListNode)

structure ListNode'rn where
  val : Int
  next : Option ListNode'rn
  deriving Inhabited, Repr, BEq

instance : PastaLean.PyTruthy ListNode'rn where truthy _ := true

instance : PastaLean.PyBool ListNode'rn where pyBool _ := true

instance : PastaLean.PyTyped ListNode'rn where pyTypeOf _ := TypeInfer.PyType.cls "ListNode"

instance : Coe ListNode'rn (Option ListNode'rn) :=
  ⟨some⟩

def ListNode'rn.new (val : Int := (0 : Int)) (next : Option ListNode'rn := Option.none) : ListNode'rn :=
  ({ val := val, next := next } : ListNode'rn)

-- Param annotated as a bare `ListNode` (NOT `Optional`), but `head = head.next` makes it nullable —
-- inference must widen the cursor to `Option ListNode` and the run twin must suffix the param class.
def get_decimal := fun (head : Option ListNode) ↦
  Id.run
    (do
      let mut head := head
      let mut ans : Int := (0 : Int)
      while (PastaLean.pyTruthy head) do
        ans := PastaLean.pyBitOr (PastaLean.pyShiftLeft ans (1 : Int)) ((head).getD default).val
        head := ((head).getD default).next
      return ans)

attribute [simp, taste_ingr] get_decimal

def get_decimal'rn := fun (head : Option ListNode'rn) ↦
  Id.run
    (do
      let mut head := head
      let mut ans : Int := (0 : Int)
      while (PastaLean.pyTruthy head) do
        ans := PastaLean.pyBitOr (PastaLean.pyShiftLeft ans (1 : Int)) ((head).getD default).val
        head := ((head).getD default).next
      return ans)

-- `-> int` DPs whose `inf` sentinel makes the value `int | float`; they return an `int` whenever the
-- target is reachable, which is what CPython prints.
def inf_dp := fun (cost : List Int) ↦
  Id.run
    (do
      -- Canonical `[inf]*n` DP: `inf` adapts to the container's float type across both twins.
      let mut n : Int := PastaLean.pyLen cost
      let mut dp : List Int := PastaLean.pyListRepeat [inf] (n +ₚ (1 : Int))
      dp := PastaLean.pySetItem dp (0 : Int) (0 : Int)
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int)) do
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
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int)) do
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
      for hb'i : i in (PastaLean.pyRange n) do
        let p'_setval_1 := PastaLean.pyListGetProof houses i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
        f := PastaLean.pyModifyItem f i (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (1 : Int) p'_setval_1)
        for j in (PastaLean.pyRange (i +ₚ (2 : Int)) (2 : Int)) do
          for p in (PastaLean.pyRange i) do
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
      for hb'i : i in (PastaLean.pyRange n) do
        let p'_setval_1 := PastaLean.pyListGetProof houses i (PastaLean.pyRange_len_bound_of_eq rfl hb'i)
        f := PastaLean.pyModifyItem f i (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (1 : Int) p'_setval_1)
        for j in (PastaLean.pyRange (i +ₚ (2 : Int)) (2 : Int)) do
          for p in (PastaLean.pyRange i) do
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
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int)) do
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
      for i in (PastaLean.pyRange (n +ₚ (1 : Int)) (1 : Int)) do
        dp := PastaLean.pySetItem dp i (PastaLean.pyMin [dp⦋i -ₚ (1 : Int)⦌ +ₚ cost⦋i -ₚ (1 : Int)⦌, dp⦋i⦌])
      let p'_ret_1 := if dp⦋n⦌ ≥ inf then -(1 : Int) else dp⦋n⦌
      return p'_ret_1)

def coin_change := fun (coins : List Int) ↦ fun (amount : Int) ↦
  Id.run
    (do
      let mut inf := PastaLean.pyNonFinite "inf"
      let mut m : Int := PastaLean.pyLen coins
      let mut n : Int := amount
      let mut f : List (List Int) :=
        (PastaLean.pyRange (m +ₚ (1 : Int))).map fun (_ : Int) => PastaLean.pyListRepeat [inf] (n +ₚ (1 : Int))
      let p'_setval_1 := (0 : Int)
      f := PastaLean.pyModifyItem f (0 : Int) (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (0 : Int) p'_setval_1)
      for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate coins (1 : Int))) do
        let i := Prod.fst p'_pair_1
        let x := Prod.snd p'_pair_1
        for j in (PastaLean.pyRange (n +ₚ (1 : Int))) do
          let p'_setval_2 := f⦋i -ₚ (1 : Int)⦌⦋j⦌
          f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
          if h_1 : j ≥ x then 
            let p'_setval_3 := PastaLean.pyMin [f⦋i⦌⦋j⦌, f⦋i⦌⦋j -ₚ x⦌ +ₚ (1 : Int)]
            f := PastaLean.pyModifyItem f i (fun p'_row_3 => PastaLean.pySetItem p'_row_3 j p'_setval_3)
      let p'_ret_1 := if f⦋m⦌⦋n⦌ ≥ inf then -(1 : Int) else f⦋m⦌⦋n⦌
      return p'_ret_1)

attribute [simp, taste_ingr] coin_change

def coin_change'rn := fun (coins : List Int) ↦ fun (amount : Int) ↦
  Id.run
    (do
      let mut inf := PastaLean.pyNonFinite "inf"
      let mut m : Int := PastaLean.pyLen coins
      let mut n : Int := amount
      let mut f : Array (Array Int) :=
        ((PastaLean.pyRange (m +ₚ (1 : Int))).map fun (_ : Int) =>
            PastaLean.pyArrayRepeat #[inf] (n +ₚ (1 : Int))) |>.toArray
      let p'_setval_1 := (0 : Int)
      f := PastaLean.pyModifyItem f (0 : Int) (fun p'_row_1 => PastaLean.pySetItem p'_row_1 (0 : Int) p'_setval_1)
      for p'_pair_1 in (PastaLean.pyIter (PastaLean.pyEnumerate coins (1 : Int))) do
        let i := Prod.fst p'_pair_1
        let x := Prod.snd p'_pair_1
        for j in (PastaLean.pyRange (n +ₚ (1 : Int))) do
          let p'_setval_2 := f⦋i -ₚ (1 : Int)⦌⦋j⦌
          f := PastaLean.pyModifyItem f i (fun p'_row_2 => PastaLean.pySetItem p'_row_2 j p'_setval_2)
          if h_1 : j ≥ x then 
            let p'_setval_3 := PastaLean.pyMin [f⦋i⦌⦋j⦌, f⦋i⦌⦋j -ₚ x⦌ +ₚ (1 : Int)]
            f := PastaLean.pyModifyItem f i (fun p'_row_3 => PastaLean.pySetItem p'_row_3 j p'_setval_3)
      let p'_ret_1 := if f⦋m⦌⦋n⦌ ≥ inf then -(1 : Int) else f⦋m⦌⦋n⦌
      return p'_ret_1)

def main' :=
  ((do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (inf_dp [(3 : Int), (1 : Int), (4 : Int)])]
      let _ ←
        PastaLean.ProofMode.pyPrintProof
            [pyPrintArg (grid_inf_dp [(1 : Int), (4 : Int), (8 : Int), (10 : Int), (20 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (dp_sentinel_return [(2 : Int), (7 : Int), (1 : Int)])]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (coin_change [(1 : Int), (2 : Int), (5 : Int)] (11 : Int))]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg (coin_change [(2 : Int)] (3 : Int))]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let _ ← pyPrintIO [pyPrintArg (inf_dp'rn [(3 : Int), (1 : Int), (4 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (grid_inf_dp'rn [(1 : Int), (4 : Int), (8 : Int), (10 : Int), (20 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (dp_sentinel_return'rn [(2 : Int), (7 : Int), (1 : Int)])]
      let _ ← pyPrintIO [pyPrintArg (coin_change'rn [(1 : Int), (2 : Int), (5 : Int)] (11 : Int))]
      let _ ← pyPrintIO [pyPrintArg (coin_change'rn [(2 : Int)] (3 : Int))]) :
    IO _)

def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()

end PastaLean.User.Root
