import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

-- Early-return linear search (mirrors early_return_break.lean): return the first index whose value
-- equals k, or -1. The loop invariant is "k absent from the prefix scanned so far".
def find_first := fun (xs : List Int) ↦ fun (k : Int) ↦
  (do
    for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
      let _ := Libraries.passta.pyPassInvariant !(PastaLean.pyContains (PastaLean.pySlice xs none (some i) none) k)
      if h_1 : xs⦋i⦌ = k then
        return i
      else
        let _ := ()
    let __py_ret_1 := -(1 : Int)
    return __py_ret_1 : Id _)

-- The current index sits strictly inside the iterated range, so it is `< n`. mvcgen hands the loop
-- body the cursor as an append split `List.range n = pref ++ cur :: suff`; grind doesn't read a bound
-- out of that on its own.
@[grind →] theorem range_mid_lt {n cur : Nat} {pref suff : List Nat}
    (h : List.range n = pref ++ cur :: suff) : cur < n := by
  have : cur ∈ List.range n := by rw [h]; simp
  exact List.mem_range.mp this

-- In bounds, PastaLean's Python-indexing `xs⦋↑j⦌` (negative-index + panic aware) is the plain element.
@[grind =] theorem pyListGetItem_ofNat (xs : List Int) (j : Nat) (h : j < xs.length) :
    xs⦋(Int.ofNat j)⦌ = xs[j] := by
  show PastaLean.pyListGetItem xs (Int.ofNat j) = xs[j]
  unfold PastaLean.pyListGetItem
  simp only [Int.ofNat_eq_coe]
  simp only [if_neg (show ¬ ((j : Int) < 0) by omega)]
  have hlen : xs.length ≠ 0 := by omega
  rw [if_neg (show ¬ ((xs.length == 0) = true) by simp [hlen]),
      if_neg (show ¬ ((((j : Int) < 0) || ((j : Int) ≥ (xs.length : Int))) = true) by simp; omega),
      show ((j : Int)).toNat = j by omega, List.getElem?_eq_getElem h]

-- If k differs from every in-range element, it is absent from the list. This is exactly the shape
-- of the loop's continue invariant at exit (prefix = the whole `List.range (pyLen xs).toNat`).
@[grind ←] theorem not_mem_of_range_ne {xs : List Int} {k : Int}
    (H : ∀ j ∈ List.range (PastaLean.pyLen xs).toNat, xs⦋Int.ofNat j⦌ ≠ k) : k ∉ xs := by
  intro hk
  obtain ⟨j, hj, hjk⟩ := List.mem_iff_getElem.mp hk
  have hlen : (PastaLean.pyLen xs).toNat = xs.length := by
    show ((xs.length : Int)).toNat = xs.length; simp
  refine H j ?_ ?_
  · rw [List.mem_range, hlen]; exact hj
  · rw [pyListGetItem_ofNat xs j hj]; exact hjk

theorem find_first_spec :
    ⦃⌜True⌝⦄ find_first xs k
    ⦃⇓ r => ⌜ (r = -1 → k ∉ xs) ∧
             (r ≠ -1 → 0 ≤ r ∧ r < PastaLean.pyLen xs ∧ xs⦋r⦌ = k) ⌝⦄ :=
  by
  mvcgen [find_first, PastaLean.pyRange_forIn, PastaLean.pyRange_forIn_start]
  invariants
    · Invariant.withEarlyReturnNewDo
        (onReturn := fun r _ => ⌜ 0 ≤ r ∧ r < PastaLean.pyLen xs ∧ xs⦋r⦌ = k ⌝)
        (onContinue := fun cur _ => ⌜ ∀ j ∈ cur.prefix, xs⦋Int.ofNat j⦌ ≠ k ⌝)
  with grind

def find_first'rn := fun (xs : List Int) ↦ fun (k : Int) ↦
  Id.run
    (do
      for i in (PastaLean.pyRange (PastaLean.pyLen xs))do
        let _ := Libraries.passta.pyPassInvariant !(PastaLean.pyContains (PastaLean.pySlice xs none (some i) none) k)
        if h_1 : xs⦋i⦌ == k then
          return i
        else
          let _ := ()
      let __py_ret_1 := -(1 : Int)
      return __py_ret_1)
