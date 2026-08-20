import Std.Tactic.Do

open Std.Do

def early_return (xs : List Nat) (k : Nat) : Id (Option Nat) := do
  for i in [0:xs.length] do
    if xs[i]! = k then
      return some i
  return none

@[grind ←]
theorem all_ne_not_mem {xs : List Nat} : (∀ (i : Nat), i ∈ [:xs.length].toList → ¬xs[i]?.getD 0 = k) → k ∉ xs := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    intro h ; simp
    and_intros
    · have := h 0 (by grind)
      grind
    · apply ih
      intro i h'
      have := h (i + 1) (by grind)
      grind

theorem early_return_thm : ⦃⌜ True ⌝⦄ early_return xs k ⦃⇓ pos => ⌜ pos.isSome ↔ k ∈ xs ⌝⦄ := by
  mvcgen [early_return]
  invariants
    · Invariant.withEarlyReturnNewDo
        (onReturn := fun x y => ⌜ ∃ v,  v < xs.length ∧ x = some v ∧ xs[v]! = k ⌝)
        (onContinue := fun cur y => ⌜ ∀ i ∈ cur.prefix, xs[i]! ≠ k ⌝)
  with grind

def break_ (xs : List Nat) (k : Nat) : Id (Option Nat) := do
  let mut res := none
  for i in [0:xs.length] do
    if xs[i]! = k then
      res := some i
      break
  return res

theorem break__thm : ⦃⌜ True ⌝⦄ break_ xs k ⦃⇓ pos => ⌜ pos.isSome ↔ k ∈ xs ⌝⦄ := by
  mvcgen [break_]
  invariants
    · ⇓ ⟨cursor, res⟩ =>
        ⌜ (∀ i ∈ cursor.prefix, i < xs.length) ∧
          (res = none → ∀ i ∈ cursor.prefix, xs[i]! ≠ k) ∧
          (∀ v, res = some v → v ∈ cursor.prefix ∧ v < xs.length ∧ xs[v]! = k) ⌝
  with (try grind)
  case vc4.post.success =>
    rename_i r h
    cases Option.eq_none_or_eq_some r
      <;> grind
