import TypeInfer.PyType

/-!
# `BEq PyType` is lawful

`PyType.lean` defines `beq` and installs `instance : BEq PyType := ⟨beq⟩`, but nothing proved the two
directions that make a `BEq` usable in a *proof*: `a == b` has to mean `a = b`. Without that, a
`Bool`-valued check over types yields a claim no theorem can consume, and `decide (a = b)` is not
available at all — `deriving DecidableEq` does not apply to `PyType`, whose `tuple`/`fn` nodes recurse
through `List PyType`.

So this file proves `LawfulBEq PyType`, which also hands over `DecidableEq PyType` through
`instDecidableEqOfLawfulBEq`. It is deliberately **Mathlib-free and on the default build path**,
unlike `TypeInfer/Theorem/`, because the certificate validator
(`TypeInfer/Certificate/Check.lean`) ships in the Mathlib-free `typeinfer` binary and decides type
equalities for a living.

`beq` recurses over the nested `tuple`/`fn` with size-based recursion, so `PyType` has no plain
structural induction: both facts go by well-founded recursion mirroring `beq` itself, exactly as
`TypeInfer/Theorem/Consistency.lean` does for `consistent`. `zip_self_eq` and `beq_refl` moved here
from that file, which now imports them.
-/

namespace TypeInfer.PyType

set_option maxHeartbeats 1000000

/-- On `as.zip as` both components of every pair coincide. -/
theorem zip_self_eq {a b : PyType} {as : List PyType} (h : (a, b) ∈ as.zip as) : a = b := by
  induction as with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · simp_all
      · exact ih h

/-- Two equal-length lists whose zipped pairs are componentwise equal are the same list. This is what
the `tuple`/`fn` cases of `eq_of_beq` reduce to: `beq` compares element by element through
`as.zip bs`, and recovering `as = bs` from that is a plain list induction. -/
theorem eq_of_zip_eq : ∀ (as bs : List PyType), as.length = bs.length →
    (∀ p ∈ as.zip bs, p.1 = p.2) → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | a :: as, b :: bs, hlen, h => by
      have hab : a = b := h (a, b) (by simp)
      have hrest : as = bs :=
        eq_of_zip_eq as bs (by simpa using hlen)
          (fun p hp => h p (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr hp))
      rw [hab, hrest]

/-! ### The two directions -/

theorem beq_refl : (a : PyType) → beq a a = true
  | .unknown | .any | .int | .bool | .str | .float | .none => by simp [beq]
  | .list e | .set e | .opt e => by simp only [beq]; exact beq_refl e
  | .dict k v => by simp only [beq, beq_refl k, beq_refl v, Bool.and_self]
  | .cls n => by simp only [beq, beq_self_eq_true]
  | .tuple es => by
      simp only [beq, beq_self_eq_true, Bool.true_and, List.all_eq_true]
      intro p _
      obtain ⟨⟨a, b⟩, hmem⟩ := p
      obtain rfl := zip_self_eq hmem
      exact beq_refl a
  | .fn as r => by
      simp only [beq, beq_self_eq_true, Bool.true_and, beq_refl r, Bool.and_true, List.all_eq_true]
      intro p _
      obtain ⟨⟨a, b⟩, hmem⟩ := p
      obtain rfl := zip_self_eq hmem
      exact beq_refl a
  termination_by a => sizeOf a
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem (List.of_mem_zip ‹_ ∈ List.zip _ _›).1; omega)

/-- `beq` decides equality: a `true` really is an equation. The catch-all `_, _ => false` arm of `beq`
carries the content — a `true` there is impossible, so every surviving pair shares a constructor and
the recursion closes it. -/
theorem eq_of_beq : ∀ (a b : PyType), beq a b = true → a = b := by
  intro a b
  induction a, b using PyType.beq.induct with
  | case1 | case2 | case3 | case4 | case5 | case6 | case7 => intro _; rfl
  | case8 x y ih => intro h; rw [ih (by simpa only [beq] using h)]
  | case9 x y ih => intro h; rw [ih (by simpa only [beq] using h)]
  | case10 x y ih => intro h; rw [ih (by simpa only [beq] using h)]
  | case11 k₁ v₁ k₂ v₂ ihk ihv =>
      intro h
      simp only [beq, Bool.and_eq_true] at h
      rw [ihk h.1, ihv h.2]
  | case12 x y => intro h; simp only [beq, beq_iff_eq] at h; rw [h]
  | case13 as bs ih =>
      intro h
      simp only [beq, beq_iff_eq, Bool.and_eq_true, List.all_eq_true] at h
      refine congrArg PyType.tuple (eq_of_zip_eq as bs h.1 ?_)
      intro p hp
      obtain ⟨x, y⟩ := p
      exact ih x y hp (h.2 ⟨(x, y), hp⟩ (List.mem_attach _ _))
  | case14 as r₁ bs r₂ ih ihr =>
      intro h
      simp only [beq, beq_iff_eq, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨⟨hlen, hall⟩, hret⟩ := h
      have hs : as = bs := by
        refine eq_of_zip_eq as bs hlen ?_
        intro p hp
        obtain ⟨x, y⟩ := p
        exact ih x y hp (hall ⟨(x, y), hp⟩ (List.mem_attach _ _))
      rw [hs, ihr hret]
  | case15 x y => intro h; cases x <;> cases y <;> simp_all [beq]

instance : LawfulBEq PyType where
  eq_of_beq {a b} h := eq_of_beq a b h
  rfl {a} := beq_refl a

/-- What the lawfulness was for: `decide (a = b)` on types, which `deriving DecidableEq` cannot
produce for `PyType` and which every `Bool` check in the certificate validator needs in order to hand
a real equation to `TypeInfer/Theorem/Certificate.lean`. -/
instance : DecidableEq PyType := instDecidableEqOfLawfulBEq

end TypeInfer.PyType
