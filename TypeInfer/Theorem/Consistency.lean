import PastaLean.Imports
import TypeInfer.PyType

/-!
# Gradual-typing consistency (`consistent`) and coercions (`reconcile`)

The join lattice governs how the engine MERGES types; `consistent` governs whether a value of one type
may FLOW where another is expected, and `reconcile` picks the coercion that makes it fit.

Main result: **`consistent_not_trans`** — `consistent` is the gradual-typing consistency relation (Siek
& Taha): reflexive (`consistent_refl`) and symmetric (`consistent_symm`) but crucially **not
transitive**. A boxed (`any`) value flows anywhere, yet that does not make two unrelated concrete types
interchangeable. Non-transitivity is exactly what separates gradual typing from subtyping.

`beq`/`consistent` recurse over the nested `tuple`/`fn` with size-based recursion, so `PyType` has no
plain structural induction: the diagonal facts (`beq_refl`, `consistent_refl`) go by well-founded
recursion mirroring the functions themselves, and the symmetric facts drive each function's `.induct`
principle and close the nested list cases with the `zip` helpers below.
-/

namespace TypeInfer.PyType

set_option maxHeartbeats 4000000

/-- On `as.zip as` both components of every pair coincide. -/
theorem zip_self_eq {a b : PyType} {as : List PyType} (h : (a, b) ∈ as.zip as) : a = b := by
  induction as with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · simp_all
      · exact ih h

/-- `List.all` of a symmetric `Bool` op is the same over `as.zip bs` and `bs.zip as` — what the
`tuple`/`fn` cases of `beq`/`consistent` symmetry reduce to once the outer function is unfolded. -/
theorem all_zip_comm (f : PyType → PyType → Bool) : ∀ (as bs : List PyType),
    (∀ a b, (a, b) ∈ as.zip bs → f a b = f b a) →
    (as.zip bs).all (fun p => f p.1 p.2) = (bs.zip as).all (fun p => f p.1 p.2)
  | [], bs, _ => by cases bs <;> rfl
  | _ :: _, [], _ => rfl
  | a :: as', b :: bs', ih => by
      simp only [List.zip_cons_cons, List.all_cons]
      rw [ih a b (by simp),
          all_zip_comm f as' bs' fun x y h => ih x y (by
            simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr h)]


/-! ### `beq` (structural equality) is reflexive and symmetric

`beq` has no absorption, so both hold on *all* of `PyType`. Reflexivity is a direct recursion; symmetry
drives `beq.induct` and closes the single `_, _ => false` catch-all by casing the two constructors (the
mismatch makes both sides `false`). -/

theorem beq_refl : (a : PyType) → beq a a = true
  | .unknown | .any | .int | .bool | .str | .float | .none => by simp [beq]
  | .list e | .set e | .opt e => by simp only [beq]; exact beq_refl e
  | .dict k v => by simp only [beq, beq_refl k, beq_refl v, Bool.and_self]
  | .cls n => by simp only [beq, beq_self_eq_true]
  | .tuple es => by
      simp only [beq, beq_self_eq_true, Bool.true_and, List.all_eq_true]
      rintro ⟨⟨a, b⟩, hmem⟩ _; obtain rfl := zip_self_eq hmem; exact beq_refl a
  | .fn as r => by
      simp only [beq, beq_self_eq_true, Bool.true_and, beq_refl r, Bool.and_true, List.all_eq_true]
      rintro ⟨⟨a, b⟩, hmem⟩ _; obtain rfl := zip_self_eq hmem; exact beq_refl a
  termination_by a => sizeOf a
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem (List.of_mem_zip ‹_ ∈ List.zip _ _›).1; omega)

theorem beq_comm (a b : PyType) : beq a b = beq b a := by
  induction a, b using PyType.beq.induct with
  | case15 x y => cases x <;> cases y <;> simp_all [beq]
  | _ =>
    simp_all only [beq] <;>
    first
    | rfl
    | grind
    | (simp only [List.all_subtype, List.unattach_attach]
       rw [all_zip_comm _ _ _ (by assumption)]; grind)


/-! ### `consistent` is a gradual-typing consistency relation -/

theorem consistent_any_l (t : PyType) : consistent .any t = true := by cases t <;> simp [consistent]
theorem consistent_any_r (t : PyType) : consistent t .any = true := by cases t <;> simp [consistent]
theorem consistent_unknown_r (t : PyType) : consistent t .unknown = true := by cases t <;> simp [consistent]

theorem consistent_refl : (a : PyType) → consistent a a = true
  | .unknown | .any | .int | .bool | .str | .float | .none => by simp [consistent, beq_refl]
  | .list e | .set e | .opt e => by simp only [consistent]; exact consistent_refl e
  | .dict k v => by simp only [consistent, consistent_refl k, consistent_refl v, Bool.and_self]
  | .cls n => by simp only [consistent, beq_refl]
  | .tuple es => by
      simp only [consistent, beq_self_eq_true, Bool.true_and, List.all_eq_true]
      rintro ⟨⟨a, b⟩, hmem⟩ _; obtain rfl := zip_self_eq hmem; exact consistent_refl a
  | .fn as r => by
      simp only [consistent, beq_self_eq_true, Bool.true_and, consistent_refl r, Bool.and_true,
        List.all_eq_true]
      rintro ⟨⟨a, b⟩, hmem⟩ _; obtain rfl := zip_self_eq hmem; exact consistent_refl a
  termination_by a => sizeOf a
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem (List.of_mem_zip ‹_ ∈ List.zip _ _›).1; omega)

/-- The **gradual guarantee**: the dynamic type `unknown` is consistent with every type, so a value
whose type we could not determine may flow anywhere. -/
theorem consistent_unknown (a : PyType) : consistent .unknown a = true := by cases a <;> simp [consistent]

theorem consistent_symm (a b : PyType) : consistent a b = consistent b a := by
  induction a, b using PyType.consistent.induct with
  | case19 a b => cases a <;> cases b <;> simp_all [consistent, beq] <;> grind
  | _ =>
    simp_all [consistent, beq_comm, consistent_any_l, consistent_any_r, consistent_unknown,
      consistent_unknown_r] <;>
    first
    | rfl
    | (simp only [List.all_subtype, List.unattach_attach]
       rw [all_zip_comm _ _ _ (by assumption)]; grind)
    | grind

--------------------------------------- LANDMARK ---------------------------------------
/-- Consistency is **not transitive** — the property that separates gradual typing from subtyping.
`int ~ any` and `any ~ str`, yet `int ≁ str`: boxing lets a value flow anywhere, but does not make two
unrelated concrete types interchangeable. -/
theorem consistent_not_trans :
    ¬ (∀ a b c : PyType, consistent a b → consistent b c → consistent a c) := by
  intro h
  have hbad : consistent .int .str :=
    h .int .any .str (by simp [consistent]) (by simp [consistent])
  simp [consistent, beq] at hbad
--------------------------------------- LANDMARK ---------------------------------------


/-! ### Coercions (`reconcile`) -/

/-- No coercion is inserted for a value that already has the expected type. -/
theorem reconcile_refl (a : PyType) : reconcile a a = .exact := by simp [reconcile, beq_refl]

/-- Every coercion decision is one of the finite, intended actions — the function is total, so a value
never gets "stuck" with no way to reach its expected type. -/
theorem reconcile_total (e a : PyType) :
    reconcile e a = .exact ∨ reconcile e a = .boolToInt ∨ reconcile e a = .intToFloat
      ∨ reconcile e a = .unwrapOpt ∨ reconcile e a = .box := by
  unfold reconcile
  repeat' split
  all_goals first
    | exact .inl rfl
    | exact .inr (.inl rfl)
    | exact .inr (.inr (.inl rfl))
    | exact .inr (.inr (.inr (.inl rfl)))
    | exact .inr (.inr (.inr (.inr rfl)))

end TypeInfer.PyType
