import TypeInfer.Theorem.Semilattice

/-!
# The precision order and `join` as least upper bound

The join induces the lattice's **precision order** `a ⊑ b := a ⊔ b = b` ("`b` is at least as informative
as `a`"). Main results:

* **`join_le`** — `join` is the LEAST upper bound for `⊑`: any common upper bound of `a` and `b`
  dominates `a ⊔ b`. With `le_join_left`/`le_join_right` this is `join = ⊔`.
* **`join_mono`** — `join` is monotone in both arguments jointly. Monotone joins are exactly the
  Knaster–Tarski precondition that makes the inference fixpoint a *least* fixpoint.

`⊑` is also shown to be a partial order (`le_refl`, `le_trans`, `le_antisymm`). Reflexivity needs
idempotence, so it is stated on the engine's `normalized` types (as `join_idem` is); antisymmetry,
transitivity, the universal property, and monotonicity hold on the full lattice.
-/

namespace TypeInfer.PyType

set_option maxHeartbeats 4000000

/-- Precision order: `a ⊑ b` iff joining `a` into `b` adds nothing — `b` already subsumes `a`. -/
def le (a b : PyType) : Prop := join a b = b

@[inherit_doc le] scoped infix:50 " ⊑ " => le

theorem le_refl {a : PyType} (ha : normalized a) : a ⊑ a := join_idem a ha

theorem le_trans {a b c : PyType} (h1 : a ⊑ b) (h2 : b ⊑ c) : a ⊑ c := by
  show join a c = c
  rw [← h2, ← join_assoc, h1]

theorem le_antisymm {a b : PyType} (h1 : a ⊑ b) (h2 : b ⊑ a) : a = b := by
  rw [← h1, join_comm a b, h2]

/-- `a ⊔ b` is an upper bound of `a` (for `normalized a`). -/
theorem le_join_left {a : PyType} (ha : normalized a) (b : PyType) : a ⊑ join a b := by
  show join a (join a b) = join a b
  rw [← join_assoc, join_idem a ha]

/-- `a ⊔ b` is an upper bound of `b` (for `normalized b`). -/
theorem le_join_right {b : PyType} (hb : normalized b) (a : PyType) : b ⊑ join a b := by
  show join b (join a b) = join a b
  rw [join_comm a b, ← join_assoc, join_idem b hb]

--------------------------------------- LANDMARK ---------------------------------------
/-- **Least** upper bound: any common upper bound of `a` and `b` dominates their join. Together with
`le_join_left`/`le_join_right` this is `join = ⊔` (the least upper bound) for `⊑`. -/
theorem join_le {a b c : PyType} (h1 : a ⊑ c) (h2 : b ⊑ c) : join a b ⊑ c := by
  show join (join a b) c = c
  rw [join_assoc, h2, h1]
--------------------------------------- LANDMARK ---------------------------------------

/-- **Monotonicity** of `join` in its left argument: `a ⊑ a' → a ⊔ b ⊑ a' ⊔ b`. Monotone joins are
exactly what makes the inference fixpoint a *least* fixpoint (Knaster–Tarski), hence well-defined and
order-independent. -/
theorem join_mono_left {a a' : PyType} (b : PyType) (ha' : normalized a') (hb : normalized b)
    (h : a ⊑ a') : join a b ⊑ join a' b :=
  join_le (le_trans h (le_join_left ha' b)) (le_join_right hb a')

/-- `unknown` (⊥) is below everything in the precision order. -/
theorem le_unknown (a : PyType) : .unknown ⊑ a := join_unknown_left a

/-- `any` (⊤) is above everything. -/
theorem le_any (a : PyType) : a ⊑ .any := join_any_right a

/-- Monotonicity in the right argument (by commutativity). -/
theorem join_mono_right {b b' : PyType} (a : PyType) (ha : normalized a) (hb' : normalized b')
    (h : b ⊑ b') : join a b ⊑ join a b' := by
  rw [join_comm a b, join_comm a b']; exact join_mono_left a hb' ha h

--------------------------------------- LANDMARK ---------------------------------------
/-- Full **monotonicity** of `join`: it is monotone in both arguments jointly, so the whole reflow step
`x ↦ ⨆ (incoming types)` is a monotone map on the lattice — the Knaster–Tarski precondition. -/
theorem join_mono {a a' b b' : PyType} (ha' : normalized a') (hb : normalized b) (hb' : normalized b')
    (h1 : a ⊑ a') (h2 : b ⊑ b') : join a b ⊑ join a' b' :=
  le_trans (join_mono_left b ha' hb h1) (join_mono_right a' ha' hb' h2)
--------------------------------------- LANDMARK ---------------------------------------

end TypeInfer.PyType
