import TypeInfer.Theorem.PrecisionOrder

/-!
# Finite generation and an unconditional Knaster–Tarski fixpoint

`Height.lean` shows the *unrestricted* lattice violates ACC (infinite ascending chains via `optⁿ` or
`listⁿ ⊥`), so a fixpoint iteration cannot be claimed to terminate over all of `PyType`. Termination is
recovered by working over a *finite* carrier, which a fixed program's join-closure supplies. The proved
result here is that half:

* **`kt_iteration_reaches_fixpoint`** — **Knaster–Tarski on a finite carrier.** For any monotone
  `F : PyType → PyType` and any *finite* set `carrier` that contains `⊥ = unknown` and is closed under
  `F`, the Kleene iteration `⊥, F ⊥, F² ⊥, …` reaches a fixpoint (`F (Fᵏ ⊥) = Fᵏ ⊥`). No ACC on the
  whole lattice is needed — finiteness of the carrier is enough, and `join`'s monotonicity (`join_mono`)
  supplies the hypothesis. This is the honest, unconditional fixpoint theorem: it says *exactly* that the
  engine terminates as soon as its working set is finite.

The remaining half — that a fixed program's join-closure *is* a finite `carrier` — reduces to a nesting
bound `depth (a ⊔ b) ≤ max (depth a) (depth b) + 1` together with "join introduces no head constructor
or class name absent from its inputs" (so the closure lives in the finite set of types built from the
program's finitely many heads/class names up to depth `d + 1`, with tuple/function arities bounded by
those in the program). That bound is *true* but delicate to formalise: the extra layer is introduced
only by the `none`/`opt`-creating arms (`join none int = opt int`), so a uniform `≤ max + 1` induction
hypothesis is too loose in the `opt a, b` catch-all and a layer-tracking invariant is needed. It is left
as the next step; the fixpoint theorem above is stated so that, once the finite `carrier` is produced,
termination follows immediately.
-/

namespace TypeInfer.PyType

open Function

set_option maxHeartbeats 4000000

/-! ### Knaster–Tarski on a finite carrier -/

--------------------------------------- LANDMARK ---------------------------------------
/-- **Knaster–Tarski, finite-carrier form.** A monotone map `F` on a finite set closed under `F` and
containing `⊥ = unknown` has its Kleene iteration `Fᵏ ⊥` reach a fixpoint. Termination comes purely from
finiteness of the carrier (which finite generation provides), not from any global height bound — the
unrestricted lattice has none. -/
theorem kt_iteration_reaches_fixpoint
    (F : PyType → PyType)
    (hmono : ∀ a b, a ⊑ b → F a ⊑ F b)
    (carrier : Finset PyType)
    (hbot : (PyType.unknown) ∈ carrier)
    (hclosed : ∀ x ∈ carrier, F x ∈ carrier) :
    ∃ k, F (F^[k] .unknown) = F^[k] .unknown := by
  by_contra hno
  push_neg at hno
  -- The iterates never stabilise: `Fⁿ⁺¹ ⊥ ≠ Fⁿ ⊥`.
  have hne : ∀ n, F^[n + 1] .unknown ≠ F^[n] .unknown := by
    intro n; rw [Function.iterate_succ_apply']; exact hno n
  -- Each iterate stays in the carrier.
  have hmem : ∀ n, F^[n] .unknown ∈ carrier := by
    intro n; induction n with
    | zero => simpa using hbot
    | succ k ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
  -- Consecutive iterates ascend: `Fⁿ ⊥ ⊑ Fⁿ⁺¹ ⊥`.
  have hstep : ∀ n, F^[n] .unknown ⊑ F^[n + 1] .unknown := by
    intro n; induction n with
    | zero => simpa using le_unknown (F^[1] .unknown)
    | succ k ih =>
        have h1 : F^[k + 1] .unknown = F (F^[k] .unknown) := Function.iterate_succ_apply' F k .unknown
        have h2 : F^[k + 2] .unknown = F (F^[k + 1] .unknown) := Function.iterate_succ_apply' F (k+1) .unknown
        rw [h2, h1]; exact hmono _ _ (h1 ▸ ih)
  -- Hence a strict, monotone chain: `i < j → Fⁱ ⊥ ⊑ Fʲ ⊥`.
  have hlt : ∀ j i, i < j → F^[i] .unknown ⊑ F^[j] .unknown := by
    intro j; induction j with
    | zero => intro i h; omega
    | succ k ih =>
        intro i h
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
        · exact le_trans (ih i h') (hstep k)
        · subst h'; exact hstep i
  -- Distinct indices give distinct iterates (a strict chain repeats nothing).
  have hne_pair : ∀ i j, i < j → F^[i] .unknown ≠ F^[j] .unknown := by
    intro i j hij heq
    rcases Nat.lt_or_ge (i + 1) j with h | h
    · have h1 : F^[i] .unknown ⊑ F^[i + 1] .unknown := hstep i
      have h2 : F^[i + 1] .unknown ⊑ F^[j] .unknown := hlt j (i + 1) h
      have h2' : F^[i + 1] .unknown ⊑ F^[i] .unknown := heq.symm ▸ h2
      exact hne i (le_antisymm h1 h2').symm
    · have hEq : i + 1 = j := by omega
      exact hne i (by rw [hEq]; exact heq.symm)
  have hinj : Function.Injective (fun n => F^[n] .unknown) := by
    intro a b hab
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact hne_pair a b h hab
    · exact hne_pair b a h hab.symm
  -- An injection `ℕ → carrier` into a finite set is impossible.
  haveI : Fintype {t : PyType // t ∈ carrier} := FinsetCoe.fintype carrier
  let g : ℕ → {t : PyType // t ∈ carrier} := fun n => ⟨F^[n] .unknown, hmem n⟩
  have hginj : Function.Injective g := fun a b h => hinj (Subtype.ext_iff.mp h)
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  exact hab (hginj heq)
--------------------------------------- LANDMARK ---------------------------------------

end TypeInfer.PyType
