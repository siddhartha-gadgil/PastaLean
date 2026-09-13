import TypeInfer.Theorem.Associativity
import TypeInfer.Theorem.Semilattice
import TypeInfer.Theorem.PrecisionOrder
import TypeInfer.Theorem.Height
import TypeInfer.Theorem.FiniteGeneration
import TypeInfer.Theorem.Soundness
import TypeInfer.Theorem.Consistency

/-!
# Correctness theorems for the TypeInfer lattice

The inference engine folds `PyType.join` over the types it observes (`joinAll`, and the `collectSigs`
fixpoint). For that fold to be well-defined and — crucially — **order-independent**, `join` must behave
as a bounded join-semilattice, and the abstract-interpretation literature is specific about what such an
analysis has to satisfy. Each requirement is proved in Lean, with no `sorry`. This module re-exports the
whole development; each file is named for its main result:

* `TypeInfer.Theorem.Associativity` — `join_comm`, `join_assoc` (+ `⊥`/`⊤` laws, `sizeOf_pos`).
* `TypeInfer.Theorem.Semilattice` — `join_idem` (bounded join-semilattice), `join_opt_any` subtlety,
  information preservation (`join_eq_unknown_iff`).
* `TypeInfer.Theorem.PrecisionOrder` — `join_le` (least upper bound), `join_mono` (monotonicity), and
  the partial order `⊑`.
* `TypeInfer.Theorem.Height` — `tower_bounded_chain`, `lattice_infinite_ascending_chain`, and
  `opt_free_infinite_ascending_chain`: the honest Knaster–Tarski status (bounded numeric core; ACC fails
  on the full lattice, and dropping `Optional` does not restore it — recursive containers over `⊥` break
  it too, so termination rests only on the finite program-generated sub-lattice).
* `TypeInfer.Theorem.FiniteGeneration` — `kt_iteration_reaches_fixpoint`: Knaster–Tarski on a finite
  carrier — the engine's fixpoint iteration reaches a least fixpoint once its working set is finite (which
  a fixed program's join-closure supplies), with no global ACC needed.
* `TypeInfer.Theorem.Soundness` — `hasType_join_left`: widening never excludes an admitted runtime value.
* `TypeInfer.Theorem.Consistency` — `consistent_refl`/`consistent_symm`/`consistent_not_trans` (gradual
  typing) and the `reconcile` coercion totality.
-/
