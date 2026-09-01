import PastaLean.PyAPI.Core

/-!
# Heap runtime — core types

The runtime backing PastaLean's opt-in **reference semantics** (`--heap`). Ported from the
`heapsl-nightly` reference design (`HeapSL.lean`), with HeapSL's `String` error dimension replaced
by PastaLean's `PyException` so heap failures compose with translated Python exceptions.

This file is deliberately **Mathlib-free of the separation-logic machinery** (`Std.Tactic.Do`,
`vcgen`, `@[frameproc]`): that layer needs a newer toolchain and lives on a separate branch
(Phase 2). The shapes here (`Heap` carrying `store/next/wf`, `HeapM` as a `def` over `EStateM`,
`Storable` as a 2-param prism) are kept **identical to HeapSL** so the proof layer can bolt on
later without reworking this runtime.
-/

namespace PastaLean

/-- A user-facing typed reference; the phantom `α` records the intended kind. Defined **before** any
generated `Val` universe so struct constructors can carry `Ref` fields natively. -/
structure Ref (α : Type) where
  addr : Nat
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

/-! ## Stores and the heap -/

/-- A partial store over the value universe `V`: addresses to optionally-present values. `V` is a
parameter, so the whole runtime is generic in the stored value type — each generated program
instantiates it with its own `Val` (one constructor per user type). -/
abbrev Store (V : Type) := Nat → Option V

-- The value universe is a parameter throughout; a section `variable` auto-generalizes every
-- `Store V`/`Heap V`/`HeapM V` definition below over `V`.
variable {V : Type}

/-- Overwrite address `l` with `v` in a store. -/
def Store.update (s : Store V) (l : Nat) (v : V) : Store V :=
  fun n => if n = l then some v else s n

/-- The singleton store holding `v` at `l`. -/
def Store.single (l : Nat) (v : V) : Store V := fun n => if n = l then some v else none

/-- The heap: a store, a fresh-address counter, and a **well-formedness** proof that every address
at or above `next` is unallocated. Making `wf` a field means every heap in scope is structurally
well-formed, so `next` is *globally* fresh — which is exactly what lets `alloc` frame soundly in the
Phase-2 separation logic. `wf` is a `Prop`, so proof irrelevance keeps it from interfering. -/
structure Heap (V : Type) where
  store : Store V
  next  : Nat
  wf    : ∀ a, a ≥ next → store a = none

/-- Allocating at the frontier `next` and bumping it preserves well-formedness. -/
theorem wf_alloc (h : Heap V) (v : V) :
    ∀ a, a ≥ h.next + 1 → (Store.update h.store h.next v) a = none := by
  intro a ha; simp only [Store.update, ite_eq_right (show a ≠ h.next by omega)]; exact h.wf a (by omega)

/-- Writing at `l` while pushing the frontier past `l` preserves well-formedness. -/
theorem wf_write (h : Heap V) (l : Nat) (v : V) :
    ∀ a, a ≥ max h.next (l + 1) → (Store.update h.store l v) a = none := by
  intro a ha; simp only [Store.update, ite_eq_right (show a ≠ l by omega)]; exact h.wf a (by omega)

/-! ## The heap monad

The base monad is `EStateM PyException (Heap V)` — state + exception. `EStateM`'s default
`Backtrackable` for the state is `nonBacktrackable` (`restore s _ := s`), so a caught exception
**keeps** the heap mutations that happened before the `raise` — matching Python (objects allocated
or mutated inside a `try` remain visible in the `except` handler). See `PALC/PyAPI/TestHeap.lean` for
the regression that pins this. -/

/-- The base monad: state + exception. `EStateM` (rather than `ExceptT PyException (StateM Heap)`)
mirrors HeapSL so its `get`/`set`/`modifyGet`/`throw` wp simp lemmas apply in Phase 2. -/
abbrev HeapBase (V : Type) := EStateM PyException (Heap V)

/-- The heap monad. A `def` (not `abbrev`) so Phase 2 can attach its *own* frame-internalizing `WP`
distinct from the base `HeapBase` instance. -/
def HeapM (V : Type) (α : Type) : Type := HeapBase V α

instance : Monad (HeapM V) := inferInstanceAs (Monad (HeapBase V))
instance : LawfulMonad (HeapM V) := inferInstanceAs (LawfulMonad (HeapBase V))
instance : MonadStateOf (Heap V) (HeapM V) := inferInstanceAs (MonadStateOf (Heap V) (HeapBase V))
instance : MonadExceptOf PyException (HeapM V) :=
  inferInstanceAs (MonadExceptOf PyException (HeapBase V))

/-- A `HeapM` program as its underlying base program. -/
def HeapM.run {α : Type} (x : HeapM V α) : HeapBase V α := x

end PastaLean
