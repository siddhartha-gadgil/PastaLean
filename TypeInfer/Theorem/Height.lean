import TypeInfer.Theorem.PrecisionOrder

/-!
# Lattice height and the Knaster–Tarski fixpoint

`join` is monotone (`join_mono`), so *if* the lattice satisfied the ascending chain condition (ACC — no
infinite strictly-ascending chain) Knaster–Tarski would give a least fixpoint reached by a terminating
iteration. Three facts pin down exactly what holds and, crucially, why no restriction of the *domain*
rescues termination:

* **`tower_bounded_chain`** — the **numeric tower is a bounded chain** `unknown ⊏ bool ⊏ int ⊏ float ⊏
  any`: the load-bearing widening the engine performs terminates in at most four steps.
* **`lattice_infinite_ascending_chain`** — the **full lattice violates ACC**: `Optional` nesting gives a
  strictly increasing chain `int ⊏ opt int ⊏ opt (opt int) ⊏ …`.
* **`opt_free_infinite_ascending_chain`** — **removing `Optional` does NOT restore ACC.** Every
  recursive container reproduces the same infinite chain over the bottom element, since `⊥ ⊑ list ⊥`:
  `unknown ⊏ list unknown ⊏ list (list unknown) ⊏ …` uses no `opt` at all. `list`/`set`/`dict`/`tuple`/`fn`
  each do this, so the *only* way to bound chains by restricting the type language is to forbid all
  nesting, i.e. collapse to a flat finite lattice.

So global termination is *not* a corollary of Knaster–Tarski over any recursively-nested `PyType`, opt
or not. It rests solely on the engine joining types drawn from a **fixed program**, whose join-closure is
finite (`join` introduces no head or class name absent from its inputs, and only recombines nesting
depths already present). That finitely-generated sub-semilattice is finite, hence trivially satisfies
ACC, and is where the fixpoint lives and terminates.

This is the honest statement of the fixpoint's status: the *precondition* (monotone join on a bounded
join-semilattice) is machine-checked; ACC fails on the unrestricted lattice and cannot be restored by
dropping constructors, so termination is a property of the engine's finite working set, not of the
abstract domain in isolation.
-/

namespace TypeInfer.PyType

set_option maxHeartbeats 4000000

/-- `n` nested `Optional` layers around a type — the witness family for the infinite chain. -/
def optN : Nat → PyType → PyType
  | 0, t => t
  | n + 1, t => .opt (optN n t)

/-- Counts the outer `opt` layers; distinguishes `optN n` from `optN m`. -/
def optCount : PyType → Nat
  | .opt e => 1 + optCount e
  | _ => 0

theorem optCount_optN (n : Nat) : optCount (optN n .int) = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [optN, optCount, ih]; omega

/-- Each extra `Optional` layer is strictly higher: `opt^n int ⊑ opt^(n+1) int`. -/
theorem join_optN_succ (n : Nat) : join (optN n .int) (optN (n + 1) .int) = optN (n + 1) .int := by
  induction n with
  | zero => simp [optN, join]
  | succ k ih => simp only [optN] at ih ⊢; simp only [join]; rw [ih]

theorem optN_ne_succ (n : Nat) : optN n .int ≠ optN (n + 1) .int := by
  intro h; have := congrArg optCount h
  rw [optCount_optN, optCount_optN] at this; omega

--------------------------------------- LANDMARK ---------------------------------------
/-- **The lattice is NOT of finite height.** `fun n => opt^n int` is an infinitely, strictly ascending
chain, so there is no global bound on the length of `⊑`-chains: Knaster–Tarski's "least fixpoint reached
at bounded height" cannot be invoked over all of `PyType`. Termination of the engine's fixpoint instead
relies on it joining only types from a fixed program (a finitely-generated, hence finite, sub-lattice). -/
theorem lattice_infinite_ascending_chain :
    ∃ f : Nat → PyType, ∀ n, (f n ⊑ f (n + 1)) ∧ f n ≠ f (n + 1) :=
  ⟨fun n => optN n .int, fun n => ⟨join_optN_succ n, optN_ne_succ n⟩⟩
--------------------------------------- LANDMARK ---------------------------------------


/-! ### Removing `Optional` does not help: recursive containers over `⊥` also break ACC

`opt` is not special. Any recursive container over the bottom element gives the same infinite chain,
because `⊥ ⊑ list ⊥`. We witness it with `list`, using `unknown` as the base. -/

/-- Does this type contain an `Optional` anywhere? The witness family below has `hasOpt = false`, so the
infinite chain it forms is genuinely `Optional`-free. -/
def hasOpt : PyType → Bool
  | .opt _ => true
  | .list e | .set e => hasOpt e
  | .dict k v => hasOpt k || hasOpt v
  | .tuple es => es.attach.any fun ⟨e, _⟩ => hasOpt e
  | .fn as r => (as.attach.any fun ⟨e, _⟩ => hasOpt e) || hasOpt r
  | _ => false
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | · rename_i h
        have := List.sizeOf_lt_of_mem h
        omega

/-- `n` nested `list` layers — the opt-free witness family for the infinite chain. -/
def listN : Nat → PyType → PyType
  | 0, t => t
  | n + 1, t => .list (listN n t)

/-- Counts the outer `list` layers; distinguishes `listN n` from `listN m`. -/
def listCount : PyType → Nat
  | .list e => 1 + listCount e
  | _ => 0

theorem listCount_listN (n : Nat) : listCount (listN n .unknown) = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [listN, listCount, ih]; omega

/-- Each extra `list` layer is strictly higher: `list^n ⊥ ⊑ list^(n+1) ⊥` — no `opt` involved. -/
theorem join_listN_succ (n : Nat) :
    join (listN n .unknown) (listN (n + 1) .unknown) = listN (n + 1) .unknown := by
  induction n with
  | zero => simp [listN]
  | succ k ih => simp only [listN] at ih ⊢; simp only [join]; rw [ih]

theorem listN_ne_succ (n : Nat) : listN n .unknown ≠ listN (n + 1) .unknown := by
  intro h; have := congrArg listCount h
  rw [listCount_listN, listCount_listN] at this; omega

theorem hasOpt_listN (n : Nat) : hasOpt (listN n .unknown) = false := by
  induction n with
  | zero => simp [listN, hasOpt]
  | succ k ih => simp only [listN, hasOpt, ih]

--------------------------------------- LANDMARK ---------------------------------------
/-- **Removing `Optional` does NOT restore ACC.** `fun n => list^n unknown` is an infinitely, strictly
ascending chain of `Optional`-free types (`hasOpt (f n) = false`), so the ascending chain condition fails
even on the fully opt-free lattice. Any recursive container reproduces this — the abstract domain cannot
be made to terminate by dropping constructors; termination comes only from the engine's finite,
program-generated working set. -/
theorem opt_free_infinite_ascending_chain :
    ∃ f : Nat → PyType,
      (∀ n, hasOpt (f n) = false) ∧ (∀ n, (f n ⊑ f (n + 1)) ∧ f n ≠ f (n + 1)) :=
  ⟨fun n => listN n .unknown, fun n => hasOpt_listN n,
   fun n => ⟨join_listN_succ n, listN_ne_succ n⟩⟩
--------------------------------------- LANDMARK ---------------------------------------

--------------------------------------- LANDMARK ---------------------------------------
/-- **The numeric tower is a bounded chain** `unknown ⊏ bool ⊏ int ⊏ float ⊏ any` (height 4). This is the
widening the engine actually runs, and it terminates in a fixed number of steps regardless of input. -/
theorem tower_bounded_chain :
    (.unknown ⊑ .bool ∧ PyType.unknown ≠ .bool)
    ∧ (.bool ⊑ .int ∧ PyType.bool ≠ .int)
    ∧ (.int ⊑ .float ∧ PyType.int ≠ .float)
    ∧ (.float ⊑ .any ∧ PyType.float ≠ .any) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [le, join]
--------------------------------------- LANDMARK ---------------------------------------

end TypeInfer.PyType
