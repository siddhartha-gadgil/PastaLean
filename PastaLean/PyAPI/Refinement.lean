import PastaLean.PyAPI.Core
import PastaLean.PyAPI.Arrays
import PastaLean.PyAPI.CommonProtocols.Length
import PastaLean.PyAPI.CommonProtocols.GetItem

/-!
# Proof-carrying container access

`pyGetItem xs i` is *total by defaulting*: out of range it panics (or returns the `Inhabited`
default). That is the honest lowering when nothing is known about `i`. But the commonest Python
indexing idiom by far — `for i in range(len(xs)): … xs[i] …` — makes the index provably in range,
and Lean can carry that proof.

This file supplies the two halves:

* `pyRange_mem_bounds` turns loop MEMBERSHIP (`i ∈ pyRange n`, which `for h : i in …` hands the body
  for free) into the arithmetic bound `0 ≤ i ∧ i < n`, and `pyRange_len_bound` specialises it to the
  `range(len(xs))` shape so the whole side condition is one term the generator can emit.
* `pyListGetProof` / `pyArrayGetProof` consume that bound and index through Lean's own `xs[i]'h`.
  No `Inhabited`, no `panic!`, no defaulting branch — the access is total *because* it is proved,
  which is what makes the generated program reason about rather than merely run.

TypeInfer decides when this applies (`TypeInfer.Refine`); everything here is what it lowers to.
-/

namespace PastaLean

/-- Every element of `range(n)` lies in `[0, n)`. This is the bridge from the loop hypothesis Lean's
`for h : i in …` binds to the arithmetic side condition an indexing proof needs. -/
theorem pyRange_mem_bounds {n i : Int} (h : i ∈ pyRange n) : 0 ≤ i ∧ i < n := by
  unfold pyRange at h
  simp at h
  obtain ⟨a, ha, rfl⟩ := h
  omega

/-- The `for i in range(len(xs))` instance of `pyRange_mem_bounds`: `pyLen` on a list IS its length,
so the loop hypothesis already bounds `i` by `xs.length`. -/
theorem pyRange_len_bound {α : Type} {xs : List α} {i : Int}
    (h : i ∈ pyRange (pyLen xs)) : 0 ≤ i ∧ i < xs.length :=
  pyRange_mem_bounds h

/-- `pyRange_len_bound` through a LENGTH ALIAS: `n = len(xs)` once, then `for i in range(n)`. The
generated code discharges `hn` by `rfl`, which holds because the alias lowers to a plain `let`. -/
theorem pyRange_len_bound_of_eq {α : Type} {xs : List α} {n i : Int}
    (hn : n = pyLen xs) (h : i ∈ pyRange n) : 0 ≤ i ∧ i < xs.length := by
  subst hn; exact pyRange_len_bound h

/-- The array-backed counterpart of `pyRange_len_bound`. -/
theorem pyRange_size_bound {α : Type} {xs : Array α} {i : Int}
    (h : i ∈ pyRange (pyLen xs)) : 0 ≤ i ∧ i < xs.size :=
  pyRange_mem_bounds h

/-- `xs[i]` where the index is PROVED in range: total, no `Inhabited` default and no `panic!`
fallback, unlike `pyListGetItem`. `h` bounds the Python (`Int`) index, which `Int.toNat` then carries
to the `List.get` the proof discharges. -/
def pyListGetProof {α : Type} (xs : List α) (i : Int) (h : 0 ≤ i ∧ i < xs.length) : α :=
  xs[i.toNat]'(by omega)

/-- `pyListGetProof` for an array-backed list (see `PastaLean.PyAPI.Arrays`). -/
def pyArrayGetProof {α : Type} (xs : Array α) (i : Int) (h : 0 ≤ i ∧ i < xs.size) : α :=
  xs[i.toNat]'(by omega)

/-- Readable proof-carrying indexing for the generated code: `xs⦋i⦌'h` is `pyListGetProof xs i h`,
deliberately echoing Lean's own `xs[i]'h` next to the plain `xs⦋i⦌`. -/
notation:max xs "⦋" i "⦌'" h => pyListGetProof xs i h

/-- A proved access agrees with the defaulting one, so replacing `pyGetItem` by `pyListGetProof` can
never change a program's behaviour — only remove the unreachable panic. -/
@[simp] theorem pyListGetProof_eq_getItem {α : Type} [Inhabited α] (xs : List α) (i : Int)
    (h : 0 ≤ i ∧ i < xs.length) : pyListGetProof xs i h = pyGetItem xs i := by
  obtain ⟨h0, hlt⟩ := h
  have hn : i.toNat < xs.length := by omega
  have hneg : ¬ i < 0 := by omega
  simp only [pyListGetProof, pyGetItem, PyGetItem.getItem, pyListGetItem, hneg, if_false,
    beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, false_or]
  rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_getElem hn]

end PastaLean
