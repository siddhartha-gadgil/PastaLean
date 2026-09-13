import PastaLean.Imports
import TypeInfer.PyType

/-!
# Commutativity and associativity of the type-lattice join

Main results: **`join_comm`** (`a ⊔ b = b ⊔ a`) and **`join_assoc`** (`(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)`),
both on the FULL lattice. Associativity is by far the slowest proof in the development: it case-splits
over all constructor *triples* (~3400 goals), so it lives in this file and can be (re)built on demand
without holding up the rest of `TypeInfer.Theorem`.

Most triples close with a two-line `simp`; the `Optional`-absorption triples (which reassociate a
recursive `join` under the `opt` combinator, needing the IH and commutativity) are handled by the
`jsolve` fixpoint macro below. The `tuple`/`tuple`/`tuple` and `fn`/`fn`/`fn` triples reassociate a
length-indexed zip-map and get their own dedicated proofs via `zip_map_assoc`.

This file also owns the `⊥`/`⊤` simp lemmas (`join_unknown_*`, `join_any_*`) and `sizeOf_pos`, which
the associativity `grind`/`jsolve` need and the rest of the development reuses.

No `maxHeartbeats` cap: the triple split is genuinely long-running. `0` means unlimited.
-/

namespace TypeInfer.PyType

set_option maxHeartbeats 0

theorem sizeOf_pos (a : PyType) : 0 < sizeOf a := by cases a <;> simp

/-! ### ⊥ = `unknown` is the identity, ⊤ = `any` is absorbing -/

@[simp] theorem join_unknown_left (a : PyType) : join .unknown a = a := by cases a <;> simp [join]
@[simp] theorem join_unknown_right (a : PyType) : join a .unknown = a := by cases a <;> simp [join]
@[simp] theorem join_any_left (a : PyType) : join .any a = .any := by cases a <;> simp [join]
@[simp] theorem join_any_right (a : PyType) : join a .any = .any := by cases a <;> simp [join]

/-! ### Commutativity (needed by the associativity `grind`) -/

/-- Class-name equality is symmetric (needed for the `cls`/`cls` fallback of `join`). -/
theorem beq_comm_cls (n m : String) : (n == m) = (m == n) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact eq_comm

/-- A zip-map is unchanged by swapping the two lists, when the operation commutes at every index. -/
theorem zip_map_swap {α} (as bs : List PyType) (f : PyType → PyType → α) (hlen : as.length = bs.length)
    (hf : ∀ i (h1 : i < as.length) (h2 : i < bs.length), f as[i] bs[i] = f bs[i] as[i]) :
    (as.zip bs).attach.map (fun x : {p // p ∈ as.zip bs} => f x.1.1 x.1.2)
    = (bs.zip as).attach.map (fun x : {p // p ∈ bs.zip as} => f x.1.1 x.1.2) := by
  apply List.ext_getElem
  · simp [hlen]
  · grind only [= List.length_map, = List.getElem_map, = List.length_attach, = List.getElem_attach,
    = List.length_zip, = List.getElem_zip]

private theorem join_comm_aux : ∀ (n : Nat) (a b : PyType), sizeOf a + sizeOf b ≤ n →
    join a b = join b a := by
  intro n
  induction n with
  | zero => intro a b h; have := sizeOf_pos a; omega
  | succ n ih =>
    intro a b hn
    cases a <;> cases b <;>
      try (first
            | rfl
            | (simp [join, beq]; done)
            | (rw [join, join]; rw [ih _ _ (by
                simp only [PyType.list.sizeOf_spec, PyType.set.sizeOf_spec, PyType.opt.sizeOf_spec]
                  at hn; omega)]))
    case cls.cls n m =>
      grind only [join, beq]
    case dict.dict k1 v1 k2 v2 =>
      simp only [join]
      rw [ih k1 k2 (by simp only [PyType.dict.sizeOf_spec] at hn; omega),
          ih v1 v2 (by simp only [PyType.dict.sizeOf_spec] at hn; omega)]
    case tuple.tuple as bs =>
      simp only [join]
      by_cases hl : as.length = bs.length
      · rw [if_pos (by simpa using hl), if_pos (by simpa using hl.symm)]; congr 1
        apply zip_map_swap as bs _ hl
        intro i h1 h2
        refine ih as[i] bs[i] ?_
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := as) h1)
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := bs) h2)
        simp only [PyType.tuple.sizeOf_spec] at hn; omega
      · rw [if_neg (by simpa using hl), if_neg (by simpa using fun h => hl h.symm)]
    case fn.fn as r1 bs r2 =>
      simp only [join]
      by_cases hl : as.length = bs.length
      · rw [if_pos (by simpa using hl), if_pos (by simpa using hl.symm)]
        rw [ih r1 r2 (by simp only [PyType.fn.sizeOf_spec] at hn; omega)]; congr 1
        apply zip_map_swap as bs _ hl
        intro i h1 h2
        refine ih as[i] bs[i] ?_
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := as) h1)
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := bs) h2)
        simp only [PyType.fn.sizeOf_spec] at hn; omega
      · rw [if_neg (by simpa using hl), if_neg (by simpa using fun h => hl h.symm)]

--------------------------------------- LANDMARK ---------------------------------------
/-- **Commutativity** of the lattice join: `a ⊔ b = b ⊔ a`. -/
theorem join_comm (a b : PyType) : join a b = join b a :=
  join_comm_aux (sizeOf a + sizeOf b) a b (Nat.le_refl _)
--------------------------------------- LANDMARK ---------------------------------------

/-! ### Associativity -/

/-- The index-wise `join` of two lists — the payload of `join (tuple as) (tuple bs)` (and of `fn`). -/
abbrev Z (as bs : List PyType) : List PyType :=
  (as.zip bs).attach.map (fun x : {p // p ∈ as.zip bs} => join x.1.1 x.1.2)

theorem z_length (as bs : List PyType) : (Z as bs).length = min as.length bs.length := by
  simp [Z, List.length_zip]

theorem join_tuple_eq {as bs : List PyType} (h : as.length = bs.length) :
    join (tuple as) (tuple bs) = tuple (Z as bs) := by
  simp only [join]; rw [if_pos (by simpa using h)]

theorem join_tuple_ne {as bs : List PyType} (h : as.length ≠ bs.length) :
    join (tuple as) (tuple bs) = any := by
  simp only [join]; rw [if_neg (by simpa using h)]

theorem join_fn_eq {as bs : List PyType} {r1 r2 : PyType} (h : as.length = bs.length) :
    join (fn as r1) (fn bs r2) = fn (Z as bs) (join r1 r2) := by
  simp only [join]; rw [if_pos (by simpa using h)]

theorem join_fn_ne {as bs : List PyType} {r1 r2 : PyType} (h : as.length ≠ bs.length) :
    join (fn as r1) (fn bs r2) = any := by
  simp only [join]; rw [if_neg (by simpa using h)]

/-- Reassociate an index-wise `join`, given index-wise associativity. -/
theorem zip_map_assoc (as bs cs : List PyType)
    (hab : as.length = bs.length) (hbc : bs.length = cs.length)
    (hf : ∀ i (h1 : i < as.length) (h2 : i < bs.length) (h3 : i < cs.length),
       join (join as[i] bs[i]) cs[i] = join as[i] (join bs[i] cs[i])) :
    Z (Z as bs) cs = Z as (Z bs cs) := by
  apply List.ext_getElem
  · simp only [z_length]; omega
  · intro i h1 h2
    simp only [Z] at *
    grind only [= List.length_map, = List.getElem_map, = List.length_attach, = List.getElem_attach,
      = List.length_zip, = List.getElem_zip]

/-- `Z` is symmetric: the zip truncates to the same length either way and `join` commutes per index.
Needed by the `opt`+`tuple`/`fn`+`none` triples, whose two groupings differ by a swapped zip. -/
theorem Z_comm (as bs : List PyType) : Z as bs = Z bs as := by
  apply List.ext_getElem
  · simp only [Z, List.length_map, List.length_attach, List.length_zip, Nat.min_comm]
  · intro i h1 h2
    simp only [Z] at *
    grind only [= List.length_map, = List.getElem_map, = List.length_attach, = List.getElem_attach,
      = List.length_zip, = List.getElem_zip, join_comm]

/-! The `opt`-absorption triples where two of the three types share a container head reduce (after the
combinator's `match`) to needing that `join a (C x) = any` is *independent of the element* `x` (given
equal lengths, for `tuple`/`fn`). Each of these is a strong induction on `a` recursing through `opt`. -/

theorem list_any_indep_aux (x y : PyType) : ∀ (n : Nat) (a : PyType), sizeOf a ≤ n →
    join a (list x) = any → join a (list y) = any := by
  intro n
  induction n with
  | zero => intro a hle _; have := sizeOf_pos a; omega
  | succ n ih =>
    intro a hle h
    cases a with
    | opt w =>
      simp only [join] at h ⊢
      have hx : join w (list x) = any := by split at h <;> simp_all
      rw [ih w (by simp only [opt.sizeOf_spec] at hle; omega) hx]
    | _ => simp_all [join, beq, reduceCtorEq]

theorem list_any_indep (a x y : PyType) (h : join a (list x) = any) : join a (list y) = any :=
  list_any_indep_aux x y (sizeOf a) a (Nat.le_refl _) h

theorem set_any_indep_aux (x y : PyType) : ∀ (n : Nat) (a : PyType), sizeOf a ≤ n →
    join a (set x) = any → join a (set y) = any := by
  intro n
  induction n with
  | zero => intro a hle _; have := sizeOf_pos a; omega
  | succ n ih =>
    intro a hle h
    cases a with
    | opt w =>
      simp only [join] at h ⊢
      have hx : join w (set x) = any := by split at h <;> simp_all
      rw [ih w (by simp only [opt.sizeOf_spec] at hle; omega) hx]
    | _ => simp_all [join, beq, reduceCtorEq]

theorem set_any_indep (a x y : PyType) (h : join a (set x) = any) : join a (set y) = any :=
  set_any_indep_aux x y (sizeOf a) a (Nat.le_refl _) h

theorem dict_any_indep_aux (k1 v1 k2 v2 : PyType) : ∀ (n : Nat) (a : PyType), sizeOf a ≤ n →
    join a (dict k1 v1) = any → join a (dict k2 v2) = any := by
  intro n
  induction n with
  | zero => intro a hle _; have := sizeOf_pos a; omega
  | succ n ih =>
    intro a hle h
    cases a with
    | opt w =>
      simp only [join] at h ⊢
      have hx : join w (dict k1 v1) = any := by split at h <;> simp_all
      rw [ih w (by simp only [opt.sizeOf_spec] at hle; omega) hx]
    | _ => simp_all [join, beq, reduceCtorEq]

theorem dict_any_indep (a k1 v1 k2 v2 : PyType) (h : join a (dict k1 v1) = any) :
    join a (dict k2 v2) = any :=
  dict_any_indep_aux k1 v1 k2 v2 (sizeOf a) a (Nat.le_refl _) h

theorem tuple_any_indep_aux (L1 L2 : List PyType) (hl : L1.length = L2.length) :
    ∀ (n : Nat) (a : PyType), sizeOf a ≤ n →
    join a (tuple L1) = any → join a (tuple L2) = any := by
  intro n
  induction n with
  | zero => intro a hle _; have := sizeOf_pos a; omega
  | succ n ih =>
    intro a hle h
    cases a with
    | opt w =>
      simp only [join] at h ⊢
      have hx : join w (tuple L1) = any := by split at h <;> simp_all
      rw [ih w (by simp only [opt.sizeOf_spec] at hle; omega) hx]
    | tuple L' =>
      simp only [join, beq_iff_eq, hl] at h ⊢
      split at h <;> split <;> first | rfl | simp_all
    | _ => simp_all [join, beq, reduceCtorEq]

theorem tuple_any_indep (a : PyType) (L1 L2 : List PyType) (hl : L1.length = L2.length)
    (h : join a (tuple L1) = any) : join a (tuple L2) = any :=
  tuple_any_indep_aux L1 L2 hl (sizeOf a) a (Nat.le_refl _) h

theorem fn_any_indep_aux (A1 : List PyType) (r1 : PyType) (A2 : List PyType) (r2 : PyType)
    (hl : A1.length = A2.length) : ∀ (n : Nat) (a : PyType), sizeOf a ≤ n →
    join a (fn A1 r1) = any → join a (fn A2 r2) = any := by
  intro n
  induction n with
  | zero => intro a hle _; have := sizeOf_pos a; omega
  | succ n ih =>
    intro a hle h
    cases a with
    | opt w =>
      simp only [join] at h ⊢
      have hx : join w (fn A1 r1) = any := by split at h <;> simp_all
      rw [ih w (by simp only [opt.sizeOf_spec] at hle; omega) hx]
    | fn A' r' =>
      simp only [join, beq_iff_eq, hl] at h ⊢
      split at h <;> split <;> first | rfl | simp_all
    | _ => simp_all [join, beq, reduceCtorEq]

theorem fn_any_indep (a : PyType) (A1 : List PyType) (r1 : PyType) (A2 : List PyType) (r2 : PyType)
    (hl : A1.length = A2.length) (h : join a (fn A1 r1) = any) : join a (fn A2 r2) = any :=
  fn_any_indep_aux A1 r1 A2 r2 hl (sizeOf a) a (Nat.le_refl _) h

-- Fixpoint tactic for the `Optional`-absorption triples: reassociate via `ih`, reduce the `join`
-- combinators (incl. `reduceIte` for the `beq` catch-all), split residual `if`s, then finish with a
-- forward-`ih`, backward-`ih`, or `grind [join_comm]` attempt. `hygiene false` lets the macro capture
-- the proof's local `ih`; `disch := omega` discharges each `ih` size premise from `hn`.
set_option hygiene false in
local macro "jsolve" : tactic => `(tactic|
  (try (simp only [opt.sizeOf_spec, list.sizeOf_spec, set.sizeOf_spec, dict.sizeOf_spec,
      tuple.sizeOf_spec, fn.sizeOf_spec, cls.sizeOf_spec] at *)
   repeat' (first
     | (simp (disch := omega) only [ih] at *)
     | (simp only [join, beq, reduceCtorEq, reduceIte, join_any_left, join_any_right,
          join_unknown_left, join_unknown_right] at *)
     | split)
   all_goals (first
     | (simp_all only [join, beq, reduceCtorEq, reduceIte, join_any_left, join_any_right,
          join_unknown_left, join_unknown_right]; done)
     | (try (simp (disch := omega) only [← ih] at *)
        simp_all only [join, beq, reduceCtorEq, reduceIte, join_any_left, join_any_right,
          join_unknown_left, join_unknown_right]; done)
     | (grind [join_comm, Z_comm, list_any_indep, set_any_indep, dict_any_indep,
          tuple_any_indep, fn_any_indep, join_any_left, join_any_right, join_unknown_left,
          join_unknown_right]))))

private theorem join_assoc_aux : ∀ (n : Nat) (a b c : PyType), sizeOf a + sizeOf b + sizeOf c ≤ n →
    join (join a b) c = join a (join b c) := by
  intro n
  induction n with
  | zero => intro a b c h; have := sizeOf_pos a; omega
  | succ n ih =>
    intro a b c hn
    cases a <;> cases b <;> cases c
    -- `tuple`/`fn` triples reassociate a length-indexed zip-map; handle them explicitly first.
    case tuple.tuple.tuple as bs cs =>
      by_cases hab : as.length = bs.length <;> by_cases hbc : bs.length = cs.length
      · rw [join_tuple_eq hab, join_tuple_eq hbc,
            join_tuple_eq (by rw [z_length]; omega), join_tuple_eq (by rw [z_length]; omega)]
        congr 1
        apply zip_map_assoc as bs cs hab hbc
        intro i h1 h2 h3
        refine ih as[i] bs[i] cs[i] ?_
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := as) h1)
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := bs) h2)
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := cs) h3)
        simp only [PyType.tuple.sizeOf_spec] at hn; omega
      · rw [join_tuple_eq hab, join_tuple_ne hbc, join_tuple_ne (by rw [z_length]; omega), join_any_right]
      · rw [join_tuple_ne hab, join_any_left, join_tuple_eq hbc, join_tuple_ne (by rw [z_length]; omega)]
      · rw [join_tuple_ne hab, join_any_left, join_tuple_ne hbc, join_any_right]
    case fn.fn.fn as r1 bs r2 cs r3 =>
      by_cases hab : as.length = bs.length <;> by_cases hbc : bs.length = cs.length
      · rw [join_fn_eq hab, join_fn_eq hbc,
            join_fn_eq (by rw [z_length]; omega), join_fn_eq (by rw [z_length]; omega)]
        congr 1
        · apply zip_map_assoc as bs cs hab hbc
          intro i h1 h2 h3
          refine ih as[i] bs[i] cs[i] ?_
          have := List.sizeOf_lt_of_mem (List.getElem_mem (l := as) h1)
          have := List.sizeOf_lt_of_mem (List.getElem_mem (l := bs) h2)
          have := List.sizeOf_lt_of_mem (List.getElem_mem (l := cs) h3)
          simp only [PyType.fn.sizeOf_spec] at hn; omega
        · refine ih r1 r2 r3 ?_
          simp only [PyType.fn.sizeOf_spec] at hn; omega
      · rw [join_fn_eq hab, join_fn_ne hbc, join_fn_ne (by rw [z_length]; omega), join_any_right]
      · rw [join_fn_ne hab, join_any_left, join_fn_eq hbc, join_fn_ne (by rw [z_length]; omega)]
      · rw [join_fn_ne hab, join_any_left, join_fn_ne hbc, join_any_right]
    all_goals
      first
      | (simp only [join, beq, reduceCtorEq, ite_true, ite_false, ite_self]; done)
      | (simp only [join, beq, reduceIte, reduceCtorEq]; split_ifs <;> simp_all only [reduceCtorEq]; done)
      | jsolve

--------------------------------------- LANDMARK ---------------------------------------
/-- **Associativity** of the lattice join, on the full lattice: `(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)`. -/
theorem join_assoc (a b c : PyType) : join (join a b) c = join a (join b c) :=
  join_assoc_aux (sizeOf a + sizeOf b + sizeOf c) a b c (Nat.le_refl _)
--------------------------------------- LANDMARK ---------------------------------------

end TypeInfer.PyType
