import TypeInfer.Theorem.Associativity
import TypeInfer.Theorem.Soundness

/-!
# The meet — combining REQUIREMENTS rather than values

`join` is the least upper bound: it merges the types that flow INTO a slot, so it widens. `meet` is
the greatest lower bound: it merges the requirements a slot's USES impose, so it narrows. The two
directions are not interchangeable, and using the wrong one loses information — a parameter used once
as an `int` and once as a `float` must be `int` (an `int` satisfies both uses), whereas `join` would
widen it to `float`, which the `int` use does not accept.

Main results, all on the FULL lattice:

* **`meet_comm`**, **`meet_assoc`** — folding requirements is order- and grouping-independent, exactly
  as `joinAll` needs `join_comm`/`join_assoc`.
* **`meet_idem`** — `a ⊓ a = a`. Unlike `join_idem` this needs NO `normalized` hypothesis: `meet` has
  no `Optional[Any]` absorption, so the degenerate case that breaks `join`'s idempotence cannot arise.
* **`meet_any_*`/`meet_unknown_*`** — ⊤ is the identity and ⊥ is absorbing (dual to `join`).
* **`hasType_meet_left`/`hasType_meet_right`** — the semantic content: a value admitted by `a ⊓ b` is
  admitted by `a` AND by `b`. So narrowing to the meet never admits a value that some use rejects,
  which is what makes it sound to commit `a ⊓ b` as the inferred type of a slot with those uses.
  This is the dual of `hasType_join_left` (widening never EXCLUDES an admitted value).
-/

namespace TypeInfer.PyType

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-! ### ⊤ = `any` is the identity, ⊥ = `unknown` is absorbing -/

@[simp] theorem meet_any_left (a : PyType) : meet .any a = a := by cases a <;> simp [meet]
@[simp] theorem meet_any_right (a : PyType) : meet a .any = a := by cases a <;> simp [meet]
@[simp] theorem meet_unknown_left (a : PyType) : meet .unknown a = .unknown := by
  cases a <;> simp [meet]
@[simp] theorem meet_unknown_right (a : PyType) : meet a .unknown = .unknown := by
  cases a <;> simp [meet]

/-! ### Commutativity -/

private theorem meet_comm_aux : ∀ (n : Nat) (a b : PyType), sizeOf a + sizeOf b ≤ n →
    meet a b = meet b a := by
  intro n
  induction n with
  | zero => intro a b h; have := sizeOf_pos a; omega
  | succ n ih =>
    intro a b hn
    cases a <;> cases b <;>
      try (first
            | rfl
            | (simp [meet, beq]; done)
            | (simp only [meet]; rw [ih _ _ (by
                simp only [PyType.list.sizeOf_spec, PyType.set.sizeOf_spec, PyType.opt.sizeOf_spec]
                  at hn; omega)]))
    case cls.cls n m =>
      grind only [meet, beq]
    case dict.dict k1 v1 k2 v2 =>
      simp only [meet]
      rw [ih k1 k2 (by simp only [PyType.dict.sizeOf_spec] at hn; omega),
          ih v1 v2 (by simp only [PyType.dict.sizeOf_spec] at hn; omega)]
    case tuple.tuple as bs =>
      simp only [meet]
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
      simp only [meet]
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
/-- **Commutativity** of the meet: `a ⊓ b = b ⊓ a`. -/
theorem meet_comm (a b : PyType) : meet a b = meet b a :=
  meet_comm_aux (sizeOf a + sizeOf b) a b (Nat.le_refl _)
--------------------------------------- LANDMARK ---------------------------------------

/-! ### Idempotence — on the FULL lattice, no `normalized` side condition -/

/-- The per-element map in the `tuple`/`fn` meet reduces to the list itself when every element is
idempotent — the `meet` counterpart of `tuple_help`. -/
theorem tuple_help_meet (es : List PyType) (h : ∀ e ∈ es, meet e e = e) :
    ((es.zip es).attach.map (fun x : {p // p ∈ es.zip es} => meet x.1.1 x.1.2)) = es := by
  apply List.ext_getElem
  · simp
  · grind only [= List.getElem_map, = List.getElem_attach, = List.getElem_zip,
    usr List.getElem_mem]

--------------------------------------- LANDMARK ---------------------------------------
/-- **Idempotence** of the meet, on every type. `join_idem` needs `normalized` because `join` collapses
`Optional[Any]` to `Any`; `meet` has no such absorption, so idempotence is unconditional. -/
theorem meet_idem : ∀ (a : PyType), meet a a = a
  | .unknown | .any | .none => by simp [meet]
  | .int | .bool | .str | .float => by simp [meet, beq]
  | .cls n => by simp [meet, beq]
  | .list e => by rw [meet, meet_idem e]
  | .set e => by rw [meet, meet_idem e]
  | .dict k v => by rw [meet, meet_idem k, meet_idem v]
  | .opt e => by rw [meet, meet_idem e]
  | .tuple es => by
      have hall : ∀ e ∈ es, meet e e = e := fun e _ => meet_idem e
      rw [meet]; simp only [beq_self_eq_true, if_true]; rw [tuple_help_meet es hall]
  | .fn args r => by
      have hall : ∀ e ∈ args, meet e e = e := fun e _ => meet_idem e
      rw [meet]; simp only [beq_self_eq_true, if_true]
      rw [tuple_help_meet args hall, meet_idem r]
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have hm := ‹_ ∈ _›; have := List.sizeOf_lt_of_mem hm; omega)
--------------------------------------- LANDMARK ---------------------------------------

/-! ### Associativity -/

/-- The index-wise `meet` of two lists — the payload of `meet (tuple as) (tuple bs)` (and of `fn`). -/
abbrev M (as bs : List PyType) : List PyType :=
  (as.zip bs).attach.map (fun x : {p // p ∈ as.zip bs} => meet x.1.1 x.1.2)

theorem m_length (as bs : List PyType) : (M as bs).length = min as.length bs.length := by
  simp [M, List.length_zip]

theorem meet_tuple_eq {as bs : List PyType} (h : as.length = bs.length) :
    meet (tuple as) (tuple bs) = tuple (M as bs) := by
  simp only [meet]; rw [if_pos (by simpa using h)]

theorem meet_tuple_ne {as bs : List PyType} (h : as.length ≠ bs.length) :
    meet (tuple as) (tuple bs) = unknown := by
  simp only [meet]; rw [if_neg (by simpa using h)]

theorem meet_fn_eq {as bs : List PyType} {r1 r2 : PyType} (h : as.length = bs.length) :
    meet (fn as r1) (fn bs r2) = fn (M as bs) (meet r1 r2) := by
  simp only [meet]; rw [if_pos (by simpa using h)]

theorem meet_fn_ne {as bs : List PyType} {r1 r2 : PyType} (h : as.length ≠ bs.length) :
    meet (fn as r1) (fn bs r2) = unknown := by
  simp only [meet]; rw [if_neg (by simpa using h)]

/-- Reassociate an index-wise `meet`, given index-wise associativity. -/
theorem zip_map_assoc_meet (as bs cs : List PyType)
    (hab : as.length = bs.length) (hbc : bs.length = cs.length)
    (hf : ∀ i (h1 : i < as.length) (h2 : i < bs.length) (h3 : i < cs.length),
       meet (meet as[i] bs[i]) cs[i] = meet as[i] (meet bs[i] cs[i])) :
    M (M as bs) cs = M as (M bs cs) := by
  apply List.ext_getElem
  · simp only [m_length]; omega
  · intro i h1 h2
    simp only [M] at *
    grind only [= List.length_map, = List.getElem_map, = List.length_attach, = List.getElem_attach,
      = List.length_zip, = List.getElem_zip]

/-- `M` is symmetric — needed by the `opt`+`tuple`/`fn` triples, whose two groupings differ by a
swapped zip. -/
theorem M_comm (as bs : List PyType) : M as bs = M bs as := by
  apply List.ext_getElem
  · simp only [M, List.length_map, List.length_attach, List.length_zip, Nat.min_comm]
  · intro i h1 h2
    simp only [M] at *
    grind only [= List.length_map, = List.getElem_map, = List.length_attach, = List.getElem_attach,
      = List.length_zip, = List.getElem_zip, meet_comm]

/-! ### Head preservation

`meet` never changes a type's head: meeting anything with a `dict` gives a `dict` or fails outright.
The associativity triples that mix two DIFFERENT heads need exactly this — e.g. to see that
`set ⊓ (x ⊓ dict)` is `unknown` whatever `x` is, since the inner meet can only be a `dict` or
`unknown` and a `set` meets neither. Each is an induction through `opt`, the one rung that can strip a
constructor. The numeric heads preserve only up to the tower (`_ ⊓ float` may narrow to `int`/`bool`),
which is what `meet_float_shape` states. -/

theorem meet_list_shape (e : PyType) : ∀ (x : PyType),
    meet x (list e) = unknown ∨ ∃ e', meet x (list e) = list e'
  | .opt w => by simp only [meet]; exact meet_list_shape e w
  | .any => Or.inr ⟨e, by simp⟩
  | .list a => Or.inr ⟨meet a e, by simp [meet]⟩
  | .unknown | .int | .bool | .str | .float | .none
  | .set _ | .dict _ _ | .tuple _ | .fn _ _ | .cls _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

theorem meet_set_shape (e : PyType) : ∀ (x : PyType),
    meet x (set e) = unknown ∨ ∃ e', meet x (set e) = set e'
  | .opt w => by simp only [meet]; exact meet_set_shape e w
  | .any => Or.inr ⟨e, by simp⟩
  | .set a => Or.inr ⟨meet a e, by simp [meet]⟩
  | .unknown | .int | .bool | .str | .float | .none
  | .list _ | .dict _ _ | .tuple _ | .fn _ _ | .cls _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

theorem meet_dict_shape (k v : PyType) : ∀ (x : PyType),
    meet x (dict k v) = unknown ∨ ∃ k' v', meet x (dict k v) = dict k' v'
  | .opt w => by simp only [meet]; exact meet_dict_shape k v w
  | .any => Or.inr ⟨k, v, by simp⟩
  | .dict a b => Or.inr ⟨meet a k, meet b v, by simp [meet]⟩
  | .unknown | .int | .bool | .str | .float | .none
  | .list _ | .set _ | .tuple _ | .fn _ _ | .cls _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

theorem meet_tuple_shape (es : List PyType) : ∀ (x : PyType),
    meet x (tuple es) = unknown ∨ ∃ es', meet x (tuple es) = tuple es'
  | .opt w => by simp only [meet]; exact meet_tuple_shape es w
  | .any => Or.inr ⟨es, by simp⟩
  | .tuple as => by
      simp only [meet]; split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
  | .unknown | .int | .bool | .str | .float | .none
  | .list _ | .set _ | .dict _ _ | .fn _ _ | .cls _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

theorem meet_fn_shape (as : List PyType) (r : PyType) : ∀ (x : PyType),
    meet x (fn as r) = unknown ∨ ∃ as' r', meet x (fn as r) = fn as' r'
  | .opt w => by simp only [meet]; exact meet_fn_shape as r w
  | .any => Or.inr ⟨as, r, by simp⟩
  | .fn bs r' => by
      simp only [meet]; split
      · exact Or.inr ⟨_, _, rfl⟩
      · exact Or.inl rfl
  | .unknown | .int | .bool | .str | .float | .none
  | .list _ | .set _ | .dict _ _ | .tuple _ | .cls _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

theorem meet_str_shape : ∀ (x : PyType), meet x str = unknown ∨ meet x str = str
  | .opt w => by simp only [meet]; exact meet_str_shape w
  | .any => Or.inr (by simp)
  | .str => Or.inr (by simp [meet, beq])
  | .unknown | .int | .bool | .float | .none
  | .list _ | .set _ | .dict _ _ | .tuple _ | .fn _ _ | .cls _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

theorem meet_none_shape : ∀ (x : PyType), meet x none = unknown ∨ meet x none = none
  | .opt _ => Or.inr (by simp [meet])
  | .any => Or.inr (by simp)
  | .none => Or.inr (by simp [meet, beq])
  | .unknown | .int | .bool | .str | .float
  | .list _ | .set _ | .dict _ _ | .tuple _ | .fn _ _ | .cls _ => Or.inl (by simp [meet, beq])

theorem meet_cls_shape (n : String) : ∀ (x : PyType),
    meet x (cls n) = unknown ∨ meet x (cls n) = cls n
  | .opt w => by simp only [meet]; exact meet_cls_shape n w
  | .any => Or.inr (by simp)
  | .cls m => by simp only [meet, beq]; split <;> simp_all
  | .unknown | .int | .bool | .str | .float | .none
  | .list _ | .set _ | .dict _ _ | .tuple _ | .fn _ _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

/-- The numeric heads preserve only up to the tower: meeting into `float` can narrow to `int` or
`bool`, but never leaves the numeric types. -/
theorem meet_float_shape : ∀ (x : PyType),
    meet x float = unknown ∨ meet x float = float ∨ meet x float = int ∨ meet x float = bool
  | .opt w => by simp only [meet]; exact meet_float_shape w
  | .any => Or.inr (Or.inl (by simp))
  | .float => Or.inr (Or.inl (by simp [meet, beq]))
  | .int => Or.inr (Or.inr (Or.inl (by simp [meet])))
  | .bool => Or.inr (Or.inr (Or.inr (by simp [meet])))
  | .unknown | .str | .none
  | .list _ | .set _ | .dict _ _ | .tuple _ | .fn _ _ | .cls _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

theorem meet_int_shape : ∀ (x : PyType),
    meet x int = unknown ∨ meet x int = int ∨ meet x int = bool
  | .opt w => by simp only [meet]; exact meet_int_shape w
  | .any => Or.inr (Or.inl (by simp))
  | .int => Or.inr (Or.inl (by simp [meet, beq]))
  | .float => Or.inr (Or.inl (by simp [meet]))
  | .bool => Or.inr (Or.inr (by simp [meet]))
  | .unknown | .str | .none
  | .list _ | .set _ | .dict _ _ | .tuple _ | .fn _ _ | .cls _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

theorem meet_bool_shape : ∀ (x : PyType), meet x bool = unknown ∨ meet x bool = bool
  | .opt w => by simp only [meet]; exact meet_bool_shape w
  | .any => Or.inr (by simp)
  | .bool | .int | .float => Or.inr (by simp [meet, beq])
  | .unknown | .str | .none
  | .list _ | .set _ | .dict _ _ | .tuple _ | .fn _ _ | .cls _ => Or.inl (by simp [meet, beq])
termination_by x => sizeOf x

/-! ### `opt` stripping and the scalar table

Unlike `join`, which keeps an `Optional` wrapper it meets against, `meet` DROPS it — `Optional[T] ⊓ U`
is `T ⊓ U`, since `U` alone admits no `None`. So an `opt` triple reduces to a strictly smaller one and
the induction hypothesis applies; these are the rewrites that expose that, one per head `opt` can be
dropped against. Together with the ground numeric table below they give the associativity solver
everything it needs to compute a `meet` whose arguments are not both variables. -/

theorem meet_opt_int (a : PyType) : meet (opt a) int = meet a int := by simp only [meet]
theorem meet_opt_bool (a : PyType) : meet (opt a) bool = meet a bool := by simp only [meet]
theorem meet_opt_str (a : PyType) : meet (opt a) str = meet a str := by simp only [meet]
theorem meet_opt_float (a : PyType) : meet (opt a) float = meet a float := by simp only [meet]
theorem meet_opt_list (a e : PyType) : meet (opt a) (list e) = meet a (list e) := by simp only [meet]
theorem meet_opt_set (a e : PyType) : meet (opt a) (set e) = meet a (set e) := by simp only [meet]
theorem meet_opt_dict (a k v : PyType) : meet (opt a) (dict k v) = meet a (dict k v) := by
  simp only [meet]
theorem meet_opt_tuple (a : PyType) (es : List PyType) :
    meet (opt a) (tuple es) = meet a (tuple es) := by simp only [meet]
theorem meet_opt_fn (a r : PyType) (as : List PyType) : meet (opt a) (fn as r) = meet a (fn as r) := by
  simp only [meet]
theorem meet_opt_cls (a : PyType) (n : String) : meet (opt a) (cls n) = meet a (cls n) := by
  simp only [meet]
theorem meet_opt_opt (a b : PyType) : meet (opt a) (opt b) = opt (meet a b) := by simp only [meet]
theorem meet_opt_none (a : PyType) : meet (opt a) none = none := by simp only [meet]
theorem meet_none_opt (a : PyType) : meet none (opt a) = none := by simp only [meet]

theorem meet_list_list (a b : PyType) : meet (list a) (list b) = list (meet a b) := by simp only [meet]
theorem meet_set_set (a b : PyType) : meet (set a) (set b) = set (meet a b) := by simp only [meet]
theorem meet_dict_dict (k v k' v' : PyType) :
    meet (dict k v) (dict k' v') = dict (meet k k') (meet v v') := by simp only [meet]
theorem meet_cls_cls_ne {n m : String} (h : n ≠ m) : meet (cls n) (cls m) = unknown := by
  simp only [meet, beq]; simp [h]

theorem meet_int_float : meet int float = int := by simp only [meet]
theorem meet_float_int : meet float int = int := by simp only [meet]
theorem meet_int_bool : meet int bool = bool := by simp only [meet]
theorem meet_bool_int : meet bool int = bool := by simp only [meet]
theorem meet_bool_float : meet bool float = bool := by simp only [meet]
theorem meet_float_bool : meet float bool = bool := by simp only [meet]

/-! ### Dropping an `Optional` on the right of a triple

All the remaining associativity triples have the same shape: the third type is an `Optional`, and the
second admits no `None`, so the wrapper is dropped on both sides and what is left is a smaller
reassociation the induction hypothesis already knows. `NoneFree` packages "meeting against `x` yields
something an `opt` strips against", which each head gets from its shape lemma. -/

/-- `x` admits no `None`, in the form associativity needs: whatever `x` is met with, an `opt` wrapper
on the other side is simply dropped. -/
def NoneFree (x : PyType) : Prop := ∀ y z : PyType, meet (opt z) (meet y x) = meet z (meet y x)

theorem noneFree_list (e : PyType) : NoneFree (list e) := by
  intro y z; rcases meet_list_shape e y with h | ⟨e', h⟩ <;> rw [h] <;> simp [meet_opt_list]
theorem noneFree_set (e : PyType) : NoneFree (set e) := by
  intro y z; rcases meet_set_shape e y with h | ⟨e', h⟩ <;> rw [h] <;> simp [meet_opt_set]
theorem noneFree_dict (k v : PyType) : NoneFree (dict k v) := by
  intro y z; rcases meet_dict_shape k v y with h | ⟨k', v', h⟩ <;> rw [h] <;> simp [meet_opt_dict]
theorem noneFree_tuple (es : List PyType) : NoneFree (tuple es) := by
  intro y z; rcases meet_tuple_shape es y with h | ⟨es', h⟩ <;> rw [h] <;> simp [meet_opt_tuple]
theorem noneFree_fn (as : List PyType) (r : PyType) : NoneFree (fn as r) := by
  intro y z; rcases meet_fn_shape as r y with h | ⟨as', r', h⟩ <;> rw [h] <;> simp [meet_opt_fn]
theorem noneFree_cls (m : String) : NoneFree (cls m) := by
  intro y z; rcases meet_cls_shape m y with h | h <;> rw [h] <;> simp [meet_opt_cls]
theorem noneFree_int : NoneFree int := by
  intro y z; rcases meet_int_shape y with h | h | h <;> rw [h] <;> simp [meet_opt_int, meet_opt_bool]
theorem noneFree_bool : NoneFree bool := by
  intro y z; rcases meet_bool_shape y with h | h <;> rw [h] <;> simp [meet_opt_bool]
theorem noneFree_str : NoneFree str := by
  intro y z; rcases meet_str_shape y with h | h <;> rw [h] <;> simp [meet_opt_str]
theorem noneFree_float : NoneFree float := by
  intro y z; rcases meet_float_shape y with h | h | h | h <;> rw [h] <;>
    simp [meet_opt_float, meet_opt_int, meet_opt_bool]

/-- An `Optional` on the RIGHT of an associativity triple, given that the middle type admits no
`None`: both sides drop the wrapper, leaving a reassociation of strictly smaller types. -/
theorem meet_opt_right (n : Nat)
    (ih : ∀ a b c : PyType, sizeOf a + sizeOf b + sizeOf c ≤ n → meet (meet a b) c = meet a (meet b c))
    (a b w : PyType) (hsz : sizeOf a + sizeOf b + sizeOf w ≤ n) (hb : NoneFree b) :
    meet (meet a b) (opt w) = meet a (meet b (opt w)) := by
  have h1 : meet b (opt w) = meet w b := by rw [meet_comm]; simpa using hb any w
  rw [meet_comm (meet a b) (opt w), hb a w, h1,
      ← ih w a b (by omega), ← ih a w b (by omega), meet_comm w a]

-- Fixpoint tactic for the `Optional` triples, mirroring `jsolve` in `Associativity`: reassociate via
-- `ih`, reduce the `meet` combinators, split residual `if`s, then close forwards, backwards, or by
-- `grind`. `hygiene false` lets the macro capture the proof's local `ih`.
set_option hygiene false in
local macro "msolve" : tactic => `(tactic|
  (try (simp only [opt.sizeOf_spec, list.sizeOf_spec, set.sizeOf_spec, dict.sizeOf_spec,
      tuple.sizeOf_spec, fn.sizeOf_spec, cls.sizeOf_spec] at *)
   repeat' (first
     | (simp (disch := omega) only [ih] at *)
     | (simp only [meet, beq, reduceCtorEq, reduceIte, meet_any_left, meet_any_right,
          meet_unknown_left, meet_unknown_right, meet_idem, meet_opt_int, meet_opt_bool,
          meet_opt_str, meet_opt_float, meet_opt_list, meet_opt_set, meet_opt_dict, meet_opt_tuple,
          meet_opt_fn, meet_opt_cls, meet_opt_opt, meet_opt_none, meet_none_opt, meet_int_float,
          meet_float_int, meet_int_bool, meet_bool_int, meet_bool_float, meet_float_bool, meet_list_list,
          meet_set_set, meet_dict_dict] at *)
     | split)
   all_goals (first
     | (simp_all only [meet, beq, reduceCtorEq, reduceIte, meet_any_left, meet_any_right,
          meet_unknown_left, meet_unknown_right, meet_idem, meet_opt_int, meet_opt_bool,
          meet_opt_str, meet_opt_float, meet_opt_list, meet_opt_set, meet_opt_dict, meet_opt_tuple,
          meet_opt_fn, meet_opt_cls, meet_opt_opt, meet_opt_none, meet_none_opt, meet_int_float,
          meet_float_int, meet_int_bool, meet_bool_int, meet_bool_float, meet_float_bool, meet_list_list,
          meet_set_set, meet_dict_dict]; done)
     | (try (simp (disch := omega) only [← ih] at *)
        simp_all only [meet, beq, reduceCtorEq, reduceIte, meet_any_left, meet_any_right,
          meet_unknown_left, meet_unknown_right, meet_idem, meet_opt_int, meet_opt_bool,
          meet_opt_str, meet_opt_float, meet_opt_list, meet_opt_set, meet_opt_dict, meet_opt_tuple,
          meet_opt_fn, meet_opt_cls, meet_opt_opt, meet_opt_none, meet_none_opt, meet_int_float,
          meet_float_int, meet_int_bool, meet_bool_int, meet_bool_float, meet_float_bool, meet_list_list,
          meet_set_set, meet_dict_dict]; done)
     | (grind [meet_comm, M_comm, meet_any_left, meet_any_right, meet_unknown_left,
          meet_unknown_right, meet_list_shape, meet_set_shape, meet_dict_shape, meet_tuple_shape,
          meet_fn_shape, meet_str_shape, meet_none_shape, meet_cls_shape, meet_float_shape,
          meet_int_shape, meet_bool_shape, meet_idem, meet_opt_int, meet_opt_bool, meet_opt_str,
          meet_opt_float, meet_opt_list, meet_opt_set, meet_opt_dict, meet_opt_tuple, meet_opt_fn,
          meet_opt_cls, meet_opt_opt, meet_opt_none, meet_none_opt, meet_int_float, meet_float_int,
          meet_int_bool, meet_bool_int, meet_bool_float, meet_float_bool, meet_list_list,
          meet_set_set, meet_dict_dict, meet_cls_cls_ne, meet_tuple_eq, meet_tuple_ne, meet_fn_eq,
          meet_fn_ne, m_length]))))

private theorem meet_assoc_aux : ∀ (n : Nat) (a b c : PyType), sizeOf a + sizeOf b + sizeOf c ≤ n →
    meet (meet a b) c = meet a (meet b c) := by
  intro n
  induction n with
  | zero => intro a b c h; have := sizeOf_pos a; omega
  | succ n ih =>
    intro a b c hn
    cases a <;> cases b <;> cases c
    case tuple.tuple.tuple as bs cs =>
      by_cases hab : as.length = bs.length <;> by_cases hbc : bs.length = cs.length
      · rw [meet_tuple_eq hab, meet_tuple_eq hbc,
            meet_tuple_eq (by rw [m_length]; omega), meet_tuple_eq (by rw [m_length]; omega)]
        congr 1
        apply zip_map_assoc_meet as bs cs hab hbc
        intro i h1 h2 h3
        refine ih as[i] bs[i] cs[i] ?_
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := as) h1)
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := bs) h2)
        have := List.sizeOf_lt_of_mem (List.getElem_mem (l := cs) h3)
        simp only [PyType.tuple.sizeOf_spec] at hn; omega
      · rw [meet_tuple_eq hab, meet_tuple_ne hbc, meet_tuple_ne (by rw [m_length]; omega),
            meet_unknown_right]
      · rw [meet_tuple_ne hab, meet_unknown_left, meet_tuple_eq hbc,
            meet_tuple_ne (by rw [m_length]; omega)]
      · rw [meet_tuple_ne hab, meet_unknown_left, meet_tuple_ne hbc, meet_unknown_right]
    case fn.fn.fn as r1 bs r2 cs r3 =>
      by_cases hab : as.length = bs.length <;> by_cases hbc : bs.length = cs.length
      · rw [meet_fn_eq hab, meet_fn_eq hbc,
            meet_fn_eq (by rw [m_length]; omega), meet_fn_eq (by rw [m_length]; omega)]
        congr 1
        · apply zip_map_assoc_meet as bs cs hab hbc
          intro i h1 h2 h3
          refine ih as[i] bs[i] cs[i] ?_
          have := List.sizeOf_lt_of_mem (List.getElem_mem (l := as) h1)
          have := List.sizeOf_lt_of_mem (List.getElem_mem (l := bs) h2)
          have := List.sizeOf_lt_of_mem (List.getElem_mem (l := cs) h3)
          simp only [PyType.fn.sizeOf_spec] at hn; omega
        · refine ih r1 r2 r3 ?_
          simp only [PyType.fn.sizeOf_spec] at hn; omega
      · rw [meet_fn_eq hab, meet_fn_ne hbc, meet_fn_ne (by rw [m_length]; omega), meet_unknown_right]
      · rw [meet_fn_ne hab, meet_unknown_left, meet_fn_eq hbc, meet_fn_ne (by rw [m_length]; omega)]
      · rw [meet_fn_ne hab, meet_unknown_left, meet_fn_ne hbc, meet_unknown_right]
    all_goals
      first
      | (simp only [meet, beq, reduceCtorEq, ite_true, ite_false, ite_self]; done)
      | (simp only [meet, beq, reduceIte, reduceCtorEq]; split_ifs <;> simp_all only [reduceCtorEq]; done)
      -- Every triple ending in an `Optional` whose middle admits no `None` is a wrapper-drop.
      | (refine meet_opt_right n ih _ _ _ ?_ (by first
            | exact noneFree_list _ | exact noneFree_set _ | exact noneFree_dict _ _
            | exact noneFree_tuple _ | exact noneFree_fn _ _ | exact noneFree_cls _
            | exact noneFree_int | exact noneFree_bool | exact noneFree_str | exact noneFree_float)
         simp only [opt.sizeOf_spec, list.sizeOf_spec, set.sizeOf_spec, dict.sizeOf_spec,
           tuple.sizeOf_spec, fn.sizeOf_spec, cls.sizeOf_spec] at hn ⊢
         omega)
      | msolve

--------------------------------------- LANDMARK ---------------------------------------
/-- **Associativity** of the meet, on the full lattice: `(a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)`. With `meet_comm`
this makes `meetAll` independent of the order the uses are visited in. -/
theorem meet_assoc (a b c : PyType) : meet (meet a b) c = meet a (meet b c) :=
  meet_assoc_aux (sizeOf a + sizeOf b + sizeOf c) a b c (Nat.le_refl _)
--------------------------------------- LANDMARK ---------------------------------------

/-! ### Semantic soundness of narrowing

The dual of `hasType_join_left`. `join` widens, and widening never EXCLUDES a value the program can
produce. `meet` narrows, and narrowing never ADMITS a value one of the uses rejects: everything the
meet admits, both sides admit. That is what licenses committing `a ⊓ b` as a slot's type once its uses
require `a` and `b`. -/

private theorem hasType_meet_left_aux : ∀ (n : Nat) (v : Val) (a b : PyType),
    sizeOf a + sizeOf b ≤ n → HasType v (meet a b) → HasType v a := by
  intro n
  induction n with
  | zero => intro v a b hn _; have := sizeOf_pos a; omega
  | succ n ih =>
    intro v a b hn h
    cases a <;> cases b
    all_goals (try (cases v <;> simp_all [HasType, meet, beq]; done))
    all_goals (try (cases v <;> simp_all only [HasType, meet, beq] <;> split at h <;>
      simp_all [HasType]; done))
    -- `list e₁ ⊓ list e₂ = list (e₁ ⊓ e₂)`: narrow each element by the IH.
    case list.list e1 e2 =>
      cases v <;> simp only [meet, HasType] at h ⊢ <;>
        first
        | exact h.elim
        | (intro x hx; exact ih x e1 e2 (by simp only [PyType.list.sizeOf_spec] at hn; omega) (h x hx))
    -- `opt` rungs: either the value is `None` (admitted by any `opt`), or it inhabits the narrowed
    -- inner type and the IH lifts it back.
    all_goals
      (simp only [meet] at h
       first
       -- `a ⊓ opt w` drops the wrapper to `w ⊓ a`; commute and the IH gives `a` back directly.
       | (rw [meet_comm] at h
          exact ih v _ _ (by simp only [PyType.opt.sizeOf_spec] at hn; omega) h)
       | (simp only [HasType]
          first
          | (rcases h with rfl | h
             · exact Or.inl rfl
             · exact Or.inr (ih v _ _ (by simp only [PyType.opt.sizeOf_spec] at hn; omega) h))
          | exact Or.inr (ih v _ _ (by simp only [PyType.opt.sizeOf_spec] at hn; omega) h)
          | (cases v <;> simp_all [HasType]))
       | (simp_all [HasType]))

--------------------------------------- LANDMARK ---------------------------------------
/-- **Semantic soundness of narrowing (left):** `HasType v (a ⊓ b) → HasType v a`. The meet only ever
admits values that `a` already admits, so narrowing a slot to the meet of its uses' requirements can
never let through a value one of those uses would reject. Dual to `hasType_join_left`. -/
theorem hasType_meet_left (v : Val) (a b : PyType) (h : HasType v (meet a b)) : HasType v a :=
  hasType_meet_left_aux (sizeOf a + sizeOf b) v a b (Nat.le_refl _) h

/-- Soundness of narrowing on the right, by commutativity. -/
theorem hasType_meet_right (v : Val) (a b : PyType) (h : HasType v (meet a b)) : HasType v b :=
  hasType_meet_left v b a (by rwa [meet_comm] at h)
--------------------------------------- LANDMARK ---------------------------------------

/-- The two directions together: the meet denotes exactly the INTERSECTION side of the requirement —
a value it admits satisfies every use. -/
theorem hasType_meet (v : Val) (a b : PyType) (h : HasType v (meet a b)) :
    HasType v a ∧ HasType v b :=
  ⟨hasType_meet_left v a b h, hasType_meet_right v a b h⟩

end TypeInfer.PyType
