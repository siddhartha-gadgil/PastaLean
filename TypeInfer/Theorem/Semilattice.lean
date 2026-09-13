import TypeInfer.Theorem.Associativity

/-!
# The join is a bounded join-semilattice

Main result: **`join_idem`** — `a ⊔ a = a` on every `normalized` type. With `join_comm`/`join_assoc`
(in `TypeInfer.Theorem.Associativity`) and the `⊥`/`⊤` laws (`join_unknown_*`/`join_any_*`, also there),
this makes `PyType`'s `join` a bounded join-semilattice, so the inference fixpoint's result is order- AND
grouping-independent.

Verification also surfaced a genuine subtlety: idempotence holds on every NORMALIZED type but **not** on
`opt any` — the engine collapses `Optional[Any]` to `Any` by construction (`join_opt_any`), so the
degenerate value never arises. `join_idem` is proved for exactly the `normalized` types, i.e. those with
no `opt any` subterm — precisely the engine's reachable types.

This file also records **information preservation**: `join a b = unknown` only when both inputs are
`unknown` (`join_eq_unknown_iff`), so merging two known types never loses all information.
-/

namespace TypeInfer.PyType

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-! ### The numeric tower `bool <: int <: float` widens to the join, in EITHER order -/

theorem join_bool_int  : join .bool .int  = .int   ∧ join .int .bool  = .int   := by
  constructor <;> simp [join]
theorem join_int_float : join .int .float = .float ∧ join .float .int = .float := by
  constructor <;> simp [join]
theorem join_bool_float: join .bool .float= .float ∧ join .float .bool= .float := by
  constructor <;> simp [join]

/-- Non-numeric conflicts go to ⊤ (`any`), as the join of incomparable elements must. -/
theorem join_conflict_str_int : join .str .int = .any ∧ join .int .str = .any := by
  constructor <;> simp [join, beq]

/-! ### The verified subtlety: `Optional[Any]` collapses to `Any`

This is *why* `join` is not naively idempotent, and it documents the invariant the engine maintains
(it never keeps an `opt any`). -/

theorem join_opt_any : join (.opt .any) (.opt .any) = .any := by simp [join]

/-- `any` and `opt any` are DISTINCT PyType *terms* (different constructors) — even though they denote
the same semantic type ("any value, including `None`", since `any` ⊇ `None` already). -/
theorem any_ne_opt_any : PyType.any ≠ .opt .any := by intro h; exact PyType.noConfusion h

/-- So `join` collapses `opt any` AWAY from its own input: the self-join is `any`, not `opt any`. This
is `join` NORMALIZING (returning the canonical representative), not a failure of idempotence — on the
`normalized` types (which `join` always outputs) idempotence holds; see `join_idem`. -/
theorem join_opt_any_ne_input : join (.opt .any) (.opt .any) ≠ .opt .any := by
  rw [join_opt_any]; exact any_ne_opt_any

/-! ### Idempotence: `join a a = a` for every normalized type

`normalized a` = "`a` has no `opt any` subterm" — the normal form the engine keeps. On these, `join`
is idempotent, proved for ALL constructors (including the nested `tuple`/`fn`/container cases). -/

/-- The engine's normal-form invariant: no `opt any` subterm (Optional[Any] is always collapsed). -/
def normalized : PyType → Bool
  | .opt e => !(e.beq .any) && normalized e
  | .list e | .set e => normalized e
  | .dict k v => normalized k && normalized v
  | .tuple es => es.attach.all (fun ⟨e, _⟩ => normalized e)
  | .fn args r => args.attach.all (fun ⟨e, _⟩ => normalized e) && normalized r
  | _ => true
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (rename_i h; have := List.sizeOf_lt_of_mem h; omega)

/-- Membership extraction for the `tuple`/`fn` element lists' normalization. -/
theorem normalized_mem {es : List PyType} (h : es.attach.all (fun ⟨e, _⟩ => normalized e) = true)
    {e} (he : e ∈ es) : normalized e = true := by
  rw [List.all_eq_true] at h; exact h ⟨e, he⟩ (List.mem_attach es ⟨e, he⟩)

/-- The per-element map in the `tuple`/`fn` join reduces to the list itself when every element is
idempotent — the key lemma for the nested cases. -/
theorem tuple_help (es : List PyType) (h : ∀ e ∈ es, join e e = e) :
    ((es.zip es).attach.map (fun x : {p // p ∈ es.zip es} => join x.1.1 x.1.2)) = es := by
  apply List.ext_getElem
  · simp
  · grind only [= List.getElem_map, = List.getElem_attach, = List.getElem_zip,
    usr List.getElem_mem]

--------------------------------------- LANDMARK ---------------------------------------
/-- **Idempotence** of the lattice join on every normalized type. -/
theorem join_idem : ∀ (a : PyType), normalized a = true → join a a = a
  | .unknown, _ | .any, _ | .none, _ => by simp [join]
  | .int, _ | .bool, _ | .str, _ | .float, _ => by simp [join, beq]
  | .cls n, _ => by simp [join, beq]
  | .list e, h => by rw [join, join_idem e (by simpa [normalized] using h)]
  | .set e, h => by rw [join, join_idem e (by simpa [normalized] using h)]
  | .dict k v, h => by
      have h' : normalized k = true ∧ normalized v = true := by simpa [normalized] using h
      rw [join, join_idem k h'.1, join_idem v h'.2]
  | .opt e, h => by
      have h' : e.beq .any = false ∧ normalized e = true := by simpa [normalized] using h
      rw [join, join_idem e h'.2]; cases e <;> simp_all [beq]
  | .tuple es, h => by
      have hw : es.attach.all (fun ⟨e, _⟩ => normalized e) = true := by simpa [normalized] using h
      have hall : ∀ e ∈ es, join e e = e := fun e he => join_idem e (normalized_mem hw he)
      rw [join]; simp only [beq_self_eq_true, if_true]; rw [tuple_help es hall]
  | .fn args r, h => by
      have h' : args.attach.all (fun ⟨e, _⟩ => normalized e) = true ∧ normalized r = true := by
        simpa [normalized] using h
      have hall : ∀ e ∈ args, join e e = e := fun e he => join_idem e (normalized_mem h'.1 he)
      rw [join]; simp only [beq_self_eq_true, if_true]
      rw [tuple_help args hall, join_idem r h'.2]
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have hm := ‹_ ∈ _›; have := List.sizeOf_lt_of_mem hm; omega)
--------------------------------------- LANDMARK ---------------------------------------

/-! ### Information preservation: `join` only reaches ⊥ from ⊥ ⊔ ⊥

Merging two KNOWN types never collapses to `unknown` (⊥) — the engine's merge moves UP the lattice,
never loses all information. Equivalently, `join a b = unknown` exactly when both inputs are `unknown`. -/

theorem join_ne_unknown (a b : PyType) (ha : a ≠ .unknown) (hb : b ≠ .unknown) :
    join a b ≠ .unknown := by
  cases a <;> cases b <;> simp_all only [ne_eq, reduceCtorEq, not_false_eq_true] <;>
    simp only [join] <;> (try split) <;> simp_all [beq]

theorem join_eq_unknown_iff (a b : PyType) :
    join a b = .unknown ↔ (a = .unknown ∧ b = .unknown) := by
  refine ⟨fun h => ?_, fun ⟨ha, hb⟩ => by subst ha; subst hb; simp⟩
  rcases Classical.em (a = .unknown) with rfl | ha
  · rcases Classical.em (b = .unknown) with rfl | hb
    · exact ⟨rfl, rfl⟩
    · rw [join_unknown_left] at h; exact absurd h hb
  · rcases Classical.em (b = .unknown) with rfl | hb
    · rw [join_unknown_right] at h; exact absurd h ha
    · exact absurd h (join_ne_unknown a b ha hb)

end TypeInfer.PyType
