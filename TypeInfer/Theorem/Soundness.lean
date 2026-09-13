import TypeInfer.Theorem.Associativity

/-!
# Semantic soundness — relating inferred types to runtime values

Main result: **`hasType_join_left`** — `HasType v a → HasType v (a ⊔ b)`. The lattice laws elsewhere
verify `join`'s ALGEBRAIC structure; this verifies its SEMANTIC meaning. For a lattice-based abstract
inferrer this is the analog of classical type soundness ("an inferred type never lies about the
runtime"): `join` OVER-APPROXIMATES — a value that had type `a` still has type `a ⊔ b`, so widening
never excludes an admitted value. Proved on the FULL lattice (`hasType_join_left`), not just the numeric
tower.
-/

namespace TypeInfer.PyType

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- A minimal model of Python runtime values (the core of PastaLean's `PyValue`). -/
inductive Val where
  | vint (n : Int) | vbool (b : Bool) | vstr (s : String) | vfloat (f : Float)
  | vnone | vlist (xs : List Val) | vcls (name : String)
  deriving Inhabited

/-- `HasType v T` : the runtime value `v` inhabits inferred type `T`. Encodes the numeric tower
(`bool <: int <: float`), `any` = ⊤ (admits everything), `unknown` = ⊥ (admits nothing), and
`opt T` = `T ∪ {None}`. -/
def HasType : Val → PyType → Prop
  | _,         .any     => True
  | _,         .unknown => False
  | .vbool _,  .bool    => True
  | .vbool _,  .int     => True         -- bool <: int
  | .vbool _,  .float   => True         -- bool <: float
  | .vint _,   .int     => True
  | .vint _,   .float   => True         -- int <: float
  | .vfloat _, .float   => True
  | .vstr _,   .str     => True
  | .vnone,    .none    => True
  | .vcls n,   .cls m   => n = m
  | .vlist xs, .list t  => ∀ x ∈ xs, HasType x t
  | v,         .opt t   => v = .vnone ∨ HasType v t
  | _,         _        => False

/-! ### The numeric tower is *semantically* real -/

theorem hasType_bool_int   (v : Val) : HasType v .bool → HasType v .int   := by cases v <;> simp [HasType]
theorem hasType_int_float  (v : Val) : HasType v .int  → HasType v .float := by cases v <;> simp [HasType]
theorem hasType_bool_float (v : Val) : HasType v .bool → HasType v .float := by cases v <;> simp [HasType]

/-! ### ⊤ admits everything, ⊥ admits nothing -/

theorem hasType_any (v : Val) : HasType v .any := by simp [HasType]
theorem not_hasType_unknown (v : Val) : ¬ HasType v .unknown := by simp [HasType]

/-! ### `join` over-approximates (soundness of the merge)

For the general shape `HasType v a → HasType v (join a b)`: when `b = unknown` the join is `a`; when
either side is `any` the join is `any` (which admits `v`); on the numeric tower it widens up the tower,
which `v` still inhabits. We prove the tower case (the semantically interesting one) in full. -/

theorem hasType_join_unknown_right (v : Val) (a : PyType) (h : HasType v a) :
    HasType v (join a .unknown) := by rw [join_unknown_right]; exact h

theorem hasType_join_any (v : Val) (a b : PyType) (h : join a b = .any) :
    HasType v (join a b) := by rw [h]; exact hasType_any v

/-- **Join over-approximates on the numeric tower:** for numeric `a`, `b`, a value of type `a` also has
type `a ⊔ b`. This is exactly the soundness of the tower widening the engine performs so that a
container written with both ints and floats stays `list[float]` rather than collapsing to `Any`. -/
theorem hasType_join_tower (v : Val) (a b : PyType)
    (ha : a = .int ∨ a = .bool ∨ a = .float) (hb : b = .int ∨ b = .bool ∨ b = .float)
    (h : HasType v a) : HasType v (join a b) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp only [join] <;>
    first
      | exact h
      | exact hasType_int_float v h
      | exact hasType_bool_int v h
      | exact hasType_bool_float v h
      | simp_all [beq]

/-! ### General semantic soundness: `join` over-approximates on the WHOLE lattice

The full statement — for *any* types `a`, `b`, a value of type `a` still has type `a ⊔ b`. So the
engine's widening never drops an admitted runtime value, on every type shape (containers, `Optional`,
classes), not just the numeric tower. The `Val` model has no `set`/`dict`/`tuple`/`fn` inhabitant, so
those `a`-heads admit nothing (`HasType` is `False`) and the claim is vacuous there; the real content is
the scalar/`none`/`cls` cases and the `list`/`Optional` congruences, the latter recursing on the element
type via the inductive hypothesis. -/
private theorem hasType_join_left_aux : ∀ (n : Nat) (v : Val) (a b : PyType),
    sizeOf a + sizeOf b ≤ n → HasType v a → HasType v (join a b) := by
  intro n
  induction n with
  | zero => intro v a b hn h; have := sizeOf_pos a; omega
  | succ n ih =>
    intro v a b hn h
    cases a <;> cases b
    -- scalar/`None`/`unknown`/`any` heads, and heads that admit no value, close by evaluation.
    all_goals (try (cases v <;> simp_all [HasType, join, beq]; done))
    -- `cls ⊔ cls` is `if n = m then cls n else any`; the value is `vcls n`, admitted either way.
    all_goals (try (cases v <;> simp_all only [HasType, join, beq] <;> split <;> simp_all [HasType]; done))
    -- `list e₁ ⊔ list e₂ = list (e₁ ⊔ e₂)`: widen each element by the IH.
    case list.list e1 e2 =>
      cases v <;> simp only [join, HasType] at h ⊢ <;>
        first
        | exact h.elim
        | (intro x hx; exact ih x e1 e2 (by simp only [PyType.list.sizeOf_spec] at hn; omega) (h x hx))
    -- `opt ⊔ X` and `X ⊔ opt`: split `join`'s Optional combinator; the `opt` branch holds because the
    -- value is `None`, or by the IH on the smaller join has the combined inner type.
    all_goals
      (simp only [join]
       split
       · simp [HasType]
       · simp only [HasType]
         first
         | (rcases h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr (ih v _ _ (by simp only [PyType.opt.sizeOf_spec] at hn; omega) h))
         | exact Or.inr (join_comm _ _ ▸ ih v _ _ (by simp only [PyType.opt.sizeOf_spec] at hn; omega) h))

--------------------------------------- LANDMARK ---------------------------------------
/-- **Semantic soundness of the merge (full lattice):** `HasType v a → HasType v (a ⊔ b)`. An inferred
type is only ever *widened* by `join`, and widening never excludes a value the program can actually
produce — the inference analogue of "a well-typed program does not go wrong" (Milner; Wright–Felleisen).
This is `#5` (semantic soundness) in full: `join` over-approximates on every type shape, not just the
numeric tower. -/
theorem hasType_join_left (v : Val) (a b : PyType) (h : HasType v a) : HasType v (join a b) :=
  hasType_join_left_aux (sizeOf a + sizeOf b) v a b (Nat.le_refl _) h
--------------------------------------- LANDMARK ---------------------------------------

/-- Soundness of the merge on the right, by commutativity. -/
theorem hasType_join_right (v : Val) (a b : PyType) (h : HasType v b) : HasType v (join a b) := by
  rw [join_comm]; exact hasType_join_left v b a h

end TypeInfer.PyType
