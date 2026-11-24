import PastaLean.PyVerify.Twin.Attr
import PastaLean.PyAPI

/-! `TwinRel` (runnable type ↔ provable type) with its instances, and the `up`/`down` normal forms. -/

namespace PastaLean.Twin

/-- A runnable type `β` and its provable counterpart `α`, related by a bijection. -/
class TwinRel (β : Type) (α : outParam Type) where
  up : α → β
  down : β → α
  down_up : ∀ a, down (up a) = a
  up_down : ∀ b, up (down b) = b

export TwinRel (up down)

attribute [twin] TwinRel.down_up TwinRel.up_down

instance (priority := low) TwinRel.refl {α : Type} : TwinRel α α :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

/-- `β` contains an `Array` (or a runnable class), so loops over it must be conjugated. No identity
instance: this is what stops `forIn_twin` from firing on an already-canonical loop. -/
class TwinNontriv (β : Type) : Prop

instance {β : Type} : TwinNontriv (Array β) := ⟨⟩
instance {β₁ β₂ : Type} [TwinNontriv β₁] : TwinNontriv (MProd β₁ β₂) := ⟨⟩
instance (priority := low) {β₁ β₂ : Type} [TwinNontriv β₂] : TwinNontriv (MProd β₁ β₂) := ⟨⟩
instance {β₁ β₂ : Type} [TwinNontriv β₁] : TwinNontriv (β₁ × β₂) := ⟨⟩
instance (priority := low) {β₁ β₂ : Type} [TwinNontriv β₂] : TwinNontriv (β₁ × β₂) := ⟨⟩
instance {β : Type} [TwinNontriv β] : TwinNontriv (Option β) := ⟨⟩
instance {β : Type} [TwinNontriv β] : TwinNontriv (List β) := ⟨⟩

instance {β α : Type} [TwinRel β α] : TwinRel (Array β) (List α) where
  up l := (l.map up).toArray
  down b := b.toList.map down
  down_up l := by simp [Function.comp_def, TwinRel.down_up]
  up_down b := by
    apply Array.ext' ; simp [Function.comp_def, TwinRel.up_down]

instance {β α : Type} [TwinRel β α] : TwinRel (List β) (List α) where
  up l := l.map up
  down b := b.map down
  down_up l := by simp [Function.comp_def, TwinRel.down_up]
  up_down b := by simp [Function.comp_def, TwinRel.up_down]

instance {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] : TwinRel (β₁ × β₂) (α₁ × α₂) where
  up p := (up p.1, up p.2)
  down p := (down p.1, down p.2)
  down_up p := by simp [TwinRel.down_up]
  up_down p := by simp [TwinRel.up_down]

instance {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] :
    TwinRel (MProd β₁ β₂) (MProd α₁ α₂) where
  up p := ⟨up p.1, up p.2⟩
  down p := ⟨down p.1, down p.2⟩
  down_up p := by simp [TwinRel.down_up]
  up_down p := by simp [TwinRel.up_down]

instance {β α : Type} [TwinRel β α] : TwinRel (Option β) (Option α) where
  up o := o.map up
  down o := o.map down
  down_up o := by cases o <;> simp [TwinRel.down_up]
  up_down o := by cases o <;> simp [TwinRel.up_down]

instance {ε β α : Type} [TwinRel β α] : TwinRel (Except ε β) (Except ε α) where
  up e := e.map up
  down e := e.map down
  down_up e := by cases e <;> simp [Except.map, TwinRel.down_up]
  up_down e := by cases e <;> simp [Except.map, TwinRel.up_down]

/-! ### Normalising `up`/`down`

Normal form: an `Array` value is `L.toArray`; a class value is `up c`; identity relations vanish. -/

@[twin] theorem up_refl {α : Type} (a : α) : @up α α TwinRel.refl a = a := rfl
@[twin] theorem down_refl {α : Type} (a : α) : @down α α TwinRel.refl a = a := rfl
@[twin] theorem up_refl_fun {α : Type} : @up α α TwinRel.refl = id := rfl
@[twin] theorem down_refl_fun {α : Type} : @down α α TwinRel.refl = id := rfl

@[twin] theorem up_array {β α : Type} [TwinRel β α] (l : List α) :
    (up l : Array β) = (l.map up).toArray := rfl
@[twin] theorem down_array {β α : Type} [TwinRel β α] (b : Array β) :
    (down b : List α) = b.toList.map down := rfl
@[twin] theorem up_list {β α : Type} [TwinRel β α] (l : List α) :
    (up l : List β) = l.map up := rfl
@[twin] theorem down_list {β α : Type} [TwinRel β α] (l : List β) :
    (down l : List α) = l.map down := rfl
@[twin] theorem up_prod {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] (a : α₁) (b : α₂) :
    (up (a, b) : β₁ × β₂) = (up a, up b) := rfl
@[twin] theorem down_prod {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] (a : β₁) (b : β₂) :
    (down (a, b) : α₁ × α₂) = (down a, down b) := rfl
@[twin] theorem up_fst {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] (p : α₁ × α₂) :
    (up p : β₁ × β₂).1 = up p.1 := rfl
@[twin] theorem up_snd {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] (p : α₁ × α₂) :
    (up p : β₁ × β₂).2 = up p.2 := rfl
@[twin] theorem down_fst {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] (p : β₁ × β₂) :
    (down p : α₁ × α₂).1 = down p.1 := rfl
@[twin] theorem down_snd {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] (p : β₁ × β₂) :
    (down p : α₁ × α₂).2 = down p.2 := rfl
@[twin] theorem up_mprod {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] (p : MProd α₁ α₂) :
    (up p : MProd β₁ β₂) = ⟨up p.1, up p.2⟩ := rfl
@[twin] theorem down_mprod {β₁ α₁ β₂ α₂ : Type} [TwinRel β₁ α₁] [TwinRel β₂ α₂] (a : β₁) (b : β₂) :
    (down (MProd.mk a b) : MProd α₁ α₂) = ⟨down a, down b⟩ := rfl
@[twin] theorem up_some {β α : Type} [TwinRel β α] (a : α) :
    (up (some a) : Option β) = some (up a) := rfl
@[twin] theorem up_none {β α : Type} [TwinRel β α] : (up (none : Option α) : Option β) = none := rfl
@[twin] theorem down_some {β α : Type} [TwinRel β α] (b : β) :
    (down (some b) : Option α) = some (down b) := rfl
@[twin] theorem down_none {β α : Type} [TwinRel β α] : (down (none : Option β) : Option α) = none := rfl
@[twin] theorem up_ok {ε β α : Type} [TwinRel β α] (a : α) :
    (up (Except.ok a : Except ε α) : Except ε β) = .ok (up a) := rfl
@[twin] theorem up_error {ε β α : Type} [TwinRel β α] (e : ε) :
    (up (Except.error e : Except ε α) : Except ε β) = .error e := rfl
@[twin] theorem down_ok {ε β α : Type} [TwinRel β α] (b : β) :
    (down (Except.ok b : Except ε β) : Except ε α) = .ok (down b) := rfl
@[twin] theorem down_error {ε β α : Type} [TwinRel β α] (e : ε) :
    (down (Except.error e : Except ε β) : Except ε α) = .error e := rfl

attribute [twin] List.map_id' List.map_id_fun List.map_id List.toList_toArray id_eq
  Function.comp_id Function.id_comp Function.comp_def

-- `l.map up` is the normal form of a list of runnable values, so `List.map_map` is not a twin rule.
@[twin] theorem map_up_down {β α : Type} [TwinRel β α] (l : List α) :
    (l.map (up : α → β)).map down = l := by simp [Function.comp_def, TwinRel.down_up]
@[twin] theorem map_down_up {β α : Type} [TwinRel β α] (l : List β) :
    (l.map (down : β → α)).map up = l := by simp [Function.comp_def, TwinRel.up_down]
/-- A list of freshly built arrays (`[[0] * m for _ in …]` in the runnable twin) is a mapped list. -/
@[twin] theorem map_toArray_twin {ι α : Type} (g : ι → List α) (l : List ι) :
    l.map (fun x => (g x).toArray) = (l.map g).map (up : List α → Array α) := by
  simp [Function.comp_def, up_array, up_refl_fun]
@[twin] theorem map_toArray_twin' {α : Type} (l : List (List α)) :
    l.map List.toArray = l.map (up : List α → Array α) := by
  simp [up_array, up_refl_fun]

end PastaLean.Twin
