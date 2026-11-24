import PastaLean.PyVerify.Twin.Relation

/-! The `@[twin]` bridge lemmas: loops over runnable state, monad plumbing, Bool tests, and each
runnable (`Array`) runtime operation against its provable (`List`) counterpart. -/

namespace PastaLean.Twin

/-! ### Loops: conjugate an `Array`-state loop to the `List`-state loop -/

/-- `ForInStep.map`, for pushing a state conjugation through a loop body's result. -/
def stepMap {β α : Type} (f : β → α) : ForInStep β → ForInStep α
  | .done b => .done (f b)
  | .yield b => .yield (f b)

@[twin] theorem stepMap_done {β α : Type} (f : β → α) (b : β) :
    stepMap f (.done b) = .done (f b) := rfl
@[twin] theorem stepMap_yield {β α : Type} (f : β → α) (b : β) :
    stepMap f (.yield b) = .yield (f b) := rfl

/-- A loop whose state type `σ` holds runnable-only data runs, step for step, as the canonical loop
over `down` of its state. Fires only on a `TwinNontriv` state, so it rewrites each loop once. -/
@[twin] theorem forIn_twin {m : Type → Type} [Monad m] [LawfulMonad m] {ι σ τ : Type}
    [TwinRel σ τ] [TwinNontriv σ] (xs : List ι) (init : σ) (g : ι → σ → m (ForInStep σ)) :
    forIn xs init g = up <$> forIn xs (down init) (fun i s => stepMap down <$> g i (up s)) := by
  induction xs generalizing init with
  | nil => simp [TwinRel.up_down]
  | cons x xs ih =>
    simp only [List.forIn_cons, TwinRel.up_down, map_bind, bind_map_left]
    congr 1; funext r
    cases r <;> simp [stepMap, ih, TwinRel.up_down]

/-- `forIn_twin` for `for h : i in xs` loops (membership-carrying bodies). -/
@[twin] theorem forIn'_twin {m : Type → Type} [Monad m] [LawfulMonad m] {ι σ τ : Type}
    [TwinRel σ τ] [TwinNontriv σ] (xs : List ι) (init : σ)
    (g : (i : ι) → i ∈ xs → σ → m (ForInStep σ)) :
    forIn' xs init g =
      up <$> forIn' xs (down init) (fun i h s => stepMap down <$> g i h (up s)) := by
  induction xs generalizing init with
  | nil => simp [TwinRel.up_down]
  | cons x xs ih =>
    simp only [List.forIn'_cons, TwinRel.up_down, map_bind, bind_map_left]
    congr 1; funext r
    cases r <;> simp [stepMap, ih, TwinRel.up_down]

attribute [twin] List.forIn_toArray

/-! ### Monad plumbing for pushing `up <$>` / `stepMap down <$>` inward -/

@[twin] theorem map_ite' {m : Type → Type} [Functor m] {α β : Type} (f : α → β) (c : Prop)
    [Decidable c] (x y : m α) : f <$> (if c then x else y) = if c then f <$> x else f <$> y := by
  split <;> rfl
@[twin] theorem map_dite' {m : Type → Type} [Functor m] {α β : Type} (f : α → β) (c : Prop)
    [Decidable c] (x : c → m α) (y : ¬c → m α) :
    f <$> (if h : c then x h else y h) = if h : c then f <$> x h else f <$> y h := by
  split <;> rfl
@[twin] theorem map_throw_exceptT {ε : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (f : α → β) (e : ε) : f <$> (throw e : ExceptT ε m α) = throw e := by
  simp [throw, throwThe, MonadExceptOf.throw]

@[twin] theorem up_ite {β α : Type} [TwinRel β α] (c : Prop) [Decidable c] (x y : α) :
    (up (if c then x else y) : β) = if c then up x else up y := by split <;> rfl
@[twin] theorem up_dite {β α : Type} [TwinRel β α] (c : Prop) [Decidable c] (x : c → α)
    (y : ¬c → α) : (up (if h : c then x h else y h) : β) = if h : c then up (x h) else up (y h) := by
  split <;> rfl
@[twin] theorem run_ite {α : Type} (c : Prop) [Decidable c] (x y : Id α) :
    (if c then x else y).run = if c then x.run else y.run := by split <;> rfl
@[twin] theorem run_dite {α : Type} (c : Prop) [Decidable c] (x : c → Id α) (y : ¬c → Id α) :
    (if h : c then x h else y h).run = if h : c then (x h).run else (y h).run := by split <;> rfl

attribute [twin] map_pure map_bind pure_bind bind_pure bind_assoc Functor.map_map bind_map_left
  Id.run_pure Id.run_bind Id.run_map

/-! ### Bool tests ↦ the decided Prop -/

@[twin] theorem beq_twin {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := Bool.beq_eq_decide_eq a b
@[twin] theorem bne_twin {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a != b) = decide (a ≠ b) := by simp [bne, Bool.beq_eq_decide_eq]
@[twin] theorem and_twin (p q : Prop) [Decidable p] [Decidable q] :
    (decide p && decide q) = decide (p ∧ q) := by simp
@[twin] theorem or_twin (p q : Prop) [Decidable p] [Decidable q] :
    (decide p || decide q) = decide (p ∨ q) := by simp
@[twin] theorem not_twin (p : Prop) [Decidable p] : (!decide p) = decide ¬p := by simp

attribute [twin] decide_eq_true_eq ne_eq Bool.and_eq_true Bool.or_eq_true Bool.not_eq_true'
  Bool.not_eq_true

/-! ### `Array` runtime ↦ `List` runtime

Each runnable-twin op on `l.toArray` is its provable-twin op on `l`, re-wrapped. -/

@[twin] theorem pyArrayAppend_twin {α : Type} (l : List α) (v : α) :
    pyArrayAppend l.toArray v = (pyAppend l v).toArray := by
  simp [pyArrayAppend, pyAppend, pyListAppend]

@[twin] theorem pyArrayExtend_twin {α : Type} (l m : List α) :
    pyArrayExtend l.toArray m.toArray = (pyExtend l m).toArray := by
  simp [pyArrayExtend, pyExtend, pyListExtend]

@[twin] theorem pyArrayReverse_twin {α : Type} (l : List α) :
    pyArrayReverse l.toArray = (pyReverse l).toArray := by
  simp [pyArrayReverse, pyReverse, pyListReverse]

@[twin] theorem pyArrayInsert_twin {α : Type} (l : List α) (i : Int) (v : α) :
    pyArrayInsert l.toArray i v = (pyInsert l i v).toArray := by
  simp [pyArrayInsert, pyInsert]

@[twin] theorem pyArrayPopValue_twin {α : Type} [Inhabited α] (l : List α) (i : Int) :
    pyArrayPopValue l.toArray i = pyPopValue l i := by
  unfold pyArrayPopValue pyPopValue
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.size_toArray] at h
    obtain ⟨rfl, hl⟩ := h
    simp only [PyPopValSeq.popValAt, pyPopIndex, Array.back!, getElem!_def, List.size_toArray,
      List.getElem?_toArray]
    split_ifs <;> first | omega | rw [show ((l.length : Int) + -1).toNat = l.length - 1 by omega]
  · simp

@[twin] theorem pyArrayPopRest_twin {α : Type} (l : List α) (i : Int) :
    pyArrayPopRest l.toArray i = (pyPopRest l i).toArray := by
  unfold pyArrayPopRest pyPopRest
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.size_toArray] at h
    obtain ⟨rfl, hl⟩ := h
    simp only [PyPopRestSeq.popRestAt, pyPopIndex, List.pop_toArray]
    split_ifs <;>
      first
      | omega
      | (rw [show ((l.length : Int) + -1).toNat = l.length - 1 by omega, List.dropLast_eq_eraseIdx]; omega)
  · simp

@[twin] theorem pyArrayPopLeftValue_twin {α : Type} [Inhabited α] (l : List α) :
    pyArrayPopLeftValue l.toArray = pyPopLeftValue l := by
  cases l <;> simp [pyArrayPopLeftValue, pyPopLeftValue]

@[twin] theorem pyArrayPopLeftRest_twin {α : Type} (l : List α) :
    pyArrayPopLeftRest l.toArray = (pyPopLeftRest l).toArray := by
  simp [pyArrayPopLeftRest, pyPopLeftRest]

private theorem repeat_loop {α : Type} (l acc : List α) (xs : List Nat) :
    (forIn (m := Id) xs acc.toArray fun _ r => ForInStep.yield (r ++ l.toArray))
      = (acc ++ (List.replicate xs.length l).flatten).toArray := by
  induction xs generalizing acc with
  | nil => simp; rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    have h := ih (acc ++ l)
    rw [← List.append_toArray] at h
    exact h.trans (by simp [List.replicate_succ])

@[twin] theorem pyArrayRepeat_twin {α : Type} (l : List α) (n : Int) :
    pyArrayRepeat l.toArray n = (pyListRepeat l n).toArray := by
  unfold pyArrayRepeat pyListRepeat
  split
  · rfl
  · simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
    have := repeat_loop l [] (List.range' 0 [0:n.toNat].size 1)
    simp only [List.nil_append, List.length_range'] at this
    exact this.trans (by simp [Std.Legacy.Range.size])

/-- `panic!` is `default` in the logic; the twins' messages and source positions differ. -/
@[twin] theorem panic_twin {α : Type} [Inhabited α] (m d : String) (l c : Nat) (msg : String) :
    (panicWithPosWithDecl m d l c msg : α) = default := rfl

@[twin] theorem pyGetItem_array_twin {α : Type} [Inhabited α] (l : List α) (i : Int) :
    pyGetItem l.toArray i = pyGetItem l i := by
  simp only [pyGetItem, PyGetItem.getItem, pyArrayGetItem, pyListGetItem, List.size_toArray]
  split_ifs <;> first | rfl | (simp only [getElem!_def, List.getElem?_toArray]; rfl)

@[twin] theorem pySetItem_array_twin {α : Type} (l : List α) (i : Int) (v : α) :
    pySetItem l.toArray i v = (pySetItem l i v).toArray := by
  simp only [pySetItem, PySetItem.setItem, pyArraySetItem, List.size_toArray]
  split_ifs <;> first | rfl | simp [Array.set!]

@[twin] theorem pyModifyItem_array_twin {α : Type} [Inhabited α] (l : List α) (i : Int)
    (g : α → α) : pyModifyItem l.toArray i g = (pyModifyItem l i g).toArray := by
  simp only [pyModifyItem, PyModifyItem.modifyItem, List.size_toArray]
  split_ifs <;> first | rfl | simp [List.modify_eq_set, List.getD_eq_getElem?_getD]

@[twin] theorem pyLen_array_twin {α : Type} (l : List α) : pyLen l.toArray = pyLen l := by
  simp [pyLen, PyLen.pyLen]

@[twin] theorem pySlice_array_twin {α : Type} (l : List α) (lo hi st : Option Int) :
    pySlice l.toArray lo hi st = (pySlice l lo hi st).toArray := by
  simp [pySlice, PySlice.slice]

@[twin] theorem pyContains_array_twin {α : Type} [BEq α] (l : List α) (x : α) :
    pyContains l.toArray x = pyContains l x := by
  simp [pyContains, PyContains.contains]

@[twin] theorem pyTruthy_array_twin {α : Type} (l : List α) : pyTruthy l.toArray = pyTruthy l := by
  simp [pyTruthy, PyTruthy.truthy]

@[twin] theorem pyBool_array_twin {α : Type} (l : List α) :
    PyBool.pyBool l.toArray = PyBool.pyBool l := by
  simp [PyBool.pyBool]

@[twin] theorem pyStringify_array_twin {α : Type} [PyPrintable α] (l : List α) :
    PyPrintable.pyStringify l.toArray = PyPrintable.pyStringify l := by
  simp [PyPrintable.pyStringify]

@[twin] theorem pyClear_array_twin {α : Type} (l : List α) :
    pyClear l.toArray = (pyClear l).toArray := by
  simp [pyClear, PyClear.pyClear, pyListClear]

@[twin] theorem pyCount_array_twin {α : Type} [DecidableEq α] (l : List α) (x : α) :
    pyCount l.toArray x = pyCount l x := by
  simp [pyCount, PyCount.pyCount]

@[twin] theorem pyIndex_array_twin {α : Type} [DecidableEq α] (l : List α) (x : α) (s : Int) :
    pyIndex l.toArray x s = pyIndex l x s := by
  simp only [pyIndex, PyIndex.pyIndex]
  rfl

@[twin] theorem pyIter_array_twin {α : Type} (l : List α) : pyIter l.toArray = pyIter l := by
  simp [pyIter, PyIterable.toPyList]

/-! ### Lists of runnable elements (`List (Array α)` rows, lists of runnable objects)

A list whose elements are runnable values is `l.map up` in normal form; each op is the provable op
on `l`, conjugated element-wise. Reads need `up default = default` (the out-of-range fallback). -/

/-- `up` preserves the `Inhabited` default (the value an out-of-range read falls back to). -/
class TwinDefault (β α : Type) [TwinRel β α] [Inhabited β] [Inhabited α] : Prop where
  up_default : (up (default : α) : β) = default

instance (priority := low) {α : Type} [Inhabited α] : @TwinDefault α α TwinRel.refl _ _ := ⟨rfl⟩
instance {β α : Type} [TwinRel β α] : TwinDefault (Array β) (List α) := ⟨rfl⟩
instance {β α : Type} [TwinRel β α] : TwinDefault (List β) (List α) := ⟨rfl⟩

@[twin] theorem pyIter_map {α β : Type} (l : List α) (f : α → β) :
    pyIter (l.map f) = (pyIter l).map f := rfl

@[twin] theorem pyLen_map {α β : Type} (l : List α) (f : α → β) : pyLen (l.map f) = pyLen l := by
  simp [pyLen, PyLen.pyLen]

@[twin] theorem pyAppend_map_twin {β α : Type} [TwinRel β α] (l : List α) (v : β) :
    pyAppend (l.map (up : α → β)) v = (pyAppend l (down v)).map up := by
  simp [pyAppend, pyListAppend, TwinRel.up_down]

theorem optGetD_map_up {β α : Type} [TwinRel β α] [Inhabited β] [Inhabited α]
    [TwinDefault β α] (o : Option α) :
    (o.map (up : α → β)).getD default = up (o.getD default) := by
  cases o <;> simp [TwinDefault.up_default]

@[twin] theorem pyGetItem_map_twin {β α : Type} [TwinRel β α] [Inhabited β] [Inhabited α]
    [TwinDefault β α] (l : List α) (i : Int) :
    pyGetItem (l.map up : List β) i = up (pyGetItem l i) := by
  simp only [pyGetItem, PyGetItem.getItem, pyListGetItem, List.length_map,
    List.getElem?_map]
  split_ifs <;> first
    | exact TwinDefault.up_default.symm
    | (split <;> simp_all)

@[twin] theorem pySetItem_map_twin {β α : Type} [TwinRel β α] (l : List α) (i : Int) (v : β) :
    pySetItem (l.map (up : α → β)) i v = (pySetItem l i (down v)).map up := by
  simp only [pySetItem, PySetItem.setItem, List.length_map]
  split_ifs <;> first | rfl | simp [List.map_set, TwinRel.up_down]

@[twin] theorem pyModifyItem_map_twin {β α : Type} [TwinRel β α] [Inhabited β] [Inhabited α]
    [TwinDefault β α] (l : List α) (i : Int) (g : β → β) :
    pyModifyItem (l.map (up : α → β)) i g = (pyModifyItem l i (fun x => down (g (up x)))).map up := by
  simp only [pyModifyItem, PyModifyItem.modifyItem, List.length_map]
  split_ifs <;> first | rfl |
    simp [List.map_set, TwinRel.up_down, List.getD_eq_getElem?_getD, optGetD_map_up]

attribute [twin] List.forIn_map

end PastaLean.Twin
