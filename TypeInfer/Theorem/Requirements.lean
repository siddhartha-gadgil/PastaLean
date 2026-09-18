import TypeInfer.Diagnostics.Basic
import TypeInfer.Theorem.Meet
import TypeInfer.Theorem.Consistency

/-!
# The requirement algebra is a bounded meet-semilattice

`TypeInfer.Diagnostics` lifts `meet` to `Req = Option PyType` so that "no requirement yet" (`none`) and
"requirements that cannot all be met" (`some unknown`) are DIFFERENT points — the distinction
`PyType`, with its single bottom, cannot make, and the reason folding uses with `join` turned every
type error into a silently boxed `PyAny`.

Everything the fold needs is inherited from `meet`:

* **`narrow_comm`**, **`narrow_assoc`**, **`narrow_idem`** — a slot's verdict does not depend on the
  order or grouping in which its uses are visited. This is the `Req` counterpart of what
  `join_comm`/`join_assoc`/`join_idem` give the value-flow fixpoint, and unlike `join_idem` it holds
  with no `normalized` side condition.
* **`narrow_top_left`/`narrow_top_right`** — `none` is the identity, so a use site that constrains
  nothing really does contribute nothing.
* **`narrow_bot_left`/`narrow_bot_right`** — a contradiction is absorbing: once two uses conflict, no
  further use can paper over it. That is what makes `contradictory` a stable verdict rather than an
  artifact of where the fold stopped.

Main result: **`hasType_commit`** — if the engine commits type `t` for a slot, then every runtime
value of type `t` satisfies *every* use that slot has. So committing the meet of a slot's
requirements is semantically sound, which is what licenses reporting a type instead of boxing.

Also **`checkAnnotation_refl`**: the annotation check never flags a slot against its own type, i.e.
the checker has no false positives on agreeing input.
-/

namespace TypeInfer

open PyType (meet_comm meet_assoc meet_idem hasType_meet consistent_refl HasType Val)

namespace Req

/-! ### Bounds -/

@[simp] theorem narrow_top_left (r : Req) : narrow top r = r := by cases r <;> rfl
@[simp] theorem narrow_top_right (r : Req) : narrow r top = r := by cases r <;> rfl

@[simp] theorem narrow_bot_left (r : Req) : narrow bot r = bot := by
  cases r <;> simp [narrow, bot]

@[simp] theorem narrow_bot_right (r : Req) : narrow r bot = bot := by
  cases r <;> simp [narrow, bot]

/-! ### Semilattice laws, inherited from `meet` -/

theorem narrow_comm (a b : Req) : narrow a b = narrow b a := by
  cases a <;> cases b <;> simp [narrow, meet_comm]

theorem narrow_assoc (a b c : Req) : narrow (narrow a b) c = narrow a (narrow b c) := by
  cases a <;> cases b <;> cases c <;> simp [narrow, meet_assoc]

theorem narrow_idem (a : Req) : narrow a a = a := by
  cases a <;> simp [narrow, meet_idem]

/-- A contradiction, once reached, is permanent — the verdict cannot be undone by a later use. -/
theorem contradictory_narrow_left {a : Req} (h : a.contradictory) (b : Req) :
    (narrow a b).contradictory := by
  match a, h with
  | some .unknown, _ => cases b <;> simp [narrow, contradictory]

/-! ### Semantic soundness of committing the meet

`Sat r v` reads "the runtime value `v` meets requirement `r`" — vacuously true when there is no
requirement. The fold only ever strengthens, so satisfying the folded requirement means satisfying
every one that went into it. -/

/-- The runtime value `v` satisfies requirement `r`. -/
def Sat (r : Req) (v : Val) : Prop :=
  match r with
  | Option.none => True
  | some t => HasType v t

/-- Satisfying a narrowed requirement means satisfying both of its parts — the `Req` lift of
`hasType_meet`. -/
theorem sat_narrow {a b : Req} {v : Val} (h : Sat (narrow a b) v) : Sat a v ∧ Sat b v := by
  match a, b with
  | Option.none, _ => exact ⟨trivial, by simpa [Sat, narrow] using h⟩
  | some _, Option.none => exact ⟨by simpa [Sat, narrow] using h, trivial⟩
  | some x, some y =>
      simp only [narrow, Sat] at h ⊢
      exact hasType_meet v x y h

/-- Folding requirements never loses one: whatever satisfies the fold satisfies each ingredient (and
the accumulator it started from). -/
theorem sat_foldl : ∀ (rs : List Req) (acc : Req) (v : Val),
    Sat (rs.foldl narrow acc) v → Sat acc v ∧ ∀ r ∈ rs, Sat r v
  | [], acc, _, h => ⟨h, by simp⟩
  | r :: rs, acc, v, h => by
      obtain ⟨hacc, hrest⟩ := sat_foldl rs (narrow acc r) v (by simpa using h)
      obtain ⟨ha, hr⟩ := sat_narrow hacc
      refine ⟨ha, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact hrest x hx

theorem sat_narrowAll {rs : List Req} {v : Val} (h : Sat (narrowAll rs) v) :
    ∀ r ∈ rs, Sat r v :=
  (sat_foldl rs top v h).2

/-- A committed type is the requirement itself: `commit?` only answers on a real, non-contradictory
requirement. -/
theorem commit_eq {r : Req} {t : PyType} (h : r.commit? = some t) : r = some t := by
  match r with
  | Option.none => simp [commit?] at h
  | some s => cases s <;> simp_all [commit?]

end Req

--------------------------------------- LANDMARK ---------------------------------------
/-- **Soundness of committing the meet of a slot's requirements.** If the engine commits `t` for a
slot whose uses demanded the types in `evidence`, then every runtime value of type `t` satisfies
*every* one of those uses. So the narrowed answer is not a guess: it is a type that provably works
everywhere the slot is used, which is exactly the licence to report it rather than box it as `PyAny`.

The dual of `hasType_join_left`, which says widening never EXCLUDES a value the program produces;
this says narrowing never ADMITS a value some use would reject. -/
theorem hasType_commit {evidence : List PyType} {t : PyType} {v : PyType.Val}
    (hc : (Req.ofEvidenceAll evidence).commit? = some t) (hv : PyType.HasType v t) :
    ∀ u ∈ evidence, u ≠ .unknown → PyType.HasType v u := by
  intro u hu hune
  have hall := Req.sat_narrowAll (rs := evidence.map Req.ofEvidence) (v := v)
    (by rw [← Req.ofEvidenceAll, Req.commit_eq hc]; exact hv)
  have hsat : Req.Sat (Req.ofEvidence u) v := hall _ (List.mem_map_of_mem hu)
  cases u <;> simp_all [Req.ofEvidence, Req.Sat]
--------------------------------------- LANDMARK ---------------------------------------

/-! ### The checker has no false positives on agreeing input -/

/-- The annotation check never flags a slot whose annotation already matches what was inferred. -/
theorem checkAnnotation_refl (scope slot : String) (t : PyType) :
    checkAnnotation scope slot t t = Option.none := by
  cases t <;> simp only [checkAnnotation] <;>
    first | rfl | rw [if_pos (PyType.consistent_refl _)]

/-- A gradual slot is never flagged: `unknown` on either side is "no static claim". -/
theorem checkAnnotation_unknown (scope slot : String) (t : PyType) :
    checkAnnotation scope slot .unknown t = Option.none ∧
      checkAnnotation scope slot t .unknown = Option.none := by
  constructor <;> cases t <;> simp [checkAnnotation]

/-- A value is never rejected by a slot with no requirements. -/
theorem checkValue_top (scope slot : String) (v : PyType) :
    checkValue scope slot Req.top v = Option.none := by simp [checkValue, Req.top, Req.commit?]

end TypeInfer
