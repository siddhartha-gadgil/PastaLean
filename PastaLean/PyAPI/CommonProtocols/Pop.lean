import PastaLean.Imports
import PastaLean.PyAPI.Dicts

namespace PastaLean

/--
Protocol for Python-style `pop`.

The key/index type `κ` and element/value type `β` are `outParam`s (not associated types):
an associated `Key`/`Elem` projection stays "stuck" and never reduces to a concrete type,
breaking resolution downstream of `pyPop`'s result. As `outParam`s they reduce concretely
once the container type `α` is known.
-/
class PyPop (α : Type) (κ : outParam Type) (β : outParam Type) where
  /--
  For dictionary-like types, `default` is used when the key is missing.
  For list-like types, `default` is used when the index is out of bounds.
  -/
  pyPop : α → κ → Option β → (Option β × α)

/--
Codegen should target this stable name; concrete types extend the behavior by adding
`PyPop` instances.
-/
def pyPop {α κ β : Type} [PyPop α κ β] (container : α) (key : κ)
    (default : Option β := none) : (Option β × α) :=
  PyPop.pyPop container key default

/--
Local list-pop helper kept here to avoid importing `PastaLean.PyAPI.Lists`, which
currently exposes other public method names that clash with dictionary names.
-/
def pyProtocolListPop (xs : List α) (idx : Int) (default : Option α := none) : (Option α × List α) :=
  if 0 <= idx then
    let natIdx := idx.toNat
    if hUpper : natIdx < xs.length then
      let value := xs.get ⟨natIdx, hUpper⟩
      (some value, xs.eraseIdx natIdx)
    else
      (default, xs)
  else
    (default, xs)

/-- Popping from List -/
instance : PyPop (List α) Int α where
  pyPop xs idx default := pyProtocolListPop xs idx default

/-! Python `pop` removes an element *and* returns it. Since the runtime containers are
immutable values, codegen splits this into two independent reads of the original container:
`pyPopValue` (the returned element) and `pyPopRest` (the container with that element removed).
The index defaults to `-1` (the last element), matching `list.pop()`; `set.pop()` removes an
arbitrary element, and "the last" is an acceptable arbitrary choice for the list-backed set. -/

/-- Normalize a possibly-negative `pop` index against a length; out-of-range stays out of range. -/
def pyPopIndex (len : Nat) (idx : Int) : Int :=
  if idx < 0 then (len : Int) + idx else idx

/-- Index-based `pop` over any ordered container (`List`, `Array`-via-`toList`, `PySet`), returning the
container's own type. Split from the *value* read so `pyPopRest` needs no `Inhabited`. -/
class PyPopRestSeq (σ : Type) where popRestAt : σ → Int → σ
/-- The element `pop(idx)` returns; needs `Inhabited` for the out-of-range fallback. -/
class PyPopValSeq (σ : Type) (α : outParam Type) where popValAt : σ → Int → α

instance : PyPopRestSeq (List α) where
  popRestAt xs idx :=
    let i := pyPopIndex xs.length idx
    if 0 ≤ i ∧ i < xs.length then xs.eraseIdx i.toNat else xs

instance [Inhabited α] : PyPopValSeq (List α) α where
  popValAt xs idx :=
    let i := pyPopIndex xs.length idx
    if 0 ≤ i ∧ i < xs.length then xs[i.toNat]! else default

/-- The element `pop(idx)` returns (defaulting to the last). Out-of-range yields `default`. -/
def pyPopValue {σ α : Type} [PyPopValSeq σ α] (xs : σ) (idx : Int := -1) : α :=
  PyPopValSeq.popValAt xs idx

/-- The container after `pop(idx)` removes its element (defaulting to the last). -/
def pyPopRest {σ : Type} [PyPopRestSeq σ] (xs : σ) (idx : Int := -1) : σ :=
  PyPopRestSeq.popRestAt xs idx

/-- Instance for popping from a HashMap. -/
instance [BEq α] [Hashable α] : PyPop (Std.HashMap α β) α β where
  pyPop m key default := pyDictPop m key default

/-- `d.pop(key[, default])` on a dict-like — value at `key` (with an optional default) and the dict
without it. Polymorphic over the concrete dict type (a plain `Std.HashMap`, a `PyDefaultDict`, …) so one
call site handles all of them — `d.pop(key)` shares its name with the 1-arg `list.pop(i)`, and the
codegen routes here once it knows the receiver is a dict. `δ` is the dict type; `κ`/`ν` (its key/value)
are `outParam`s of it. -/
class PyDictKeyPop (δ : Type) (κ : outParam Type) (ν : outParam Type) where
  keyPopValue : δ → κ → ν          -- `d.pop(key)`  — value at key (its `default` if absent)
  keyGetOr    : δ → κ → ν → ν      -- `d.pop(key, dflt)` — value at key, else `dflt`
  keyPopRest  : δ → κ → δ          -- the dict without `key`

instance [BEq α] [Hashable α] [Inhabited β] : PyDictKeyPop (Std.HashMap α β) α β where
  keyPopValue m key := (m.get? key).getD default
  keyGetOr m key d := (m.get? key).getD d
  keyPopRest m key := m.erase key

def pyDictKeyPopValue [PyDictKeyPop δ κ ν] (d : δ) (key : κ) : ν := PyDictKeyPop.keyPopValue d key
def pyDictKeyPopRest [PyDictKeyPop δ κ ν] (d : δ) (key : κ) : δ := PyDictKeyPop.keyPopRest d key

/-! Dict `d.pop(key, default)` splits like the list pop: `pyDictPopValue` is `d[key]` (or the default
when absent), `pyDictPopRest` is the map without that key. Both are polymorphic (`PyDictKeyPop`), so
`Counter`/`defaultdict.pop(k, dflt)` work as well as a plain dict. -/

/-- The value `d.pop(key, default)` returns: `d[key]` if present, else `default`. -/
def pyDictPopValue [PyDictKeyPop δ κ ν] (d : δ) (key : κ) (default : ν) : ν :=
  PyDictKeyPop.keyGetOr d key default

/-- The dict after `d.pop(key, ...)` removes `key`. -/
def pyDictPopRest [PyDictKeyPop δ κ ν] (d : δ) (key : κ) : δ := PyDictKeyPop.keyPopRest d key

end PastaLean
