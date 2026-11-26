import PastaLean.PyAPI.PyPanic
import PastaLean.Imports
import PastaLean.PyAPI.Core
import PastaLean.PyAPI.CommonProtocols.Iterable

namespace PastaLean

/--
Typeclass for Python-style item access, `container[index]`.

The index type `ι` and value type `β` are `outParam`s (not associated types) so that the
result type of `pyGetItem c i` reduces to a concrete type once the container type is known —
an associated-type projection like `inst.Value` would stay stuck and break downstream
typeclass resolution (e.g. `PyPrintable`/`PyHAdd` on the result). Codegen emits one stable
name `pyGetItem c i` for the generic index case; string and tuple indexing keep their own
dedicated lowering.
-/
class PyGetItem (α : Type) (ι : outParam Type) (β : outParam Type) where
  getItem : α → ι → β

/-- Dispatch `container[index]` through the `PyGetItem` typeclass. -/
def pyGetItem {α ι β : Type} [PyGetItem α ι β] (c : α) (i : ι) : β :=
  PyGetItem.getItem c i

/-- Readable indexing notation for the generated code: `c⦋i⦌` is exactly `pyGetItem c i`, so it
works for every `PyGetItem` instance (lists, strings, dicts, `Option`-wrapped values) and chains
for nested access: `m⦋i⦌⦋j⦌`.
You can write it like \rsimplex and \lsimplex
-/
notation:max c "⦋" i "⦌" => pyGetItem c i

/-- Lists index by `Int` with Python negative-index semantics (reusing `pyListGetItem`). -/
instance {β : Type} [Inhabited β] : PyGetItem (List β) Int β where
  getItem xs i := pyListGetItem xs i

/-- A homogeneous tuple `(a, b, c, …)` (a nested product all of one type) supports Python-style
indexing `t[i]` by flattening to a `List α` and indexing that, so both constant and variable indices
work (`t[2]`, `t[i]`). It reuses the recursive `PyIterable (α × β) α` flatten. A heterogeneous tuple
has no such `PyIterable`, so its element types differ per slot — that case is handled by static
projection in the subscript codegen, which knows the constant index at compile time. -/
instance {α β : Type} [PyIterable (α × β) α] [Inhabited α] : PyGetItem (α × β) Int α where
  getItem p i := pyListGetItem (pyIter p) i

/-- A string indexed by `Int` yields the one-character string at that position (negative indices
count from the end), since Python has no separate character type — `s[i]` is a length-1 `str`.
This keeps `s[i]` interoperable with string literals (`s[i] == 'x'`), `ord`, and the string
methods, all of which are `String`-oriented. An out-of-range index yields the empty string. -/
instance : PyGetItem String Int String where
  getItem s i := pyStringGetItemStr s i

/-- Indexing into an `Option`-wrapped value (e.g. an element read from a `[None] * n` placeholder
list after it has been filled): unwrap and index the contents. A `none` (never-filled) slot
yields the element default, mirroring how Python would have stored a real value before indexing. -/
instance {α ι β : Type} [Inhabited α] [Inhabited β] [PyGetItem α ι β] : PyGetItem (Option α) ι β where
  getItem o i := pyGetItem (o.getD default) i

/-- Dictionaries index by key; a missing key panics with a `KeyError`, matching Python's
strict `d[k]` (use `d.get(k, default)` for the non-raising form). -/
instance {κ ν : Type} [BEq κ] [Hashable κ] [Inhabited ν] : PyGetItem (Std.HashMap κ ν) κ ν where
  getItem m k :=
    match m.get? k with
    | some v => v
    | none => PastaLean.pyPanic "KeyError"

end PastaLean
