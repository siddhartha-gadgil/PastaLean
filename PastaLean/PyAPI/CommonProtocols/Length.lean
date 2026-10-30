import PastaLean.PyAPI.PyPanic
import PastaLean.Imports

namespace PastaLean

/--
Typeclass for Python-style length queries.

Use this for builtins like `len(x)` when one Python surface operation should work
across several Lean runtime types.

This file defines the stable public Lean surface `pyLen`; individual runtime types
extend it by adding `PyLen` instances rather than changing codegen.
-/
class PyLen (α : Type) where
  pyLen : α → Int

/-- Dispatch `len`-style queries through the `PyLen` typeclass. -/
def pyLen {α : Type} [PyLen α] (x : α) : Int :=
  PyLen.pyLen x

/-- Lists use their element count as Python length. -/
instance : PyLen (List α) where
  pyLen xs := xs.length

/-- Strings use their Lean string length as Python length. -/
instance : PyLen String where
  pyLen s := s.length

/-- Hash maps use their number of stored key-value pairs as Python length. -/
instance [BEq α] [Hashable α] : PyLen (Std.HashMap α β) where
  pyLen m := m.size

/-- `len` of a nullable value: unwrap and measure, or raise as Python's `len(None)` does. Fires when a
`None`-initialised variable later holds a sized value and `len` is called in a truth-guarded branch. -/
instance {α : Type} [PyLen α] : PyLen (Option α) where
  pyLen
    | some x => pyLen x
    | none   => PastaLean.pyPanic "TypeError: object of type 'NoneType' has no len()"

end PastaLean
