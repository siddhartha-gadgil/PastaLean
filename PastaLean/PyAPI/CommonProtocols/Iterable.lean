import PastaLean.PyAPI.PyPanic
import PastaLean.Imports

namespace PastaLean

/--
Typeclass for Python-style iteration.

Use this when codegen should normalize different iterable runtime values into one
public Lean operation, `pyIter`, without caring which concrete type supplied the
elements.
-/
class PyIterable (α : Type) (β : outParam Type) where
  toPyList : α → List β

/-- Dispatch Python-style iteration through the `PyIterable` protocol. -/
def pyIter {α β : Type} [inst : PyIterable α β] (value : α) : List β :=
  inst.toPyList value

/--
Unpack exactly two elements from a Python-style iterable.

This matches the common tuple-assignment shape `a, b = value` and raises a runtime-style
error when the iterable length is not exactly two.
-/
def pyUnpack2 {α β : Type} [inst : PyIterable α β] [Inhabited β] (value : α) : β × β :=
  match pyIter value with
  | [first, second] => (first, second)
  | [] => PastaLean.pyPanic "ValueError: not enough values to unpack (expected 2, got 0)"
  | [_] => PastaLean.pyPanic "ValueError: not enough values to unpack (expected 2, got 1)"
  | _ => PastaLean.pyPanic "ValueError: too many values to unpack (expected 2)"


/-- Lists are already Python-style iterables. -/
instance : PyIterable (List α) α where
  toPyList := id

/-- Arrays iterate by converting to lists. -/
instance : PyIterable (Array α) α where
  toPyList := Array.toList

/-- Strings iterate over their characters as one-character strings, since Python has no separate
character type — iterating a `str` yields length-1 `str`s. This keeps loop variables, `pyList`
casts, and comprehensions over strings interoperable with string literals and methods. -/
instance : PyIterable String String where
  toPyList s := s.toList.map (·.toString)

/-- Dictionaries iterate over keys, matching Python's default dictionary iteration. -/
instance [BEq α] [Hashable α] : PyIterable (Std.HashMap α β) α where
  toPyList m := m.toList.map Prod.fst

/--
Homogeneous 2-tuples can participate in Python-style iterable builtins by exposing
their elements as a two-element list.
-/
instance : PyIterable (α × α) α where
  toPyList p := [p.1, p.2]

/-- A homogeneous n-tuple `(a, b, c, …)` is the nested product `α × (α × …)`; iterate it by prepending
the head to the iterated tail. With the 2-tuple base above this flattens any all-`α` tuple to a
`List α`, so `for x in (1, 2, 3)`, `pairwise((-1, 0, 1, 0, -1))`, etc. work without turning the tuple
into a list. A heterogeneous tuple (`(int, str)`) has no `PyIterable` for its tail, so it is left
un-iterable — matching that Python only iterates a tuple element-by-element when the caller expects
one type. -/
instance [inst : PyIterable β α] : PyIterable (α × β) α where
  toPyList p := p.1 :: inst.toPyList p.2

end PastaLean
