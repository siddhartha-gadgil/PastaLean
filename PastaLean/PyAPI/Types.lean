import PastaLean.PyAPI.PyAny
import TypeInfer.PyType

/-!
# `type()` and `isinstance()` — runtime type introspection

Python's `type(x)` and `isinstance(x, T)` inspect a value's runtime type. We reuse `TypeInfer.PyType`
as the runtime type-object — it already enumerates every Python type INCLUDING user classes (`.cls
"Trie"`), so `type(trie) == Trie` works without a second enum. Containers are compared by their
*head* (Python's `list`/`dict`/`tuple`/`set` type objects carry no element type), so `pyType` returns
element-less containers (`.list .unknown`, …) and codegen emits the matching element-less tag.

`type(x) == int` lowers to `pyType x == PyType.int`; `isinstance(x, int)` to `pyIsInstance x
PyType.int` — with Python's `bool ⊂ int` subclassing respected.
-/

namespace PastaLean

open TypeInfer (PyType)

/-- Maps a Lean value to the `PyType` its runtime type represents. One instance per modelled type;
`PyAny` dispatches on its runtime tag. Containers report element-less (Python's `type()` does). A user
class gets a generated `instance : PyTyped C := ⟨fun _ => .cls "C"⟩` alongside its structure. -/
class PyTyped (α : Type) where
  pyTypeOf : α → PyType

/-- `type(x)` — the Python runtime type of `x`. -/
def pyType {α : Type} [PyTyped α] (x : α) : PyType := PyTyped.pyTypeOf x

instance : PyTyped PyAny where
  pyTypeOf x := match x with
    | .int _ => .int
    | .bool _ => .bool
    | .str _ => .str
    | .float _ => .float
    | .list _ => .list .unknown
    | .dict _ => .dict .unknown .unknown
    | .none => .none

instance : PyTyped Int    where pyTypeOf _ := .int
instance : PyTyped Nat    where pyTypeOf _ := .int
instance : PyTyped Bool   where pyTypeOf _ := .bool
instance : PyTyped String where pyTypeOf _ := .str
instance : PyTyped Float  where pyTypeOf _ := .float
instance : PyTyped Rat    where pyTypeOf _ := .float
instance {α : Type} : PyTyped (List α)  where pyTypeOf _ := .list .unknown
instance {α : Type} : PyTyped (Array α) where pyTypeOf _ := .list .unknown
instance {α β : Type} : PyTyped (α × β) where pyTypeOf _ := .tuple []
instance {α β : Type} [BEq α] [Hashable α] : PyTyped (Std.HashMap α β) where
  pyTypeOf _ := .dict .unknown .unknown

/-- `isinstance(x, t)` — is `x`'s runtime type `t` (or a subclass)? Python's numeric tower has
`bool ⊂ int`, so `isinstance(True, int)` is `True`; every other type is checked by equality. -/
def pyIsInstance {α : Type} [PyTyped α] (x : α) (t : PyType) : Bool :=
  let actual := pyType x
  actual == t || (t == .int && actual == .bool)

/-- `isinstance(x, (t₁, …, tₙ))` — a tuple of types means "any of". Codegen folds this over the tags. -/
def pyIsInstanceAny {α : Type} [PyTyped α] (x : α) (ts : List PyType) : Bool :=
  ts.any (pyIsInstance x)

end PastaLean

/-- `type(x).__name__`: the Python name of a runtime type. -/
def TypeInfer.PyType.__name__ : TypeInfer.PyType → String
  | .int => "int" | .bool => "bool" | .str => "str" | .float => "float" | .none => "NoneType"
  | .list _ => "list" | .set _ => "set" | .tuple _ => "tuple" | .dict _ _ => "dict"
  | .opt t => TypeInfer.PyType.__name__ t | .cls c => c | .fn _ _ => "function"
  | .any | .unknown => "object"
