import Mathlib
import PastaLean.PyAPI.Core

namespace PastaLean

/-!
`isinstance(x, T)`. A Lean value's type is static, so the test reduces to comparing the Python type
name of `x`'s Lean type with `T` — decided at elaboration time, not by inspecting the value.
-/

/-- The Python type name a Lean type stands for (`Int` → `"int"`, `List α` → `"list"`, …). -/
class PyTypeName (α : Type) where
  pyTypeName : String

instance : PyTypeName Int := ⟨"int"⟩
instance : PyTypeName Nat := ⟨"int"⟩
instance : PyTypeName Bool := ⟨"bool"⟩
instance : PyTypeName String := ⟨"str"⟩
instance : PyTypeName Char := ⟨"str"⟩
instance : PyTypeName Float := ⟨"float"⟩
instance : PyTypeName Rat := ⟨"float"⟩
instance : PyTypeName Real := ⟨"float"⟩
instance {α : Type} : PyTypeName (List α) := ⟨"list"⟩
instance {α : Type} : PyTypeName (Array α) := ⟨"list"⟩
instance {α β : Type} : PyTypeName (α × β) := ⟨"tuple"⟩
instance {α β : Type} [BEq α] [Hashable α] : PyTypeName (Std.HashMap α β) := ⟨"dict"⟩
instance {α : Type} : PyTypeName (Option α) := ⟨"NoneType"⟩

/-- Python's builtin subclass edges that `isinstance` honours. `bool` is a subclass of `int`, so
`isinstance(True, int)` is `True`; `int` is *not* a subclass of `float`. -/
def pyTypeIsSubclass (sub super : String) : Bool :=
  sub == super || (sub == "bool" && super == "int")

def pyIsInstance {α : Type} [PyTypeName α] (_x : α) (ty : String) : Bool :=
  pyTypeIsSubclass (PyTypeName.pyTypeName α) ty

/-- `isinstance(x, (T₁, …, Tₙ))`: true when any of the alternatives matches. -/
def pyIsInstanceAny {α : Type} [PyTypeName α] (x : α) (tys : List String) : Bool :=
  tys.any (pyIsInstance x)

end PastaLean
