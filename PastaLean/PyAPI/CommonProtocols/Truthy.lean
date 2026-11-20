import PastaLean.Imports

namespace PastaLean

/--
Python truthiness, `bool(x)` — the implicit conversion used by `if x:`, `while x:`, `not x`,
and boolean operators. Numbers are truthy when non-zero; strings/lists/dicts/sets when
non-empty; `None`/`Option.none` is falsy; an actual `Bool` is itself.

Codegen wraps condition expressions in `pyTruthy` so a non-`Bool` value (the common
`if cnt:` / `while stack:` idiom) is accepted where Lean wants a `Bool`. `PyTruthy Bool` is
the identity, so wrapping an already-boolean test (e.g. a comparison) is a no-op.
-/
class PyTruthy (α : Type) where
  truthy : α → Bool

/-- Dispatch Python truthiness through the `PyTruthy` typeclass. -/
@[simp, grind]
def pyTruthy {α : Type} [PyTruthy α] (x : α) : Bool := PyTruthy.truthy x

instance : PyTruthy Bool where truthy b := b
instance : PyTruthy Int where truthy n := n != 0
instance : PyTruthy Nat where truthy n := n != 0
instance : PyTruthy Rat where truthy q := q != 0
instance : PyTruthy Float where truthy x := x != 0.0
instance : PyTruthy Char where truthy _ := true
instance : PyTruthy String where truthy s := !s.isEmpty
instance {α : Type} : PyTruthy (List α) where truthy xs := !xs.isEmpty
-- `bool(x)` on a nullable recurses into the payload: `None` is falsy, `some v` is `bool(v)` (so
-- `some 0`, `some ""`, `some []` are falsy, matching Python — `if x:` where `x` may be `None` or `0`).
-- Falls back to `isSome` only when the payload has no `PyTruthy` (nothing to recurse into).
instance {α : Type} [PyTruthy α] : PyTruthy (Option α) where
  truthy | none => false | some v => PyTruthy.truthy v
instance (priority := 50) {α : Type} : PyTruthy (Option α) where truthy o := o.isSome
instance {κ ν : Type} [BEq κ] [Hashable κ] : PyTruthy (Std.HashMap κ ν) where
  truthy m := !m.isEmpty

/-- Python's `a or b` for a nullable `a` and a plain `b` (`items or []`): the payload when truthy,
else `b` (`None` is falsy, so it is never the result). -/
def pyOrElse {α : Type} [PyTruthy α] (a : Option α) (b : α) : α :=
  match a with
  | some v => if PyTruthy.truthy v then v else b
  | none => b

end PastaLean
