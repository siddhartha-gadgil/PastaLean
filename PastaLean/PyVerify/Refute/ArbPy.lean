import PastaLean.PyVerify.Refute.Arb
import PastaLean.PyAPI.PyAny
import PastaLean.PyAPI.Sets
import PastaLean.PyAPI.Dicts

/-!
# Generators for PastaLean's own runtime types

Dicts (`Std.HashMap`), sets (`PySet`, insertion-ordered) and untyped values (`PyAny`). A dict reads back
in its Lean iteration order; CPython rebuilds it in that order, so any difference in how the two
iterate shows up as a fidelity finding rather than being hidden.
-/

namespace PastaLean.Refute

open Plausible

partial def PyAny.toLitImpl : PyAny → PyLit
  | .int n => .int n
  | .bool b => .bool b
  | .str s => .str s
  | .float q => ToPyLit.toLit q
  | .list xs => .list (xs.map PyAny.toLitImpl)
  | .none => .none

instance : ToPyLit PyAny := ⟨PyAny.toLitImpl⟩

/-- A boxed value from a small universe; lists nest at most `depth` deep. -/
partial def genPyAny (depth : Nat) : Gen PyAny := do
  let k ← Gen.choose Nat 0 (if depth == 0 then 4 else 5) (by omega)
  match k.val with
  | 0 => return .int (← genInt)
  | 1 => return .bool (← Gen.chooseAny Bool)
  | 2 => return .str (← (PyArb.arb : Gen String))
  | 3 => return .float (ratOfDyadic (← genDyadic))
  | 4 => return .none
  | _ => do
      let n ← Gen.choose Nat 0 3 (by omega)
      return .list (← (List.range n.val).mapM fun _ => genPyAny (depth - 1))

instance : PyArb PyAny where
  arb := genPyAny 2
  shrink
    | .int n => .none :: (shrinkInt n).map .int
    | .str s => .none :: (PyArb.shrink s).map .str
    | .list xs => .none :: xs ++ (List.range xs.length).map fun i => PyAny.list (xs.eraseIdx i)
    | .none => []
    | _ => [.none]
  enum d lim :=
    ((PyArb.enum d lim : List Int).map PyAny.int ++ [PyAny.none, PyAny.bool false, PyAny.bool true] ++
      (PyArb.enum d lim : List String).map PyAny.str).take lim

instance [ToPyLit α] [BEq α] [Hashable α] : ToPyLit (PySet α) where
  toLit s := .set (s.toList.map ToPyLit.toLit)
instance [PyArb α] [BEq α] [Hashable α] : PyArb (PySet α) where
  arb := do return pySetFromList (← (PyArb.arb : Gen (List α)))
  shrink s := (PyArb.shrink s.toList).map pySetFromList
  enum d lim := ((PyArb.enum d lim : List (List α)).map pySetFromList).take lim

instance [ToPyLit κ] [ToPyLit ν] [BEq κ] [Hashable κ] : ToPyLit (Std.HashMap κ ν) where
  toLit m := .dict (m.toList.map fun (k, v) => (ToPyLit.toLit k, ToPyLit.toLit v))
instance [PyArb κ] [PyArb ν] [BEq κ] [Hashable κ] : PyArb (Std.HashMap κ ν) where
  arb := do return Std.HashMap.ofList (← (PyArb.arb : Gen (List (κ × ν))))
  shrink m := (PyArb.shrink m.toList).map Std.HashMap.ofList
  enum d lim := ((PyArb.enum d lim : List (List (κ × ν))).map Std.HashMap.ofList).take lim

end PastaLean.Refute
