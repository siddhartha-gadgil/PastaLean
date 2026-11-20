import Lean

/-!
# `PyLit` — a value every world can read

A counterexample has to mean the same input in CPython, in the runnable twin (`Float`, `Array`) and in
the provable twin (`ℚ`, `List`). `PyLit` is that shared value: generators produce one, the Python side
decodes it to a Python object, and `litToExpr` places it at whatever Lean type a binder has.

Floats are `float k e = k / 2^e` — dyadic, so the value is exact as a CPython float, a Lean `Float`
(for `|k| < 2^53`) and a `ℚ`. `rat`, `double` and `exc` only ever appear as *results*.
-/

namespace PastaLean.Refute

open Lean

inductive PyLit where
  | int (n : Int)
  | bool (b : Bool)
  | str (s : String)
  | none
  | float (k : Int) (e : Nat)
  | rat (n : Int) (d : Nat)
  | double (bits : UInt64)
  | list (xs : List PyLit)
  | tuple (xs : List PyLit)
  | dict (kvs : List (PyLit × PyLit))
  | set (xs : List PyLit)
  | obj (cls : String) (fields : List (String × PyLit))
  | exc (kind : String)
  /-- A callable: a finite table and a default (`lambda x: {0: 42}.get(x, 0)`). -/
  | fn (table : List (PyLit × PyLit)) (dflt : PyLit)
  deriving Repr, BEq, Inhabited

/-- A size every shrink step must strictly decrease, so shrinking terminates (Plausible's `minimize`
recurses for as long as candidates keep failing). -/
partial def PyLit.measure : PyLit → Nat
  | .int n | .rat n _ => n.natAbs
  | .float k e => k.natAbs + e
  | .str s | .exc s => s.length
  | .bool b => if b then 1 else 0
  | .none => 0
  | .double b => b.toNat
  | .list xs | .tuple xs | .set xs => xs.foldl (· + ·.measure + 1) 0
  | .dict kvs => kvs.foldl (fun a (k, v) => a + k.measure + v.measure + 1) 0
  | .obj _ fs => fs.foldl (· + ·.2.measure) 0
  | .fn t d => t.foldl (fun a (k, v) => a + k.measure + v.measure + 1) d.measure

/-- The `k / 2^e` of a dyadic float in lowest terms. -/
def normDyadic (k : Int) (e : Nat) : Int × Nat := Id.run do
  let mut k := k
  let mut e := e
  while e > 0 && k % 2 == 0 do
    k := k / 2
    e := e - 1
  return (k, e)

/-- An exact decimal for `k / 2^e` (every dyadic has one), always with a `.` so Python reads a float. -/
def dyadicDecimal (k : Int) (e : Nat) : String :=
  let (k, e) := normDyadic k e
  let sign := if k < 0 then "-" else ""
  let m := k.natAbs * 5 ^ e
  let digits := toString m
  if e == 0 then s!"{sign}{digits}.0" else
  let digits := String.ofList (List.replicate (e + 1 - min digits.length (e + 1)) '0') ++ digits
  let cut := digits.length - e
  s!"{sign}{digits.take cut}.{digits.drop cut}"

/-- A Python string literal (double-quoted, escapes for `\`, `"` and non-printables). -/
def pyStrLit (s : String) : String :=
  let body := s.foldl (fun acc c =>
    acc ++ match c with
      | '\\' => "\\\\" | '"' => "\\\"" | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
      | c => if c.toNat < 32 || c.toNat == 127 then s!"\\x{String.ofList (Nat.toDigits 16 c.toNat)}" else c.toString) ""
  "\"" ++ body ++ "\""

partial def PyLit.toPyString : PyLit → String
  | .int n => toString n
  | .bool b => if b then "True" else "False"
  | .str s => pyStrLit s
  | .none => "None"
  | .float k e => dyadicDecimal k e
  | .rat n d => s!"Fraction({n}, {d})"
  | .double bits => s!"struct.unpack('<d', ({bits}).to_bytes(8, 'little'))[0]"
  | .list xs => "[" ++ ", ".intercalate (xs.map toPyString) ++ "]"
  | .tuple [x] => "(" ++ toPyString x ++ ",)"
  | .tuple xs => "(" ++ ", ".intercalate (xs.map toPyString) ++ ")"
  | .dict kvs => "{" ++ ", ".intercalate (kvs.map fun (k, v) => toPyString k ++ ": " ++ toPyString v) ++ "}"
  | .set [] => "set()"
  | .set xs => "{" ++ ", ".intercalate (xs.map toPyString) ++ "}"
  | .obj cls fs => cls ++ "(" ++ ", ".intercalate (fs.map fun (n, v) => n ++ "=" ++ toPyString v) ++ ")"
  | .exc kind => s!"<raises {kind}>"
  | .fn t d => "(lambda x: {" ++ ", ".intercalate (t.map fun (k, v) => toPyString k ++ ": " ++ toPyString v)
      ++ "}.get(x, " ++ toPyString d ++ "))"

partial def PyLit.toJson : PyLit → Json
  | .int n => Json.mkObj [("int", Lean.toJson n)]
  | .bool b => Json.mkObj [("bool", Lean.toJson b)]
  | .str s => Json.mkObj [("str", Lean.toJson s)]
  | .none => Json.mkObj [("none", Json.null)]
  | .float k e => Json.mkObj [("float", Json.arr #[Lean.toJson k, Lean.toJson e])]
  | .rat n d => Json.mkObj [("rat", Json.arr #[Lean.toJson n, Lean.toJson d])]
  | .double bits => Json.mkObj [("double", Lean.toJson bits.toNat)]
  | .list xs => Json.mkObj [("list", Json.arr (xs.map PyLit.toJson).toArray)]
  | .tuple xs => Json.mkObj [("tuple", Json.arr (xs.map PyLit.toJson).toArray)]
  | .dict kvs => Json.mkObj [("dict", Json.arr (kvs.map fun (k, v) => Json.arr #[PyLit.toJson k, PyLit.toJson v]).toArray)]
  | .set xs => Json.mkObj [("set", Json.arr (xs.map PyLit.toJson).toArray)]
  | .obj cls fs => Json.mkObj [("obj", Json.mkObj [("cls", Lean.toJson cls),
      ("fields", Json.mkObj (fs.map fun (n, v) => (n, PyLit.toJson v)))])]
  | .exc kind => Json.mkObj [("exc", Lean.toJson kind)]
  | .fn t d => Json.mkObj [("fn", Json.mkObj [
      ("table", Json.arr (t.map fun (k, v) => Json.arr #[PyLit.toJson k, PyLit.toJson v]).toArray),
      ("default", PyLit.toJson d)])]

partial def PyLit.fromJson? (j : Json) : Except String PyLit := do
  let some (tag, v) := (match j with | .obj kvs => kvs.toList.head? | _ => Option.none)
    | throw s!"PyLit: expected a one-key object, got {j.compress}"
  let arr : Except String (Array Json) := v.getArr?
  match tag with
  | "int" => return .int (← v.getInt?)
  | "bool" => return .bool (← v.getBool?)
  | "str" => return .str (← v.getStr?)
  | "none" => return .none
  | "float" => let a ← arr; return .float (← a[0]!.getInt?) (← a[1]!.getNat?)
  | "rat" => let a ← arr; return .rat (← a[0]!.getInt?) (← a[1]!.getNat?)
  | "double" => return .double (← v.getNat?).toUInt64
  | "list" => return .list (← (← arr).toList.mapM fromJson?)
  | "tuple" => return .tuple (← (← arr).toList.mapM fromJson?)
  | "set" => return .set (← (← arr).toList.mapM fromJson?)
  | "dict" => return .dict (← (← arr).toList.mapM fun kv => do
      let p ← kv.getArr?
      return ((← fromJson? p[0]!), (← fromJson? p[1]!)))
  | "obj" => do
      let cls ← (v.getObjValAs? String "cls")
      let fs ← v.getObjVal? "fields"
      let fields ← match fs with
        | .obj kvs => kvs.toList.mapM fun (n, x) => do return (n, ← fromJson? x)
        | _ => throw "PyLit.obj: fields must be an object"
      return .obj cls fields
  | "exc" => return .exc (← v.getStr?)
  | "fn" => do
      let t ← (← v.getObjVal? "table").getArr?
      return .fn (← t.toList.mapM fun kv => do
          let p ← kv.getArr?
          return ((← fromJson? p[0]!), (← fromJson? p[1]!)))
        (← fromJson? (← v.getObjVal? "default"))
  | t => throw s!"PyLit: unknown tag {t}"

instance : ToJson PyLit := ⟨PyLit.toJson⟩
instance : FromJson PyLit := ⟨PyLit.fromJson?⟩

/-- How a Lean value of a Python-visible type reads back as a `PyLit`. -/
class ToPyLit (α : Type) where
  toLit : α → PyLit

end PastaLean.Refute
