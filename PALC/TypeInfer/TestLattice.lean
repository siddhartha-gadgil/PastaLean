import TypeInfer
-- The lattice-law verification (`TypeInfer.Theorem`: join is a bounded semilattice, `consistent` is a
-- gradual-typing relation, `reconcile` is total — all proved on the real `PyType`) is kept off the
-- `lake build`/py2lean path (see `TypeInfer.lean`); import it here so `lake test` still checks it.
import TypeInfer.Theorem

/-! Unit checks for the type lattice. Each `#guard` fails the build if it is false. -/

open Lean TypeInfer
open TypeInfer.PyType (join joinAll consistent elemType isKnown)

/-! ### `join` — the least upper bound -/

-- `unknown` carries no information, so it yields to anything.
#guard join .unknown .int == .int
#guard join .int .unknown == .int
#guard join .unknown .unknown == PyType.unknown

-- Incompatible types go to `any`, the signal to box.
#guard join .int .str == .any
#guard join .any .int == .any
#guard join (.list .int) (.list .str) == .list .any

-- Python's `bool` is a subclass of `int`: `True + 1 = 2`.
#guard join .int .bool == .int
#guard join .bool .int == .int
#guard join .bool .bool == PyType.bool

-- `None` on one path makes the type optional.
#guard join (.cls "TreeNode") .none == .opt (.cls "TreeNode")
#guard join .none (.opt .int) == .opt .int
#guard join .none .none == PyType.none

-- Containers join elementwise.
#guard join (.list .unknown) (.list .int) == .list .int
#guard join (.dict .str .int) (.dict .str .bool) == .dict .str .int
#guard join (.tuple [.int, .str]) (.tuple [.bool, .str]) == .tuple [.int, .str]
-- Tuples of different lengths have no common Lean type.
#guard join (.tuple [.int]) (.tuple [.int, .int]) == .any

#guard joinAll [.int, .bool, .int] == .int
#guard joinAll [] == PyType.unknown

/-! ### `join` is a lub: commutative, idempotent, absorbing -/

private def sample : List PyType :=
  [.unknown, .any, .int, .bool, .str, .float, .none, .list .int, .set .str,
   .tuple [.int, .str], .dict .str .int, .opt .int, .cls "TreeNode"]

#guard sample.all fun a => join a a == a
#guard sample.all fun a => sample.all fun b => join a b == join b a
#guard sample.all fun a => join a .unknown == a
#guard sample.all fun a => join a .any == .any
-- The result is always at least as high as each input, so the fixpoint climbs and terminates.
#guard sample.all fun a => sample.all fun b => consistent a (join a b)

/-! ### `consistent` — reflexive and symmetric, but *not* transitive (Siek & Taha) -/

#guard sample.all fun a => consistent a a
#guard sample.all fun a => sample.all fun b => consistent a b == consistent b a

-- `any` is consistent with everything; that is what lets a boxed value flow anywhere.
#guard sample.all fun a => consistent .any a
-- …and this is exactly why it is not transitive: `int ~ any` and `any ~ str`, but `int ≁ str`.
#guard consistent .int .any && consistent .any .str && !consistent .int .str

#guard consistent (.opt .int) .none
#guard consistent (.opt .int) .int
#guard !consistent (.list .int) (.list .str)

-- The gradual guarantee: `unknown` (no info yet) is consistent with every concrete type.
#guard [PyType.int, .str, .float, .list .int, .dict .str .int, .none].all fun t => consistent .unknown t

/-! ### `reconcile` — the coercion a value needs to fit an expected slot

Checks on the real `PyType.reconcile` (were `native_decide` theorems in `Lattice.lean`'s `Production`
block; `#guard` evaluates them directly, no `native_decide` needed). -/

open TypeInfer.PyType (reconcile) in
section
#guard reconcile .int .bool == .boolToInt
#guard reconcile (.cls "TreeNode") (.opt (.cls "TreeNode")) == .unwrapOpt
#guard reconcile .int .str == .box
#guard reconcile (.list .int) (.list .int) == .exact
end

/-! ### `elemType` — what an iterable yields -/

#guard elemType (.list .str) == PyType.str
#guard elemType (.dict .str .int) == PyType.str
#guard elemType .str == PyType.str
#guard elemType .int == PyType.unknown

/-! ### `ofAnnotation` — reading Python annotations

The IR shapes below are exactly what `node_visitor.py` emits. -/

private def name (id : String) : Json :=
  Json.mkObj [("node_type", .str "Name"), ("id", .str id)]

private def subscript (v s : Json) : Json :=
  Json.mkObj [("node_type", .str "Subscript"), ("value", v), ("slice", s)]

private def tuple (elts : List Json) : Json :=
  Json.mkObj [("node_type", .str "Tuple"), ("elts", Json.arr elts.toArray)]

#guard ofAnnotation (name "int") == PyType.int
#guard ofAnnotation (name "TreeNode") == .cls "TreeNode"
-- `Any` is the gradual dynamic type ("no info"), not a conflict — so it reads as `unknown`.
#guard ofAnnotation (name "Any") == PyType.unknown
-- …but a concrete union `int | str` genuinely conflicts, so it reads as `any` (→ boxed).
#guard ofAnnotation (Json.mkObj
    [("node_type", .str "BinOp"), ("op", .str "bitor"), ("left", name "int"), ("right", name "str")])
  == PyType.any
#guard ofAnnotation (subscript (name "list") (name "str")) == .list .str
-- `List[List[int]]` — the pre-pass lowercases `List`, but accept both spellings.
#guard ofAnnotation (subscript (name "List") (subscript (name "list") (name "int")))
     == .list (.list .int)
#guard ofAnnotation (subscript (name "dict") (tuple [name "str", name "int"])) == .dict .str .int
#guard ofAnnotation (subscript (name "tuple") (tuple [name "int", name "int"]))
     == .tuple [.int, .int]

-- `Optional[TreeNode]` reaches us as `TreeNode | None`.
#guard ofAnnotation (Json.mkObj
    [("node_type", .str "BinOp"), ("op", .str "bitor"), ("left", name "TreeNode"),
     ("right", Json.mkObj [("node_type", .str "Constant"), ("value", Json.null)])])
  == .opt (.cls "TreeNode")

-- A string forward reference.
#guard ofAnnotation (Json.mkObj [("node_type", .str "Constant"), ("value", .str "ListNode")])
  == .cls "ListNode"

-- Unrecognised shapes are `unknown`, never an error.
#guard ofAnnotation (Json.mkObj [("node_type", .str "Call")]) == PyType.unknown

/-! ### `ofValue` — reading a literal's shape -/

private def const (v : Json) (kind : String := "") : Json :=
  let base := [("node_type", Json.str "Constant"), ("value", v)]
  Json.mkObj (if kind.isEmpty then base else base ++ [("python_literal_kind", .str kind)])

private def listOf (elts : List Json) : Json :=
  Json.mkObj [("node_type", .str "List"), ("elts", Json.arr elts.toArray)]

#guard ofValue (const (.num 0)) == PyType.int
#guard ofValue (const (.num 0) "float") == PyType.float
#guard ofValue (const (.bool true)) == PyType.bool
#guard ofValue (const (.str "hi")) == PyType.str
#guard ofValue (const Json.null) == PyType.none
#guard ofValue (listOf [const (.num 0), const (.num 1)]) == .list .int

-- `[0] * n` and `n * [0]` both build a list of ints.
private def mulBy (left right : Json) : Json :=
  Json.mkObj [("node_type", .str "BinOp"), ("op", .str "mul"), ("left", left), ("right", right)]

#guard ofValue (mulBy (listOf [const (.num 0)]) (name "n")) == .list .int
#guard ofValue (mulBy (name "n") (listOf [const (.num 0)])) == .list .int
-- Plain arithmetic is not a list.
#guard ofValue (mulBy (const (.num 2)) (name "n")) == PyType.unknown

-- A mixed list joins to `.list .any`: the elements genuinely conflict, so it materialises as
-- `List PyAny` (below) rather than being guessed at one element's type.
#guard ofValue (listOf [const (.num 0), const (.str "a")]) == .list .any
#guard ofValue (listOf []) == .list .unknown

#guard ofValue (Json.mkObj [("node_type", .str "Dict"), ("entries", Json.arr
  #[Json.mkObj [("key", const (.str "a")), ("value", const (.num 1))]])]) == .dict .str .int

/-! ### `toAnnotation?` — writing an annotation back

A round-trip on every fully-known type; `none` for `.unknown` (no information); and the concrete
`PyAny` fallback for `.any` (a genuine conflict), which reads back as the class `PyAny`. -/

#guard sample.all fun t =>
  if t.isKnown then (toAnnotation? t).map ofAnnotation == some t
  else if t == .any then (toAnnotation? t).map ofAnnotation == some (PyType.cls "PyAny")
  else toAnnotation? t == none

#guard toAnnotation? (.list .unknown) == none
-- `.any` and a container of it materialise as `PyAny` / `List PyAny`, so heterogeneous literals box.
#guard (toAnnotation? .any).map ofAnnotation == some (PyType.cls "PyAny")
#guard (toAnnotation? (.list .any)).map ofAnnotation == some (PyType.list (.cls "PyAny"))

/-! ### `toTypeSyntax?` — emitting the Lean type -/

/-- `Syntax.reprint` pads every atom, so collapse runs of spaces before comparing. -/
private def squash (s : String) : String :=
  String.intercalate " " ((s.splitOn " ").filter (!·.isEmpty))

private def emitted (t : PyType) : Option String :=
  Unhygienic.run do
    let floatTy : TSyntax `term := ⟨mkIdent `Rat⟩
    return (← toTypeSyntax? floatTy t).map fun s => squash (s.raw.reprint.getD "")

#guard emitted .int == some "Int"
#guard emitted (.list .int) == some "List Int"
#guard emitted (.opt (.cls "TreeNode")) == some "Option TreeNode"
#guard emitted (.dict .str .int) == some "Std.HashMap String Int"
#guard emitted (.tuple [.int, .str]) == some "Int × String"
#guard emitted .float == some "Rat"
-- Sets are an insertion-ordered array + hash index in the runtime (`PyAPI/Sets.lean`).
#guard emitted (.set .int) == some "PastaLean.PySet Int"
-- Nothing to emit for an unknown slot; the binder stays untyped (P3 will box it).
#guard emitted .unknown == none
-- `any` is the KNOWN-dynamic top type → the runtime `PyAny`, so a `list[any]` materialises as a total
-- running fallback rather than leaving instance search stuck.
#guard emitted (.list .any) == some "List PyAny"
