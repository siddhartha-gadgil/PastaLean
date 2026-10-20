import TypeInfer.PyType

/-!
# Python annotations ↔ `PyType`

`ofAnnotation` reads a type annotation out of the JSON IR, `toAnnotation?` writes one back.
The pre-pass in `annotate_python.py` has already normalised `typing.List[int]` to `list[int]` and
`Optional[X]` to `X | None`, so only the builtin generic spellings need handling here.
-/

namespace TypeInfer

open Lean

private def nodeType? (json : Json) : Option String :=
  (json.getObjValAs? String "node_type").toOption

/-- `typing`'s capitalised spellings, folded onto the builtin ones. -/
private def canonical (name : String) : String :=
  match name with
  | "Int" => "int" | "Bool" => "bool" | "String" | "Str" => "str" | "Float" => "float"
  | "List" => "list" | "Set" => "set" | "FrozenSet" => "frozenset"
  | "Dict" | "Mapping" => "dict" | "Tuple" => "tuple" | "Sequence" | "Iterable" => "list"
  | n => n

/-- Builtin annotation names. Anything else is a user class. `Any`/`object` are the *gradual*
dynamic type — "no static information" — so they read as `.unknown` (⊥), NOT `.any` (⊤, which means
concrete types that genuinely conflict, e.g. an `int | str` union that must be boxed). -/
private def baseTypes : List (String × PyType) :=
  -- A BARE, unparameterised `list`/`set` annotation (`def f(xs: list)`) means `list[Any]` in Python;
  -- the element is the dynamic top (`.any`→`PyAny`), NOT `.unknown` (⊥) — ⊥ is right for an inferable
  -- *value* (an RHS literal can fill it) but a *parameter* has no RHS, so ⊥ leaves `List ?m` stuck.
  -- A boxed list is indexed/iterated by a concrete `Int`, which the `List PyAny` instances handle.
  -- NOTE `dict`/`tuple` stay `.unknown`: a boxed `Std.HashMap PyAny PyAny` cannot be keyed by a
  -- concrete `Int` (`PyDictKeyPop`'s `outParam` key resolves to `PyAny`, and an `Int` key pins it to
  -- `ℤ` with no coercion) — a bare `dict` param needs key/value back-inference from usage instead.
  [ ("int", .int), ("bool", .bool), ("str", .str), ("float", .float),
    ("None", .none), ("Any", .unknown), ("object", .unknown),
    ("list", .list .any), ("set", .set .any), ("frozenset", .set .any),
    ("dict", .dict .unknown .unknown), ("tuple", .tuple []) ]

/-- Generic containers written `c[...]`, keyed by the name before the bracket. -/
private def containerOf (name : String) (args : List PyType) : Option PyType :=
  -- An explicit `List[Any]` element (⊥) has no inference source, exactly like a bare `list` param, so
  -- it must be the dynamic top `.any`→`PyAny` (a boxed `List PyAny` indexes by a concrete `Int`), not
  -- the stuck `⊥` that leaves `List ?m`. Same reasoning as the bare-`list` base type above.
  let unkToAny (e : PyType) : PyType := if e == .unknown then .any else e
  match name, args with
  | "list", [e] => some (.list (unkToAny e))
  | "set", [e] | "frozenset", [e] => some (.set (unkToAny e))
  | "dict", [k, v] => some (.dict k v)
  -- A `defaultdict`/`Counter` behaves as a dict for inference; only its EMITTED Lean type
  -- differs (`PyDefaultDict`, not `Std.HashMap`), which the codegen annotation reader handles.
  | "defaultdict", [k, v] => some (.dict k v)
  | "tuple", es => some (.tuple es)
  | "Optional", [e] => some (.opt e)
  | "Union", es => some (PyType.joinAll es)
  | _, _ => none

/-- Read a Python type annotation. Unrecognised shapes are `unknown`, never an error. -/
partial def ofAnnotation (json : Json) : PyType :=
  match nodeType? json with
  | some "Name" =>
      match (json.getObjValAs? String "id").toOption with
      | some id => match baseTypes.lookup (canonical id) with
          | some t => t
          | none => .cls id
      | none => .unknown
  -- A string forward reference: `def f(root: "TreeNode")`.
  | some "Constant" =>
      match json.getObjVal? "value" with
      | .ok (.str s) => ofAnnotation (Json.mkObj [("node_type", .str "Name"), ("id", .str s)])
      -- `...` is a null with its kind named; it claims no type, unlike a literal `None`.
      | .ok .null =>
          if (json.getObjValAs? String "python_literal_kind").toOption == some "ellipsis" then
            .unknown
          else .none
      | _ => .unknown
  -- `typing.List[int]` if the pre-pass left it alone.
  | some "Attribute" =>
      match (json.getObjValAs? String "attr").toOption with
      | some attr => ofAnnotation (Json.mkObj [("node_type", .str "Name"), ("id", .str attr)])
      | none => .unknown
  -- `X | None`, which is how `Optional[X]` reaches us.
  | some "BinOp" =>
      if (json.getObjValAs? String "op").toOption == some "bitor" then
        match json.getObjVal? "left", json.getObjVal? "right" with
        | .ok l, .ok r => PyType.join (ofAnnotation l) (ofAnnotation r)
        | _, _ => .unknown
      else .unknown
  | some "Subscript" =>
      let name := match json.getObjVal? "value" with
        | .ok v => match nodeType? v with
            | some "Name" => (v.getObjValAs? String "id").toOption
            | some "Attribute" => (v.getObjValAs? String "attr").toOption
            | _ => none
        | _ => none
      -- `Callable[[A, B], R]`: slice is a `Tuple` whose first element is the `List` of argument
      -- annotations and whose second is the return annotation.
      if name == some "Callable" then
        match json.getObjVal? "slice" with
        | .ok slice =>
            if nodeType? slice == some "Tuple" then
              let elts := (slice.getObjValAs? (Array Json) "elts").toOption.getD #[]
              match elts[0]?, elts[1]? with
              | some argsJson, some retJson =>
                  let argAnns := (argsJson.getObjValAs? (Array Json) "elts").toOption.getD #[]
                  .fn (argAnns.toList.map ofAnnotation) (ofAnnotation retJson)
              | _, _ => .unknown
            else .unknown
        | _ => .unknown
      else
        let args := match json.getObjVal? "slice" with
          | .ok slice =>
              if nodeType? slice == some "Tuple" then
                ((slice.getObjValAs? (Array Json) "elts").toOption.getD #[]).toList.map ofAnnotation
              else [ofAnnotation slice]
          | _ => []
        match name with
        | some n => (containerOf (canonical n) args).getD .unknown
        | none => .unknown
  | _ => .unknown

private def nameAnn (id : String) : Json :=
  Json.mkObj [("node_type", .str "Name"), ("id", .str id)]

private def subscriptAnn (container : String) (args : List Json) : Json :=
  let slice := match args with
    | [a] => a
    | _ => Json.mkObj [("node_type", .str "Tuple"), ("elts", Json.arr args.toArray)]
  Json.mkObj [("node_type", .str "Subscript"), ("value", nameAnn container), ("slice", slice)]

/-- Write a `PyType` back as an annotation node. `none` when the type is not fully known, since
an unknown annotation is worse than no annotation — it would name a type that does not exist. -/
def toAnnotation? (t : PyType) : Option Json := do
  match t with
  -- `.unknown` is "no information" → no annotation (let Lean infer). `.any` is the *known*-dynamic
  -- top type — a genuine union like `[1, "hi", [2]]` should be inferred to `List PyAny`
  | .unknown => none
  | .any => nameAnn "PyAny"
  | .int => nameAnn "int"
  | .bool => nameAnn "bool"
  | .str => nameAnn "str"
  | .float => nameAnn "float"
  | .none => nameAnn "None"
  | .cls n => nameAnn n
  | .list e => subscriptAnn "list" [← toAnnotation? e]
  | .set e => subscriptAnn "set" [← toAnnotation? e]
  | .opt e => subscriptAnn "Optional" [← toAnnotation? e]
  | .dict k v => subscriptAnn "dict" [← toAnnotation? k, ← toAnnotation? v]
  | .tuple es => subscriptAnn "tuple" (← es.mapM toAnnotation?)
  | .fn as r =>
      let argList := Json.mkObj [("node_type", .str "List"),
        ("elts", Json.arr (← as.mapM toAnnotation?).toArray)]
      subscriptAnn "Callable" [argList, ← toAnnotation? r]

end TypeInfer
