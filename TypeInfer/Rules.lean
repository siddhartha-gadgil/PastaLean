import TypeInfer.PyType
import TypeInfer.Annotation
import TypeInfer.Value
import Libraries.Registry

/-!
# Typing rules

Two functions drive the fixpoint in `Solve.lean`:

* `typeOfExpr env e` — the type of an expression, using what we already know about the variables
  in `env`. (`ofValue` in `Value.lean` only sees a literal's shape; this also follows names, calls,
  subscripts and operators.)
* `applyStmt env s` — how one statement updates what we know. An assignment *learns* a type; a
  mutation like `xs.append(3)` teaches us `xs` holds ints even though `xs` started as `[]`.

Both only ever `join` new facts in, so the env climbs the lattice and the fixpoint terminates.
-/

namespace TypeInfer

open Lean

/-- What we know about the variables in scope. -/
abbrev Env := Std.HashMap String PyType

/-- Return type of each user function, filled in by the interprocedural pass (`Solve.lean`). A
call to a function listed here resolves to its return type instead of `unknown`. -/
abbrev Sigs := Std.HashMap String PyType

private def nodeType? (j : Json) : Option String := (j.getObjValAs? String "node_type").toOption
private def field (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
private def eltsOf (j : Json) : List Json := ((j.getObjValAs? (Array Json) "elts").toOption.getD #[]).toList

/-- A subscript index that is a non-negative integer literal, for static tuple projection. -/
def literalIndex? (slice : Json) : Option Nat :=
  if nodeType? slice == some "Constant" then
    match slice.getObjVal? "value" with
    | .ok (.num ⟨m, 0⟩) => if m ≥ 0 then some m.toNat else none
    | _ => none
  else none

/-- The result type of arithmetic `a ⊕ b` (as opposed to `join`, which is "same slot, two types").
`+` concatenates strings and lists; on numbers it promotes toward `float`. -/
def arith : PyType → PyType → PyType
  | .str, .str => .str
  | .list a, .list b => .list (a.join b)
  -- Arithmetic on a boxed value stays boxed (`PyAny + int` dispatches on the tag → `PyAny`).
  | .any, _ | _, .any => .any
  | a, b =>
      if a.isNumeric && b.isNumeric then
        if a == .float || b == .float then .float else .int
      else .unknown

/-- Builtins whose result type is fixed regardless of the argument. -/
private def constReturnBuiltins : List (String × PyType) :=
  [ ("len", .int), ("ord", .int), ("int", .int), ("str", .str), ("input", .str),
    ("bool", .bool), ("float", .float), ("chr", .str), ("hash", .int),
    ("bin", .str), ("hex", .str), ("oct", .str) ]

/-- Methods whose result type is fixed regardless of the receiver. -/
private def constReturnMethods : List (String × PyType) :=
  [ ("split", .list .str), ("rsplit", .list .str), ("splitlines", .list .str),
    ("join", .str), ("strip", .str), ("lstrip", .str), ("rstrip", .str),
    ("lower", .str), ("upper", .str), ("replace", .str), ("format", .str),
    ("title", .str), ("swapcase", .str), ("casefold", .str), ("center", .str),
    ("removeprefix", .str), ("removesuffix", .str), ("rjust", .str), ("ljust", .str),
    ("count", .int), ("find", .int), ("rfind", .int), ("index", .int),
    ("lstrip", .str), ("rstrip", .str),
    ("startswith", .bool), ("endswith", .bool), ("isdigit", .bool), ("isalpha", .bool) ]

mutual

/-- The type of an expression under the current environment. `sigs` gives user functions' return
types. Total: `unknown` when unsure. -/
partial def typeOfExpr (sigs : Sigs) (env : Env) (e : Json) : PyType :=
  match nodeType? e with
  | some "Name" => ((e.getObjValAs? String "id").toOption.bind (env.get? ·)).getD .unknown
  | some "Constant" => ofValue e
  | some "List" => .list (PyType.joinAll ((eltsOf e).map (typeOfExpr sigs env)))
  | some "Set" => .set (PyType.joinAll ((eltsOf e).map (typeOfExpr sigs env)))
  | some "Tuple" => .tuple ((eltsOf e).map (typeOfExpr sigs env))
  | some "Dict" =>
      let entries := ((e.getObjValAs? (Array Json) "entries").toOption.getD #[]).toList
      let part (k : String) := entries.map fun en => (field en k).elim .unknown (typeOfExpr sigs env)
      .dict (PyType.joinAll (part "key")) (PyType.joinAll (part "value"))
  | some "Range" => .list .int
  | some "BinOp" =>
      match field e "left", field e "right" with
      | some l, some r =>
          let lt := typeOfExpr sigs env l
          let rt := typeOfExpr sigs env r
          match (e.getObjValAs? String "op").toOption with
          -- `[0] * n` / `n * [0]` repeats a list; every other `*` is arithmetic.
          | some "mul" =>
              match lt, rt with
              | .list _, _ => lt
              | _, .list _ => rt
              | _, _ => arith lt rt
          -- Python's `/` is always true division, so `int / int` is a `float`.
          | some "div" => .float
          | _ => arith lt rt
      | _, _ => .unknown
  | some "UnaryOp" =>
      if (e.getObjValAs? String "op").toOption == some "not" then .bool
      else (field e "operand").elim .unknown (typeOfExpr sigs env)
  | some "Compare" => .bool
  | some "BoolOp" =>
      -- `a and b` / `a or b` evaluate to one operand, so the type is their join.
      PyType.joinAll (((e.getObjValAs? (Array Json) "values").toOption.getD #[]).toList.map (typeOfExpr sigs env))
  | some "IfExp" =>
      match field e "body", field e "orelse" with
      | some b, some o => (typeOfExpr sigs env b).join (typeOfExpr sigs env o)
      | _, _ => .unknown
  | some "Subscript" =>
      match field e "value" with
      | some c =>
          let ct := typeOfExpr sigs env c
          -- A slice (`xs[a:b]`, `xs[::-1]`) returns the *same* container type; a plain index projects.
          if (field e "slice").any (fun s => nodeType? s == some "Slice") then ct
          else match ct with
          -- `t[k]` for a literal index projects the k-th element; otherwise the elements join.
          | .tuple es =>
              match (field e "slice").bind literalIndex? with
              | some i => es[i]?.getD (PyType.joinAll es)
              | none => PyType.joinAll es
          -- `d[k]` yields the value; `xs[i]` / `s[i]` yield the element.
          | .dict _ v => v
          | _ => ct.elemType
      | none => .unknown
  | some "Call" => typeOfCall sigs env e
  -- `x.attr`: the field's declared type, looked up as `"Class.field"` in `sigs` (populated from each
  -- `ClassDef`). Without this a chained access like `root.left.val` cannot see that `root.left` is
  -- itself `Option TreeNode`, so the unwrap would only fire on the outermost receiver.
  | some "Attribute" =>
      match field e "value", (e.getObjValAs? String "attr").toOption with
      | some recv, some attr =>
          match (typeOfExpr sigs env recv).classNameOf? with
          | some c => (sigs.get? s!"{c}.{attr}").getD .unknown
          | none => .unknown
      | _, _ => .unknown
  -- Comprehensions: bind each generator target from its iterable's element type, then type the
  -- element/key/value in that extended env (so `[[float('inf')]*k for _ in range(n)]` is
  -- `list[list[float]]`, not `list[Any]`).
  | some "ListComp" | some "SetComp" | some "GeneratorExp" | some "DictComp" =>
      let gens := (e.getObjValAs? (Array Json) "generators").toOption.getD #[]
      let env' := gens.foldl (fun env gen =>
        match (field gen "target").bind (fun t => (t.getObjValAs? String "id").toOption), field gen "iter" with
        | some name, some iter => env.insert name (typeOfExpr sigs env iter).elemType
        | _, _ => env) env
      match nodeType? e with
      | some "DictComp" =>
          .dict ((field e "key").elim .unknown (typeOfExpr sigs env'))
                ((field e "value").elim .unknown (typeOfExpr sigs env'))
      | some "SetComp" => .set ((field e "elt").elim .unknown (typeOfExpr sigs env'))
      | _ => .list ((field e "elt").elim .unknown (typeOfExpr sigs env'))
  -- A lambda is a function value. Its arity must match how `lambdaStx` lowers it: a lambda whose
  -- parameters are *all* defaulted (`lambda i=i: …`) — or has none — becomes a nullary `fun () ↦ …`
  -- thunk, so it types as `fn [] ret`; otherwise every parameter is an arrow binder. The body is
  -- typed in an env extended with the parameters (defaulted ones from their default's type), so a
  -- heap `list` of closures (`f.append(lambda: …)`) can learn a concrete element type.
  | some "Lambda" => Id.run do
      let argsNode := field e "args"
      let params := (argsNode.bind (·.getObjValAs? (Array Json) "args" |>.toOption)).getD #[]
      let defaults := (argsNode.bind (·.getObjValAs? (Array Json) "defaults" |>.toOption)).getD #[]
      let firstDefault := params.size - defaults.size
      let mut env' := env
      let mut argTys : Array PyType := #[]
      for i in [0:params.size] do
        let p := params[i]!
        let annTy? : Option PyType := (field p "annotation").bind fun a =>
          if a.isNull then none else some (ofAnnotation a)
        let pty : PyType := match annTy? with
          | some t => t
          | none => if i ≥ firstDefault then typeOfExpr sigs env defaults[i - firstDefault]! else .unknown
        match (p.getObjValAs? String "arg").toOption with
        | some nm => env' := env'.insert nm pty
        | none => pure ()
        argTys := argTys.push pty
      let allDefaulted := !params.isEmpty && defaults.size == params.size
      let retTy := (field e "body").elim .unknown (typeOfExpr sigs env')
      return .fn (if allDefaulted then [] else argTys.toList) retTy
  -- An f-string (`f"…"`) is always a `str`, regardless of the interpolated values' types.
  | some "JoinedStr" => .str
  | _ => .unknown

/-- The type a call returns. -/
partial def typeOfCall (sigs : Sigs) (env : Env) (e : Json) : PyType :=
  let args := ((e.getObjValAs? (Array Json) "args").toOption.getD #[]).toList
  match field e "func" with
  | some func =>
      match nodeType? func with
      | some "Name" =>
          match (func.getObjValAs? String "id").toOption with
          -- A builtin's return type wins; otherwise a user function's inferred return type.
          | some name =>
              match builtinReturn sigs env name args with
              | .unknown => (sigs.get? name).getD .unknown
              | t => t
          | none => .unknown
      | some "Attribute" =>
          -- A supported library call (`np.dot`, `math.pow`) resolves via the single library entry
          -- point in `Libraries/Registry.lean` (which knows each library's return types); anything
          -- else is a method on the receiver. TypeInfer never names a specific library.
          -- `collections.Counter()` / `collections.defaultdict(list)`: a module-qualified collection
          -- constructor resolves exactly like its bare (star-imported) form. Used when the library
          -- registry has no type for the member, which is the case for the `collections` shims.
          let fallback : PyType :=
            match (func.getObjValAs? String "attr").toOption with
            | some attr =>
                if ["Counter", "defaultdict", "OrderedDict", "deque"].contains attr then
                  builtinReturn sigs env attr args
                else methodReturn sigs env attr (field func "value") args
            | none => .unknown
          match (func.getObjValAs? String "library_module").toOption,
                (func.getObjValAs? String "library_member").toOption with
          | some m, some mem =>
              match Libraries.libraryMemberReturn? m mem (args.head?.elim .unknown (typeOfExpr sigs env)) with
              | some t => t
              | none => fallback
          | _, _ => fallback
      | _ => .unknown
  | none => .unknown

/-- Return type of a builtin `name(args)`; `unknown` for non-builtins. -/
partial def builtinReturn (sigs : Sigs) (env : Env) (name : String) (args : List Json) : PyType :=
  match constReturnBuiltins.lookup name with
  | some t => t
  | none =>
      let arg0 := args.head?.elim .unknown (typeOfExpr sigs env)
      match name with
      | "range" => .list .int
      | "list" | "sorted" | "reversed" => .list arg0.elemType
      | "set" | "frozenset" => .set arg0.elemType
      | "tuple" => .list arg0.elemType
      | "dict" => arg0
      -- collections/itertools constructors, so a captured `graph = defaultdict(list)` etc. is typed
      -- (an untyped closure-captured binder is the biggest `stuck`/`Unknown identifier` cascade).
      | "Counter" => .dict arg0.elemType .int
      | "OrderedDict" => arg0
      | "deque" => .list arg0.elemType
      | "accumulate" => .list arg0.elemType
      | "defaultdict" =>
          let vt := match args.head?.bind (·.getObjValAs? String "id" |>.toOption) with
            | some "list" => .list .unknown
            | some "set" => .set .unknown
            | some "dict" => .dict .unknown .unknown
            | some "int" | some "float" => .int
            | _ => .unknown
          .dict .unknown vt
      -- `min(a, b, …)` / `max(a, b, …)` return the join of all their arguments — a float sentinel
      -- and an int accumulator (`ans = max(ans, cur - inf)`) make the result `float`, which then
      -- flows back to the accumulator. The single-argument container form uses the element type.
      | "min" | "max" =>
          if args.length == 1 then
            if arg0.elemType != .unknown then arg0.elemType else arg0
          else PyType.joinAll (args.map (typeOfExpr sigs env))
      | "abs" | "sum" =>
          -- element for the container forms, else the argument itself.
          if args.length == 1 && arg0.elemType != .unknown then arg0.elemType else arg0
      -- `zip(a, b, …)` → list of tuples of the element types; `enumerate(a)` → list[(int, elem)];
      -- `pairwise(a)` → list of consecutive (elem, elem) pairs.
      | "zip" => .list (.tuple (args.map (fun a => (typeOfExpr sigs env a).elemType)))
      | "enumerate" => .list (.tuple [.int, arg0.elemType])
      | "pairwise" => .list (.tuple [arg0.elemType, arg0.elemType])
      | _ => .unknown

/-- Return type of `recv.attr(args)`. -/
partial def methodReturn (sigs : Sigs) (env : Env) (attr : String) (recv : Option Json) (args : List Json) : PyType :=
  match constReturnMethods.lookup attr with
  | some t => t
  | none =>
      let recvT := recv.elim .unknown (typeOfExpr sigs env)
      match attr with
      | "keys" => .list (match recvT with | .dict k _ => k | _ => .unknown)
      | "values" => .list (match recvT with | .dict _ v => v | _ => .unknown)
      | "items" => .list (match recvT with | .dict k v => .tuple [k, v] | _ => .unknown)
      -- `d.get(k)` gives `Optional[V]`; `d.get(k, default)` uses the default to type the result.
      | "get" =>
          let fromRecv := match recvT with | .dict _ v => v | _ => recvT.elemType
          match args[1]? with
          | some d => fromRecv.join (typeOfExpr sigs env d)
          | none => .opt fromRecv
      -- `d.pop(k)`/`d.setdefault(k)` return `V`; return `xs.pop()`/`q.popleft()`/`q.popright()`
      | "pop" | "popleft" | "popright" | "setdefault" =>
          let fromRecv := match recvT with | .dict _ v => v | _ => recvT.elemType
          fromRecv.join (args[1]?.elim .unknown (typeOfExpr sigs env))
      | "copy" => recvT
      | _ =>
          -- A user method with a declared return type, keyed `"Class.method"` in `sigs`.
          match recvT.classNameOf? with
          | some c => (sigs.get? s!"{c}.{attr}").getD .unknown
          | none => .unknown

end

end TypeInfer
