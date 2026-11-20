import TypeInfer.PyType
import TypeInfer.Annotation
import TypeInfer.Value
-- The type engine consumes only the Mathlib-free type-behaviour view (return shapes + teaches);
-- the codegen `Registry` (runtime names → Mathlib) is deliberately NOT imported here.
import Libraries.TypeBehaviour
import Libraries.Behaviour

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

/-- `float('inf')` / `float('nan')` — a non-finite sentinel, not a computed float. -/
private def isNonFiniteFloatCall (name : String) (args : List Json) : Bool :=
  name == "float" &&
  match args.head? with
  | some a =>
      nodeType? a == some "Constant" &&
      match (a.getObjVal? "value").toOption with
      | some (.str s) =>
          let t := s.toLower
          t == "inf" || t == "-inf" || t == "nan" || t == "infinity" || t == "-infinity"
      | _ => false
  | none => false

/-- A negative integer literal (`-1`), whether folded into a `Constant` or an unary-minus node.
    Used to detect `a ** -k`, which yields a `float` even for an `int` base (`2 ** -1 = 0.5`). -/
private def isNegativeIntLiteral (e : Json) : Bool :=
  match nodeType? e with
  | some "Constant" =>
      match e.getObjVal? "value" with
      | .ok (.num ⟨m, 0⟩) => m < 0
      | _ => false
  | some "UnaryOp" =>
      (e.getObjValAs? String "op").toOption == some "usub" &&
      match field e "operand" with
      | some o =>
          nodeType? o == some "Constant" &&
          match o.getObjVal? "value" with
          | .ok (.num ⟨m, 0⟩) => m > 0
          | _ => false
      | none => false
  | _ => false

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
    ("bin", .str), ("hex", .str), ("oct", .str),
    -- Predicates and identity/representation builtins whose result type is fixed (independent of args).
    ("any", .bool), ("all", .bool), ("isinstance", .bool), ("issubclass", .bool),
    ("callable", .bool), ("id", .int), ("repr", .str), ("ascii", .str), ("format", .str) ]

mutual

/-- The type of an expression under the current environment. `sigs` gives user functions' return
types. Total: `unknown` when unsure. -/
partial def typeOfExpr (sigs : Sigs) (env : Env) (e : Json) : PyType :=
  match nodeType? e with
  | some "Name" =>
      match (e.getObjValAs? String "id").toOption with
      | some id =>
          match env.get? id with
          | some t => t
          -- A bare reference to a user function is a callable returning that function's inferred type,
          -- so passing it (`f(g)`) lets a higher-order body's `g()` resolve to `g`'s return.
          | none => match sigs.get? id with
                    | some rt => .fn [] rt
                    | none => .unknown
      | none => .unknown
  | some "Constant" => ofValue e
  | some "List" => .list (PyType.joinAll ((eltsOf e).map (typeOfExpr sigs env)))
  | some "Set" => .set (PyType.joinAll ((eltsOf e).map (typeOfExpr sigs env)))
  | some "Tuple" => .tuple ((eltsOf e).map (typeOfExpr sigs env))
  | some "Dict" =>
      let entries := ((e.getObjValAs? (Array Json) "entries").toOption.getD #[]).toList
      -- Each entry is a `k: v` pair, or a `**d` spread (contributing `d`'s own key/value types), so
      -- `merged = {**d1, **d2}` types as the join of `d1`/`d2` rather than dropping out.
      let contrib := entries.map fun en =>
        match field en "spread" with
        | some sp => match typeOfExpr sigs env sp with
                     | .dict sk sv => (sk, sv)
                     | _ => (.unknown, .unknown)
        | none => ((field en "key").elim .unknown (typeOfExpr sigs env),
                   (field en "value").elim .unknown (typeOfExpr sigs env))
      .dict (PyType.joinAll (contrib.map (·.1))) (PyType.joinAll (contrib.map (·.2)))
  | some "Range" => .list .int
  | some "BinOp" =>
      match field e "left", field e "right" with
      | some l, some r =>
          let lt := typeOfExpr sigs env l
          let rt := typeOfExpr sigs env r
          -- A class operand dispatches to its dunder: the return type of `C.__add__` (or of the
          -- `@overload` for this operand, `C.__sub__'T`).
          let dunder? : Option String := match (e.getObjValAs? String "op").toOption with
            | some "add" => some "__add__" | some "sub" => some "__sub__" | some "mul" => some "__mul__"
            | some "div" => some "__truediv__" | some "floordiv" => some "__floordiv__"
            | some "mod" => some "__mod__" | _ => none
          let classRet? : Option PyType := match lt, dunder? with
            | .cls c, some d =>
                let operand := rt.operandName
                (sigs.get? s!"{c}.{d}'{operand}").orElse (fun _ => sigs.get? s!"{c}.{d}")
            | _, _ => none
          match classRet? with
          | some t => t
          | none =>
          match (e.getObjValAs? String "op").toOption with
          -- `[0] * n` / `n * [0]` repeats a list; every other `*` is arithmetic.
          | some "mul" =>
              match lt, rt with
              | .list _, _ => lt
              | _, .list _ => rt
              -- string repeat `s * n` / `n * s` (`"ab" * 3`)
              | .str, _ | _, .str => .str
              | _, _ => arith lt rt
          -- `s % args` is %-formatting → str; `n % m` is modulo (arithmetic).
          | some "mod" => match lt with | .str => .str | _ => arith lt rt
          -- Python's `/` is true division, so a NUMERIC left operand gives a `float` (`int / int`,
          -- `float / n`). But `/` is overloaded — `pathlib.Path / "sub"` is a `Path`, not a float — so
          -- only commit `float` when the left is actually numeric; otherwise leave it unknown. A boxed
          -- operand stays boxed (`PyAny / 2` dispatches on the tag → `PyAny`).
          | some "div" => match lt, rt with
              | .any, _ | _, .any => .any
              | _, _ => match lt with | .int | .float | .bool => .float | _ => .unknown
          -- `a ** -k` is a `float` even for an `int` base (`2 ** -1 = 0.5`); a FRACTIONAL exponent
          -- (`x ** 0.5`, a root) is always a `float` regardless of base (pow requires a numeric base,
          -- so this is sound even when the base type is still `unknown`); else keep the base's type.
          | some "pow" =>
              if rt == .float then .float
              else if isNegativeIntLiteral r && lt == .int then .float
              else arith lt rt
          -- `+` concatenation: with one KNOWN str/list operand and the other still `unknown`, a
          -- well-typed program forces the unknown to that type (`str + x` errors unless `x` is a str),
          -- so `v + "\n"` is `str` — which lets a `list[str]` built by `lines.append(v + "\n")` type.
          | some "add" =>
              match lt, rt with
              | .str, .unknown | .unknown, .str => .str
              | .list a, .unknown | .unknown, .list a => .list a
              | _, _ => arith lt rt
          | _ => arith lt rt
      | _, _ => .unknown
  | some "UnaryOp" =>
      if (e.getObjValAs? String "op").toOption == some "not" then .bool
      else (field e "operand").elim .unknown (typeOfExpr sigs env)
  | some "Compare" => .bool
  | some "BoolOp" =>
      -- `a and b` / `a or b` evaluate to one operand, so the type is their join; under `or` a `None`
      -- before the last operand is falsy and never the result (`items or []` is a list).
      let ts := ((e.getObjValAs? (Array Json) "values").toOption.getD #[]).toList.map (typeOfExpr sigs env)
      let ts := if (e.getObjValAs? String "op").toOption == some "or" then
          ts.dropLast.map (fun t => match t with | .opt u => u | u => u) ++ ts.getLast?.toList
        else ts
      PyType.joinAll ts
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
          -- A class NAME as receiver (`MyClass.class_var`) isn't in `env`; fall back to `sigs` where a
          -- class is `.cls Name`, so class-variable / static access resolves like an instance access.
          let recvT := match typeOfExpr sigs env recv with
            | .unknown =>
                if nodeType? recv == some "Name" then
                  ((recv.getObjValAs? String "id").toOption.bind (sigs.get? ·)).getD .unknown
                else .unknown
            | t => t
          match recvT.classNameOf? with
          -- A METHOD reference `obj.method` (not a call) is a function value → `callable`; the `#fn`
          -- key holds its signature. A data field falls through to its declared type.
          | some c => match sigs.get? s!"{c}.{attr}#fn" with
                      | some fnT => fnT
                      | none => (sigs.get? s!"{c}.{attr}").getD .unknown
          | none => .unknown
      | _, _ => .unknown
  -- Comprehensions: bind each generator target from its iterable's element type, then type the
  -- element/key/value in that extended env (so `[[float('inf')]*k for _ in range(n)]` is
  -- `list[list[float]]`, not `list[Any]`).
  | some "ListComp" | some "SetComp" | some "GeneratorExp" | some "DictComp" =>
      let gens := (e.getObjValAs? (Array Json) "generators").toOption.getD #[]
      let env' := gens.foldl (fun env gen =>
        match field gen "target", field gen "iter" with
        | some target, some iter =>
            let elemT := (typeOfExpr sigs env iter).elemType
            match nodeType? target with
            | some "Name" => match (target.getObjValAs? String "id").toOption with
                | some name => env.insert name elemT | none => env
            -- A tuple target (`for k, v in d.items()`) distributes the element type: a tuple element
            -- binds position-wise (`k : str, v : int`), any other iterable element goes to each name.
            | some "Tuple" | some "List" =>
                let elts := (target.getObjValAs? (Array Json) "elts").toOption.getD #[]
                (Array.range elts.size).foldl (fun env i =>
                  match (elts[i]!.getObjValAs? String "id").toOption with
                  | some nm =>
                      let t := match elemT with | .tuple ts => ts[i]?.getD .unknown | _ => elemT.elemType
                      env.insert nm t
                  | none => env) env
            | _ => env
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
          -- `super()` inside a method: the enclosing class's base is seeded as `super#cls`, so
          -- `super().m()` reads the base's `m` (recv typed to the base class here).
          | some "super" => (env.get? "super#cls").getD .unknown
          -- A builtin's return type wins; otherwise a user function's inferred return type.
          | some name =>
              match builtinReturn sigs env name args with
              | .unknown =>
                  match (sigs.get? name).getD .unknown with
                  -- A call to a function-VALUED variable (`b = some_func; b()`) uses the `.fn` return.
                  | .unknown => match env.get? name with
                                | some (.fn _ ret) => ret
                                | _ => .unknown
                  | t => t
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
                -- A module-qualified collections constructor (`collections.Counter()`) declares its
                -- return in `collectionsBehaviour?`; `defaultdict` reads its factory arg's identifier
                -- (so it stays in `builtinReturn`); anything else is a method call.
                match Libraries.memberTypeBehaviour? "collections" attr with
                | some b => b.returns (args.map (typeOfExpr sigs env))
                | none => if attr == "defaultdict" then builtinReturn sigs env attr args
                          else methodReturn sigs env attr (field func "value") args
            | none => .unknown
          match (func.getObjValAs? String "library_module").toOption,
                (func.getObjValAs? String "library_member").toOption with
          | some m, some mem =>
              match Libraries.libraryMemberReturn? m mem (args.head?.elim .unknown (typeOfExpr sigs env)) with
              | some t => t
              | none => fallback
          | _, _ => fallback
      -- Calling any OTHER expression (`d["b"]()`, `a[0]()`, `(x if c else y)()`): if it evaluates to
      -- a function, the call yields that function's return type. Sound — a heterogeneous container's
      -- element joins to `.any`, whose `.fn` return is `.any` (→ no concrete claim).
      | _ =>
          match typeOfExpr sigs env func with
          | .fn _ ret => ret
          | _ => .unknown
  | none => .unknown

/-- Return type of a builtin `name(args)`; `unknown` for non-builtins. -/
partial def builtinReturn (sigs : Sigs) (env : Env) (name : String) (args : List Json) : PyType :=
  -- `float('inf')`/`float('nan')` is a POLYMORPHIC sentinel: it adapts to the numeric type of
  -- whatever container/expression it lands in (an int DP keeps `int`, a float DP keeps `float`),
  -- rather than forcing everything to `float`. So it is the numeric bottom (`.unknown`), joining up
  -- to the surrounding values — codegen's `pyNonFinite` then picks the `PyNonFinite Int/Rat/Float`.
  if isNonFiniteFloatCall name args then .unknown else
  match constReturnBuiltins.lookup name with
  | some t => t
  -- `defaultdict(list)` reads its factory ARGUMENT's identifier (a `list`/`set`/`int` name node), not
  -- just an argument type, so it can't be a `List PyType → PyType` behaviour and stays here.
  | none => if name == "defaultdict" then
      let vt := match args.head?.bind (·.getObjValAs? String "id" |>.toOption) with
        | some "list" => .list .unknown
        | some "set" => .set .unknown
        | some "dict" => .dict .unknown .unknown
        | some "int" | some "float" => .int
        -- A callable factory that is not a bare type name (`defaultdict(lambda: [0]*m)`): its RETURN
        -- type is the value type (`list[int]` here), so the empty defaultdict's value is pinned.
        | _ => match args.head?.map (typeOfExpr sigs env) with
               | some (.fn _ r) => r
               | _ => .unknown
      .dict .unknown vt
    -- `map(f, xs)` yields a list of `f`'s RESULTS, so its element is `f`'s return type — read from a
    -- named callback (`int`→int cast, or a user fn's inferred return). Lets `list(map(int, l))` type
    -- as `list[int]`, so a mut var reassigned str-list→int-list joins to `List PyAny` (Option A boxing).
    else if name == "map" then
      match args.head?.bind (·.getObjValAs? String "id" |>.toOption) with
      | some f => .list ((constReturnBuiltins.lookup f).getD ((sigs.get? f).getD .unknown))
      | none => .list .unknown
    -- `product`/`combinations`/`permutations` back each result COMBINATION with a Lean `List` (no
    -- variadic tuple type), so their element is `list[E]`, not a `Prod` — the for-target unpack must
    -- index, not `Prod.fst`. Element `E` = join of the inputs' element types (product) / the single
    -- iterable's element type (combinations/permutations).
    else if name == "product" then
      .list (.list (PyType.joinAll (args.map (fun a => (typeOfExpr sigs env a).elemType))))
    else if name == "combinations" || name == "permutations" then
      .list (.list (args.head?.elim .unknown (fun a => (typeOfExpr sigs env a).elemType)))
    -- `reduce(f, iterable[, init])` folds `f` over the iterable; its result is `f`'s return type (a
    -- binary `f : (T,T)->T` over `T` elements yields `T`). Read `f`'s return from a named callback,
    -- falling back to the iterable's element type.
    else if name == "reduce" then
      let elemTy := args[1]?.elim .unknown (fun a => (typeOfExpr sigs env a).elemType)
      match args.head?.bind (·.getObjValAs? String "id" |>.toOption) with
      | some f =>
          let r := (constReturnBuiltins.lookup f).getD ((sigs.get? f).getD .unknown)
          if r == .unknown then elemTy else r
      | none => elemTy
    -- Every other arg-dependent builtin / star-imported member declares its return SHAPE in
    -- `Libraries.bareBehaviour?`, so this engine no longer hardcodes any member's name (§27).
    else match Libraries.bareTypeBehaviour? name with
      | some b => b.returns (args.map (typeOfExpr sigs env))
      | none => .unknown

/-- Return type of `recv.attr(args)` — entirely `methodBehaviour?`-driven, with the RECEIVER as
effective argument 0 (so `d.get(k, default)` reads the receiver and the default from the arg types).
The engine names no method. -/
partial def methodReturn (sigs : Sigs) (env : Env) (attr : String) (recv : Option Json) (args : List Json) : PyType :=
  let recvT0 := recv.elim .unknown (typeOfExpr sigs env)
  -- A class NAME used as a receiver (`MyClass.func()` — a static/class method, or the class object)
  -- isn't in `env` (class names aren't bound as values), so `typeOfExpr` returns unknown. Fall back to
  -- `sigs`, where a class is registered as `.cls Name`, and resolve the method on it.
  let recvName? := recv.bind (fun r =>
    if nodeType? r == some "Name" then (r.getObjValAs? String "id").toOption else none)
  -- (A class name reads as a constructor value `.fn [] (.cls C)` through `typeOfExpr`.)
  let isClassName := recvName?.any fun n => sigs.get? n == some (.cls n)
  let recvT := if recvT0 == .unknown || isClassName then
      (recvName?.bind (sigs.get? ·)).getD .unknown
    else recvT0
  -- A user method call `obj.attr(...)` on a class instance resolves to `Class.attr`'s inferred return.
  let userMethod : PyType := match recvT with
    | .cls c => (sigs.get? s!"{c}.{attr}").getD .unknown
    | .opt (.cls c) => (sigs.get? s!"{c}.{attr}").getD .unknown
    | _ => .unknown
  match userMethod with
  | .unknown => ((Libraries.methodBehaviour? attr).map (·.returns (recvT :: args.map (typeOfExpr sigs env)))).getD .unknown
  | t => t

end

end TypeInfer
