import TypeInfer.Rules

/-!
# The intraprocedural fixpoint

`inferFunction` works out a type for every local in one function: seed the parameters from their
annotations, then walk the body over and over — learning a little more each pass — until nothing
changes. Because every update only `join`s upward, the environment can only climb the lattice, so
it settles.

`stampTypes` then writes each settled type back onto the IR as a `_ty` field on the binder
(parameters, assignment targets, `for` targets), where the code generator reads it.

Nested `def`s are handled by seeding their inference with the enclosing function's environment, so a
captured variable already has a type when the helper is lifted out.
-/

namespace TypeInfer

open Lean

private def nodeTypeOf (j : Json) : Option String := (j.getObjValAs? String "node_type").toOption
private def getField (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
private def nameId? (j : Json) : Option String :=
  if nodeTypeOf j == some "Name" then (j.getObjValAs? String "id").toOption else none

/-- For a (possibly nested) subscript target `f[h][i][j]`, the base name `f` and the nesting depth
(here `3`), so codegen can learn `f : list[list[list[<v>]]]` from a deep `f[h][i][j] = v`. -/
private partial def subscriptBaseDepth (target : Json) : Option (String × Nat) :=
  if nodeTypeOf target == some "Subscript" then
    match getField target "value" with
    | some v => match nameId? v with
        | some n => some (n, 1)
        | none => (subscriptBaseDepth v).map (fun (b, d) => (b, d + 1))
    | none => none
  else none

/-- The statement lists nested directly in `s` (`if`/`for`/`while`/`with`/`try` blocks), not
descending into a nested `def`/`class` (those have their own scope). -/
private def childBlocks (s : Json) : List (List Json) := Id.run do
  if nodeTypeOf s == some "FunctionDef" || nodeTypeOf s == some "ClassDef" then return []
  let mut blocks := #[]
  for f in #["body", "orelse", "finalbody"] do
    if let .ok elems := s.getObjValAs? (Array Json) f then blocks := blocks.push elems.toList
  if let .ok handlers := s.getObjValAs? (Array Json) "handlers" then
    for h in handlers do
      if let .ok elems := h.getObjValAs? (Array Json) "body" then blocks := blocks.push elems.toList
  return blocks.toList

/-- A bare `container.append/add(v)` statement, teaching the container's element type. The receiver
may itself be an index (`graph[k].append(v)` on a `defaultdict(list)`), which teaches the OUTER
container's value type instead. -/
def applyMutation (sigs : Sigs) (env : Env) (value : Json) : Env :=
  if nodeTypeOf value != some "Call" then env else
  match getField value "func" with
  | some func =>
      if nodeTypeOf func != some "Attribute" then env else
      match (func.getObjValAs? String "attr").toOption, getField func "value" with
      | some attr, some recv =>
          let args := ((value.getObjValAs? (Array Json) "args").toOption.getD #[]).toList
          let elemFrom (i : Nat) : PyType := (args[i]?).elim .unknown (typeOfExpr sigs env)
          let learned : PyType := match attr with
            -- `add` is a SET method — learn `.set`, not `.list`, so `s = set()` (`.set unknown`)
            -- refines to `.set T` instead of joining `.set` with `.list` (→ unknown → PyAny).
            | "add" => .set (elemFrom 0)
            | "append" | "insert" => .list (elemFrom (if attr == "insert" then 1 else 0))
            | "extend" => match args[0]?.elim .unknown (typeOfExpr sigs env) with
                          | .list e => .list e
                          | _ => .unknown
            | _ => .unknown
          if learned == .unknown then env
          else
            let join1 (env : Env) (n : String) (t : PyType) : Env :=
              env.insert n ((env.get? n |>.getD .unknown).join t)
            match nameId? recv with
            | some cname => join1 env cname learned
            | none =>
                -- `graph[k].append(v)`: the mutated thing is the VALUE at `k`, so `graph` is a
                -- dict from the index type to `learned` (or a list of `learned`).
                if nodeTypeOf recv == some "Subscript" then
                  match (getField recv "value").bind nameId? with
                  | some base =>
                      let kt := (getField recv "slice").elim .unknown (typeOfExpr sigs env)
                      let outer := match env.get? base |>.getD .unknown with
                        | .list _ => .list learned
                        | _ => .dict kt learned
                      join1 env base outer
                  | none => env
                else env
      | _, _ => env
  | none => env

/-- Bind an assignment/loop/comprehension target to type `t`, distributing a tuple type over a
tuple target (`a, b = pair`). Only joins known facts in. -/
partial def bindTargetType (env : Env) (target : Json) (t : PyType) : Env :=
  match nodeTypeOf target with
  | some "Name" =>
      match nameId? target with
      | some n => if t == .unknown then env else env.insert n ((env.get? n |>.getD .unknown).join t)
      | none => env
  | some "Tuple" | some "List" =>
      let elts := (target.getObjValAs? (Array Json) "elts").toOption.getD #[]
      match t with
      | .tuple es => (Array.range elts.size).foldl (fun e i => bindTargetType e elts[i]! (es[i]?.getD .unknown)) env
      | _ => elts.foldl (fun e elt => bindTargetType e elt t.elemType) env
  | _ => env

/-- A `FunctionDef`'s type as a value: `fn[param annotations] → return annotation` (un-annotated
slots are `unknown`). Lets a nested def referenced by name (`return mul`, `key=mul`) be typed as a
function, so a higher-order caller's callback param is refined from the call site. -/
private def functionSignatureType (fn : Json) : PyType :=
  let args := ((getField fn "args").bind (fun a => (a.getObjValAs? (Array Json) "args").toOption)).getD #[]
  let argTypes := args.toList.map fun a =>
    match getField a "annotation" with
    | some ann => if ann.isNull then PyType.unknown else ofAnnotation ann
    | none => PyType.unknown
  let ret := match getField fn "returns" with
    | some r => if r.isNull then PyType.unknown else ofAnnotation r
    | none => PyType.unknown
  PyType.fn argTypes ret

/-- Update the environment with what one statement teaches us. Only ever `join`s facts in. -/
def applyStmt (sigs : Sigs) (env : Env) (s : Json) : Env :=
  let learn (env : Env) (name : String) (t : PyType) : Env :=
    if t == .unknown then env else env.insert name ((env.get? name |>.getD .unknown).join t)
  match nodeTypeOf s with
  -- A nested `def foo(...)` binds `foo` to its function type, so `return foo` / `key=foo` is typed.
  | some "FunctionDef" =>
      match s.getObjValAs? String "name" with
      | .ok nm => env.insert nm (functionSignatureType s)
      | _ => env
  | some "AnnAssign" =>
      match (getField s "target").bind nameId?, getField s "annotation" with
      | some name, some ann => env.insert name (ofAnnotation ann)   -- an explicit annotation wins
      | _, _ => env
  | some "Assign" =>
      match getField s "target", getField s "value" with
      | some target, some value =>
          match nameId? target with
          | some name => learn env name (typeOfExpr sigs env value)
          -- `xs[i] = v` teaches the element/value type of the container `xs`.
          | none =>
              -- A TUPLE target distributes, exactly as in a `for` (`a, (b, c) = …` after desugaring
              -- leaves `b, c = tmp`, whose element types are what pick tuple- over list-unpacking).
              if nodeTypeOf target == some "Tuple" || nodeTypeOf target == some "List" then
                bindTargetType env target (typeOfExpr sigs env value)
              else if nodeTypeOf target == some "Subscript" then
                match (getField target "value").bind nameId? with
                | some cname =>
                    let vt := typeOfExpr sigs env value
                    -- A SLICE target (`t[a:b] = xs`) replaces a run with a LIST, so `t` and the RHS
                    -- share a type; an INDEX target (`t[i] = v`) makes `t` a list OF `v`'s type.
                    let isSlice := (getField target "slice").any (nodeTypeOf · == some "Slice")
                    let learned := match env.get? cname |>.getD .unknown with
                      | .dict _ _ => .dict ((getField target "slice").elim .unknown (typeOfExpr sigs env)) vt
                      | _ => if isSlice then vt else .list vt
                    learn env cname learned
                -- Nested `f[h][i][j] = v` teaches `f : list[list[list[<v>]]]` (grid/tensor DP).
                | none => match subscriptBaseDepth target with
                    | some (base, depth) =>
                        learn env base ((List.range depth).foldl (fun t _ => PyType.list t) (typeOfExpr sigs env value))
                    | none => env
              else env
      | _, _ => env
  | some "AugAssign" =>
      match getField s "target", getField s "value" with
      | some target, some value =>
          match nameId? target with
          | some name => learn env name (arith (env.get? name |>.getD .unknown) (typeOfExpr sigs env value))
          -- `counts[k] += 1` teaches both sides of `counts` (a `Counter()` starts fully unknown).
          | none =>
              if nodeTypeOf target == some "Subscript" then
                match (getField target "value").bind nameId? with
                | some cname =>
                    let vt := typeOfExpr sigs env value
                    let isSlice := (getField target "slice").any (nodeTypeOf · == some "Slice")
                    let learned := match env.get? cname |>.getD .unknown with
                      | .dict _ v => .dict ((getField target "slice").elim .unknown (typeOfExpr sigs env)) (arith v vt)
                      | _ => if isSlice then vt else .list vt
                    learn env cname learned
                -- Nested `f[h][i][j] += v` widens the deep element (`join` at that depth).
                | none => match subscriptBaseDepth target with
                    | some (base, depth) =>
                        learn env base ((List.range depth).foldl (fun t _ => PyType.list t) (typeOfExpr sigs env value))
                    | none => env
              else env
      | _, _ => env
  | some "For" =>
      match getField s "target", getField s "iter" with
      -- `bindTargetType` also distributes over a TUPLE target (`for a, b in pairs`), which a plain
      -- name lookup misses — leaving `a`/`b` untyped, and anything they index untyped in turn.
      | some target, some iter => bindTargetType env target (typeOfExpr sigs env iter).elemType
      | _, _ => env
  -- `xs.append(v)` / `xs.add(v)` teaches that `xs` holds values of `v`'s type.
  | some "Expr" =>
      match getField s "value" with
      | some value => applyMutation sigs env value
      | none => env
  | _ => env

/-- Bind a comprehension target's names, but ONLY where the name is not already bound in `outer` — a
comprehension target that shadows an outer variable owns a separate (Python-3) scope, so it must not
overwrite the outer type. Fresh names are bound (harmless, and lets a call inside the comprehension
hint the callee); shadowing names are left as the outer binding. -/
private partial def bindCompTargetFresh (outer : Env) (env : Env) (target : Json) (t : PyType) : Env :=
  match nodeTypeOf target with
  | some "Name" =>
      match nameId? target with
      | some n => if outer.contains n || t == .unknown then env else env.insert n t
      | none => env
  | some "Tuple" | some "List" =>
      let elts := (target.getObjValAs? (Array Json) "elts").toOption.getD #[]
      match t with
      | .tuple es => (Array.range elts.size).foldl (fun e i => bindCompTargetFresh outer e elts[i]! (es[i]?.getD .unknown)) env
      | _ => elts.foldl (fun e elt => bindCompTargetFresh outer e elt t.elemType) env
  | _ => env

/-- Bind every comprehension target in `json` (`[… for x in xs]`, `for a,b in zip(...)`) from its
iterable's element type, so a call inside the comprehension sees the target typed. Fresh names only:
a target shadowing an outer variable keeps the outer binding (see `bindCompTargetFresh`). -/
partial def compBindings (sigs : Sigs) (env : Env) (json : Json) : Env :=
  let env :=
    if ["ListComp", "SetComp", "DictComp", "GeneratorExp"].contains (nodeTypeOf json |>.getD "") then
      let gens := (json.getObjValAs? (Array Json) "generators").toOption.getD #[]
      gens.foldl (fun e gen =>
        match getField gen "target", getField gen "iter" with
        | some target, some iter => bindCompTargetFresh env e target (typeOfExpr sigs e iter).elemType
        | _, _ => e) env
    else env
  match json with
  | .arr xs => xs.foldl (compBindings sigs) env
  | .obj fs => fs.toList.foldl (fun e (_, v) => compBindings sigs e v) env
  | _ => env

/-- Every statement in a body, flattened through nested blocks but not into nested `def`s. -/
private partial def flatStmts (stmts : List Json) : List Json :=
  stmts.foldl (fun acc s => acc ++ [s] ++ (childBlocks s).flatMap flatStmts) []

/-- The declared parameter names of `fn`, in order. -/
def paramNames (fn : Json) : Array String := Id.run do
  let mut names := #[]
  let .ok args := fn.getObjVal? "args" | return names
  let .ok argsArr := args.getObjValAs? (Array Json) "args" | return names
  for arg in argsArr do
    if let .ok name := arg.getObjValAs? String "arg" then names := names.push name
  return names

/-- Parameter name → annotated type for a `FunctionDef` (annotated params only). -/
private def paramSeed (fn : Json) : Env := Id.run do
  let mut env : Env := {}
  let .ok args := fn.getObjVal? "args" | return env
  let .ok argsArr := args.getObjValAs? (Array Json) "args" | return env
  for arg in argsArr do
    if let .ok name := arg.getObjValAs? String "arg" then
      match getField arg "annotation" with
      | some ann => if !ann.isNull then env := env.insert name (ofAnnotation ann)
      | none => pure ()
  return env

/-- The type a **type-exclusive** method pins its receiver to, or `unknown`. Only methods that belong
to exactly ONE builtin type are listed — Python semantics, exhaustively. Shared methods are omitted
on purpose (`pop` is list AND dict; `remove` is list AND set; `index`/`count` are list/str/tuple;
`update` is dict AND set) so a receiver is never mis-typed. -/
private def methodReceiverType? (attr : String) : PyType :=
  -- str-only: no list/dict/set/tuple has these.
  if ["split", "rsplit", "splitlines", "upper", "lower", "title", "capitalize", "casefold",
      "swapcase", "strip", "lstrip", "rstrip", "replace", "startswith", "endswith", "find", "rfind",
      "join", "format", "format_map", "ljust", "rjust", "center", "zfill", "encode", "expandtabs",
      "partition", "rpartition", "removeprefix", "removesuffix", "translate", "maketrans",
      "isdigit", "isalpha", "isalnum", "isspace", "isupper", "islower", "istitle", "isnumeric",
      "isdecimal", "isidentifier", "isprintable", "isascii"].contains attr then .str
  -- list-only: str/dict/set lack these (`pop`/`remove`/`index`/`count` are shared → excluded).
  else if ["append", "extend", "insert", "sort", "reverse"].contains attr then .list .unknown
  -- dict-only: `keys`/`values`/`items`/`get`/`setdefault`/`popitem`/`fromkeys` (`update`/`pop` shared).
  else if ["keys", "values", "items", "get", "setdefault", "popitem", "fromkeys"].contains attr
    then .dict .unknown .unknown
  -- set-only: `add`/`discard`/`issubset`/… (`remove`/`update`/`union`&co are shared or on frozenset).
  else if ["add", "discard", "issubset", "issuperset", "isdisjoint", "symmetric_difference",
           "symmetric_difference_update", "difference_update", "intersection_update"].contains attr
    then .set .unknown
  else .unknown

/-- What `name`'s usage in one expression unambiguously tells us — enumerated exhaustively over the
Python signals that pin exactly one type: a type-exclusive method on it (`p.split()` → str), an
int-only operator over it (`p << 1`, `p >> 1`, `~p` — bitwise `& | ^` are int OR set, so NOT here),
or a type-fixing builtin arg (`ord(p)` → str, `chr(p)` → int). Genuinely ambiguous uses (`p[i]`,
`for x in p`, `len(p)`, `p + q`) stay `unknown` — the fixpoint fills them in. -/
private partial def usageType (name : String) (json : Json) : PyType :=
  let isName (j : Option Json) : Bool := j.bind nameId? == some name
  let here : PyType :=
    match nodeTypeOf json with
    | some "Call" =>
        match getField json "func" with
        -- `p.method(...)`: a type-exclusive method pins `p`.
        | some func =>
            if nodeTypeOf func == some "Attribute" then
              if isName (getField func "value") then
                (func.getObjValAs? String "attr").toOption.elim .unknown methodReceiverType?
              else .unknown
            -- `ord(p)` → p is a one-char str; `chr(p)` → p is an int.
            else match nameId? func with
              | some fn =>
                  let args := (json.getObjValAs? (Array Json) "args").toOption.getD #[]
                  -- `p(...)` — the param is CALLED, so it is a function of this arity (a higher-order
                  -- callback); the arg/return types are refined from the call site interprocedurally.
                  if fn == name then .fn (List.replicate args.size .unknown) .unknown
                  else if args.any (fun a => nameId? a == some name) then
                    if fn == "ord" then .str else if fn == "chr" then .int else .unknown
                  else .unknown
              | none => .unknown
        | none => .unknown
    -- Shift is int-only in Python (`p << 1`); `& | ^` also work on sets, so they pin nothing.
    | some "BinOp" =>
        match (json.getObjValAs? String "op").toOption with
        | some op =>
            if ["lshift", "rshift"].contains op
               && (isName (getField json "left") || isName (getField json "right")) then .int
            else .unknown
        | none => .unknown
    -- `~p` (bitwise NOT) is int-only.
    | some "UnaryOp" =>
        if (json.getObjValAs? String "op").toOption == some "invert" && isName (getField json "operand")
        then .int else .unknown
    | _ => .unknown
  let sub := match json with
    | .arr xs => PyType.joinAll (xs.toList.map (usageType name))
    | .obj fs => PyType.joinAll (fs.toList.map (fun (_, v) => usageType name v))
    | _ => .unknown
  here.join sub

/-- Seed each unannotated parameter from unambiguous body usage (`p.split()` → str, `p.append()` →
list, `p.keys()` → dict). This is the safe part of the use-based inference the old Python pre-pass
did. -/
private def paramUsageSeed (fn : Json) : Env := Id.run do
  let body := fn.getObjValAs? (Array Json) "body" |>.toOption.getD #[]
  let mut env : Env := {}
  for name in paramNames fn do
    let t := usageType name (Json.arr body)
    if t != .unknown then env := env.insert name t
  return env

/-- Infer a type for every local in `fn`, reflowing to a fixpoint. `outer` seeds the environment
with the enclosing scope so a nested def's captures start typed; `hints` seeds unannotated
parameters with types learned from call sites; `sigs` resolves calls to user functions. Precedence:
enclosing captures > annotations > call-site hints > body-usage. -/
partial def inferFunction (sigs : Sigs) (outer hints : Env) (fn : Json) : Env := Id.run do
  let body := (fn.getObjValAs? (Array Json) "body").toOption.getD #[]
  let stmts := flatStmts body.toList
  -- Weakest → strongest: body-usage, enclosing captures, call-site hints, annotations. Hints and
  -- annotations override captures because a parameter shadows an outer name of the same name (a
  -- nested `def dfs(root)` inside a scope with its own `root` must use its call-site type).
  let mut env := paramUsageSeed fn
  env := outer.fold (fun m k v => m.insert k v) env
  env := hints.fold (fun m k v => m.insert k v) env
  env := (paramSeed fn).fold (fun m k v => m.insert k v) env
  let bodyJson := Json.arr body
  -- Reflow until stable. The lattice climbs, so a small cap is a sound floor, not a correctness risk.
  for _ in [0:8] do
    -- `compBindings` types comprehension targets so a call inside a comprehension can hint the callee
    -- (`[f(point) for point in data]`). It binds only FRESH names — a comprehension target that
    -- shadows an outer variable owns a separate scope (Python-3), so clobbering the outer type (a
    -- loop `v : int` vs a comprehension `v : list[int]` → `any`) would poison it. Fresh-only respects
    -- that: never downgrade an outer binding.
    let next := compBindings sigs (stmts.foldl (applyStmt sigs) env) bodyJson
    if next.size == env.size && next.fold (fun ok k v => ok && (env.get? k |>.getD .unknown) == v) true then
      env := next
      break
    env := next
  return env

/-- The type `fn` returns: the join of every `return <e>` under its inferred environment. A bare
`return` (no value) or falling off the end contributes `None`. -/
partial def returnTypeOf (sigs : Sigs) (hints : Env) (fn : Json) : PyType := Id.run do
  let env := inferFunction sigs {} hints fn
  let body := (fn.getObjValAs? (Array Json) "body").toOption.getD #[]
  let mut ret : PyType := .unknown
  for s in flatStmts body.toList do
    if nodeTypeOf s == some "Return" then
      match getField s "value" with
      | some v => if !v.isNull then ret := ret.join (typeOfExpr sigs env v) else ret := ret.join .none
      | none => ret := ret.join .none
  return ret

/-! ### Writing the inferred types back onto the IR as `_ty` -/

/-- A `defaultdict[k, v]` annotation node, for a dict whose runtime backing is `PyDefaultDict`. -/
private def defaultDictAnnotation? (k v : PyType) : Option Json := do
  let kj ← toAnnotation? k
  let vj ← toAnnotation? v
  return Json.mkObj [("node_type", .str "Subscript"),
    ("value", Json.mkObj [("node_type", .str "Name"), ("id", .str "defaultdict")]),
    ("slice", Json.mkObj [("node_type", .str "Tuple"), ("elts", Json.arr #[kj, vj])])]

/-- Stamp `_ty` (an annotation node) on a target if we know a fully-determined type for it, unless a
`_ty` is already present (the interprocedural pass stamps first; a later intraprocedural pass must
not clobber its richer result). Tuple targets stamp each element. -/
partial def stampTarget (env : Env) (target : Json) (allowDict : Bool := true) : Json :=
  match nodeTypeOf target with
  | some "Name" =>
      if (getField target "_ty").isSome then target
      else
        -- Only ascribe a local when Lean cannot infer it from the assignment's RHS on its own — i.e.
        -- an empty/none-shaped container (`xs = []`, `d = {}`) whose element type is otherwise stuck.
        -- For a determined RHS (a numpy/division result, a literal), ascribing would *force* a type
        -- (e.g. `ℚ`) that fights what the RHS actually elaborates to (e.g. `Float`); leave it to Lean.
        match (nameId? target).filter (· != "_") |>.bind (env.get? ·) with
        -- A variable that is two incompatible types across paths (`y = 10/x` then `y = 0`) is boxed
        -- as `PyAny`, so the reassignments coerce instead of clashing.
        | some .any =>
            target.setObjVal! "_ty" (Json.mkObj [("node_type", .str "Name"), ("id", .str "PyAny")])
        | some t =>
            -- A dict from a `defaultdict`/`Counter` call is backed by `PyDefaultDict`, not the
            -- `Std.HashMap` a plain `dict[_, _]` annotation emits, so it is stamped as
            -- `defaultdict[k, v]` — which the codegen annotation reader maps to the library type.
            let ann? := match t, allowDict with
              | .dict k v, false => defaultDictAnnotation? k v
              | _, _ => toAnnotation? t
            if t.needsAscription then
              match ann? with
              | some ann => target.setObjVal! "_ty" ann
              | none => target
            else target
        | none => target
  | some "Tuple" | some "List" =>
      match target.getObjValAs? (Array Json) "elts" with
      | .ok elts => target.setObjVal! "elts" (Json.arr (elts.map (stampTarget env · allowDict)))
      | _ => target
  | _ => target

/-- Does parameter `name` appear in a position that `PyAny` can serve but an un-inferred type
leaves Lean's instance search stuck on? Containers — `x[i]`, `x[i]=v`, `for _ in x`, `len(x)` — and
truthy contexts — `x and y`, `not x`, `if x`, `while x` (all `PyTruthy`). Boxing such a param as
`PyAny` (which delegates to the runtime tag) turns a compile error into a total, running program.
Does not descend into nested defs (separate scope). -/
partial def usedInPyAnyPosition (name : String) (json : Json) : Bool :=
  if nodeTypeOf json == some "FunctionDef" then false
  else
    let isName (field : String) : Bool := (getField json field).bind nameId? == some name
    let hitHere : Bool := match nodeTypeOf json with
      | some "Subscript" => isName "value"
      | some "For" => isName "iter"
      | some "If" | some "While" => isName "test"
      | some "UnaryOp" => (json.getObjValAs? String "op").toOption == some "not" && isName "operand"
      | some "BoolOp" =>
          ((json.getObjValAs? (Array Json) "values").toOption.getD #[]).any (fun v => nameId? v == some name)
      | some "Call" =>
          (getField json "func").bind nameId? == some "len" &&
            ((json.getObjValAs? (Array Json) "args").toOption.getD #[]).any (fun a => nameId? a == some name)
      -- `x is None` / `x is not None` on an otherwise-unknown `x`: box it so `pyIsNone x` resolves
      -- (`PyIsNone PyAny`) instead of leaving `x` an untyped binder that forces `Option _`.
      | some "Compare" =>
          let op := (json.getObjValAs? String "op").toOption
          let isNoneJson : Option Json → Bool := fun
            | some j => nodeTypeOf j == some "Constant" && (j.getObjVal? "value").toOption == some Json.null
            | none => false
          (op == some "is" || op == some "isnot") &&
            ((isName "left" && isNoneJson (getField json "right")) ||
             (isName "right" && isNoneJson (getField json "left")))
      | _ => false
    hitHere || (match json with
      | .arr xs => xs.any (usedInPyAnyPosition name)
      | .obj fs => fs.toList.any (fun (_, v) => usedInPyAnyPosition name v)
      | _ => false)

/-- Add `_ty` to each unannotated parameter we could type (a nested capture, or a rare
un-hinted param). An explicit annotation, or an existing `_ty`, always wins. -/
private def stampParams (env : Env) (fn : Json) : Json :=
  let body := (fn.getObjValAs? (Array Json) "body").toOption.getD #[]
  let pyAnyTy := Json.mkObj [("node_type", .str "Name"), ("id", .str "PyAny")]
  match fn.getObjVal? "args" with
  | .ok args =>
      match args.getObjValAs? (Array Json) "args" with
      | .ok argsArr =>
          let argsArr := argsArr.map fun arg =>
            match arg.getObjValAs? String "arg" with
            | .ok name =>
                let annotated := match getField arg "annotation" with
                  | some a => !a.isNull
                  | none => false
                if annotated || (getField arg "_ty").isSome then arg
                else
                  -- A residual-unknown param is boxed as `PyAny` only when it is used in a
                  -- container-dispatch position (else it would compile-error); otherwise it is left
                  -- bare for Lean's own body unification, which keeps it provable.
                  let boxIfStuck := fun () =>
                    if body.any (usedInPyAnyPosition name) then arg.setObjVal! "_ty" pyAnyTy else arg
                  match env.get? name with
                  -- A parameter used at genuinely different types (`.any`, e.g. `add(a,b)` called
                  -- with ints and strings) is always boxed so one definition dispatches on the tag.
                  | some (.any) => arg.setObjVal! "_ty" pyAnyTy
                  | some t =>
                      if t.isKnown then
                        match toAnnotation? t with
                        | some ann => arg.setObjVal! "_ty" ann
                        | none => arg
                      else boxIfStuck ()
                  | none => boxIfStuck ()
            | _ => arg
          fn.setObjVal! "args" (args.setObjVal! "args" (Json.arr argsArr))
      | _ => fn
  | _ => fn

/-- Mark every `t[k]` where `t` is a tuple-typed name (`tuple[a, b, …]`) with its arity
(`_PastaLean_tuple_arity`), so the subscript codegen static-projects the exact slot instead of
`pyGetItem` (which has no instance for a heterogeneous product). Does not descend into a nested `def`
(separate scope, its own env). -/
partial def markTuples (env : Env) (json : Json) : Json :=
  if nodeTypeOf json == some "FunctionDef" then json
  else
    let json :=
      if nodeTypeOf json == some "Subscript" then
        match getField json "value" with
        | some v =>
            match (nameId? v).bind (env.get? ·) with
            | some (.tuple es) =>
                json.setObjVal! "value"
                  (v.setObjVal! "_PastaLean_tuple_arity" (Json.num (JsonNumber.mk (Int.ofNat es.length) 0)))
            | _ => json
        | none => json
      else json
    match json with
    | .arr xs => Json.arr (xs.map (markTuples env))
    | .obj fs => Json.mkObj (fs.toList.map (fun (k, v) => (k, markTuples env v)))
    | _ => json

/-- Mark every `x.attr` whose receiver `x` is `Option`-typed with
`_unwrap_opt`, so the field codegen emits `(x.getD default).attr` instead of the invalid
`Option.attr` projection. Covers the tree/linked-list traversal case (`root.val`, `root.left`).
Also stamps `_ref_class = C` on an `x.attr` whose OWN type is a class `C` (a field holding a heap
reference, e.g. `head.next : Optional[Node]`), so `--heap` codegen registers a local bound to it
(`nxt = head.next`) as a heap object and dereferences through it. Skips nested defs (own scope). -/
partial def markOptAttrs (sigs : Sigs) (env : Env) (json : Json) : Json :=
  if nodeTypeOf json == some "FunctionDef" then json
  else
    let json :=
      if nodeTypeOf json == some "Attribute" then
        let json := match (getField json "value").map (typeOfExpr sigs env) with
          | some (.opt _) => json.setObjVal! "_unwrap_opt" (Json.bool true)
          | _ => json
        match (typeOfExpr sigs env json).classNameOf? with
        | some c => json.setObjVal! "_ref_class" (Json.str c)
        | none => json
      else json
    match json with
    | .arr xs => Json.arr (xs.map (markOptAttrs sigs env))
    | .obj fs => Json.mkObj (fs.toList.map (fun (k, v) => (k, markOptAttrs sigs env v)))
    | _ => json

/-- Every positional argument list of a call `name(...)` anywhere in `json`. -/
partial def collectCallArgLists (name : String) (json : Json) : Array (Array Json) :=
  let here := if nodeTypeOf json == some "Call" && (getField json "func").bind nameId? == some name
    then #[(json.getObjValAs? (Array Json) "args").toOption.getD #[]] else #[]
  let rest := match json with
    | .arr xs => xs.foldl (fun acc e => acc ++ collectCallArgLists name e) #[]
    | .obj fs => fs.toList.foldl (fun acc (_, v) => acc ++ collectCallArgLists name v) #[]
    | _ => #[]
  here ++ rest

/-- Param-type hints for a nested def `fn` from the arg types at every call to it in `roots`. Two
passes so a recursive arg (`dfs(node.left)`) is re-typed once its param is seeded from the first,
non-recursive call (`dfs(root)`) — the join is what makes a tree `dfs` param `Optional[TreeNode]`. -/
def nestedParamHints (sigs : Sigs) (env : Env) (fn : Json) (roots : Array Json) : Env := Id.run do
  let name := (fn.getObjValAs? String "name").toOption.getD ""
  let params := paramNames fn
  if name == "" || params.isEmpty then return {}
  let callLists := roots.foldl (fun acc r => acc ++ collectCallArgLists name r) #[]
  if callLists.isEmpty then return {}
  let mut hints : Env := {}
  for _ in [0:2] do
    let env2 := hints.fold (fun m k v => m.insert k v) env
    for args in callLists do
      for i in [0:min params.size args.size] do
        let t := typeOfExpr sigs env2 args[i]!
        if t != .unknown then
          hints := hints.insert params[i]! (((hints.get? params[i]!).getD .unknown).join t)
  return hints

/-- Stamp an int-literal `Constant` with `_ty = float` (so codegen emits `(0 : ℚ)`). -/
private def stampIfIntConst (e : Json) : Json :=
  if nodeTypeOf e == some "Constant" && (getField e "_ty").isNone
     && e.getObjValAs? String "python_literal_kind" != .ok "float"
     && (match (e.getObjVal? "value").toOption with | some (.num ⟨_, 0⟩) => true | _ => false) then
    match toAnnotation? .float with | some ann => e.setObjVal! "_ty" ann | none => e
  else e

/-- A container whose innermost element is `float` (`list[float]`, `list[list[list[float]]]`, …). -/
private partial def deepFloatContainer : PyType → Bool
  | .list .float | .set .float => true
  | .list e | .set e => deepFloatContainer e
  | _ => false

/-- A list/set literal or a `[x] * n` repeat — a value whose element type an ascription can fix. -/
private def isListLitOrRepeat (v : Json) : Bool :=
  match nodeTypeOf v with
  | some "List" | some "Set" => true
  | some "BinOp" => (v.getObjValAs? String "op").toOption == some "mul"
      && ((getField v "left").any (fun l => nodeTypeOf l == some "List")
          || (getField v "right").any (fun r => nodeTypeOf r == some "List"))
  | _ => false

/-- For a float-typed container assigned `value`, coerce its int-literal ELEMENTS to float. Descends
list/set literals, the `[x] * n` repeat, and comprehensions — so a nested `[[[0]*n for _] for _]`
DP grid (`list[list[list[float]]]`) coerces its innermost `0` to `(0 : ℚ)`. -/
private partial def stampFloatListElems (value : Json) : Json :=
  match nodeTypeOf value with
  | some "Constant" => stampIfIntConst value
  | some "List" | some "Set" =>
      match value.getObjValAs? (Array Json) "elts" with
      | .ok elts => value.setObjVal! "elts" (Json.arr (elts.map stampFloatListElems))
      | _ => value
  | some "BinOp" =>
      -- `[x] * n` (or `n * [x]`): descend ONLY into the list operand, never the count `n` (whose
      -- constants — e.g. the `1` in `n + 1` — must stay `Int`).
      let descendIfList (side : String) (v : Json) : Json :=
        (getField v side).elim v fun o =>
          if nodeTypeOf o == some "List" then v.setObjVal! side (stampFloatListElems o) else v
      descendIfList "right" (descendIfList "left" value)
  | some "ListComp" | some "SetComp" | some "GeneratorExp" =>
      (getField value "elt").elim value (fun e => value.setObjVal! "elt" (stampFloatListElems e))
  | some "DictComp" =>
      (getField value "value").elim value (fun e => value.setObjVal! "value" (stampFloatListElems e))
  | _ => value

mutual

/-- Infer types for `fn` (seeded by `outer` captures and `hints` for unannotated params, resolving
calls with `sigs`), stamp its params and every binder in its body, and recurse into nested defs.
A function whose returns disagree (`.any`) and that has no return annotation is marked `_box_return`
so codegen boxes its result as `PyAny`. -/
partial def stampFunction (sigs : Sigs) (outer hints : Env) (fn : Json) : Json :=
  let env1 := inferFunction sigs outer hints fn
  -- Second pass: a param that pass 1 leaves `unknown` but that is used in a `PyAny`-dispatch position
  -- WILL be boxed to `PyAny` by codegen. Seed those as `.any` and re-infer, so `PyAny` propagates
  -- through the body (`for x in nums: total += x*2` → `total : PyAny`) and matches what codegen emits;
  -- otherwise `total` stays `Int` and the `total := <PyAny>` reassignment fails to type-check.
  let body := (fn.getObjValAs? (Array Json) "body").toOption.getD #[]
  let pyAnySeed : Env := (paramNames fn).foldl (fun m name =>
    if (env1.get? name).getD .unknown == .unknown && body.any (usedInPyAnyPosition name)
    then m.insert name .any else m) hints
  let env := if pyAnySeed.size == hints.size then env1 else inferFunction sigs outer pyAnySeed fn
  let fn := stampParams env fn
  let fn := match fn.getObjValAs? String "name" with
    | .ok name =>
        -- The return type from its annotation if it has one (a union like `int | str` reads as
        -- `.any`), else the inferred one. `.any` means the returns genuinely disagree → box; a fully
        -- known type is stamped as `_ret_ty` so codegen can ascribe it (a recursive or effectful def
        -- needs its return type in the signature — this is what annotate_python's `-> T` provided).
        let annotated := match getField fn "returns" with | some r => !r.isNull | none => false
        let retType := if annotated then ofAnnotation ((getField fn "returns").getD Json.null)
                       else (sigs.get? name).getD .unknown
        -- Flag a body that mixes `int` and `float` return statements (types read under the
        -- *global-seeded* `env` — `sigs`/`returnTypeOf` run globals-free and miss a global `inf`).
        -- ONLY a mix needs it: the first `return <int>` would pin the `Id.run` codomain to `ℤ`, then a
        -- later `return <float>` fails; codegen ascribes the codomain to `ℚ`/`Float` (gated on
        -- `!_real_fn`) so both coerce. A pure-`float` body needs no ascription (Lean infers it).
        -- `sawOther` covers `int`/`bool` and `unknown` (a `return t` whose `t` TypeInfer left unknown
        -- but Lean will infer `ℤ`) — anything that could pin the codomain to `ℤ` ahead of the float.
        let (sawOther, sawFloat) : Bool × Bool := Id.run do
          let mut so := false; let mut sf := false
          for st in flatStmts ((fn.getObjValAs? (Array Json) "body").toOption.getD #[]).toList do
            if nodeTypeOf st == some "Return" then
              match (getField st "value").bind (fun v => if v.isNull then none else some (typeOfExpr sigs env v)) with
              | some .float => sf := true
              | some .int | some .bool | some .unknown => so := true
              | _ => pure ()
          return (so, sf)
        let fn := if sawOther && sawFloat then fn.setObjVal! "_ret_float" (Json.bool true) else fn
        if retType == (.any : PyType) then fn.setObjVal! "_box_return" (Json.bool true)
        else if !annotated && retType.isKnown then
          match toAnnotation? retType with
          | some ann => fn.setObjVal! "_ret_ty" ann
          | none => fn
        else fn
    | _ => fn
  match fn.getObjValAs? (Array Json) "body" with
  | .ok body => fn.setObjVal! "body"
      (Json.arr (((body.map (stampStmt sigs env body)).map (markTuples env)).map (markOptAttrs sigs env)))
  | _ => fn

/-- Stamp a (possibly nested) tuple-unpack target with the list-vs-`Prod` access mode at EVERY level,
driven by the type `ty` of the value it unpacks. `for k, (l, r) in enumerate(queries)` unpacks a
`(int, list[int])`: the outer level is a `Prod` but the inner `(l, r)` unpacks a `list[int]`, so it
must be indexed, not projected. A flat marker on the outer target alone misses the inner level. -/
partial def stampUnpackShape (target : Json) (ty : PyType) : Json :=
  if nodeTypeOf target == some "Tuple" then
    match target.getObjValAs? (Array Json) "elts" with
    | .ok elts => Id.run do
        let childTy : Nat → PyType := fun i => match ty with
          | .list e => e
          | .tuple ts => ts.getD i .unknown
          | _ => .unknown
        let mut newElts := #[]
        for i in [0:elts.size] do
          newElts := newElts.push (stampUnpackShape elts[i]! (childTy i))
        let t := target.setObjVal! "elts" (Json.arr newElts)
        match ty with
        | .list _ => return t.setObjVal! "_list_unpack" (Json.bool true)
        | .tuple _ =>
            -- Under `--heap` each container element unpacks to its object-ref (`Ref (List …)`); record a
            -- per-element mask so codegen registers those targets as container-refs (later len/[]/iter deref).
            let anyContainer := (Array.range elts.size).any (fun i => (childTy i).isContainer)
            let t := if anyContainer then
                t.setObjVal! "_unpack_container_mask"
                  (Json.arr ((Array.range elts.size).map (fun i => Json.bool (childTy i).isContainer)))
              else t
            return t.setObjVal! "_tuple_unpack" (Json.bool true)
        | _ => return t
    | _ => target
  else target

/-- Stamp `<typesKey>`: for each name a block leaks out (listed under `namesKey`, e.g.
`if_assigned_names`) that we can type, its annotation — so codegen ascribes the hoisted
`let mut x : T := default`. A genuinely dynamic var (`.any`) yields `PyAny`; an `unknown` one is
omitted (`toAnnotation?` → none), leaving codegen's untyped `let mut x := default` for Lean to infer. -/
private partial def stampHoistTypes (env : Env) (namesKey typesKey : String) (s : Json) : Json :=
  match s.getObjValAs? (Array String) namesKey with
  | .ok names =>
      -- Only ascribe where it is safe (`needsAscription`): a `.float` binder must stay unascribed, or
      -- a `ℚ` ascription fights a real-context `ℝ` branch value; `.any` DOES need it (→ `PyAny`).
      let entries := names.toList.filterMap (fun nm =>
        match env.get? nm with
        | some t => if t.needsAscription then (toAnnotation? t).map (fun ann => (nm, ann)) else none
        | none => none)
      if entries.isEmpty then s else s.setObjVal! typesKey (Json.mkObj entries)
  | _ => s

/-- Stamp one statement: its target, its nested blocks, and any nested def. -/
partial def stampStmt (sigs : Sigs) (env : Env) (roots : Array Json) (s : Json) : Json :=
  if nodeTypeOf s == some "FunctionDef" then
    let ownBody := (s.getObjValAs? (Array Json) "body").toOption.getD #[]
    stampFunction sigs env (nestedParamHints sigs env s (roots ++ ownBody)) s
  else Id.run do
    let mut s := s
    match nodeTypeOf s with
    | some "Assign" | some "AnnAssign" | some "AugAssign" | some "For" =>
        if let some t := getField s "target" then
          let allowDict := match getField s "value" with
            | some v =>
                nodeTypeOf v != some "Call"
                || ((getField v "func").bind (·.getObjValAs? String "library_module" |>.toOption)).isNone
            | none => true
          s := s.setObjVal! "target" (stampTarget env t allowDict)
    | _ => pure ()
    -- `c[i] = v` into a float-element container: stamp the *value* so codegen ascribes it to the
    -- element type. An un-ascribed `Int` value otherwise pins `PySetItem`'s value `outParam` to `ℤ`,
    -- which never resolves against a `List ℚ` / `Float` container (`dp = [float('inf')]*n; dp[0]=0`).
    if nodeTypeOf s == some "Assign" then
      match getField s "target", getField s "value" with
      | some target, some value =>
          -- `typeOfExpr` on the lvalue descends any subscript depth (`dp[i]`, `f[i][j]`) and dicts,
          -- so this covers 1-D and N-D float containers alike.
          if nodeTypeOf target == some "Subscript" && (getField value "_ty").isNone
             && typeOfExpr sigs env target == .float then
            if let some ann := toAnnotation? .float then
              s := s.setObjVal! "value" (value.setObjVal! "_ty" ann)
          -- `x = <int literal>` where `x` is a float-typed scalar (`ans = 0; ans = max(ans, inf)`):
          -- stamp the literal so codegen coerces `(0 : ℚ)` and Lean infers `x : ℚ`, WITHOUT ascribing
          -- the binder — that would force `ℚ` over a transcendental `ℝ` in a pure-float var.
          else if (nameId? target).any (fun n => (env.get? n).getD .unknown == .float)
             && nodeTypeOf value == some "Constant" && (getField value "_ty").isNone
             && typeOfExpr sigs env value == .int then
            if let some ann := toAnnotation? .float then
              s := s.setObjVal! "value" (value.setObjVal! "_ty" ann)
          -- `f = [0]*n` / `f = [inf]*n` where `f` is a float-typed container that later holds floats:
          -- coerce int-literal elements to float, and ascribe a list-literal/`[x]*n` value to the
          -- float container so a polymorphic element (`inf`) adapts to the mode float — otherwise
          -- `[inf]*n` binds `List ℚ` and a run-twin `dp[0] = 0` (`(0 : Float)`) clashes.
          else if (nameId? target).bind (env.get? ·) |>.any deepFloatContainer then
            let ct := ((nameId? target).bind (env.get? ·)).getD .unknown
            let value := stampFloatListElems value
            let value := if isListLitOrRepeat value && (getField value "_ty").isNone then
                (toAnnotation? ct).elim value (value.setObjVal! "_ty" ·)
              else value
            s := s.setObjVal! "value" value
      | _, _ => pure ()
    -- A tuple target unpacked from a *list* value (not a tuple) uses list indexing, not `Prod`:
    -- `for a, b in edges` with `edges : list[list[int]]`, or `a, b = np.shape(x)` (returns a list).
    -- Mark the target so codegen can tell.
    -- `for a, b in edges` (`edges : list[list[int]]`) indexes; `for k, (l, r) in enumerate(queries)`
    -- is a `Prod` outer with a list inner — stampUnpackShape marks each level from the element type.
    if nodeTypeOf s == some "For" then
      match getField s "target", getField s "iter" with
      | some target, some iter =>
          if nodeTypeOf target == some "Tuple" then
            s := s.setObjVal! "target" (stampUnpackShape target (typeOfExpr sigs env iter).elemType)
      | _, _ => pure ()
    -- `a, b = t[k]` (`t : list[(int,int)]`) reads a `Prod`; `a, b = np.shape(x)` reads a list.
    if nodeTypeOf s == some "Assign" then
      match getField s "target", getField s "value" with
      | some target, some value =>
          if nodeTypeOf target == some "Tuple" then
            s := s.setObjVal! "target" (stampUnpackShape target (typeOfExpr sigs env value))
      | _, _ => pure ()
    -- A name a branch/try leaks out (Python has no block scope; Lean does) is hoisted by codegen to
    -- `let mut x : T := default` before the block. Stamp its type T so the hoist is ascribed — PyAny
    -- for a genuinely dynamic var, so `default` resolves (to `emptyPyAny`); unknown types are omitted.
    s := stampHoistTypes env "if_assigned_names" "if_assigned_types" s
    s := stampHoistTypes env "try_assigned_names" "try_assigned_types" s
    s := stampHoistTypes env "for_assigned_names" "for_assigned_types" s
    s := stampHoistTypes env "while_assigned_names" "while_assigned_types" s
    for f in #["body", "orelse", "finalbody"] do
      if let .ok elems := s.getObjValAs? (Array Json) f then
        s := s.setObjVal! f (Json.arr (elems.map (stampStmt sigs env roots)))
    if let .ok handlers := s.getObjValAs? (Array Json) "handlers" then
      let handlers := handlers.map fun h =>
        match h.getObjValAs? (Array Json) "body" with
        | .ok elems => h.setObjVal! "body" (Json.arr (elems.map (stampStmt sigs env roots)))
        | _ => h
      s := s.setObjVal! "handlers" (Json.arr handlers)
    return s

end

/-! ### Interprocedural: return types flow to call sites, argument types flow to parameters -/

/-- Inferred type of each parameter of each user function, by position. -/
abbrev ParamSigs := Std.HashMap String (Array PyType)

/-- Every top-level `FunctionDef` in a module or mutual group, in order. -/
private def topFunctions (module : Json) : Array Json :=
  ((module.getObjValAs? (Array Json) "body").toOption.getD #[]).filter
    (nodeTypeOf · == some "FunctionDef")

/-- Module top-level statements that are not function defs (e.g. `print(add(3, 4))` at module scope):
their call sites refine callee params too, so `add` boxes whether it is called from a def or not. -/
private def topLevelStmts (module : Json) : Array Json :=
  ((module.getObjValAs? (Array Json) "body").toOption.getD #[]).filter
    (nodeTypeOf · != some "FunctionDef")

/-- The hint environment for `fn`'s parameters from `params` (its inferred per-position types). -/
private def hintsFor (params : ParamSigs) (fn : Json) : Env := Id.run do
  let names := paramNames fn
  let types := (params.get? ((fn.getObjValAs? String "name").toOption.getD "")).getD #[]
  let mut env : Env := {}
  for i in [0:names.size] do
    if let some t := types[i]? then if t != .unknown then env := env.insert names[i]! t
  return env

/-- Collect `(calleeName, argumentTypes)` for every direct call `foo(a, b, …)` in `json`, typing the
arguments under `env`. Nested calls are included; method calls are ignored (no positional callee). -/
private partial def collectCalls (sigs : Sigs) (env : Env) (json : Json) : Array (String × Array PyType) :=
  let here : Array (String × Array PyType) :=
    if nodeTypeOf json == some "Call" then
      match getField json "func" with
      | some func =>
          match (nodeTypeOf func, (func.getObjValAs? String "id").toOption) with
          | (some "Name", some name) =>
              let args := ((json.getObjValAs? (Array Json) "args").toOption.getD #[]).map (typeOfExpr sigs env)
              #[(name, args)]
          | _ => #[]
      | none => #[]
    else #[]
  let sub := match json with
    | .arr xs => xs.foldl (fun acc x => acc ++ collectCalls sigs env x) #[]
    | .obj fs => fs.toList.foldl (fun acc (_, v) => acc ++ collectCalls sigs env v) #[]
    | _ => #[]
  here ++ sub

/-- The `Name` decorators of a `FunctionDef`, e.g. `@double` → `"double"`. Attribute/Call decorators
(`@a.b`, `@lru_cache(...)`) are skipped — a user decorator whose type we can unify is a bare name. -/
private def decoratorNamesOf (fn : Json) : Array String :=
  ((fn.getObjValAs? (Array Json) "decorator_list").toOption.getD #[]).filterMap fun d =>
    if nodeTypeOf d == some "Name" then nameId? d else none

/-- Join `argTypes` into `params[name]` position-by-position (missing positions start `unknown`). -/
private def refineParams (params : ParamSigs) (name : String) (arity : Nat) (argTypes : Array PyType) : ParamSigs :=
  let cur := (params.get? name).getD (Array.replicate arity .unknown)
  let next := (Array.range cur.size).map fun i =>
    (cur[i]!).join (argTypes[i]?.getD .unknown)
  params.insert name next

/-- Field types of every class in the module, keyed `"Class.field"` so `typeOfExpr` can type a field
access. Mirrors the struct codegen: an explicit annotation wins; otherwise an `__init__` param
defaulting to `None` types the field `Option Class` (the recursive `TreeNode.left`/`ListNode.next`
pattern); otherwise the initialising param's annotation or the type of its default. -/
private def classFieldSigs (module : Json) : Sigs := Id.run do
  let mut out : Sigs := {}
  for st in topLevelStmts module do
    if nodeTypeOf st != some "ClassDef" then continue
    let .ok cls := st.getObjValAs? String "name" | continue
    let methods := (st.getObjValAs? (Array Json) "methods").toOption.getD #[]
    -- `__init__` params: their declared/default type, and which ones default to `None`.
    let mut ptype : Env := {}
    let mut noneParams : List String := []
    if let some init := methods.find? (·.getObjValAs? String "name" == .ok "__init__") then
      let argsJson := (getField init "args").getD Json.null
      let argsArr := (argsJson.getObjValAs? (Array Json) "args").toOption.getD #[]
      let defaults := (argsJson.getObjValAs? (Array Json) "defaults").toOption.getD #[]
      let offset := argsArr.size - defaults.size
      for i in [0:argsArr.size] do
        if let .ok nm := argsArr[i]!.getObjValAs? String "arg" then
          if let some ann := getField argsArr[i]! "annotation" then
            if !ann.isNull then ptype := ptype.insert nm (ofAnnotation ann)
          if i ≥ offset then
            let d := defaults[i - offset]!
            if nodeTypeOf d == some "Constant" && (getField d "value") == some Json.null then
              noneParams := nm :: noneParams
            else if !ptype.contains nm then ptype := ptype.insert nm (ofValue d)
    for f in (st.getObjValAs? (Array Json) "fields").toOption.getD #[] do
      if let .ok fname := f.getObjValAs? String "name" then
        let annT := match getField f "annotation" with
          | some ann => if ann.isNull then .unknown else ofAnnotation ann
          | none => .unknown
        let t := if annT != .unknown then annT else
          match getField f "init" with
          | some init =>
              -- `self.left = left` where `left` defaults to `None` → the recursive node pattern.
              match nameId? init with
              | some p =>
                  if noneParams.contains p then .opt (.cls cls) else (ptype.get? p).getD .unknown
              -- Otherwise type the initialiser itself, under the `__init__` params
              -- (`self.p = list(range(n))` → `list[int]`, which `ofValue` alone cannot see).
              | none => typeOfExpr {} ptype init
          | none => .unknown
        if t != .unknown then out := out.insert s!"{cls}.{fname}" t
  return out

/-- True when a type names a user class anywhere. Such a type must NOT be written back as an
annotation: the run twin renames `TreeNode` to `TreeNode'rn`, and only the struct codegen's own
class-name path applies that suffix — a literal annotation would pin the unsuffixed name. -/
private partial def mentionsClass : PyType → Bool
  | .cls _ => true
  | .list e | .set e | .opt e => mentionsClass e
  | .dict k v => mentionsClass k || mentionsClass v
  | .tuple es => es.any mentionsClass
  | .fn as r => as.any mentionsClass || mentionsClass r
  | _ => false

/-- Write each class field's inferred type into its (empty) `annotation` slot, which the struct
codegen already prefers over its own literal-shape guess — so a container field stops silently
defaulting to `Int`. -/
private def stampClassFields (fields : Sigs) (cls : String) (st : Json) : Json :=
  match st.getObjValAs? (Array Json) "fields" with
  | .ok fs => st.setObjVal! "fields" (Json.arr (fs.map fun f =>
      match f.getObjValAs? String "name" with
      | .ok fname =>
          let unannotated := match getField f "annotation" with
            | some ann => ann.isNull
            | none => true
          match unannotated, (fields.get? s!"{cls}.{fname}").filter (!mentionsClass ·) |>.bind toAnnotation? with
          | true, some ann => f.setObjVal! "annotation" ann
          | _, _ => f
      | _ => f))
  | _ => st

/-- Co-evolve every function's return type AND its parameter types to a fixpoint: a callee's return
flows to its callers, and a caller's argument types flow to the callee's parameters. Both only climb
the lattice, so this settles. -/
partial def collectSigs (module : Json) : Sigs × ParamSigs := Id.run do
  let fns := topFunctions module
  -- Seed each function's parameters with their annotations (unknown where unannotated).
  let mut params : ParamSigs := {}
  for fn in fns do
    if let .ok name := fn.getObjValAs? String "name" then
      let seed := paramSeed fn
      params := params.insert name ((paramNames fn).map fun p => (seed.get? p).getD .unknown)
  -- Class field types share the `sigs` table under `"Class.field"` keys (no Python function name
  -- contains a dot, so they cannot collide with a return type).
  let mut sigs : Sigs := classFieldSigs module
  for _ in [0:6] do
    let mut nextSigs := sigs
    let mut nextParams := params
    for fn in fns do
      if let .ok name := fn.getObjValAs? String "name" then
        let hints := hintsFor params fn
        nextSigs := nextSigs.insert name (returnTypeOf sigs hints fn)
        -- refine callees' params from this function's call sites, typed under its own env.
        let env := inferFunction sigs {} hints fn
        for (callee, argTypes) in collectCalls sigs env fn do
          if params.contains callee then
            nextParams := refineParams nextParams callee argTypes.size argTypes
    -- Module top-level call sites (outside any def), typed under an empty env (literal args).
    for stmt in topLevelStmts module do
      for (callee, argTypes) in collectCalls sigs {} stmt do
        if params.contains callee then
          nextParams := refineParams nextParams callee argTypes.size argTypes
    -- Decorator unification: `@d def g` is `g = d(g_raw)`, so g's type and d's wrapped-parameter
    -- type are the same. Flow each into the other: g's `.fn` type refines d's parameter 0 (so a
    -- decorator's `f` is learned from the function it wraps), and d's parameter 0 — if a function
    -- type — refines g's parameters (so an int-typed decorator pins an otherwise-unknown g's params).
    for fn in fns do
      if let .ok gname := fn.getObjValAs? String "name" then
        for d in decoratorNamesOf fn do
          if nextParams.contains d then
            let gParams := (nextParams.get? gname).getD #[]
            let gRet := (nextSigs.get? gname).getD .unknown
            nextParams := refineParams nextParams d 1 #[PyType.fn gParams.toList gRet]
            match ((nextParams.get? d).getD #[])[0]? with
            | some (PyType.fn argTs _) =>
                nextParams := refineParams nextParams gname gParams.size argTs.toArray
            | _ => pure ()
    let stable := nextSigs.size == sigs.size
      && nextSigs.fold (fun ok k v => ok && (sigs.get? k |>.getD .unknown) == v) true
      && nextParams.fold (fun ok k v => ok && (params.get? k |>.getD #[]) == v) true
    sigs := nextSigs; params := nextParams
    if stable then break
  return (sigs, params)

/-- Stamp ONLY tuple-unpack shapes (`_tuple_unpack`/`_list_unpack`/`_unpack_container_mask`) across a
statement tree, driven by interprocedural `sigs`/`env`. Used for the `__main__` guard body: it runs at
module scope but — unlike a function body — must NOT get the full `stampStmt` treatment, whose
`stampTarget` value-type ascriptions would perturb byte-identical value-mode output (the guard was
historically unstamped). Single-value container returns are already handled by the driver's
`_returns_container` pass; only the per-element unpack mask (nothing else supplies it) is needed so
`xs, ys = make_pair()` registers each target as a container-ref under `--heap`. -/
partial def stampUnpackShapes (sigs : Sigs) (env : Env) (s : Json) : Json :=
  if nodeTypeOf s == some "FunctionDef" then s
  else Id.run do
    let mut s := s
    if nodeTypeOf s == some "For" then
      match getField s "target", getField s "iter" with
      | some target, some iter =>
          if nodeTypeOf target == some "Tuple" then
            s := s.setObjVal! "target" (stampUnpackShape target (typeOfExpr sigs env iter).elemType)
      | _, _ => pure ()
    if nodeTypeOf s == some "Assign" then
      match getField s "target", getField s "value" with
      | some target, some value =>
          if nodeTypeOf target == some "Tuple" then
            s := s.setObjVal! "target" (stampUnpackShape target (typeOfExpr sigs env value))
      | _, _ => pure ()
    for f in #["body", "orelse", "finalbody"] do
      if let .ok elems := s.getObjValAs? (Array Json) f then
        s := s.setObjVal! f (Json.arr (elems.map (stampUnpackShapes sigs env)))
    return s

/-- Stamp `_ty` across one top-level node, resolving calls with `sigs` and seeding each function's
unannotated params from `params`. The driver sends one statement per request; a `FunctionDef`, a
`ClassDef` (each method) or a `Module` (a mutual group) is stamped, anything else is unchanged. -/
partial def stampNodeWith (sigs : Sigs) (params : ParamSigs) (globals : Env) (s : Json) : Json :=
  -- Seed a function with module-level globals, minus any name its own parameters shadow (params win).
  let outerFor (fn : Json) : Env := (paramNames fn).foldl (·.erase ·) globals
  match nodeTypeOf s with
  | some "FunctionDef" => stampFunction sigs (outerFor s) (hintsFor params s) s
  | some "ClassDef" =>
      let s := match s.getObjValAs? String "name" with
        | .ok cls => stampClassFields sigs cls s
        | _ => s
      -- A class keeps its methods under "methods"; older nodes use "body".
      #["methods", "body"].foldl (fun s key =>
        match s.getObjValAs? (Array Json) key with
        | .ok ms => s.setObjVal! key (Json.arr (ms.map fun m =>
            if nodeTypeOf m == some "FunctionDef" then stampFunction sigs (outerFor m) (hintsFor params m) m else m))
        | _ => s) s
  | some "Module" =>
      match s.getObjValAs? (Array Json) "body" with
      | .ok body => s.setObjVal! "body" (Json.arr (body.map (stampNodeWith sigs params globals)))
      | _ => s
  | some "If" =>
      -- The `__main__` guard lowers to Lean's `def main`; its body runs at module scope but is only
      -- reached by the intraprocedural per-request fallback (empty `sigs`), which resolves every call
      -- to `.unknown` and so misses the tuple-unpack container mask for `xs, ys = make_pair()`. Stamp
      -- just the unpack shapes here with the full interprocedural `sigs` — NOT the full `stampStmt`,
      -- whose value-type ascriptions would perturb byte-identical value-mode output. `markOptAttrs` IS
      -- run: it only stamps `_unwrap_opt` (an Option-receiver deref like `node.val` is invalid Lean
      -- unless unwrapped, in either mode) and `_ref_class` (inert in value mode), so a `__main__`
      -- linked-list/tree traversal derefs correctly too.
      if (s.getObjValAs? Bool "is_main_guard").toOption == some true then
        let genv := inferFunction sigs globals {} s
        let stampBlock (key : String) (s : Json) : Json :=
          match s.getObjValAs? (Array Json) key with
          | .ok body => s.setObjVal! key
              (Json.arr (body.map (fun st => markOptAttrs sigs genv (stampUnpackShapes sigs genv st))))
          | _ => s
        stampBlock "orelse" (stampBlock "body" s)
      else s
  | _ => s

/-- Intraprocedural stamping of a single node (no cross-function info). Used per-request as a
fallback; `inferModule` supersedes it when the whole module is available. -/
partial def stampNode (s : Json) : Json := stampNodeWith {} {} {} s

/-- Whole-module inference: co-evolve return and parameter types to a fixpoint, then stamp each
top-level node with that knowledge. This is what the `inferTypes` backend task runs. -/
def inferModule (module : Json) : Json :=
  let (sigs, params) := collectSigs module
  -- Module-level globals (`inf = float('inf')`, config constants) seed every function so a body that
  -- reads a global sees its type — e.g. `f = [[inf]*k for _ in range(n)]` becomes `list[list[float]]`.
  let globals : Env := (topLevelStmts module).foldl (applyStmt sigs) {}
  -- Mark each statement `_inferred` so the per-request fallback pass (which lacks module context and
  -- would re-derive worse types, e.g. a global-fed `float` local mis-stamped `int`) skips it.
  let mark (s : Json) : Json := (stampNodeWith sigs params globals s).setObjVal! "_inferred" (Json.bool true)
  match module.getObjValAs? (Array Json) "body" with
  | .ok body => module.setObjVal! "body" (Json.arr (body.map mark))
  | _ => mark module

end TypeInfer
