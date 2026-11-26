import TypeInfer.Rules

namespace TypeInfer

open Lean

def nodeTypeOf (j : Json) : Option String := (j.getObjValAs? String "node_type").toOption
def getField (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
def nameId? (j : Json) : Option String :=
  if nodeTypeOf j == some "Name" then (j.getObjValAs? String "id").toOption else none

/-- For a (possibly nested) subscript target `f[h][i][j]`, the base name `f` and the nesting depth
(here `3`), so codegen can learn `f : list[list[list[<v>]]]` from a deep `f[h][i][j] = v`. -/
partial def subscriptBaseDepth (target : Json) : Option (String × Nat) :=
  if nodeTypeOf target == some "Subscript" then
    match getField target "value" with
    | some v => match nameId? v with
        | some n => some (n, 1)
        | none => (subscriptBaseDepth v).map (fun (b, d) => (b, d + 1))
    | none => none
  else none

/-- For a nested subscript `base[k0][i]…`, the FIRST index `k0` (the slice of the innermost subscript
whose value is the base `Name`). When `base` is a dict, this is the dict KEY — `cnt[c][i] += 1` reads
`cnt`'s value (a list) at key `c`, not a nested list grid. -/
partial def innermostSubscriptKey? (target : Json) : Option Json :=
  if nodeTypeOf target == some "Subscript" then
    match getField target "value" with
    | some v => match nameId? v with
        | some _ => getField target "slice"
        | none => innermostSubscriptKey? v
    | none => none
  else none

/-- The statement lists nested directly in `s` (`if`/`for`/`while`/`with`/`try` blocks), not
descending into a nested `def`/`class` (those have their own scope). -/
def childBlocks (s : Json) : List (List Json) := Id.run do
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
      let args := ((value.getObjValAs? (Array Json) "args").toOption.getD #[]).toList
      -- A method's RECEIVER is effective argument 0, so `xs.append(v)` and `heappush(h, v)` share one
      -- path — the member's `Behaviour.teaches?` says which effective arg is the container and which
      -- is the element, and how (list / set / spliced-elements). The engine hardcodes no member name.
      let behArgs? : Option (Libraries.Behaviour × List Json) := match nodeTypeOf func with
        | some "Name" =>
            (Libraries.bareTypeBehaviour? ((func.getObjValAs? String "id").toOption.getD "")).map (·, args)
        | some "Attribute" => match getField func "value" with
            | some recv =>
                -- A user class instance's method (`node.insert(...)`) must NOT be read as a same-named
                -- container method (`list.insert`): that would re-teach the receiver as a list and
                -- corrupt its `.cls C` type. Skip library behaviours when the receiver is a class. Only
                -- a bare-name receiver is checked (via `env`, cheap) — never a full `typeOfExpr` on an
                -- arbitrary receiver expression, which can recurse badly on nested calls/subscripts.
                let recvIsClass := match (nameId? recv).bind env.get? with
                  | some (.cls _) | some (.opt (.cls _)) => true
                  | _ => false
                if recvIsClass then none
                else (Libraries.methodBehaviour? ((func.getObjValAs? String "attr").toOption.getD "")).map (·, recv :: args)
            | none => none
        | _ => none
      match behArgs?.bind (fun (b, ea) => b.teaches?.map (·, ea)) with
      | some (teach, ea) =>
          let typeAt (i : Nat) : PyType := (ea[i]?).elim .unknown (typeOfExpr sigs env)
          let (cIdx, learned) : Nat × PyType := match teach with
            | .pushList c e => (c, .list (typeAt e))
            | .pushSet c e => (c, .set (typeAt e))
            | .extendList c e => (c, match typeAt e with | .list x => .list x | _ => .unknown)
          if learned == .unknown then env else
          let join1 (n : String) (t : PyType) : Env := env.insert n ((env.get? n |>.getD .unknown).join t)
          match ea[cIdx]? with
          | some target => match nameId? target with
              | some cname => join1 cname learned
              -- `graph[k].append(v)`: the mutated value is at `k`, so `graph` is a dict/list of it.
              | none => if nodeTypeOf target == some "Subscript" then
                  match (getField target "value").bind nameId? with
                  | some base =>
                      let kt := (getField target "slice").elim .unknown (typeOfExpr sigs env)
                      let outer := match env.get? base |>.getD .unknown with
                        | .list _ => .list learned | _ => .dict kt learned
                      join1 base outer
                  | none => env
                else env
          | none => env
      | none => env
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
      -- A starred target (`a, *b, c = …`) binds the star to a LIST of the middle elements and the
      -- fixed targets around it to the corresponding element types.
      match elts.findIdx? (nodeTypeOf · == some "Starred") with
      | some k =>
          let after := elts.size - k - 1
          let elemAt (i : Nat) : PyType := match t with
            | .tuple es => es[i]?.getD .unknown
            | _ => t.elemType
          Id.run do
            let mut e := env
            for i in [0:k] do e := bindTargetType e elts[i]! (elemAt i)
            -- The star collects the middle span as a list of the joined middle element type.
            let midCount := (match t with | .tuple es => es.length | _ => 0)
            let midTypes := (List.range (max 0 (midCount - k - after))).map (fun j => elemAt (k + j))
            if let some starTgt := (elts[k]!.getObjVal? "value").toOption then
              e := bindTargetType e starTgt (.list (PyType.joinAll midTypes))
            for j in [0:after] do
              e := bindTargetType e elts[k + 1 + j]! (elemAt (midCount - after + j))
            return e
      | none =>
      match t with
      | .tuple es => (Array.range elts.size).foldl (fun e i => bindTargetType e elts[i]! (es[i]?.getD .unknown)) env
      | _ => elts.foldl (fun e elt => bindTargetType e elt t.elemType) env
  | _ => env

/-- A `FunctionDef`'s type as a value: `fn[param annotations] → return annotation` (un-annotated
slots are `unknown`). Lets a nested def referenced by name (`return mul`, `key=mul`) be typed as a
function, so a higher-order caller's callback param is refined from the call site. -/
def functionSignatureType (fn : Json) : PyType :=
  let args := ((getField fn "args").bind (fun a => (a.getObjValAs? (Array Json) "args").toOption)).getD #[]
  let argTypes := args.toList.map fun a =>
    match getField a "annotation" with
    | some ann => if ann.isNull then PyType.unknown else ofAnnotation ann
    | none => PyType.unknown
  let ret := match getField fn "returns" with
    | some r => if r.isNull then PyType.unknown else ofAnnotation r
    | none => PyType.unknown
  PyType.fn argTypes ret

/-- The container an index store `c[k] = v` into a not-yet-typed `c` reveals: a `str` key cannot index a
list, so `dict[str, v]`; otherwise `list[v]`. -/
def indexedStore (sigs : Sigs) (env : Env) (target : Json) (vt : PyType) : PyType :=
  if (getField target "slice").elim PyType.unknown (typeOfExpr sigs env) == .str then .dict .str vt else .list vt

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
      | some name, some ann => env.insert name (ofAnnotation ann (anyDynamic := true))   -- an explicit annotation wins
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
                      | _ => if isSlice then vt else indexedStore sigs env target vt
                    learn env cname learned
                -- Nested `f[h][i][j] = v` teaches `f : list[list[list[<v>]]]` (grid/tensor DP).
                | none => match subscriptBaseDepth target with
                    | some (base, depth) =>
                        let vt := typeOfExpr sigs env value
                        match env.get? base |>.getD .unknown with
                        -- The base is already a dict (`g = defaultdict(list)`): `g[k][i] = v` indexes the
                        -- dict's VALUE (a list) at key `k`, NOT a nested list grid — learn the key from the
                        -- innermost index and the value as `list^(depth-1) vt`, so the dict isn't clobbered
                        -- into `list[list]` (which would `join` to `.any`).
                        | .dict k v =>
                            let kt := (innermostSubscriptKey? target).elim .unknown (typeOfExpr sigs env)
                            let valTy := (List.range (depth - 1)).foldl (fun t _ => PyType.list t) vt
                            -- Only widen a list-shaped (or still-unknown) value; a dict-valued dict
                            -- (`defaultdict(dict)`) keeps its value — the nested index is a further key.
                            let newV := match v with | .unknown | .list _ => v.join valTy | _ => v
                            learn env base (.dict (k.join kt) newV)
                        | _ => learn env base ((List.range depth).foldl (fun t _ => PyType.list t) vt)
                    | none => env
              else env
      | _, _ => env
  | some "AugAssign" =>
      match getField s "target", getField s "value" with
      | some target, some value =>
          -- Python's `/=` is TRUE division, so `x /= n` widens `x` to `float` even for integer
          -- operands (`pre = 1; pre /= 10`); every other augmented op keeps the numeric `arith` result.
          let augCombine (a b : PyType) : PyType :=
            if (s.getObjValAs? String "op").toOption == some "div" then
              (match a, b with | .any, _ | _, .any => .any | _, _ => .float)
            -- `s |= t` / `&=` / `-=` / `^=` are SET operations, not arithmetic: the result is a set whose
            -- element type joins both sides (`s = set(); s |= set(range(n))` makes `s : set[int]`).
            else match a, b with
              | .set ea, .set eb => .set (ea.join eb)
              | .unknown, .set eb => .set eb
              | .set ea, _ => .set ea
              -- `xs += ys` / `xs += [v]` is list concatenation: widen the element type by joining both
              -- sides (`nums : list[int]; nums += [float('inf')]` makes `nums : list[float]`).
              | .list ea, .list eb => .list (ea.join eb)
              | _, _ => arith a b
          match nameId? target with
          | some name => learn env name (augCombine (env.get? name |>.getD .unknown) (typeOfExpr sigs env value))
          -- `counts[k] += 1` teaches both sides of `counts` (a `Counter()` starts fully unknown).
          | none =>
              if nodeTypeOf target == some "Subscript" then
                match (getField target "value").bind nameId? with
                | some cname =>
                    let vt := typeOfExpr sigs env value
                    let isSlice := (getField target "slice").any (nodeTypeOf · == some "Slice")
                    let learned := match env.get? cname |>.getD .unknown with
                      | .dict _ v => .dict ((getField target "slice").elim .unknown (typeOfExpr sigs env))
                          (if v == .unknown then vt else augCombine v vt)
                      | _ => if isSlice then vt else indexedStore sigs env target vt
                    learn env cname learned
                -- Nested `f[h][i][j] += v` widens the deep element (`join` at that depth).
                | none => match subscriptBaseDepth target with
                    | some (base, depth) =>
                        let vt := typeOfExpr sigs env value
                        match env.get? base |>.getD .unknown with
                        -- Dict-of-containers `cnt[c][i] += 1`: learn the key from the innermost index and
                        -- the value as `list^(depth-1) vt` — never clobber the dict into a nested list.
                        | .dict k v =>
                            let kt := (innermostSubscriptKey? target).elim .unknown (typeOfExpr sigs env)
                            let valTy := (List.range (depth - 1)).foldl (fun t _ => PyType.list t) vt
                            -- Only widen a list-shaped (or still-unknown) value; a dict-valued dict
                            -- (`defaultdict(dict)`) keeps its value — the nested index is a further key.
                            let newV := match v with | .unknown | .list _ => v.join valTy | _ => v
                            learn env base (.dict (k.join kt) newV)
                        | _ => learn env base ((List.range depth).foldl (fun t _ => PyType.list t) vt)
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
partial def bindCompTargetFresh (outer : Env) (env : Env) (target : Json) (t : PyType) : Env :=
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


end TypeInfer
