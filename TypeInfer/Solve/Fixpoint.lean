import TypeInfer.Solve.Usage

namespace TypeInfer

open Lean


/-- Every `FunctionDef` reachable in `json` (the function itself + nested helpers) → its parameters'
ANNOTATED types (unannotated ⇒ `.unknown`). Lets `usageType` type an argument from the callee's
annotation: `digits(x: int)` ⇒ a value passed to `digits` is `int`. -/
partial def collectFnParams (json : Json) : Std.HashMap String (Array PyType) := Id.run do
  let mut m : Std.HashMap String (Array PyType) := {}
  let here : Option (String × Array PyType) := do
    guard (nodeTypeOf json == some "FunctionDef")
    let nm ← (json.getObjValAs? String "name").toOption
    let args ← ((json.getObjVal? "args").toOption).bind (fun a => (a.getObjValAs? (Array Json) "args").toOption)
    let ptys := args.map fun a => match getField a "annotation" with
      | some ann => if ann.isNull then PyType.unknown else ofAnnotation ann
      | none => PyType.unknown
    some (nm, ptys)
  if let some (nm, ptys) := here then m := m.insert nm ptys
  match json with
  | .arr xs => for x in xs do m := (collectFnParams x).fold (fun a k v => a.insert k v) m
  | .obj fs => for (_, v) in fs do m := (collectFnParams v).fold (fun a k v => a.insert k v) m
  | _ => pure ()
  return m

/-- A function's parameter types for the callee-annotation rule: each annotated param's declared type,
each UNANNOTATED param's shallow usage-inferred type (`is_prime(a)` with `a < 2` ⇒ `[int]`). Shallow —
uses only annotation-level callee info (`collectFnParams`), so it can't recurse without bound. -/
def nestedParamSig (fn : Json) : Array PyType :=
  let body := (fn.getObjValAs? (Array Json) "body").toOption.getD #[]
  let fnP := collectFnParams fn
  let known := paramSeed fn
  let args := (((fn.getObjVal? "args").toOption).bind (·.getObjValAs? (Array Json) "args" |>.toOption)).getD #[]
  args.map fun a =>
    match getField a "annotation" with
    | some ann => if ann.isNull
        then usageType fnP known 1 ((a.getObjValAs? String "arg").toOption.getD "") (Json.arr body)
        else ofAnnotation ann
    | none => usageType fnP known 1 ((a.getObjValAs? String "arg").toOption.getD "") (Json.arr body)

/-- `q = sorted(p)` / `list(p)` / `reversed(p)` (possibly sliced, `sorted(p)[::-1]`): `q` is a LIST
whose ELEMENT equals `p`'s element. Unlike a copy/slice this does NOT preserve `p`'s container (`sorted`
turns a `str` into `list[str]`), so it only soundly back-propagates a NON-`str` element (`list[int]` ⇒
`p : list[int]`; a `str` element would reintroduce the str-vs-`list[str]` ambiguity). -/
partial def listProducingSource (e : Json) : Option String :=
  match nodeTypeOf e with
  | some "Subscript" =>
      if (getField e "slice").any (nodeTypeOf · == some "Slice")
      then (getField e "value").bind listProducingSource else none
  | some "Call" =>
      match (getField e "func").bind nameId? with
      | some fn => if ["sorted", "list", "reversed"].contains fn
          then (((e.getObjValAs? (Array Json) "args").toOption.getD #[])[0]?).bind nameId? else none
      | none => none
  | _ => none

/-- `q = p.keys()` / `list(p.keys())` (`p` a Name): `q`'s element type is `p`'s KEY type, so a decisive
use of `q` (`for k in q: k.islower()`) pins the dict key. Returns `p`. -/
partial def dictKeysSource (e : Json) : Option String :=
  match nodeTypeOf e with
  | some "Call" =>
      match getField e "func" with
      | some func =>
          if nodeTypeOf func == some "Attribute" && (func.getObjValAs? String "attr").toOption == some "keys"
          then (getField func "value").bind nameId?
          else if nameId? func == some "list"
          then (((e.getObjValAs? (Array Json) "args").toOption.getD #[])[0]?).bind dictKeysSource
          else none
      | none => none
  | _ => none

/-- The loop variable of a `for <c> in <name>` anywhere in `body` (first match), else `none`. -/
partial def loopVarOver (name : String) (j : Json) : Option String :=
  if nodeTypeOf j == some "For" && (getField j "iter").bind nameId? == some name
  then (getField j "target").bind nameId?
  else match j with
    | .arr xs => xs.findSome? (loopVarOver name)
    | .obj fs => fs.toList.findSome? (fun (_, v) => loopVarOver name v)
    | _ => none

/-- Seed each unannotated parameter from unambiguous body usage (`p.split()` → str, `p.append()` →
list, `p.keys()` → dict). This is the safe part of the use-based inference the old Python pre-pass did. -/
def paramUsageSeed (fn : Json) : Env := Id.run do
  let body := fn.getObjValAs? (Array Json) "body" |>.toOption.getD #[]
  -- Enrich the annotation-only callee map with each nested helper's INFERRED param signature, so a
  -- value passed to an UNannotated helper (`is_prime(x)`) picks up the helper's used-inferred type.
  let mut fnParams := collectFnParams fn
  for st in flatStmts body.toList do
    if nodeTypeOf st == some "FunctionDef" then
      if let some nm := (st.getObjValAs? String "name").toOption then
        fnParams := fnParams.insert nm (nestedParamSig st)
  -- Known scalar types of names, for the ordered-comparison anchor: param annotations plus any local
  -- assigned a literal (`ans = ""` ⇒ str, `lo = 0` ⇒ int), so `word < ans` pins `word` to `str` and
  -- `x < lo` pins `x` to `int` — soundly (ordered comparison needs order-compatible operands).
  let mut known : Env := paramSeed fn
  let learnLit (m : Env) (tgt : Json) (val : Option Json) : Env :=
    match nameId? tgt, val.bind literalType? with
    | some nm, some t => if t == .unknown then m else m.insert nm ((m.get? nm |>.getD .unknown).join t)
    | _, _ => m
  for s in flatStmts body.toList do
    if nodeTypeOf s == some "Assign" then
      let val := getField s "value"
      -- A single-target assign carries `target` (singular); only chained `a = b = v` uses `targets`.
      let tgts := (getField s "target").toArray
                  ++ (getField s "targets").elim #[] (fun t => (t.getArr?).toOption.getD #[])
      for tgt in tgts do
        match nodeTypeOf tgt, val.bind (fun v => getField v "elts") with
        -- `a, b = 0, ""`: zip tuple targets with tuple-literal values.
        | some "Tuple", some (.arr vs) =>
            for (te, ve) in ((tgt.getObjValAs? (Array Json) "elts").toOption.getD #[]).zip vs do
              known := learnLit known te (some ve)
        | _, _ => known := learnLit known tgt val
  -- Transparent aliases: `q = p` (copy) or `q = p[a:b]` (slice) give `q` the SAME container type as
  -- `p` (a slice of a `str` is a `str`, of a `list` a `list`), so a type-exclusive use of `q`
  -- (`q.replace(...)`, `q.isdigit()`) pins `p` too. `q = p[i]` (a single element) is EXCLUDED — that
  -- is the ambiguous element case. Followed one hop; enough for `ans = text; ans.replace(...)`.
  let aliasRoot : Std.HashMap String String := Id.run do
    let mut m : Std.HashMap String String := {}
    for s in flatStmts body.toList do
      if nodeTypeOf s == some "Assign" then
        if let some q := (getField s "target").bind nameId? then
          match getField s "value" with
          | some v =>
              if let some p := nameId? v then m := m.insert q p
              else if nodeTypeOf v == some "Subscript" && (getField v "slice").any (nodeTypeOf · == some "Slice") then
                if let some p := (getField v "value").bind nameId? then m := m.insert q p
          | none => pure ()
    return m
  -- `sorted_list = sorted(p)[::-1]`: back-propagate only a NON-`str` list element (see `listProducingSource`).
  let listAliasRoot : Std.HashMap String String := Id.run do
    let mut m : Std.HashMap String String := {}
    for s in flatStmts body.toList do
      if nodeTypeOf s == some "Assign" then
        if let some q := (getField s "target").bind nameId? then
          if let some p := (getField s "value").bind listProducingSource then m := m.insert q p
    return m
  -- `keys = list(p.keys())`: `keys`' element type is `p`'s KEY type (see `dictKeysSource`).
  let keysAliasRoot : Std.HashMap String String := Id.run do
    let mut m : Std.HashMap String String := {}
    for s in flatStmts body.toList do
      if nodeTypeOf s == some "Assign" then
        if let some q := (getField s "target").bind nameId? then
          if let some p := (getField s "value").bind dictKeysSource then m := m.insert q p
    return m
  let mut env : Env := {}
  for name in paramNames fn do
    -- fuel 1: loop-variable inference may fire at the top level but not nest (see `usageType`).
    let mut t := usageType fnParams known 1 name (Json.arr body)
    -- A decisive direct scalar use (`p.isalpha()`, `ord(p)`, `p << 1`) OVERRIDES any container guess
    -- from element access (`p[i].upper()` ⇒ `list[str]`): a `str`/`int` scalar and its element form
    -- would otherwise join to `.any`. Sound — Python would `TypeError` if `p` were the container. A
    -- transparent alias (`y = p[6:]; y.isdigit()`) is decisive too: a list-slice has no `.isdigit()`.
    let mut decisive := decisiveScalarType name (Json.arr body)
    for (q, p) in aliasRoot.toList do
      if p == name then decisive := decisive.join (decisiveScalarType q (Json.arr body))
    if decisive.isKnown then t := decisive
    -- Only when the param has no direct signal, fall back to a transparent alias local's usage —
    -- recovers a `str`/`list` param whose only decisive use is through a copy/slice binding
    -- (`ans = text; ans.replace(...)` ⇒ `text : str`). Skip an alias whose own type is ambiguous
    -- (`.any`/`unknown`, e.g. a type-changing local) so it never poisons the param.
    if t == .unknown then
      for (q, p) in aliasRoot.toList do
        if p == name then
          let qt := usageType fnParams known 1 q (Json.arr body)
          if qt.isKnown && qt != .any then t := t.join qt
      -- `sorted_list = sorted(p)[::-1]; for x in sorted_list: is_prime(x:int)` ⇒ `p : list[int]`.
      -- Only a NON-`str` list element (see `listProducingSource`), so it never mis-types a `str` param.
      for (q, p) in listAliasRoot.toList do
        if p == name then
          match usageType fnParams known 1 q (Json.arr body) with
          | .list e => if e.isKnown && e != .str then t := t.join (.list e)
          | _ => pure ()
    -- `keys = list(p.keys())`: a decisive key element (`for k in keys: k.islower()` ⇒ str) makes
    -- `p : dict[key, Any]`. Runs even when `p` is already `dict[⊥,⊥]` (from `.keys()`), refining the
    -- key via `join`; values stay dynamic — a keys-iteration never constrains them.
    for (q, p) in keysAliasRoot.toList do
      if p == name then
        -- `q` is KNOWN to be a list (`list(p.keys())`), so read its element from the loop var's
        -- DECISIVE scalar use (`for k in q: k.islower()` ⇒ str) — bypassing `usageType`'s str-vs-list
        -- guard, which wrongly abstains here because it can't see that `q` is a list.
        match (loopVarOver q (Json.arr body)).map (decisiveScalarType · (Json.arr body)) with
        | some e => if e.isKnown then t := t.join (.dict e .any)
        | none => pure ()
    if t != .unknown then env := env.insert name t
  return env

/-- Names `fn` binds directly — params plus `=`/`for`/annotated targets in its own body (through
`if`/`for` blocks, not into deeper nested defs). A name used in `fn` but NOT here is a capture of an
enclosing scope. -/
def localAssignNames (fn : Json) : List String := Id.run do
  let mut names := (paramNames fn).toList
  for s in flatStmts ((fn.getObjValAs? (Array Json) "body").toOption.getD #[]).toList do
    match nodeTypeOf s with
    | some "Assign" =>
        for t in (s.getObjValAs? (Array Json) "targets").toOption.getD #[] do
          if let some n := nameId? t then names := n :: names
    | some "AnnAssign" | some "AugAssign" | some "For" =>
        if let some n := (getField s "target").bind nameId? then names := n :: names
    | _ => pure ()
  return names

/-- The container name a teaching METHOD mutation (`xs.append(v)`, `s.add(v)`) targets, for the
capture pass. Only `recv.method(...)` receivers — a free `heappush(h, v)` capture is rarer and left to
the enclosing-scope pass. -/
def mutationReceiverName? (value : Json) : Option String :=
  if nodeTypeOf value != some "Call" then none else
  match getField value "func" with
  | some func =>
      if nodeTypeOf func == some "Attribute" then
        match getField func "value" with
        | some recv =>
            if ((Libraries.methodBehaviour? ((func.getObjValAs? String "attr").toOption.getD "")).bind (·.teaches?)).isSome
            then match nameId? recv with
              | some n => some n
              -- `nums[i].append(v)`: the mutated container is the subscript BASE (`nums`).
              | none => if nodeTypeOf recv == some "Subscript" then (getField recv "value").bind nameId? else none
            else none
        | none => none
      else none
  | none => none

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

/-- The combined parameter types of every nested `def` in `body`, from their call sites (`roots` is
the enclosing body). Lets a captured `d[param].append(v)` INSIDE a nested def teach the OUTER `d`'s
key from `param`'s type — which lives only in the inner scope. -/
def nestedDefParamEnv (sigs : Sigs) (env : Env) (body : Array Json) (roots : Array Json) : Env :=
  body.foldl (fun e nf =>
    if nodeTypeOf nf == some "FunctionDef"
    then (nestedParamHints sigs env nf roots).fold (fun m k v => m.insert k v) e
    else e) {}

/-- Apply container-teaching mutations found INSIDE nested defs to the enclosing `env`, so a capture
learns its element type across scopes (`nums = []` here, `nums.append(x)` in a sibling `def dfs`, then
`nums[i]` in `def build` — all one `List Int`). A name a nested def binds itself (param or `=`) is a
shadow, not a capture, so it is skipped; only names already in `env` are refined (join-only, never a
downgrade). `paramEnv` carries the enclosing nested def's parameter types so `d[param]` inside it can
pin the captured `d`'s key. The enclosing scope's own mutations are handled by `applyStmt`. -/
partial def applyCaptureMutations (sigs : Sigs) (shadowed : List String) (paramEnv : Env)
    (insideDef : Bool) (env : Env) (json : Json) : Env := Id.run do
  let entering := nodeTypeOf json == some "FunctionDef"
  let shadowed := if entering then shadowed ++ localAssignNames json else shadowed
  let inside := insideDef || entering
  let mut env := env
  if inside then
    if let some cname := mutationReceiverName? json then
      if !shadowed.contains cname && (env.get? cname).isSome then
        -- Type the mutation with the enclosing nested def's params visible (`d[offset]` needs
        -- `offset : int`), but write back ONLY the receiver so those inner params never leak out.
        let typingEnv := paramEnv.fold (fun m k v => m.insert k v) env
        match (applyMutation sigs typingEnv json).get? cname with
        | some t => env := env.insert cname t
        | none => pure ()
  match json with
  | .arr xs => return xs.foldl (applyCaptureMutations sigs shadowed paramEnv inside) env
  | .obj fs => return fs.toList.foldl (fun e (_, v) => applyCaptureMutations sigs shadowed paramEnv inside e v) env
  | _ => return env

/-- Every `(container-name, index-type)` from a subscript READ `base[idx]` anywhere in `json` (`base`
a plain Name, not a slice). Container writes already teach element types (`applyStmt`/`applyMutation`),
but the KEY of a dict is only pinned by *usage* — `d = defaultdict(int)` knows its value type yet
leaves the key `unknown` until a `d[k]` read fixes it. This is the read side of Python's
"infer from all usages". -/
partial def collectSubscriptKeys (sigs : Sigs) (env : Env) (json : Json) : Array (String × PyType) :=
  let here : Array (String × PyType) :=
    if nodeTypeOf json == some "Subscript" then
      match (getField json "value").bind nameId?, getField json "slice" with
      | some cname, some slice =>
          if nodeTypeOf slice == some "Slice" then #[] else #[(cname, typeOfExpr sigs env slice)]
      | _, _ => #[]
    else #[]
  let rest := match json with
    | .arr xs => xs.foldl (fun acc e => acc ++ collectSubscriptKeys sigs env e) #[]
    | .obj fs => fs.toList.foldl (fun acc (_, v) => acc ++ collectSubscriptKeys sigs env v) #[]
    | _ => #[]
  here ++ rest

/-- Pin a dict's KEY type from every subscript-read `d[k]`, joining `typeof(k)` into the key. Only
touches names ALREADY typed as a dict (so a list `xs[i]` is never mis-widened to a dict); a genuinely
undetermined container stays undetermined here — the write side decides list-vs-dict. -/
def learnFromReads (sigs : Sigs) (env : Env) (json : Json) : Env :=
  (collectSubscriptKeys sigs env json).foldl (fun e (cname, kt) =>
    if kt == .unknown then e else
    match e.get? cname |>.getD .unknown with
    | .dict k v => e.insert cname (.dict (k.join kt) v)
    | _ => e) env

/-- Collect `(dictName, keyType, valType)` from every dict-method call `d.pop(k, default)` /
`d.get(k, default)` / `d.setdefault(k, v)` — the key is arg 0, the value the (optional) arg 1. `.pop`
is also a LIST method (`xs.pop(i)`), so the caller must guard on `d` already being dict-typed. -/
partial def collectDictKV (sigs : Sigs) (env : Env) (json : Json) : Array (String × PyType × PyType) :=
  let here : Array (String × PyType × PyType) :=
    if nodeTypeOf json == some "Call" then
      match getField json "func" with
      | some func =>
          if nodeTypeOf func == some "Attribute"
              && ["pop", "get", "setdefault"].contains ((func.getObjValAs? String "attr").toOption.getD "") then
            match (getField func "value").bind nameId? with
            | some dname =>
                let args := (json.getObjValAs? (Array Json) "args").toOption.getD #[]
                let kt := if args.size ≥ 1 then typeOfExpr sigs env args[0]! else .unknown
                let vt := if args.size ≥ 2 then typeOfExpr sigs env args[1]! else .unknown
                #[(dname, kt, vt)]
            | none => #[]
          else #[]
      | none => #[]
    else #[]
  let rest := match json with
    | .arr xs => xs.foldl (fun acc e => acc ++ collectDictKV sigs env e) #[]
    | .obj fs => fs.toList.foldl (fun acc (_, v) => acc ++ collectDictKV sigs env v) #[]
    | _ => #[]
  here ++ rest

/-- Refine a dict's key/value from `d.pop`/`.get`/`.setdefault` calls (see `collectDictKV`). Only
touches names ALREADY dict-typed — a bare `dict` param seeds as `dict[⊥,⊥]`, so a `counts.pop(k, -1)`
fills its key/value in and it materialises as a concrete `Std.HashMap`, not a stuck metavariable. -/
def learnFromDictMethods (sigs : Sigs) (env : Env) (json : Json) : Env :=
  (collectDictKV sigs env json).foldl (fun e (cname, kt, vt) =>
    match e.get? cname |>.getD .unknown with
    | .dict k v => e.insert cname (.dict (if kt == .unknown then k else k.join kt)
                                         (if vt == .unknown then v else v.join vt))
    | _ => e) env

/-- Seed a parameter whose DEFAULT is a known function as a callable returning that function's type:
`def f(a=g): return a()` makes `a` a `Callable[…, g's return]`, so `a()` resolves to `g`'s return
(and any variable bound to it follows). `sigs g` is g's inferred return type. -/
def defaultCallableSeed (sigs : Sigs) (fn : Json) : Env := Id.run do
  let mut m : Env := {}
  let some argsNode := (fn.getObjVal? "args").toOption | return m
  let params := (argsNode.getObjValAs? (Array Json) "args").toOption.getD #[]
  let defaults := (argsNode.getObjValAs? (Array Json) "defaults").toOption.getD #[]
  if defaults.isEmpty then return m
  let firstDefault := params.size - defaults.size
  for i in [0:params.size] do
    if i ≥ firstDefault then
      if let some g := nameId? defaults[i - firstDefault]! then
        if let some rt := sigs.get? g then
          if rt != .unknown then
            if let .ok pn := params[i]!.getObjValAs? String "arg" then
              m := m.insert pn (.fn [] rt)
  return m

/-- Seed a parameter's type from a SCALAR-literal default: `def f(verbose=False)` ⇒ `verbose : bool`,
`n=0` ⇒ `int`, `name=""` ⇒ `str`. Only scalar literals (bool/int/str/float) — a `None` default gives no
concrete type (the param is nullable, resolved by usage), and a container default (`x=[]`) would only
pin an unknown element. Weaker than an explicit annotation or body usage, which override it. -/
def defaultLiteralSeed (sigs : Sigs) (fn : Json) : Env := Id.run do
  let mut m : Env := {}
  let some argsNode := (fn.getObjVal? "args").toOption | return m
  let params := (argsNode.getObjValAs? (Array Json) "args").toOption.getD #[]
  let defaults := (argsNode.getObjValAs? (Array Json) "defaults").toOption.getD #[]
  if defaults.isEmpty then return m
  let firstDefault := params.size - defaults.size
  for i in [0:params.size] do
    if i ≥ firstDefault then
      let t := typeOfExpr sigs {} defaults[i - firstDefault]!
      if t == .int || t == .bool || t == .str || t == .float then
        if let .ok pn := params[i]!.getObjValAs? String "arg" then
          m := m.insert pn t
  return m

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
  -- A bare container from an annotation/hint (`list`/`set`/`dict` with `.any`/`.unknown` element)
  -- keeps a concrete element that body-usage found: `l: list` + `[x+1 for x in l]` ⇒ `list[int]`.
  -- Shape and concretely-named elements still win over usage.
  let refineElem (ann usage : PyType) : PyType :=
    let pick (a u : PyType) : PyType := if a == .any || a == .unknown then (if u.isKnown then u else a) else a
    match ann, usage with
    | .list a, .list u => .list (pick a u)
    | .set a, .set u => .set (pick a u)
    | .dict ak av, .dict uk uv => .dict (pick ak uk) (pick av uv)
    -- The nullable recursive-node pattern for an ANNOTATED param: `def dfs(node: TreeNode)` whose body
    -- feeds it `.left`/`.right`/`None` (so usage widened it to `Optional[TreeNode]`) is really nullable.
    -- Keep the widened `.opt (.cls c)` rather than letting the bare `.cls c` annotation clobber it —
    -- `stampParams` then chooses `_mut_opt` (reassigned) or an `Optional c` param `_ty` (read+recursed).
    | .cls c, .opt (.cls c') => if c == c' then .opt (.cls c) else ann
    | _, _ => ann
  let mergeRefining (src : Env) (env : Env) : Env :=
    src.fold (fun m k v => m.insert k (refineElem v (m.get? k |>.getD .unknown))) env
  -- Explicit local annotations (`result: list[int] = []`, kept as `_decl_ty` by the visitor) are
  -- authoritative: they override the type inferred from the RHS/usage and stay sticky across the reflow
  -- (an append of an untypeable element must not widen an annotated `list[int]` to `list[PyAny]`).
  -- `refineElem` keeps a concrete annotated element while letting a BARE `list` annotation take the
  -- usage element, so this never loses information.
  let declTypes : Env := stmts.foldl (fun m s =>
    if nodeTypeOf s == some "Assign" then
      match (getField s "target").bind nameId?, getField s "_decl_ty" with
      | some name, some ann => m.insert name (ofAnnotation ann)
      | _, _ => m
    else m) {}
  let mut env := paramUsageSeed fn
  env := mergeRefining (defaultLiteralSeed sigs fn) env
  env := mergeRefining outer env
  env := mergeRefining hints env
  env := mergeRefining (paramSeed fn) env
  env := mergeRefining (defaultCallableSeed sigs fn) env
  env := mergeRefining declTypes env
  let bodyJson := Json.arr body
  -- Reflow until stable. The lattice climbs, so a small cap is a sound floor, not a correctness risk.
  for _ in [0:8] do
    -- `compBindings` types comprehension targets so a call inside a comprehension can hint the callee
    -- (`[f(point) for point in data]`). It binds only FRESH names — a comprehension target that
    -- shadows an outer variable owns a separate scope (Python-3), so clobbering the outer type (a
    -- loop `v : int` vs a comprehension `v : list[int]` → `any`) would poison it. Fresh-only respects
    -- that: never downgrade an outer binding.
    let paramEnv := nestedDefParamEnv sigs env body #[bodyJson]
    let stepped := applyCaptureMutations sigs [] paramEnv false (stmts.foldl (applyStmt sigs) env) bodyJson
    let stepped := learnFromReads sigs stepped bodyJson
    let stepped := learnFromDictMethods sigs stepped bodyJson
    let next := mergeRefining declTypes (compBindings sigs stepped bodyJson)
    if next.size == env.size && next.fold (fun ok k v => ok && (env.get? k |>.getD .unknown) == v) true then
      env := next
      break
    env := next
  -- A decisive scalar body use (`ord(p)`, `p.isdigit()`, `p << 1`) is authoritative: the body would
  -- `TypeError` on any other type, so it overrides an `.any`/`.unknown` a call site forced (a nested
  -- helper reached via `map(f, <PyAny>)` or a loop over an untyped source).
  for name in paramNames fn do
    let cur := (env.get? name).getD .unknown
    if cur == .any || cur == .unknown then
      let d := decisiveScalarType name (Json.arr body)
      if d.isKnown then env := env.insert name d
  return env

/-- The return type given an ALREADY-inferred body env — the half of `returnTypeOf` after
`inferFunction`. Split out so a caller that already holds the env (the interprocedural fixpoint, which
also needs it for call-site refinement) computes the body env ONCE instead of inferring it twice. -/
partial def returnTypeFromEnv (sigs : Sigs) (env : Env) (fn : Json) : PyType := Id.run do
  let body := (fn.getObjValAs? (Array Json) "body").toOption.getD #[]
  let mut ret : PyType := .unknown
  let mut sawValueReturn := false
  for s in flatStmts body.toList do
    if nodeTypeOf s == some "Return" then
      match getField s "value" with
      | some v =>
          if !v.isNull then
            ret := ret.join (typeOfExpr sigs env v)
            sawValueReturn := true
          else
            ret := ret.join .none
      | none => ret := ret.join .none
  -- A function that never returns a VALUE (`def f(): pass`, or only bare `return`) returns `None` —
  -- so a call `y = f()` is typed `None`, not left unknown. Sound (Python's implicit `return None`).
  return if sawValueReturn then ret else .none

partial def returnTypeOf (sigs : Sigs) (hints : Env) (fn : Json) (outer : Env := {}) : PyType :=
  returnTypeFromEnv sigs (inferFunction sigs outer hints fn) fn


end TypeInfer
