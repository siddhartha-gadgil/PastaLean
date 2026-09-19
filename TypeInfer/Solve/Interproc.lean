import TypeInfer.Solve.Stamp

namespace TypeInfer

open Lean

/-! ### Interprocedural: return types flow to call sites, argument types flow to parameters -/

/-- Inferred type of each parameter of each user function, by position. -/
abbrev ParamSigs := Std.HashMap String (Array PyType)

/-- Every top-level `FunctionDef` in a module or mutual group, in order. -/
def topFunctions (module : Json) : Array Json :=
  ((module.getObjValAs? (Array Json) "body").toOption.getD #[]).filter
    (nodeTypeOf · == some "FunctionDef")

/-- Module top-level statements that are not function defs (e.g. `print(add(3, 4))` at module scope):
their call sites refine callee params too, so `add` boxes whether it is called from a def or not. -/
def topLevelStmts (module : Json) : Array Json :=
  ((module.getObjValAs? (Array Json) "body").toOption.getD #[]).filter
    (nodeTypeOf · != some "FunctionDef")

/-- Top-level `ClassDef`s of a module. -/
def classDefsOf (module : Json) : Array Json :=
  ((module.getObjValAs? (Array Json) "body").toOption.getD #[]).filter (nodeTypeOf · == some "ClassDef")

/-- The `FunctionDef` methods of a class (stored under `methods`, or `body` on older nodes). -/
def methodsOf (classDef : Json) : Array Json :=
  (#["methods", "body"].foldl (fun acc key =>
    acc ++ (classDef.getObjValAs? (Array Json) key).toOption.getD #[]) #[]).filter
    (nodeTypeOf · == some "FunctionDef")

/-- Names of every class defined at module top level. -/
def classNamesOf (module : Json) : Std.HashSet String :=
  (classDefsOf module).foldl (fun s c => (c.getObjValAs? String "name").toOption.elim s s.insert) {}

/-- Direct base-class names of a `ClassDef` (`class C(A, B)` → `["A", "B"]`), keeping only plain-name
bases (`object`, a dotted/generic base, etc. are dropped — nothing to inherit locally). -/
def baseNamesOf (classDef : Json) : Array String :=
  ((classDef.getObjValAs? (Array Json) "bases").toOption.getD #[]).filterMap fun b =>
    (nameId? b).filter (· != "object")

/-- True when `fn`'s first parameter is `self` — an instance method, as opposed to a `@staticmethod`. -/
def isInstanceMethod (fn : Json) : Bool := (paramNames fn)[0]? == some "self"

/-- A call's argument types as a POSITIONAL array: the positional args, plus each keyword argument
`k=v` placed at the index `k` holds in the callee's parameter names `pnames` (gaps stay `unknown`, the
join's neutral element). Without this a `show(flag=True)` teaches its callee's `flag` nothing. -/
def callArgTypes (sigs : Sigs) (env : Env) (pnames : Array String) (call : Json) : Array PyType :=
  let args := ((call.getObjValAs? (Array Json) "args").toOption.getD #[]).map (typeOfExpr sigs env)
  let kws : List (Nat × PyType) := match getField call "keywords" with
    | some (.obj kfs) => kfs.toList.filterMap (fun (k, v) =>
        (pnames.findIdx? (· == k)).map (fun i => (i, typeOfExpr sigs env v)))
    | _ => []
  if kws.isEmpty then args else
  let size := kws.foldl (fun n (i, _) => max n (i + 1)) args.size
  kws.foldl (fun a (i, t) => a.set! i t) (args ++ Array.replicate (size - args.size) PyType.unknown)

/-- Collect `Class.method(...)` call sites for method-parameter inference, keyed `"Class.method"` (a
dot no Python function name has). Two shapes resolve a class: a qualified call on a class *name*
(`BinaryIndexedTree.lowbit(x)`, static or explicit-`self`) and an instance call whose receiver types
to `.cls C` (`tree.update(a, b)`, `self.query(x)`). An instance method's arg list is prefixed with the
receiver's `.cls C` so it aligns with the `self` parameter. Skips nested defs' own scopes only in that
`env` is the enclosing one; the walk itself is exhaustive. -/
partial def collectMethodCalls (sigs : Sigs) (env : Env) (classNames : Std.HashSet String)
    (methodSelf : Std.HashMap String Bool) (pnames : Std.HashMap String (Array String))
    (json : Json) : Array (String × Array PyType) :=
  -- A keyword argument is matched against the method's params MINUS `self` (slot 0 is the receiver,
  -- which no call site writes); the receiver type is prefixed back on afterwards.
  let argsOf (key : String) (dropSelf : Bool) : Array PyType :=
    let ps := (pnames.get? key).getD #[]
    callArgTypes sigs env (if dropSelf then ps.extract 1 ps.size else ps) json
  let here : Array (String × Array PyType) :=
    match nodeTypeOf json, getField json "func" with
    | some "Call", some func =>
        -- A constructor call `C(args)` (func is the class NAME) refines `C.__init__`'s params, with a
        -- leading `self : .cls C` — so `Rectangle(5, 10)` types `__init__(self, width, height)`.
        if nodeTypeOf func == some "Name" then
          match (nameId? func).filter classNames.contains with
          | some cname =>
              #[(s!"{cname}.__init__", #[PyType.cls cname] ++ argsOf s!"{cname}.__init__" true)]
          | none => #[]
        else if nodeTypeOf func != some "Attribute" then #[] else
        match (func.getObjValAs? String "attr").toOption, getField func "value" with
        | some attr, some recv =>
            match nameId? recv with
            -- Qualified on a class name: static (args as-is) or explicit-self (prefix `.cls C`).
            | some rname =>
                if classNames.contains rname then
                  let key := s!"{rname}.{attr}"
                  let selfed := (methodSelf.get? key).getD false
                  let args := argsOf key selfed
                  #[(key, if selfed then #[PyType.cls rname] ++ args else args)]
                else instanceCall attr recv
            | none => instanceCall attr recv
        | _, _ => #[]
    | _, _ => #[]
  here ++ (match json with
    | .arr xs => xs.foldl (fun acc x => acc ++ collectMethodCalls sigs env classNames methodSelf pnames x) #[]
    | .obj fs => fs.toList.foldl (fun acc (_, v) => acc ++ collectMethodCalls sigs env classNames methodSelf pnames v) #[]
    | _ => #[])
where
  /-- An instance call `recv.attr(args)` where `recv : .cls C` → `C.attr` with the args prefixed by
  the receiver's `.cls C` (the `self` slot). -/
  instanceCall (attr : String) (recv : Json) : Array (String × Array PyType) :=
    match (typeOfExpr sigs env recv).classNameOf? with
    | some c =>
        let key := s!"{c}.{attr}"
        let ps := (pnames.get? key).getD #[]
        #[(key, #[PyType.cls c] ++ callArgTypes sigs env (ps.extract 1 ps.size) json)]
    | none => #[]

/-- The hint environment for the parameters named in `fn`, drawn from `params[key]` (its inferred
per-position types). `key` is the callee's name — a bare function name, or `"Class.method"` for a
class method. -/
def hintsForKey (params : ParamSigs) (fn : Json) (key : String) : Env := Id.run do
  let names := paramNames fn
  let types := (params.get? key).getD #[]
  let mut env : Env := {}
  for i in [0:names.size] do
    if let some t := types[i]? then if t != .unknown then env := env.insert names[i]! t
  return env

/-- The hint environment for `fn`'s parameters from `params` (its inferred per-position types). -/
def hintsFor (params : ParamSigs) (fn : Json) : Env :=
  hintsForKey params fn ((fn.getObjValAs? String "name").toOption.getD "")

/-- Collect `(calleeName, argumentTypes)` for every direct call `foo(a, b, …)` in `json`, typing the
arguments under `env`. Nested calls are included; method calls are ignored (no positional callee).
`pnames` gives each callee's parameter names, so keyword arguments land in the right slot. -/
partial def collectCalls (sigs : Sigs) (env : Env) (pnames : Std.HashMap String (Array String))
    (json : Json) : Array (String × Array PyType) :=
  let here : Array (String × Array PyType) :=
    if nodeTypeOf json == some "Call" then
      match getField json "func" with
      | some func =>
          match (nodeTypeOf func, (func.getObjValAs? String "id").toOption) with
          | (some "Name", some name) =>
              #[(name, callArgTypes sigs env ((pnames.get? name).getD #[]) json)]
          | _ => #[]
      | none => #[]
    else #[]
  let sub := match json with
    | .arr xs => xs.foldl (fun acc x => acc ++ collectCalls sigs env pnames x) #[]
    | .obj fs => fs.toList.foldl (fun acc (_, v) => acc ++ collectCalls sigs env pnames v) #[]
    | _ => #[]
  here ++ sub

/-- The `Name` decorators of a `FunctionDef`, e.g. `@double` → `"double"`. Attribute/Call decorators
(`@a.b`, `@lru_cache(...)`) are skipped — a user decorator whose type we can unify is a bare name. -/
def decoratorNamesOf (fn : Json) : Array String :=
  ((fn.getObjValAs? (Array Json) "decorator_list").toOption.getD #[]).filterMap fun d =>
    if nodeTypeOf d == some "Name" then nameId? d else none

/-- Join `argTypes` into `params[name]` position-by-position (missing positions start `unknown`). -/
def refineParams (params : ParamSigs) (name : String) (arity : Nat) (argTypes : Array PyType) : ParamSigs :=
  let cur := (params.get? name).getD (Array.replicate arity .unknown)
  let next := (Array.range cur.size).map fun i =>
    (cur[i]!).join (argTypes[i]?.getD .unknown)
  params.insert name next

/-- Field types of every class in the module, keyed `"Class.field"` so `typeOfExpr` can type a field
access. Mirrors the struct codegen: an explicit annotation wins; otherwise an `__init__` param
defaulting to `None` types the field `Option Class` (the recursive `TreeNode.left`/`ListNode.next`
pattern); otherwise the initialising param's annotation or the type of its default. -/
def classFieldSigs (module : Json) (params : ParamSigs := {}) : Sigs := Id.run do
  let mut out : Sigs := {}
  for st in topLevelStmts module do
    if nodeTypeOf st != some "ClassDef" then continue
    let .ok cls := st.getObjValAs? String "name" | continue
    let methods := (st.getObjValAs? (Array Json) "methods").toOption.getD #[]
    -- `__init__` params: their declared/default type, and which ones default to `None`.
    let mut ptype : Env := {}
    let mut noneParams : List String := []
    if let some init := methods.find? (fun m => (m.getObjValAs? String "name").toOption == some "__init__") then
      -- Seed from inferred call-site param types (`Rectangle(5, 10)` ⇒ `width, height : int`), so a
      -- field `self.width = width` on an UNannotated param still gets a concrete type.
      let initNames := paramNames init
      let initInferred := (params.get? s!"{cls}.__init__").getD #[]
      for i in [0:initNames.size] do
        if let some t := initInferred[i]? then
          if t != .unknown then ptype := ptype.insert initNames[i]! t
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
        -- A class-level variable (`class_var = 0`) has a `default` value but no `self.x = …` init.
        let fromDefault : PyType := match getField f "default" with
          | some d => if d.isNull then .unknown else ofValue d
          | none => .unknown
        let t := if annT != .unknown then annT else
          match getField f "init" with
          | some init =>
              if init.isNull then fromDefault else
              -- `self.left = left` where `left` defaults to `None` → the recursive node pattern.
              match nameId? init with
              | some p =>
                  if noneParams.contains p then .opt (.cls cls) else (ptype.get? p).getD .unknown
              -- A DIRECT `self.x = None` → `Option C`; `self.x = [None]*k` → `List (Option C)` — the
              -- recursive-node child pointer / children array. (These stay class-mentioning so
              -- `stampClassFields` leaves them unannotated for the struct codegen to type.)
              | none =>
                  if isNoneConst init then .opt (.cls cls)
                  else if isListOfNone init then .list (.opt (.cls cls))
                  -- Otherwise type the initialiser itself, under the `__init__` params
                  -- (`self.p = list(range(n))` → `list[int]`, which `ofValue` alone cannot see).
                  else typeOfExpr {} ptype init
          | none => fromDefault
        if t != .unknown then out := out.insert s!"{cls}.{fname}" t
  return out

/-- True when a type names a user class anywhere. Such a type must NOT be written back as an
annotation: the run twin renames `TreeNode` to `TreeNode'rn`, and only the struct codegen's own
class-name path applies that suffix — a literal annotation would pin the unsuffixed name. -/
partial def mentionsClass : PyType → Bool
  | .cls _ => true
  | .list e | .set e | .opt e => mentionsClass e
  | .dict k v => mentionsClass k || mentionsClass v
  | .tuple es => es.any mentionsClass
  | .fn as r => as.any mentionsClass || mentionsClass r
  | _ => false

/-- Write each class field's inferred type into its (empty) `annotation` slot, which the struct
codegen already prefers over its own literal-shape guess — so a container field stops silently
defaulting to `Int`. -/
def stampClassFields (fields : Sigs) (cls : String) (st : Json) : Json :=
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

/-- Split a `Class.member` key into its owning class and the member below it. A base name can itself
be dotted (`abc.ABC`), so the owner is the shortest dot-delimited prefix `owners` knows. -/
private partial def ownerSplit (owners : Std.HashSet String) (k : String) : Option (String × String) :=
  let rec go (acc : String) : List String → Option (String × String)
    | [] | [_] => none
    | p :: rest =>
        let owner := if acc.isEmpty then p else acc ++ "." ++ p
        if owners.contains owner then some (owner, String.intercalate "." rest) else go owner rest
  go "" (k.splitOn ".")

/-- A `Class.member` table indexed by owning class. Built once per inheritance pass so a subclass
reads its base's members straight out of a map, instead of the whole table being rescanned for every
(subclass, base) pair. -/
private def membersByOwner {α : Type} (owners : Std.HashSet String)
    (entries : List (String × α)) : Std.HashMap String (Array (String × α)) :=
  entries.foldl (fun m (k, v) =>
    match ownerSplit owners k with
    | some (owner, suffix) => m.insert owner (((m.get? owner).getD #[]).push (suffix, v))
    | none => m) {}

/-- Co-evolve every function's return type AND its parameter types to a fixpoint: a callee's return
flows to its callers, and a caller's argument types flow to the callee's parameters. Both only climb
the lattice, so this settles. -/
-- `seedSigs`/`seedParams` carry the REPO-GLOBAL signature table (every other module's function
-- returns, class types and parameter types, keyed by qualified/mangled name). Seeding the tables with
-- them is what lets a per-module fixpoint resolve a cross-module call `x = other.f()` or constructor
-- `x = OtherClass()` — the shared-table repo-level design. Empty by default = single-module behaviour.
partial def collectSigs (module : Json) (seedSigs : Sigs := {}) (seedParams : ParamSigs := {}) :
    Sigs × ParamSigs := Id.run do
  let fns := topFunctions module
  -- Fill an annotation-derived param array's `unknown` slots from an incoming seed (cross-module
  -- call-site refinement), never widening a concrete annotation. Keeps cross-module param info alive
  -- through this module's own re-seed, since a function is only ever inferred in its defining module.
  let seedFill (name : String) (arr : Array PyType) : Array PyType :=
    match seedParams.get? name with
    | some prior => arr.mapIdx (fun i t => if t == .unknown then (prior[i]?.getD .unknown) else t)
    | none => arr
  -- Seed each function's parameters with their annotations (unknown where unannotated).
  let mut params : ParamSigs := seedParams
  -- Each callable's parameter NAMES under the same keys, so a keyword argument at a call site finds
  -- its slot (`callArgTypes`).
  let mut pnames : Std.HashMap String (Array String) := {}
  for fn in fns do
    if let .ok name := fn.getObjValAs? String "name" then
      let seed := paramSeed fn
      pnames := pnames.insert name (paramNames fn)
      params := params.insert name (seedFill name ((paramNames fn).map fun p => (seed.get? p).getD .unknown))
  -- Class methods join the same table under `"Class.method"` keys (a dot no function name has), so
  -- their params are refined from call sites just like a free function's. `methodSelf` records which
  -- take a leading `self` (an instance method) vs a `@staticmethod`, so a qualified `Class.m(...)` call
  -- prefixes the receiver type only for the former.
  let classNames := classNamesOf module
  let methodEntries : Array (String × String × Json) := (classDefsOf module).foldl (fun acc cd =>
    match (cd.getObjValAs? String "name").toOption with
    | some cls => acc ++ (methodsOf cd).filterMap (fun m =>
        (m.getObjValAs? String "name").toOption.map (fun mn => (cls, mn, m)))
    | none => acc) #[]
  let mut methodSelf : Std.HashMap String Bool := {}
  for (cls, mn, m) in methodEntries do
    let key := s!"{cls}.{mn}"
    let seed := paramSeed m
    pnames := pnames.insert key (paramNames m)
    params := params.insert key (seedFill key ((paramNames m).map fun p => (seed.get? p).getD .unknown))
    methodSelf := methodSelf.insert key (isInstanceMethod m)
  -- Class field types share the `sigs` table under `"Class.field"` keys; a bare class name maps to
  -- `.cls C`, so a `t = C(...)` constructor call types `t` (letting `t.method(...)` resolve `C.method`).
  let mut sigs : Sigs := seedSigs.fold (fun m k v => m.insert k v) (classFieldSigs module)
  for cls in classNames.toList do sigs := sigs.insert cls (.cls cls)
  -- Hints for a method, with `self : .cls C` seeded (an instance method's receiver).
  let methodHints (params : ParamSigs) (cls key : String) (m : Json) : Env :=
    let h := hintsForKey params m key
    if isInstanceMethod m then h.insert "self" (.cls cls) else h
  -- Each class's direct base names, for MRO member propagation inside the fixpoint below.
  let baseMap : Array (String × Array String) := (classDefsOf module).filterMap fun cd =>
    (cd.getObjValAs? String "name").toOption.map (fun c => (c, baseNamesOf cd))
  -- The only class names the member index is ever asked about.
  let baseSet : Std.HashSet String := baseMap.foldl (fun s (_, bs) => bs.foldl (·.insert ·) s) {}
  for _ in [0:6] do
    -- Refresh class field types from the current (refined) `__init__` params so a field on an
    -- unannotated ctor param (`self.width = width`, `width` learned as `int` from `Rectangle(5,10)`)
    -- gets a concrete type — which then types `self.width * self.height` in a method's return.
    sigs := (classFieldSigs module params).fold (fun acc k v => acc.insert k v) sigs
    -- Inheritance / MRO (SOUND, static single/linear inheritance): copy each base's members
    -- (`Base.field`/`Base.method` return in `sigs`, method-param types in `params`) to the subclass
    -- key `Sub.member` when the subclass does not override — so an inherited FIELD accessed in a
    -- method (`B(A)` whose `func` returns `self.a`, `a` set by `A.__init__`) and an inherited METHOD
    -- call (`b.func()`) both resolve. Inside the loop + iterated so `self.a` is known BEFORE the
    -- method's return is computed, and multi-level chains (C→B→A) close.
    -- A pass copies one level, so only a chain needs another one: the loop stops as soon as a pass
    -- inserts nothing, and each pass indexes both tables by owning class (`membersByOwner`) rather
    -- than rescanning them per (subclass, base) pair. Scanning every pair on every one of `baseMap.size`
    -- passes was cubic — a module with a few hundred inherited classes took minutes.
    let mut pass := 0
    let mut changed := true
    while changed && pass < baseMap.size do
      pass := pass + 1
      changed := false
      let sigMembers := membersByOwner baseSet sigs.toList
      let parMembers := membersByOwner baseSet params.toList
      for (cls, bases) in baseMap do
        for base in bases do
          for (suffix, v) in (sigMembers.get? base).getD #[] do
            let subKey := s!"{cls}.{suffix}"
            if !sigs.contains subKey then
              sigs := sigs.insert subKey v
              changed := true
          for (suffix, v) in (parMembers.get? base).getD #[] do
            let subKey := s!"{cls}.{suffix}"
            if !params.contains subKey then
              params := params.insert subKey v
              changed := true
    let mut nextSigs := sigs
    let mut nextParams := params
    let refineFrom (nextParams : ParamSigs) (calls : Array (String × Array PyType)) : ParamSigs :=
      calls.foldl (fun p (callee, argTypes) =>
        if params.contains callee then refineParams p callee argTypes.size argTypes else p) nextParams
    -- Function VALUES (`.fn` with inferred returns): a `g = some_func` / `return some_func` reads as
    -- `callable`, a `func(param_func)` refines `func`'s callback param, and a higher-order
    -- `def func(a): return a()` specialises its return per call.
    let fnEnv : Env := fns.foldl (fun e fn =>
      match fn.getObjValAs? String "name" with
      | .ok nm => (match functionSignatureType fn with
                   | .fn as _ => e.insert nm (.fn as ((sigs.get? nm).getD .unknown))
                   | t => e.insert nm t)
      | _ => e) {}
    for fn in fns do
      if let .ok name := fn.getObjValAs? String "name" then
        let hints := hintsFor params fn
        -- Infer the body env ONCE and reuse it for both the return type and the call-site refinement
        -- (the return and the calls need the same env, so `returnTypeOf`'s internal re-inference was
        -- pure duplication — the single dominant cost of a fixpoint iteration).
        let env := inferFunction sigs fnEnv hints fn
        nextSigs := nextSigs.insert name (returnTypeFromEnv sigs env fn)
        nextParams := refineFrom nextParams (collectCalls sigs env pnames fn)
        nextParams := refineFrom nextParams (collectMethodCalls sigs env classNames methodSelf pnames fn)
    -- Class methods: refine callees from each method body, with `self` typed to its class.
    for (cls, mn, m) in methodEntries do
      let key := s!"{cls}.{mn}"
      let hints := methodHints params cls key m
      -- Seed the enclosing class's first base as `super#cls` so `super().method()` in the body reads
      -- the base's method return (`class B(A): def func(self): return super().func()` → `A.func`).
      let hints := match (baseMap.find? (·.1 == cls)).bind (·.2[0]?) with
        | some b => hints.insert "super#cls" (.cls b)
        | none => hints
      let env := inferFunction sigs fnEnv hints m
      let ret := returnTypeFromEnv sigs env m
      nextSigs := nextSigs.insert key ret
      -- Also store the method's FUNCTION type under a `#fn`-suffixed key (no Python name has `#`), so a
      -- method REFERENCE `obj.method` (not a call) types as a function → `callable`, distinct from a
      -- data field. `obj.method()` still reads the return type via `key`.
      let methParams := ((params.get? key).getD #[]).toList.drop (if isInstanceMethod m then 1 else 0)
      nextSigs := nextSigs.insert s!"{key}#fn" (.fn methParams ret)
      nextParams := refineFrom nextParams (collectCalls sigs env pnames m)
      nextParams := refineFrom nextParams (collectMethodCalls sigs env classNames methodSelf pnames m)
    -- Module top-level call sites (outside any def), typed under `fnEnv` PLUS the module-level
    -- variable types (`a = A()` ⇒ `a : A`), so a constructor arg that is a class instance refines the
    -- callee's param: `b = B(a)` teaches `B.__init__`'s `a : A`, hence `self.a : A`, hence
    -- `self.a.func()` resolves the cross-class method.
    let moduleEnv := (topLevelStmts module).foldl (applyStmt sigs) fnEnv
    for stmt in topLevelStmts module do
      nextParams := refineFrom nextParams (collectCalls sigs moduleEnv pnames stmt)
      nextParams := refineFrom nextParams (collectMethodCalls sigs moduleEnv classNames methodSelf pnames stmt)
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

/-- Benchmark-only: stamp `_bench_ty` on a target — a Name from its `globals` type, or a tuple/list
target by distributing the value type `ty` over its leaves (nested unpack included). Codegen never
reads `_bench_ty`, so this is inert for translation. -/
partial def stampBenchTarget (globals : Env) (ty : PyType) : Json → Json
  | t =>
    match nodeTypeOf t with
    | some "Name" =>
        match ((nameId? t).bind globals.get?).bind (fun gt => toAnnotation? (containerFillAny gt)) with
        | some ann => t.setObjVal! "_bench_ty" ann
        | none => match toAnnotation? (containerFillAny ty) with
                  | some ann => t.setObjVal! "_bench_ty" ann
                  | none => t
    | some "Starred" =>
        match getField t "value" with
        | some inner => t.setObjVal! "value" (stampBenchTarget globals (.list ty.elemType) inner)
        | none => t
    | some "Tuple" | some "List" =>
        match t.getObjValAs? (Array Json) "elts" with
        | .ok elts =>
            let elemTypes : Nat → PyType := match ty with
              | .tuple es => fun i => es[i]?.getD .unknown
              | _ => fun _ => ty.elemType
            t.setObjVal! "elts" (Json.arr ((Array.range elts.size).map fun i =>
              stampBenchTarget globals (elemTypes i) elts[i]!))
        | _ => t
    | _ => t

-- Benchmark-only: stamp `_bench_ty` on the targets inside a module-level BLOCK body (a `for`/`while`/
-- `if` at module scope), threading the env sequentially so a body-local variable (`for y in xs: z = y`)
-- and the loop target itself are typed. Codegen never reads `_bench_ty`, so this is inert.
mutual
partial def stampBenchInner (sigs : Sigs) (env : Env) (s : Json) : Json :=
  -- Stamp comprehension targets in a top-level comprehension (`ls = [f(a) for a in range(10)]` binds
  -- `a : int`); function-body comprehensions get this in `stampFunction`, module-level ones need it here.
  let s := stampCompTargets sigs env s
  let s := match nodeTypeOf s with
    | some "Assign" | some "AnnAssign" | some "AugAssign" | some "For" =>
        match getField s "target" with
        | some t =>
            let valTy := match nodeTypeOf s with
              | some "For" => (getField s "iter").elim .unknown (fun it => (typeOfExpr sigs env it).elemType)
              | _ => (getField s "value").elim .unknown (typeOfExpr sigs env)
            s.setObjVal! "target" (stampBenchTarget env valTy t)
        | none => s
    | _ => s
  match nodeTypeOf s with
  | some "For" =>
      let bodyEnv := match getField s "target", getField s "iter" with
        | some tg, some it => bindTargetType env tg (typeOfExpr sigs env it).elemType
        | _, _ => env
      let s := match s.getObjValAs? (Array Json) "body" with
        | .ok b => s.setObjVal! "body" (Json.arr (stampBenchBody sigs bodyEnv b)) | _ => s
      match s.getObjValAs? (Array Json) "orelse" with
      | .ok b => s.setObjVal! "orelse" (Json.arr (stampBenchBody sigs env b)) | _ => s
  | some "While" | some "If" =>
      let s := match s.getObjValAs? (Array Json) "body" with
        | .ok b => s.setObjVal! "body" (Json.arr (stampBenchBody sigs env b)) | _ => s
      match s.getObjValAs? (Array Json) "orelse" with
      | .ok b => s.setObjVal! "orelse" (Json.arr (stampBenchBody sigs env b)) | _ => s
  | _ => s

/-- Stamp a block's statements in order, threading the env via `applyStmt` so later statements see
earlier assignments (and the loop/block context). -/
partial def stampBenchBody (sigs : Sigs) (env : Env) (stmts : Array Json) : Array Json := Id.run do
  let mut e := env
  let mut out := #[]
  for s in stmts do
    let s := stampBenchInner sigs e s
    out := out.push s
    e := applyStmt sigs e s
  return out
end

/-- Stamp `_ty` across one top-level node, resolving calls with `sigs` and seeding each function's
unannotated params from `params`. The driver sends one statement per request; a `FunctionDef`, a
`ClassDef` (each method) or a `Module` (a mutual group) is stamped, anything else is unchanged. -/
partial def stampNodeWith (sigs : Sigs) (params : ParamSigs) (globals : Env) (s : Json) : Json :=
  -- Seed a function with module-level globals, minus any name its own parameters shadow (params win).
  let outerFor (fn : Json) : Env := (paramNames fn).foldl (·.erase ·) globals
  match nodeTypeOf s with
  | some "FunctionDef" => stampFunction sigs (outerFor s) (hintsFor params s) s
  | some "ClassDef" =>
      let cls := (s.getObjValAs? String "name").toOption.getD ""
      let s := if cls.isEmpty then s else stampClassFields sigs cls s
      -- A class keeps its methods under "methods"; older nodes use "body". Each method's params are
      -- keyed `"Class.method"` in `params` (from call-site inference), and `self : .cls Class` seeds
      -- the outer env so `self.field`/`self.method(...)` resolve.
      #["methods", "body"].foldl (fun s key =>
        match s.getObjValAs? (Array Json) key with
        | .ok ms => s.setObjVal! key (Json.arr (ms.map fun m =>
            if nodeTypeOf m == some "FunctionDef" then
              let mn := (m.getObjValAs? String "name").toOption.getD ""
              let outer := if isInstanceMethod m then (outerFor m).insert "self" (.cls cls) else outerFor m
              let stamped := stampFunction sigs outer (hintsForKey params m s!"{cls}.{mn}") m
              -- Method return types live in `sigs` under the qualified `Class.method` key, which
              -- stampFunction's bare-name lookup misses; fill `_ret_ty` here when unstamped/unboxed.
              if (getField stamped "_ret_ty").isNone && (getField stamped "_box_return").isNone then
                match (sigs.get? s!"{cls}.{mn}").bind (fun t => toAnnotation? (containerFillAny t)) with
                | some ann => stamped.setObjVal! "_ret_ty" ann
                | none => stamped
              else stamped
            else m))
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
      -- whose value-type ascriptions would perturb byte-identical value-mode output.
      if (s.getObjValAs? Bool "is_main_guard").toOption == some true then
        let genv := inferFunction sigs globals {} s
        let stampBlock (key : String) (s : Json) : Json :=
          match s.getObjValAs? (Array Json) key with
          | .ok body => s.setObjVal! key (Json.arr (body.map (stampUnpackShapes sigs genv)))
          | _ => s
        stampBlock "orelse" (stampBlock "body" s)
      -- A non-guard module-level `if`: stamp body/orelse targets so a branch-local var (`if c: z=1
      -- else: z=2`) is typed (benchmark-only).
      else stampBenchInner sigs globals s
  | some "Assign" | some "AnnAssign" | some "AugAssign" =>
      -- Benchmark-only: stamp a module-level target's inferred type as `_bench_ty` (codegen ignores
      -- it) so the harness sees top-level variable inferences. Never writes `_ty`, so byte-identical
      -- value-mode codegen is unperturbed. A tuple/list target distributes the value's type over its
      -- leaves (nested unpack included), mirroring `bindTargetType`.
      match getField s "target" with
      | some t =>
          -- The type a Name leaf gets: its own `globals` type (flow-insensitive final), which for a
          -- unique unpack target is exactly what the value distributes.
          let valTy := (getField s "value").elim .unknown (typeOfExpr sigs globals)
          s.setObjVal! "target" (stampBenchTarget globals valTy t)
      | none => s
  -- A module-level `for`/`while` (non-guard `if` reaches here too): stamp the target AND recurse into
  -- the body, threading the loop/block env so body-local variables are typed (benchmark-only).
  | some "For" | some "While" => stampBenchInner sigs globals s
  | _ => s

/-- Intraprocedural stamping of a single node (no cross-function info). Used per-request as a
fallback; `inferModule` supersedes it when the whole module is available. -/
partial def stampNode (s : Json) : Json := stampNodeWith {} {} {} s

/-- Every plain-`Name` decorator applied anywhere in the module (`@dec`, including inside nested
defs). A function used as a decorator receives the decorated object as its first argument. -/
partial def collectDecoratorNames : Json → List String
  | json =>
    let here := if nodeTypeOf json == some "FunctionDef" || nodeTypeOf json == some "ClassDef"
      then (decoratorNamesOf json).toList else []
    here ++ (match json with
      | .arr xs => xs.toList.flatMap collectDecoratorNames
      | .obj fs => fs.toList.flatMap (fun (_, v) => collectDecoratorNames v)
      | _ => [])

/-- Benchmark-only: a function used as `@dec` takes the decorated function/class as its first
argument, so that param is `callable` (a `_bench_ty` read-out — its precise signature is unknown, so
it is not a real `_ty`). Stamps every FunctionDef named in `decoNames`, at any nesting depth. -/
partial def stampDecoratorParams (decoNames : List String) : Json → Json
  | json =>
    let json := match json with
      | .arr xs => Json.arr (xs.map (stampDecoratorParams decoNames))
      | .obj fs => Json.mkObj (fs.toList.map (fun (k, v) => (k, stampDecoratorParams decoNames v)))
      | _ => json
    if nodeTypeOf json == some "FunctionDef"
       && ((json.getObjValAs? String "name").toOption.any decoNames.contains) then
      match (getField json "args").bind (·.getObjValAs? (Array Json) "args" |>.toOption) with
      | some argsArr =>
          match argsArr[0]? with
          | some a0 =>
              if (getField a0 "_ty").isNone && (getField a0 "_bench_ty").isNone
                 && ((getField a0 "annotation").all (·.isNull)) then
                let a0' := a0.setObjVal! "_bench_ty"
                  (Json.mkObj [("node_type", Json.str "Name"), ("id", Json.str "Callable")])
                json.setObjVal! "args" (((getField json "args").getD Json.null).setObjVal! "args"
                  (Json.arr (argsArr.set! 0 a0')))
              else json
          | none => json
      | none => json
    else json

/-- Stamp every top-level node of a module with an ALREADY-COMPUTED signature/parameter table. Split
out of `inferModule` so a caller that already ran `collectSigs` (e.g. the repo-level pass, which
collects signatures to a fixpoint first) can reuse them instead of re-running the fixpoint. -/
def stampModuleWith (module : Json) (sigs : Sigs) (params : ParamSigs) : Json :=
  -- Module-level globals (`inf = float('inf')`, config constants) seed every function so a body that
  -- reads a global sees its type — e.g. `f = [[inf]*k for _ in range(n)]` becomes `list[list[float]]`.
  -- Top-level function names are seeded as their `.fn` value type so a `g = some_func` reference (a
  -- function value) reads as `callable`; `topLevelStmts` drops the defs themselves.
  let fnSeed : Env := (topFunctions module).foldl (fun e fn =>
    match fn.getObjValAs? String "name" with
    | .ok nm =>
        let sig := match functionSignatureType fn with
          | .fn as _ => .fn as ((sigs.get? nm).getD .unknown)
          | t => t
        e.insert nm sig
    | _ => e) {}
  let globals : Env := (topLevelStmts module).foldl (applyStmt sigs) fnSeed
  let decoNames := collectDecoratorNames module
  let mark (s : Json) : Json :=
    stampDecoratorParams decoNames ((stampNodeWith sigs params globals s).setObjVal! "_inferred" (Json.bool true))
  match module.getObjValAs? (Array Json) "body" with
  | .ok body => module.setObjVal! "body" (Json.arr (body.map mark))
  | _ => mark module

/-- Whole-module inference: co-evolve return and parameter types to a fixpoint, then stamp each
top-level node with that knowledge. This is what the `inferTypes` backend task runs. -/
def inferModule (module : Json) (seedSigs : Sigs := {}) (seedParams : ParamSigs := {}) : Json :=
  let (sigs, params) := collectSigs module seedSigs seedParams
  stampModuleWith module sigs params


end TypeInfer
