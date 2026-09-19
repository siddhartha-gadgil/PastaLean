import TypeInfer.Diagnostics.Basic
import TypeInfer.Annotation
import TypeInfer.Solve.Fixpoint

/-!
# The checking pass — reading verdicts off an already-stamped module

Inference writes `_ty` / `_ret_ty` stamps; the SOURCE annotation fields (`annotation`, `returns`)
survive the pipeline untouched next to them. So checking needs no second analysis: it walks the
stamped IR and, at every slot that carries BOTH a written annotation and an inferred type, asks
`checkAnnotation` whether the two are consistent. Unannotated parameters get the other half —
`checkUses` over each use site's evidence, which reports the pairs of uses no single type satisfies.

Both are decided by machinery proved in `TypeInfer.Theorem.Requirements`: `checkAnnotation_refl`
(never flags a slot against its own type) and `hasType_commit` (a committed requirement really is
satisfied by every use). The pass is total — an unparseable annotation reads back as `unknown`, which
by `checkAnnotation_unknown` is silently gradual rather than an error.
-/

namespace TypeInfer

open Lean

/-- A present, non-null field. -/
private def liveField? (j : Json) (k : String) : Option Json :=
  match getField j k with
  | some v => if v.isNull then Option.none else some v
  | Option.none => Option.none

/-- The source position the front end stamped on a node (`_line`/`_col`), `(0, 0)` when it carried
none — a node synthesised by a pre-pass, or one inlined from another file. -/
private def posOf (j : Json) : Nat × Nat :=
  ((j.getObjValAs? Nat "_line").toOption.getD 0, (j.getObjValAs? Nat "_col").toOption.getD 0)

/-- Stamp a node's position onto every diagnostic that does not already carry one. -/
private def atNode (j : Json) (ds : Array Diagnostic) : Array Diagnostic :=
  let (l, c) := posOf j
  if l == 0 then ds else ds.map (Diagnostic.at l c)

/-- Evidence an annotation may be checked against DIRECTLY. Scalar evidence names the type its use
demands (`p.isalpha()` ⇒ `str`, `p << 1` ⇒ `int`), and `consistent` already lets Python's numeric
tower through, so `x: float` used as `x + 1` is not flagged. Container evidence is excluded: the
element rules are list-biased (`p[i] % 2` reads as `list[int]`), which is a fine JOIN contribution but
would false-positive against a `dict` or `str` annotation that indexes just as legally. -/
private def isScalarEvidence : PyType → Bool
  | .int | .bool | .float | .str | .none => true
  | _ => false

/-- An element type a `str` can actually yield. Indexing or iterating a string gives strings, so
`list[str]` evidence is exactly what a genuine `str` slot produces under the list-biased rules. -/
private def strElement : PyType → Bool
  | .str | .unknown | .any => true
  | _ => false

/-- Container evidence a SCALAR annotation may be checked against. `p.append(q)` or `p[i] + 1` says
the slot is a container, which `int`/`float`/`bool`/`None` admit no operation of. `str` is the one
scalar that indexes and iterates, so it is accused only on a container a string could never produce
(`list[int]`, `dict[…]`) — never on `list[str]`, which is just its own characters read back. -/
private def checkableContainer : PyType → PyType → Bool
  | .str, .list e | .str, .set e => !strElement e
  | .str, .dict _ _ => true
  | .str, _ => false
  | _, .list _ | _, .set _ | _, .dict _ _ | _, .tuple _ => true
  | _, _ => false

/-- Does the body use `name` as a CONTAINER — index it, iterate it, take its `len`, or test membership
in it? A number has no such operation at all, so any one of these refutes an `int`/`float`/`bool`/`None`
annotation outright, with no need for the evidence rules to name a specific container type. `str` is
excluded by the caller: it indexes and iterates like a sequence. -/
private partial def usedAsContainer (name : String) (json : Json) : Bool :=
  -- A nested `def` taking a parameter of the same name binds a DIFFERENT variable; its uses say
  -- nothing about this one.
  if nodeTypeOf json == some "FunctionDef" && (paramNames json).contains name then false else
  let isN (o : Option Json) : Bool := o.bind nameId? == some name
  let iterOf (j : Json) : Bool := isN (getField j "iter")
  let here : Bool :=
    match nodeTypeOf json with
    | some "Subscript" => isN (getField json "value")
    | some "For" | some "comprehension" => iterOf json
    | some "ListComp" | some "SetComp" | some "DictComp" | some "GeneratorExp" =>
        ((json.getObjValAs? (Array Json) "generators").toOption.getD #[]).any iterOf
    | some "Compare" =>
        ["in", "notin"].contains ((json.getObjValAs? String "op").toOption.getD "")
          && isN (getField json "right")
    | some "Call" | some "Range" =>
        let args := (json.getObjValAs? (Array Json) "args").toOption.getD #[]
        match (getField json "func").bind nameId? with
        | some fn =>
            ["len", "sorted", "enumerate", "reversed", "list", "set", "tuple", "sum"].contains fn
              && args.size == 1 && isN args[0]?
        | _ => false
    | _ => false
  here || (match json with
    | .arr xs => xs.any (usedAsContainer name)
    | .obj fs => fs.toList.any (fun (_, v) => usedAsContainer name v)
    | _ => false)

/-- Every LOCAL whose inferred type inference already wrote as a `_ty` stamp on its binding target.
Supplied to `usageEvidence` as its `known` env, which is what lets an ordered comparison anchor:
`while i <= n` with `i : int` says `n` is an `int`, since Python 3 refuses to order an `int` against a
`str`. Anchoring on a stamp cannot manufacture a false accusation — a local whose type came FROM the
annotation agrees with it by construction. -/
private partial def localStamps (json : Json) : Env :=
  let here : List (String × PyType) :=
    match nodeTypeOf json with
    | some "Assign" | some "AnnAssign" | some "For" | some "AugAssign" =>
        match (liveField? json "target").bind nameId?,
              (liveField? json "target").bind (liveField? · "_ty") with
        | some n, some t => [(n, ofAnnotation t)]
        | _, _ => []
    | _ => []
  let sub : List (String × PyType) := match json with
    | .arr xs => xs.toList.flatMap (fun x => (localStamps x).toList)
    | .obj fs => fs.toList.flatMap (fun (_, v) => (localStamps v).toList)
    | _ => []
  -- A name bound at two different types joins, and `usageEvidence` only anchors on a scalar, so a
  -- retyped local widens itself out of the anchor set rather than picking one of its types.
  (here ++ sub).foldl (fun m (k, v) => m.insert k ((m.get? k |>.getD v).join v)) {}

/-- Evidence a USE-CONFLICT may be built from. Container and callable evidence is excluded: the
element rules are list-biased (indexing a `str` reads back as `list[str]`, so a string parameter
contradicts itself), and an unannotated slot handed a `dict` in one call and a list of pairs in
another is Python's own idiom rather than a contradiction. `None` goes with them — `def f(x=None)`
guarded before use is the Optional idiom. What is left is a clash between two committed scalars,
`str` against `int`, which no type satisfies in any dialect. -/
private def isConflictEvidence : PyType → Bool
  | .int | .bool | .float | .str => true
  | _ => false

/-- One `arg` node's verdicts. An ANNOTATED parameter is checked against its body uses rather than
against its own `_ty` stamp — inference seeds the stamp FROM the annotation, so comparing the two can
only ever agree. The uses are the independent evidence, which is what makes this a check and not a
tautology. -/
private def diagnoseArg (fnParams : Std.HashMap String (Array PyType)) (scope : String)
    (body : Json) (locals : Env) (arg : Json) : Array Diagnostic :=
  let name := (arg.getObjValAs? String "arg").toOption.getD ""
  if name.isEmpty || name == "self" || name == "cls" then #[] else
  let evidence := usageEvidence fnParams (locals.erase name) 1 name body
  atNode arg <| match liveField? arg "annotation" with
  | some ann =>
      let a := ofAnnotation ann
      -- Both sides must be scalar. A class-shaped annotation is not necessarily a class: an
      -- unresolved alias (`_TYPE_TIMEOUT = Union[float, None]`) reads back as `cls`, and accusing it
      -- of contradicting an `int` use would be reporting our own missing alias table as a bug.
      if isScalarEvidence a then
        let uses := (evidence.filter (fun e => isScalarEvidence e || checkableContainer a e)).filterMap
          (checkAnnotation scope name a) |>.take 1 |>.toArray
        -- A numeric annotation has no container operations at all, so a single indexing/iteration is
        -- decisive even when no rule can name the container's element type.
        if !uses.isEmpty then uses
        else if a != .str && usedAsContainer name body then
          (checkAnnotation scope name a (.list .unknown)).toArray
        else #[]
      else #[]
  -- No annotation to check against, so the only available judgment is whether the uses AGREE.
  | Option.none => (checkUses scope name (evidence.filter isConflictEvidence)).2.toArray

/-- Erase every declared RETURN type. Inference seeds a function's return from its `-> T`, so an
annotation checked against the resulting stamp can only ever agree; re-inferring the stripped program
is what makes the body's answer independent evidence, and turns the comparison into a real check.

Parameter annotations deliberately stay: a return's claim is checked against what the body computes
GIVEN its declared inputs (`def total(a: int, b: int) -> str: return a + b` is an error precisely
because `a`/`b` are `int`). Parameters get their own independent evidence from `usageEvidence`, which
never consults a stamp. -/
partial def stripAnnotations (json : Json) : Json :=
  match json with
  | .arr xs => .arr (xs.map stripAnnotations)
  | .obj fs =>
      let drop : List String := match (json.getObjValAs? String "node_type").toOption with
        | some "FunctionDef" | some "AsyncFunctionDef" => ["returns"]
        | _ => []
      Json.mkObj (fs.toList.filterMap (fun (k, v) =>
        if drop.contains k then Option.none else some (k, stripAnnotations v)))
  | other => other

/-- Each function's dotted name → the return type inferred for it. -/
partial def returnStamps (scope : String) (json : Json) : Std.HashMap String PyType :=
  let (scope', here) := match nodeTypeOf json with
    | some "FunctionDef" | some "AsyncFunctionDef" =>
        let n := (json.getObjValAs? String "name").toOption.getD ""
        let fq := if scope.isEmpty then n else scope ++ "." ++ n
        let t := ((liveField? json "_ret_ty").orElse (fun _ => liveField? json "_bench_ret_ty")).elim
          PyType.unknown ofAnnotation
        (fq, [(fq, t)])
    -- A class re-scopes too. Without it two `__exit__`s in one module collide on one key, and the
    -- last one wins — so a `-> None` method gets checked against a sibling class's `-> bool` body.
    | some "ClassDef" =>
        let n := (json.getObjValAs? String "name").toOption.getD ""
        (if scope.isEmpty then n else scope ++ "." ++ n, [])
    | _ => (scope, [])
  let sub : List (String × PyType) := match json with
    | .arr xs => xs.toList.flatMap (fun x => (returnStamps scope' x).toList)
    | .obj fs => fs.toList.flatMap (fun (_, v) => (returnStamps scope' v).toList)
    | _ => []
  (here ++ sub).foldl (fun m (k, v) => m.insert k v) {}

/-- Was this function a GENERATOR before the pre-passes ran? `lowerGenerators` materialises `yield`
into a list accumulator, so a `def fixture() -> None:` that yields infers `list[None]` — the
accumulator's type, not a contradiction of what was written. The prologue the lowering prepends is
the marker; `__gen'acc` contains a `'`, so no Python source can have written it. -/
private def isLoweredGenerator (body : Array Json) : Bool :=
  match body[0]? with
  | some st => (getField st "target").bind nameId? == some "__gen'acc"
  | none => false

/-- Every diagnostic in one stamped module. `scope` is the dotted enclosing-function path;
`bareReturns` is the return type each function gets with all annotations stripped. -/
partial def diagnoseNode (fnParams : Std.HashMap String (Array PyType))
    (bareReturns : Std.HashMap String PyType) (scope : String)
    (json : Json) : Array Diagnostic :=
  let here : Array Diagnostic :=
    match nodeTypeOf json with
    | some "FunctionDef" | some "AsyncFunctionDef" =>
        let fnName := (json.getObjValAs? String "name").toOption.getD ""
        let fq := if scope.isEmpty then fnName else scope ++ "." ++ fnName
        let bodyArr := (json.getObjValAs? (Array Json) "body").toOption.getD #[]
        let body := Json.arr bodyArr
        let args := (liveField? json "args").getD Json.null
        let group (k : String) : Array Json := (args.getObjValAs? (Array Json) k).toOption.getD #[]
        let locals := localStamps body
        let params := (group "args" ++ group "posonlyargs" ++ group "kwonlyargs").flatMap
          (diagnoseArg fnParams fq body locals)
        -- Returns are checked only SCALAR-against-SCALAR. A container/class inferred return is not
        -- reliable enough to accuse the annotation with (`list[PyAny]` vs `list[TokenInfo]`, a
        -- subclass returned for an annotated `Self`), and an inferred `None` is what a degraded body
        -- leaves behind rather than a real void — both would be inference gaps reported as program
        -- errors.
        let ret : Array Diagnostic :=
          match liveField? json "returns" with
          | some ann =>
              let a := ofAnnotation ann
              let inferred := if isLoweredGenerator bodyArr then .unknown else bareReturns.getD fq .unknown
              -- A container ANNOTATION is still never accused (`list[PyAny]` vs `list[TokenInfo]`);
              -- a container INFERENCE under a scalar annotation is the other direction, and as
              -- decidable as the parameter case.
              if isScalarEvidence a && inferred != .none
                 && (isScalarEvidence inferred || checkableContainer a inferred) then
                atNode ann ((checkAnnotation fq "<return>" a inferred).toArray)
              else #[]
          | Option.none => #[]
        atNode json (params ++ ret)
    -- `x: T = e` — the annotation is the claim, the VALUE is the evidence. The front end lowers an
    -- annotated assignment that has a value to an `Assign` carrying `_decl_ty` (a bare `AnnAssign`
    -- survives only when there is no value, and has nothing to check). The target's own `_ty` is
    -- seeded FROM the annotation, so comparing the two could only ever agree.
    | some "Assign" =>
        match (liveField? json "target").bind nameId?, liveField? json "_decl_ty" with
        | some n, some ann =>
            let a := ofAnnotation ann
            let v := match liveField? json "value" with
              | some val =>
                  (literalType? val).getD ((liveField? val "_ty").elim PyType.unknown ofAnnotation)
              | Option.none => .unknown
            -- A `None` initialiser is the implicit-Optional idiom (`_argv_ptr: int = None`, filled in
            -- later), not a claim about the slot — and the parameter judgment already declines to
            -- accuse `None` for the same reason, so accusing it here would contradict that.
            if isScalarEvidence a && v != .none && (isScalarEvidence v || checkableContainer a v) then
              atNode json ((checkAnnotation scope n a v).toArray)
            else #[]
        | _, _ => #[]
    | _ => #[]
  -- A nested `def`, or a `class`, re-scopes its children; every other node keeps the current scope.
  -- The class must be in the path for the same reason `returnStamps` needs it — two same-named
  -- methods in one module would otherwise share one key.
  let scope' := match nodeTypeOf json with
    | some "FunctionDef" | some "AsyncFunctionDef" | some "ClassDef" =>
        let n := (json.getObjValAs? String "name").toOption.getD ""
        if scope.isEmpty then n else scope ++ "." ++ n
    | _ => scope
  let sub : Array Diagnostic := match json with
    | .arr xs => xs.flatMap (diagnoseNode fnParams bareReturns scope')
    | .obj fs => (fs.toList.map (fun (_, v) => diagnoseNode fnParams bareReturns scope' v)).foldl (· ++ ·) #[]
    | _ => #[]
  here ++ sub

/-! ### Call sites

The parameter and return checks read a function against its own body; this one reads it against its
CALLERS. A call is the one place a declared type is used rather than described, so `f("x")` against
`def f(n: int)` is an error with no inference involved at all. -/

/-- Contains no `?` and no `Any`, at any depth — so a literal's type is a complete claim and a
mismatch against it is a real one. `[]` (`list[?]`) and `{}` are excluded by this. -/
private partial def fullyKnown : PyType → Bool
  | .unknown | .any => false
  | .list e | .set e | .opt e => fullyKnown e
  | .dict k v => fullyKnown k && fullyKnown v
  | .tuple es => es.all fullyKnown
  | .fn as r => as.all fullyKnown && fullyKnown r
  | _ => true

/-- Every callable a bare `f(...)` in this module can resolve to: its name → the declared
`(parameter, type)` list. METHODS are excluded (their calls go through an attribute, which this pass
does not resolve), and so is any name defined twice — two same-named `def`s make the target of a call
ambiguous, and a wrong guess would be a false positive. -/
private partial def callSigs (json : Json) : Std.HashMap String (Option (Array (String × PyType))) :=
  let here : List (String × Option (Array (String × PyType))) :=
    match nodeTypeOf json with
    | some "FunctionDef" | some "AsyncFunctionDef" =>
        let nm := (json.getObjValAs? String "name").toOption.getD ""
        let a := (liveField? json "args").getD Json.null
        let pos := ((a.getObjValAs? (Array Json) "posonlyargs").toOption.getD #[])
          ++ ((a.getObjValAs? (Array Json) "args").toOption.getD #[])
        let vararg := (liveField? a "vararg").isSome || (liveField? a "kwarg").isSome
        let named := pos.map fun p =>
          ((p.getObjValAs? String "arg").toOption.getD "",
            (liveField? p "annotation").elim PyType.unknown ofAnnotation)
        if nm.isEmpty || vararg || named.any (fun (n, _) => n == "self" || n == "cls")
        then [(nm, Option.none)] else [(nm, some named)]
    | _ => []
  let sub : List (String × Option (Array (String × PyType))) := match json with
    | .arr xs => xs.toList.flatMap (fun x => (callSigs x).toList)
    | .obj fs => fs.toList.flatMap (fun (_, v) => (callSigs v).toList)
    | _ => []
  (here ++ sub).foldl (fun m (k, v) => if m.contains k then m.insert k Option.none else m.insert k v) {}

/-- One diagnostic per call argument whose LITERAL type contradicts the parameter's annotation. Only
literals are judged: a `Name` argument would need the caller's environment, and an expression would
need inference, but `f("x")` against `def f(n: int)` needs neither. -/
private partial def diagnoseCalls (sigs : Std.HashMap String (Option (Array (String × PyType))))
    (json : Json) : Array Diagnostic :=
  let here : Array Diagnostic :=
    match nodeTypeOf json with
    | some "Call" =>
        atNode json <| match (liveField? json "func").bind nameId? |>.bind sigs.get? |>.join with
        | some named =>
            let fn := ((liveField? json "func").bind nameId?).getD ""
            let args := (json.getObjValAs? (Array Json) "args").toOption.getD #[]
            if args.any (nodeTypeOf · == some "Starred") || args.size > named.size then #[] else
            (Array.range args.size).filterMap fun i =>
              match literalType? args[i]!, named[i]? with
              | some t, some (pname, ptype) =>
                  if fullyKnown t && fullyKnown ptype then
                    let (l, c) := posOf args[i]!
                    (checkAnnotation fn pname ptype t).map (Diagnostic.at l c)
                  else Option.none
              | _, _ => Option.none
        | Option.none => #[]
    | _ => #[]
  let sub : Array Diagnostic := match json with
    | .arr xs => xs.flatMap (diagnoseCalls sigs)
    | .obj fs => (fs.toList.map (fun (_, v) => diagnoseCalls sigs v)).foldl (· ++ ·) #[]
    | _ => #[]
  here ++ sub

/-! ### Opaque class names

`ofAnnotation` turns every name it does not recognise into `.cls n`, but only a name this module
DEFINES as a class is really a class. A `TypeVar` (`T = TypeVar("T")`) is a binder, not a type:
`def f(x: list[T], y: list[T])` says the two parameters agree, not that either is a list of some
nominal `T`. An imported name is no better — it may be a type alias, a `typing` special form, or a
class whose constructor accepts what is being passed, and this pass sees none of that. So a
diagnostic naming a class the module does not define is withheld. -/

/-- Class names this module defines outright, the only ones a judgment may name. -/
private partial def localClasses (json : Json) : Std.HashSet String :=
  let here : List String :=
    match nodeTypeOf json with
    | some "ClassDef" => ((json.getObjValAs? String "name").toOption).toList
    | _ => []
  let sub : List String := match json with
    | .arr xs => xs.toList.flatMap (fun x => (localClasses x).toList)
    | .obj fs => fs.toList.flatMap (fun (_, v) => (localClasses v).toList)
    | _ => []
  Std.HashSet.ofList (here ++ sub)

/-- Does this type name a class the module does not define, at any depth? -/
private partial def mentionsOpaque (defined : Std.HashSet String) : PyType → Bool
  | .cls n => !defined.contains n
  | .list e | .set e | .opt e => mentionsOpaque defined e
  | .dict k v => mentionsOpaque defined k || mentionsOpaque defined v
  | .tuple es => es.any (mentionsOpaque defined)
  | .fn as r => as.any (mentionsOpaque defined) || mentionsOpaque defined r
  | _ => false

/-- Check one stamped module. `bareStamped` is the SAME module inferred with every annotation stripped
(see `stripAnnotations`), supplying the independent answer the written annotations are checked
against. -/
def diagnoseModule (stamped bareStamped : Json) : Array Diagnostic :=
  let diags := diagnoseNode (collectFnParams stamped) (returnStamps "" bareStamped) "" stamped
    ++ diagnoseCalls (callSigs stamped) stamped
  let defined := localClasses stamped
  diags.filter fun d => !(mentionsOpaque defined d.expected || mentionsOpaque defined d.actual)

end TypeInfer
