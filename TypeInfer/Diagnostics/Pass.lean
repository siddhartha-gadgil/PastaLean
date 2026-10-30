import TypeInfer.Certificate.Basic
import TypeInfer.Annotation
import TypeInfer.Solve.Fixpoint
import TypeInfer.Diagnostics.Exact

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

**The pass yields `Slot`s, and the diagnostics are read off them** (`diagnoseModule`). Each judgment
site reaches one verdict about one slot, and every judgment here reports at most one diagnostic — the
annotated-parameter check takes the first failing use, and `checkUses` stops at the first
contradiction because `Req` contradiction is absorbing. So a slot and its diagnostic are the same
fact in two shapes, and recording the slot keeps what the old pass threw away: the evidence weighed,
and the verdict on the slots that PASSED. `TypeInfer.certifyModule` is that record; see
`TypeInfer/Certificate.lean`.
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
    | .obj fs => (Exact.visible fs.toList).any (fun (_, v) => usedAsContainer name v)
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
    | .obj fs => (Exact.visible fs.toList).flatMap (fun (_, v) => (localStamps v).toList)
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

/-- May a clash between this slot's uses be REPORTED? Only when at least one of them is an
unambiguous signal — a shift or `~` (int), `ord`/`chr`, or a type-exclusive method.

Two merely *suggestive* uses are not enough, because several of the evidence rules are inference
hints rather than requirements: `x * 2` reads as `int`, yet `str * int` and `list * int` are both
legal Python repetition, and `x == "done"` reads as `str`, yet Python's `==` is total and comparing an
`int` to a string is a legal (always-false) test. Meeting two hints produced a contradiction that the
program did not actually contain — `ch = text[i]; ch == "a"; ch * 2` was reported as a type error on
real code. One decisive signal on either side is what makes the clash real: a value that is genuinely
shifted cannot also be the string the other use wants.

Found by the mypy_primer sweep, and it was never specific to local variables — the same false
positive fires on a parameter, where this judgment has lived all along. -/
private def conflictReportable (name : String) (body : Json) : Bool :=
  decisiveScalarType name body != .unknown

/-- Build one slot: the body uses it weighed, and the verdict reached on them. -/
private def mkSlot (scope name : String) (kind : SlotKind) (pos : Nat × Nat) (judgment : Judgment)
    (reqs : List PyType) (origin : Origin) (verdict : Verdict) : Slot :=
  { scope, name, kind, line := pos.1, col := pos.2, judgment, verdict,
    evidence := reqs.map (fun r => { origin, req := r }) }

/-- The names this function body BINDS, in binding order, not descending into a nested `def` or
`class` (those are visited in their own right and bind their own names). The same four binding forms
`localStamps` reads, minus the stamp. -/
private partial def localTargets (json : Json) : List (String × Nat × Nat) :=
  match nodeTypeOf json with
  | some "FunctionDef" | some "AsyncFunctionDef" | some "ClassDef" => []
  | nt =>
      let at? (n : Option String) : List (String × Nat × Nat) :=
        n.toList.map (fun v => let (l, c) := posOf json; (v, l, c))
      let here : List (String × Nat × Nat) :=
        match nt with
        -- A target carrying `_decl_ty` was written `x: T = e`, and the annotated-local judgment
        -- already covers it against its value. Judging it a second time by its uses would give the
        -- same variable two slots, which is what the validator's grounding rule refuses.
        | some "Assign" =>
            if (liveField? json "_decl_ty").isSome then []
            else at? ((liveField? json "target").bind nameId?)
        | some "AnnAssign" | some "For" | some "AugAssign" =>
            at? ((liveField? json "target").bind nameId?)
        | _ => []
      let sub : List (String × Nat × Nat) := match json with
        | .arr xs => xs.toList.flatMap localTargets
        | .obj fs => (Exact.visible fs.toList).flatMap (fun (_, v) => localTargets v)
        | _ => []
      here ++ sub

/-- One `arg` node's verdict. An ANNOTATED parameter is checked against its body uses rather than
against its own `_ty` stamp — inference seeds the stamp FROM the annotation, so comparing the two can
only ever agree. The uses are the independent evidence, which is what makes this a check and not a
tautology. -/
private def diagnoseArg (fnParams : Std.HashMap String (Array PyType)) (scope : String)
    (body : Json) (locals : Env) (ex : Exact.Ctx) (arg : Json) : Array Slot :=
  let name := (arg.getObjValAs? String "arg").toOption.getD ""
  if name.isEmpty || name == "self" || name == "cls" then #[] else
  let evidence := usageEvidence fnParams (locals.erase name) 1 name body
  let mk := mkSlot scope name .param (posOf arg)
  match liveField? arg "annotation" with
  | some ann =>
      let a := ofAnnotation ann
      -- Both sides must be scalar. A class-shaped annotation is not necessarily a class: an
      -- unresolved alias (`_TYPE_TIMEOUT = Union[float, None]`) reads back as `cls`, and accusing it
      -- of contradicting an `int` use would be reporting our own missing alias table as a bug.
      if isScalarEvidence a then
        -- Exact evidence is already a fact about `a` (see `Exact.lean`), so it skips the filter the
        -- inference hints need.
        let exact := if a != .none && ex.env.contains name then Exact.paramEvidence ex name a body else []
        let weighed := evidence.filter (fun e => isScalarEvidence e || checkableContainer a e) ++ exact
        match weighed.filterMap (checkAnnotation scope name a) with
        | d :: _ => #[mk (.declared a) weighed .bodyUse (.rejects d.expected d.actual)]
        | [] =>
            -- A numeric annotation has no container operations at all, so a single indexing/iteration
            -- is decisive even when no rule can name the container's element type. The synthesised
            -- `list ?` goes into the evidence, so the verdict still replays from what is recorded.
            if a != .str && usedAsContainer name body then
              match checkAnnotation scope name a (.list .unknown) with
              | some d => #[mk (.declared a) (weighed ++ [.list .unknown]) .bodyUse
                              (.rejects d.expected d.actual)]
              | Option.none => #[mk (.declared a) weighed .bodyUse .agrees]
            else #[mk (.declared a) weighed .bodyUse .agrees]
      else #[]
  -- No annotation to check against, so the only available judgment is whether the uses AGREE.
  | Option.none =>
      let reqs := evidence.filter isConflictEvidence
      let (req, diags) := checkUses scope name reqs
      match diags with
      | d :: _ =>
          if conflictReportable name body then
            #[mk .uses reqs .bodyUse (.conflict d.expected d.actual)]
          -- Two suggestive uses that disagree say nothing certain, so the slot is left unjudged
          -- rather than accused.
          else #[]
      | [] =>
          -- No conflict, so the fold is not contradictory and `commit?` answers exactly when some use
          -- constrained the slot.
          match req.commit? with
          | some t => #[mk .uses reqs .bodyUse (.commits t)]
          | Option.none => #[mk .uses reqs .bodyUse .unconstrained]

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
    | .obj fs => (Exact.visible fs.toList).flatMap (fun (_, v) => (returnStamps scope' v).toList)
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

/-- Stamp a node's position onto every slot that does not already carry one. -/
private def atNodeSlots (j : Json) (ss : Array Slot) : Array Slot :=
  let (l, c) := posOf j
  if l == 0 then ss else ss.map (Slot.at l c)

/-- Was this node inlined from ANOTHER file by `resolve_local_imports`? Inference wants those defs —
resolving imports is what lets a call into a sibling module be typed at all — but judging them here
reports another file's code while checking this one: the verdict is a duplicate of the one that file
gets on its own pass, and it carries no usable position. -/
private def isForeign (j : Json) : Bool :=
  (j.getObjValAs? Bool "_foreign").toOption == some true

/-- Is this definition decorated `@no_type_check` (bare or `typing.no_type_check`)? PEP 484: its
annotations — and, on a class, those of everything inside it — are not to be checked. -/
private def noTypeCheck (j : Json) : Bool :=
  ((j.getObjValAs? (Array Json) "decorator_list").toOption.getD #[]).any fun d =>
    nameId? d == some "no_type_check" || (d.getObjValAs? String "attr").toOption == some "no_type_check"

/-- Every judged slot in one stamped module. `scope` is the dotted enclosing-function path;
`bareReturns` is the return type each function gets with all annotations stripped. -/
partial def diagnoseNode (fnParams : Std.HashMap String (Array PyType))
    (bareReturns : Std.HashMap String PyType) (mod : Exact.Module)
    (globals : Std.HashMap String PyType) (ctxs : Std.HashMap String Exact.Ctx) (cur : Option String)
    (scope : String) (json : Json) : Array Slot :=
  if noTypeCheck json then #[] else
  let here : Array Slot :=
    if isForeign json then #[] else
    match nodeTypeOf json with
    | some "FunctionDef" | some "AsyncFunctionDef" =>
        let fnName := (json.getObjValAs? String "name").toOption.getD ""
        let fq := if scope.isEmpty then fnName else scope ++ "." ++ fnName
        let bodyArr := (json.getObjValAs? (Array Json) "body").toOption.getD #[]
        let body := Json.arr bodyArr
        let args := (liveField? json "args").getD Json.null
        let group (k : String) : Array Json := (args.getObjValAs? (Array Json) k).toOption.getD #[]
        let locals := localStamps body
        let ex := ctxs.getD fq (Exact.fnCtx mod globals cur fq json)
        let paramNodes := group "args" ++ group "posonlyargs" ++ group "kwonlyargs"
        let params := paramNodes.flatMap (diagnoseArg fnParams fq body locals ex)
        -- Locals get the judgment an unannotated parameter gets — do the uses agree? — so a variable
        -- used as both a `str` and an `int` is reported wherever it is bound, not only when it came
        -- in as an argument. Recording them is also what makes the certificate cover the whole
        -- function rather than only its boundary.
        let bound := paramNodes.toList.filterMap (fun a => (a.getObjValAs? String "arg").toOption)
        -- First binding wins: a name rebound later is the same slot, and its first binding is where
        -- a reader looks for it.
        let vars := (localTargets body).foldl
          (fun acc (n, l, c) =>
            if n.isEmpty || bound.contains n || acc.any (fun (m, _, _) => m == n) then acc
            else acc ++ [(n, l, c)]) []
        let localSlots : Array Slot := vars.toArray.flatMap fun (n, l, c) =>
          let reqs := (usageEvidence fnParams (locals.erase n) 1 n body).filter isConflictEvidence
          let (req, diags) := checkUses fq n reqs
          let mk := mkSlot fq n .localVariable (l, c) .uses reqs .bodyUse
          match diags with
          | d :: _ =>
              -- Unreportable: the slot is dropped rather than recorded as unconstrained, because its
              -- evidence really does conflict and a certificate claiming otherwise would not replay.
              if conflictReportable n body then #[mk (.conflict d.expected d.actual)]
              else #[]
          | [] => match req.commit? with
                  | some t => #[mk (.commits t)]
                  | Option.none => #[mk .unconstrained]
        -- Returns are checked only SCALAR-against-SCALAR. A container/class inferred return is not
        -- reliable enough to accuse the annotation with (`list[PyAny]` vs `list[TokenInfo]`, a
        -- subclass returned for an annotated `Self`), and an inferred `None` is what a degraded body
        -- leaves behind rather than a real void — both would be inference gaps reported as program
        -- errors.
        let ret : Array Slot :=
          match liveField? json "returns" with
          | some ann =>
              let a := ofAnnotation ann
              let gen := isLoweredGenerator bodyArr
              let inferred := if gen then .unknown else bareReturns.getD fq .unknown
              -- A container ANNOTATION is still never accused (`list[PyAny]` vs `list[TokenInfo]`);
              -- a container INFERENCE under a scalar annotation is the other direction, and as
              -- decidable as the parameter case.
              let usable (t : PyType) : Bool :=
                t != .none && (isScalarEvidence t || checkableContainer a t)
              -- Each `return e` whose type is exact is evidence on its own: one ill-typed return is an
              -- error whatever the others return.
              let exactRets :=
                if gen || !Exact.concreteAnnotation (Exact.classNames mod) ann then []
                else (Exact.returnTypes ex body).filter usable
              let ev := (if usable inferred then [inferred] else []) ++ exactRets
              if isScalarEvidence a && !ev.isEmpty then
                let mk := mkSlot fq "<return>" .returnType (posOf ann) (.declared a) ev .returnBody
                atNodeSlots ann #[match ev.filterMap (checkAnnotation fq "<return>" a) with
                                  | d :: _ => mk (.rejects d.expected d.actual)
                                  | [] => mk .agrees]
              else #[]
          | Option.none => #[]
        -- `self.f = v` against the type the class declares for `f` (in its body or as
        -- `self.f: T = …`), keyed under the declaring class.
        let fieldSlots : Array Slot :=
          match cur with
          | Option.none => #[]
          | some cls =>
              if !ex.selfFree then #[] else
              (flatStmts bodyArr.toList).toArray.filterMap fun st => do
                guard (nodeTypeOf st == some "Assign")
                let tgt ← liveField? st "target"
                guard (nodeTypeOf tgt == some "Attribute" && (liveField? tgt "value").bind nameId? == some "self")
                let f ← (tgt.getObjValAs? String "attr").toOption
                let (owner, ann) ← Exact.fieldDecl? mod cls f
                guard (Exact.concreteAnnotation (Exact.classNames mod) ann)
                let a := ofAnnotation ann
                guard (isScalarEvidence a && a != .none)
                let v ← (liveField? st "value").bind (Exact.exactType? ex)
                guard (v != .none && (isScalarEvidence v || checkableContainer a v))
                let slot := "self." ++ f
                let mk := mkSlot owner slot .annotatedLocal (posOf st) (.declared a) [v] .valueFlow
                some (match checkAnnotation owner slot a v with
                      | some d => mk (.rejects d.expected d.actual)
                      | Option.none => mk .agrees)
        atNodeSlots json (params ++ localSlots ++ ret ++ fieldSlots)
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
              let mk := mkSlot scope n .annotatedLocal (posOf json) (.declared a) [v] .valueFlow
              atNodeSlots json #[match checkAnnotation scope n a v with
                                 | some d => mk (.rejects d.expected d.actual)
                                 | Option.none => mk .agrees]
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
  let cur' := if nodeTypeOf json == some "ClassDef" then (json.getObjValAs? String "name").toOption else cur
  let sub : Array Slot := match json with
    | .arr xs => xs.flatMap (diagnoseNode fnParams bareReturns mod globals ctxs cur' scope')
    | .obj fs => ((Exact.visible fs.toList).map (fun (_, v) => diagnoseNode fnParams bareReturns mod globals ctxs cur' scope' v)).foldl (· ++ ·) #[]
    | _ => #[]
  here ++ sub

/-! ### Call sites

The parameter and return checks read a function against its own body; this one reads it against its
CALLERS. A call is the one place a declared type is used rather than described, so `f("x")` against
`def f(n: int)` is an error with no inference involved at all. The callee may be a function this
module defines once, a class (its `__init__`), or a method reached through `self`, an instance of a
local class, or the class itself; the argument may be anything `Exact.exactType?` can type. -/

/-- A callee's parameters after the bound receiver: positional ones in order, then keyword-only ones,
each with its annotation (`null` when absent) and whether it defaults to `None` (the implicit-Optional
idiom, which accepts `None` whatever it is annotated). `none` with `*args`/`**kwargs`, which take
arguments this pass does not follow. -/
private def calleeParams (fn : Json) (drop : Bool) :
    Option (Array (String × Json × Bool) × Array (String × Json × Bool)) := do
  let a ← liveField? fn "args"
  if (liveField? a "vararg").isSome || (liveField? a "kwarg").isSome then Option.none
  let grp (k : String) : Array Json := (a.getObjValAs? (Array Json) k).toOption.getD #[]
  let full := grp "posonlyargs" ++ grp "args"
  if drop && full.isEmpty then Option.none
  let defaults := grp "defaults"
  let entry (p : Json) (dflt : Option Json) : String × Json × Bool :=
    ((p.getObjValAs? String "arg").toOption.getD "", (getField p "annotation").getD .null,
     dflt.any isNoneConst)
  let firstDefault := full.size - defaults.size
  let pos := (Array.range full.size).map fun k =>
    entry full[k]! (if k ≥ firstDefault then defaults[k - firstDefault]? else Option.none)
  let kwDefaults := grp "kw_defaults"
  let kwo := (Array.range (grp "kwonlyargs").size).map fun k =>
    entry (grp "kwonlyargs")[k]! kwDefaults[k]?
  return (if drop then pos.extract 1 pos.size else pos, kwo)

/-- Resolve a call's target to `(slot scope, definition, receiver bound?)`. -/
private def resolveCallee (mod : Exact.Module) (ex : Exact.Ctx) (func : Json) :
    Option (String × Json × Bool) :=
  -- Decorators other than `staticmethod`/`classmethod` may replace the function entirely.
  let methodCall (cls m : String) (onInstance : Bool) : Option (String × Json × Bool) := do
    if !(Exact.classNames mod).contains cls then Option.none
    let (owner, fn) ← Exact.methodOf? mod cls m
    let decos := Exact.decoratorNames fn
    if decos.any (fun d => d != "staticmethod" && d != "classmethod") then Option.none
    let isStatic := decos.contains "staticmethod"
    if !onInstance && !isStatic && !decos.contains "classmethod" then Option.none
    return (owner ++ "." ++ m, fn, !isStatic)
  match nodeTypeOf func with
  | some "Name" => do
      let f ← nameId? func
      if let some (fq, fn) := ex.localFns.get? f then
        if (Exact.decoratorNames fn).isEmpty then some (fq, fn, false) else Option.none
      else if ex.shadowed.contains f then Option.none
      else if let some (fq, fn) := mod.functions.get? f then
        if (Exact.decoratorNames fn).isEmpty then some (fq, fn, false) else Option.none
      -- A class whose construction a `__new__` controls does not take `__init__`'s arguments.
      else if mod.classes.contains f && (Exact.methodOf? mod f "__new__").isNone then
        methodCall f "__init__" true
      else Option.none
  | some "Attribute" => do
      let recv ← getField func "value"
      let m ← (func.getObjValAs? String "attr").toOption
      if nameId? recv == some "self" && ex.selfFree then methodCall (← ex.curClass) m true
      else match Exact.exactType? ex recv with
        | some (.cls c) => methodCall c m true
        | _ => do
            let c ← nameId? recv
            if ex.shadowed.contains c || !mod.classes.contains c then Option.none
            methodCall c m false
  | _ => Option.none

/-- Does this type name a class anywhere inside it? -/
private partial def mentionsCls : PyType → Bool
  | .cls _ => true
  | .list e | .set e | .opt e => mentionsCls e
  | .dict k v => mentionsCls k || mentionsCls v
  | .tuple es => es.any mentionsCls
  | .fn as r => as.any mentionsCls || mentionsCls r
  | _ => false

/-- May an argument of type `t` be judged against parameter type `p` by `consistent`? It compares
classes by NAME, so an instance of a subclass would be refused where Python accepts it. A class
argument is judged only when its whole ancestry is local and does not reach the parameter's class;
any other class position is left alone. -/
private def classDecidable (mod : Exact.Module) (p t : PyType) : Bool :=
  if !mentionsCls p && !mentionsCls t then true else
  match t with
  | .cls c =>
      match Exact.ancestry? mod c with
      | Option.none => false
      | some anc =>
          match p with
          | .cls d | .opt (.cls d) => d != c && !anc.contains d
          | q => !mentionsCls q
  | q => !mentionsCls q && (match p with | .cls _ | .opt (.cls _) => true | _ => false)

/-- The judged arguments of one call. -/
private def callSlots (mod : Exact.Module) (ex : Exact.Ctx) (call : Json) : Array Slot := Id.run do
  let some func := liveField? call "func" | return #[]
  let some (scope, fn, drop) := resolveCallee mod ex func | return #[]
  let some (pos, kwo) := calleeParams fn drop | return #[]
  let args := (call.getObjValAs? (Array Json) "args").toOption.getD #[]
  if args.any (nodeTypeOf · == some "Starred") || args.size > pos.size then return #[]
  let kws : List (String × Json) := match getField call "keywords" with
    | some (.obj fs) => fs.toList
    | _ => []
  let pairs := (List.range args.size).map (fun k => (pos[k]!, args[k]!)) ++
    kws.filterMap (fun (k, v) => ((pos ++ kwo).find? (·.1 == k)).map (·, v))
  let classes := Exact.classNames mod
  return pairs.toArray.filterMap fun ((pname, ann, noneDefault), arg) => do
    guard (!ann.isNull && Exact.concreteAnnotation classes ann)
    let p := ofAnnotation ann
    let t ← Exact.exactType? ex arg
    -- `None` is the implicit-Optional idiom here as everywhere else in the checker.
    guard (t != .unknown && t != .any && t != .none && classDecidable mod p t)
    let origin : Origin :=
      if ["Constant", "List", "Set", "Tuple", "Dict"].contains ((nodeTypeOf arg).getD "") then .callLiteral
      else .callArgument
    let mk := mkSlot scope pname .callArgument (posOf arg) (.declared p) [t] origin
    some (match checkAnnotation scope pname p t with
          | some d => mk (.rejects d.expected d.actual)
          | Option.none => mk .agrees)

/-- Every judged call argument in the module, each in the context of its enclosing function. -/
partial def diagnoseCalls (mod : Exact.Module) (globals : Std.HashMap String PyType)
    (ctxs : Std.HashMap String Exact.Ctx) (scope : String) (ex : Exact.Ctx) (json : Json) : Array Slot :=
  let nt := nodeTypeOf json
  let isComp := ["ListComp", "SetComp", "DictComp", "GeneratorExp"].contains (nt.getD "")
  let exHere := if isComp then Exact.withGenerators ex json else ex
  let here : Array Slot :=
    if isForeign json then #[] else
    if nt == some "Call" then atNodeSlots json (callSlots mod exHere json) else #[]
  let name := (json.getObjValAs? String "name").toOption.getD ""
  let scope' := match nt with
    | some "FunctionDef" | some "AsyncFunctionDef" | some "ClassDef" =>
        if scope.isEmpty then name else scope ++ "." ++ name
    | _ => scope
  let ex' : Exact.Ctx := match nt with
    | some "FunctionDef" | some "AsyncFunctionDef" =>
        ctxs.getD scope' (Exact.fnCtx mod globals ex.curClass scope' json)
    | some "ClassDef" => { mod, curClass := (json.getObjValAs? String "name").toOption }
    | some "Lambda" => Exact.enterScope exHere json
    | _ => exHere
  let sub : Array Slot := match json with
    | .arr xs => xs.flatMap (diagnoseCalls mod globals ctxs scope' ex')
    | .obj fs => ((Exact.visible fs.toList).map (fun (_, v) => diagnoseCalls mod globals ctxs scope' ex' v)).foldl (· ++ ·) #[]
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
    | .obj fs => (Exact.visible fs.toList).flatMap (fun (_, v) => (localClasses v).toList)
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

/-- Every function's exact context, keyed by its dotted path — built once and shared by the body and
call-site passes. -/
partial def fnContexts (mod : Exact.Module) (globals : Std.HashMap String PyType)
    (cur : Option String) (scope : String) (json : Json) : Std.HashMap String Exact.Ctx :=
  let nt := nodeTypeOf json
  let name := (json.getObjValAs? String "name").toOption.getD ""
  let scope' := match nt with
    | some "FunctionDef" | some "AsyncFunctionDef" | some "ClassDef" =>
        if scope.isEmpty then name else scope ++ "." ++ name
    | _ => scope
  let here : List (String × Exact.Ctx) := match nt with
    | some "FunctionDef" | some "AsyncFunctionDef" => [(scope', Exact.fnCtx mod globals cur scope' json)]
    | _ => []
  let cur' := if nt == some "ClassDef" then some name else cur
  let sub : List (String × Exact.Ctx) := match json with
    | .arr xs => xs.toList.flatMap (fun x => (fnContexts mod globals cur' scope' x).toList)
    | .obj fs => (Exact.visible fs.toList).flatMap (fun (_, v) => (fnContexts mod globals cur' scope' v).toList)
    | _ => []
  Std.HashMap.ofList (here ++ sub)

/-- Check one stamped module, as a list of judged slots. `bareStamped` is the SAME module inferred
with every annotation stripped (see `stripAnnotations`), supplying the independent answer the written
annotations are checked against.

The opaque-class rule withholds a slot whose *failure* names a class the module does not define —
exactly the diagnostics the old pass filtered. A slot that PASSED is kept whatever it names: it
accuses nobody, and dropping it would thin the certificate for no gain. -/
def certifySlots (ast stamped bareStamped : Json) : Array Slot :=
  let mod := Exact.withDeclaredFields (Exact.mkModule stamped) ast
  let top := Exact.moduleCtx mod stamped
  let ctxs := fnContexts mod top.env Option.none "" stamped
  let slots := diagnoseNode (collectFnParams stamped) (returnStamps "" bareStamped) mod top.env ctxs Option.none "" stamped
    ++ diagnoseCalls mod top.env ctxs "" top stamped
  let defined := localClasses stamped
  slots.filter fun s =>
    match s.expectedDiagnostic? with
    | some d => !(mentionsOpaque defined d.expected || mentionsOpaque defined d.actual)
    | Option.none => true

/-- Every diagnostic in one stamped module — read off the slots, since each judgment reports at most
one and builds it from the verdict's own two types. -/
def diagnoseModule (ast stamped bareStamped : Json) : Array Diagnostic :=
  (certifySlots ast stamped bareStamped).filterMap Slot.diagnostic?

/-- The full record of one checking run: the program it is about, every slot judged, and the
diagnostics that follow. `ast` is the module as the caller handed it over, before the pre-passes — the
same JSON a validator will be given, so `irHashOf` agrees on both sides. -/
def certifyModule (ast stamped bareStamped : Json) : Cert :=
  let slots := certifySlots ast stamped bareStamped
  let diags := slots.filterMap Slot.diagnostic?
  { version := certVersion, irHash := irHashOf ast, slots := slots.toList,
    diagnostics := diags.toList, ok := diags.isEmpty }

end TypeInfer
