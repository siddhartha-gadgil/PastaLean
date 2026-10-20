import TypeInfer.Certificate.Basic
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
        | .obj fs => fs.toList.flatMap (fun (_, v) => localTargets v)
        | _ => []
      here ++ sub

/-- One `arg` node's verdict. An ANNOTATED parameter is checked against its body uses rather than
against its own `_ty` stamp — inference seeds the stamp FROM the annotation, so comparing the two can
only ever agree. The uses are the independent evidence, which is what makes this a check and not a
tautology. -/
private def diagnoseArg (fnParams : Std.HashMap String (Array PyType)) (scope : String)
    (body : Json) (locals : Env) (arg : Json) : Array Slot :=
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
        let weighed := evidence.filter (fun e => isScalarEvidence e || checkableContainer a e)
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

/-- Every judged slot in one stamped module. `scope` is the dotted enclosing-function path;
`bareReturns` is the return type each function gets with all annotations stripped. -/
partial def diagnoseNode (fnParams : Std.HashMap String (Array PyType))
    (bareReturns : Std.HashMap String PyType) (scope : String)
    (json : Json) : Array Slot :=
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
        let paramNodes := group "args" ++ group "posonlyargs" ++ group "kwonlyargs"
        let params := paramNodes.flatMap (diagnoseArg fnParams fq body locals)
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
              let inferred := if isLoweredGenerator bodyArr then .unknown else bareReturns.getD fq .unknown
              -- A container ANNOTATION is still never accused (`list[PyAny]` vs `list[TokenInfo]`);
              -- a container INFERENCE under a scalar annotation is the other direction, and as
              -- decidable as the parameter case.
              if isScalarEvidence a && inferred != .none
                 && (isScalarEvidence inferred || checkableContainer a inferred) then
                let mk := mkSlot fq "<return>" .returnType (posOf ann) (.declared a) [inferred] .returnBody
                atNodeSlots ann #[match checkAnnotation fq "<return>" a inferred with
                                  | some d => mk (.rejects d.expected d.actual)
                                  | Option.none => mk .agrees]
              else #[]
          | Option.none => #[]
        atNodeSlots json (params ++ localSlots ++ ret)
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
  let sub : Array Slot := match json with
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

/-- One slot per call argument whose LITERAL type is checked against the parameter's annotation. Only
literals are judged: a `Name` argument would need the caller's environment, and an expression would
need inference, but `f("x")` against `def f(n: int)` needs neither. -/
private partial def diagnoseCalls (sigs : Std.HashMap String (Option (Array (String × PyType))))
    (json : Json) : Array Slot :=
  let here : Array Slot :=
    if isForeign json then #[] else
    match nodeTypeOf json with
    | some "Call" =>
        atNodeSlots json <| match (liveField? json "func").bind nameId? |>.bind sigs.get? |>.join with
        | some named =>
            let fn := ((liveField? json "func").bind nameId?).getD ""
            let args := (json.getObjValAs? (Array Json) "args").toOption.getD #[]
            if args.any (nodeTypeOf · == some "Starred") || args.size > named.size then #[] else
            (Array.range args.size).filterMap fun i =>
              match literalType? args[i]!, named[i]? with
              | some t, some (pname, ptype) =>
                  if fullyKnown t && fullyKnown ptype then
                    let mk := mkSlot fn pname .callArgument (posOf args[i]!) (.declared ptype) [t]
                      .callLiteral
                    some (match checkAnnotation fn pname ptype t with
                          | some d => mk (.rejects d.expected d.actual)
                          | Option.none => mk .agrees)
                  else Option.none
              | _, _ => Option.none
        | Option.none => #[]
    | _ => #[]
  let sub : Array Slot := match json with
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

/-- Check one stamped module, as a list of judged slots. `bareStamped` is the SAME module inferred
with every annotation stripped (see `stripAnnotations`), supplying the independent answer the written
annotations are checked against.

The opaque-class rule withholds a slot whose *failure* names a class the module does not define —
exactly the diagnostics the old pass filtered. A slot that PASSED is kept whatever it names: it
accuses nobody, and dropping it would thin the certificate for no gain. -/
def certifySlots (stamped bareStamped : Json) : Array Slot :=
  let slots := diagnoseNode (collectFnParams stamped) (returnStamps "" bareStamped) "" stamped
    ++ diagnoseCalls (callSigs stamped) stamped
  let defined := localClasses stamped
  slots.filter fun s =>
    match s.expectedDiagnostic? with
    | some d => !(mentionsOpaque defined d.expected || mentionsOpaque defined d.actual)
    | Option.none => true

/-- Every diagnostic in one stamped module — read off the slots, since each judgment reports at most
one and builds it from the verdict's own two types. -/
def diagnoseModule (stamped bareStamped : Json) : Array Diagnostic :=
  (certifySlots stamped bareStamped).filterMap Slot.diagnostic?

/-- The full record of one checking run: the program it is about, every slot judged, and the
diagnostics that follow. `ast` is the module as the caller handed it over, before the pre-passes — the
same JSON a validator will be given, so `irHashOf` agrees on both sides. -/
def certifyModule (ast stamped bareStamped : Json) : Cert :=
  let slots := certifySlots stamped bareStamped
  let diags := slots.filterMap Slot.diagnostic?
  { version := certVersion, irHash := irHashOf ast, slots := slots.toList,
    diagnostics := diags.toList, ok := diags.isEmpty }

end TypeInfer
