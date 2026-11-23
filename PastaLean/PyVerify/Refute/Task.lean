import PastaLean.PyVerify.Refute.Tactic
import PastaLean.PyVerify.Refute.Solve
import PastaLean.PyAPI.RunPure

/-!
# The `refute` backend task

Given an elaborated program, search for and cross-check counterexamples in BOTH Lean worlds:

* **provable** — the obligation theorem itself (exact `ℚ`, `List`), certified by the kernel when refuted;
* **runnable** — the checker's `'rn` twin (`Float`, `Array`): the statement `∀ args, pre'rn args → chk'rn args`.

Every witness — found here, or handed in (e.g. by a CPython-side search) — is evaluated in both worlds,
so the Python side can classify agreement and divergence against CPython itself. All values travel as
`PyLit`, placed at each world's own binder types by `litToExpr`.
-/

namespace PastaLean.Refute

open Lean Meta Elab

/-- One obligation, by the names of its Lean artifacts (any may be absent). -/
structure Target where
  id : String
  theorem? : Option Name := none
  provPre? : Option Name := none
  provChk? : Option Name := none
  runPre? : Option Name := none
  runChk? : Option Name := none
  /-- The contract's `raises:` exceptions. -/
  allowed : List String := []

def nameOpt (j : Json) (k : String) : Option Name :=
  match j.getObjValAs? String k with
  | .ok s => if s.isEmpty then none else some s.toName
  | .error _ => none

def Target.ofJson (j : Json) : Target :=
  { id := (j.getObjValAs? String "id").toOption.getD "",
    theorem? := nameOpt j "theorem", provPre? := nameOpt j "provPre", provChk? := nameOpt j "provChk",
    runPre? := nameOpt j "runPre", runChk? := nameOpt j "runChk",
    allowed := (j.getObjValAs? (List String) "raises").toOption.getD [] }

def configOfJson (j : Json) (base : RefuteConfig) : RefuteConfig :=
  let n (k : String) (d : Nat) : Nat := (j.getObjValAs? Nat k).toOption.getD d
  { base with numInst := n "numInst" base.numInst, maxSize := n "maxSize" base.maxSize,
              seed := n "seed" base.seed, timeMs := n "timeMs" base.timeMs,
              perCaseMs := n "perCaseMs" base.perCaseMs, enumDepth := n "enumDepth" base.enumDepth,
              enumMax := n "enumMax" base.enumMax,
              plausible := (j.getObjValAs? Bool "plausible").toOption.getD base.plausible,
              solver := (j.getObjValAs? Bool "solver").toOption.getD base.solver,
              intCap := n "intCap" base.intCap }

/-- A program constant with its universe parameters (if any) set to `0`, ready to evaluate. -/
def constZ (n : Name) : MetaM Expr := do
  let info ← getConstInfo n
  return mkConst n (info.levelParams.map fun _ => levelZero)

/-- A checker's verdict as a `Bool`: a checker of a function that can raise is monadic, and runs from an
empty state (`PyRunPure`); an exception it does not catch (not one its contract's `raises:` allows) is a
violation, recorded like any runtime error so the witness reports its kind. -/
def checkerBool (app : Expr) : MetaM Expr := mkAppM ``PastaLean.runPure #[app]

/-- `∀ args, pre args = true → chk args = true` from a checker (and optional precondition) constant.
Binders are read off the checker's type without unfolding a monadic codomain into more arrows. -/
def checkerStatement (chk : Name) (pre? : Option Name) : MetaM Expr := do
  let chkTy ← inferType (← constZ chk)
  forallTelescope chkTy fun args _ => do
    let concl ← mkEq (← checkerBool (mkAppN (← constZ chk) args)) (toExpr true)
    let body ← match pre? with
      | some pre => mkArrow (← mkEq (← checkerBool (mkAppN (← constZ pre) args)) (toExpr true)) concl
      | none => pure concl
    mkForallFVars args body

/-- The argument types of a checker constant. -/
def checkerArgTypes (chk : Name) : MetaM (Array Expr) := do
  forallTelescope (← inferType (← constZ chk)) fun args _ => args.mapM inferType

/-- Evaluate a closed `Bool` term. -/
unsafe def evalBoolUnsafe (e : Expr) : MetaM Bool := do
  evalExpr Bool (mkConst ``Bool) (← instantiateMVars e)

@[implemented_by evalBoolUnsafe]
opaque evalBool (e : Expr) : MetaM Bool

/-- Set when a judgement outlived its deadline: its thread keeps running, so the backend needs a restart. -/
initialize judgeHung : IO.Ref Bool ← IO.mkRef false

def judgeTimeout : String := "refute: the witness ran past its deadline"

unsafe def evalBoolWithinUnsafe (ms : Nat) (e : Expr) : MetaM Bool := do
  let f ← evalExpr (Unit → Bool) (← mkArrow (mkConst ``Unit) (mkConst ``Bool))
    (mkLambda `_ .default (mkConst ``Unit) (← instantiateMVars e))
  -- the error log is per thread: the evaluating thread's error is carried back to this one
  let t ← IO.asTask (prio := .dedicated) do
    discard <| pyErrorLog.swap none
    let b ← IO.lazyPure f
    return (b, ← pyErrorLog.swap none)
  let start ← IO.monoMsNow
  while !(← IO.hasFinished t) do
    if (← IO.monoMsNow) - start > ms then
      judgeHung.set true
      throwError judgeTimeout
    IO.sleep 2
  match t.get with
  | .ok (b, err) => if err.isSome then pyErrorLog.set err
                    return b
  | .error err => throwError (toString err)

/-- `evalBool`, giving up after `ms` (a witness that loops); a stuck evaluation keeps its thread. -/
@[implemented_by evalBoolWithinUnsafe]
opaque evalBoolWithin (ms : Nat) (e : Expr) : MetaM Bool

/-- What a world says about a witness: does it pass the precondition, does the property hold, the Python
error the evaluation raised (`exc`), and a runtime error hit while the value stayed the logical default
(`panic`, provable twin only). -/
def judgeJson (pass holds : Option Bool) (err : Option String := none) (exc : Option String := none)
    (panic : Option String := none) : Json :=
  Json.mkObj ([("guard", toJson pass), ("holds", toJson holds)] ++
    (match err with | some e => [("error", toJson e)] | none => []) ++
    (match exc with | some e => [("exc", toJson e)] | none => []) ++
    (match panic with | some e => [("panic", toJson e)] | none => []))

/-- A judgement that failed: a witness past its deadline reads `Timeout`, as a hung search's does. -/
def judgeError (e : Exception) : MetaM Json := do
  let msg ← e.toMessageData.toString
  return if msg == judgeTimeout then judgeJson (some true) none none (some "Timeout")
    else judgeJson none none (some msg)

/-- Run `x`, returning the Python error a runtime function hit meanwhile (see `pyErrorLog`). -/
def withPyError (x : MetaM α) : MetaM (α × Option String) := do
  discard <| (pyErrorLog.swap none : IO _)
  let a ← x
  return (a, ← (pyErrorLog.swap none : IO _))

/-- Evaluate a witness against a checker (and precondition) in one world. With `executes` (the runnable
twin) a runtime error is a raise, as under CPython: in the precondition it rejects the input, in the
property it violates it. Otherwise (the provable twin) the logical value stands and the error is noted. -/
def judgeChecker (chk : Name) (pre? : Option Name) (ws : List PyLit) (executes := true)
    (allowed : List String := []) (ms : Nat := 1000) : MetaM Json := do
  try
    let tys ← checkerArgTypes chk
    if tys.size != ws.length then return judgeJson none none (some "arity mismatch")
    let args ← (tys.toList.zip ws).mapM fun (τ, w) => litToExpr τ w
    let (guardOk, gexc) ← withPyError do match pre? with
      | some pre => evalBoolWithin ms (← checkerBool (mkAppN (← constZ pre) args.toArray))
      | none => pure true
    if !guardOk || (executes && gexc.isSome) then return judgeJson (some false) none
    let (holds, exc) ← withPyError do
      evalBoolWithin ms (← checkerBool (mkAppN (← constZ chk) args.toArray))
    if exc.any (errAllowed allowed) then return judgeJson (some true) (some true)
    if executes then return judgeJson (some true) (some (holds && exc.isNone)) none exc
    return judgeJson (some true) (some holds) none none (exc <|> gexc)
  catch e => judgeError e

/-- Evaluate a witness against the obligation theorem (its guards, then its body), by `decide`. -/
def judgeTheorem (thm : Name) (ws : List PyLit) (allowed : List String := []) (ms : Nat := 1000) :
    MetaM Json := do
  try
    let ty ← instantiateMVars (← getConstInfo thm).type
    withObligation ty fun ob => do
      if ob.data.size != ws.length then return judgeJson none none (some "arity mismatch")
      let tys ← ob.data.mapM inferType
      let vals ← (tys.toList.zip ws).mapM fun (τ, w) => litToExpr τ w
      let inst (e : Expr) : Expr := e.replaceFVars ob.data vals.toArray
      for g in ob.guards do
        match ← mkDecideRunnable (inst (← inferType g)) with
        | .error e => return judgeJson none none (some e)
        | .ok d => if !(← evalBoolWithin ms d) then return judgeJson (some false) none
      -- The theorem's own truth: a runtime error inside it is the logical default, noted as `panic`.
      match ← mkDecideRunnable (inst ob.body) with
      | .error e => return judgeJson (some true) none (some e)
      | .ok d =>
        let (holds, exc) ← withPyError (evalBoolWithin ms d)
        if exc.any (errAllowed allowed) then return judgeJson (some true) (some true)
        return judgeJson (some true) (some holds) none none exc
  catch e => judgeError e

def searchJson (o : SearchOutcome) (names : Array (Name × Expr)) (cert : Option String) : MetaM Json := do
  let binders ← names.mapM fun (n, τ) => do
    return Json.mkObj [("name", toJson n.eraseMacroScopes.toString), ("type", toJson (toString (← ppExpr τ)))]
  return o.toJson.mergeObj (Json.mkObj [("binders", Json.arr binders), ("kernel", toJson cert.isSome),
    ("proof", toJson (cert.getD "")),
    ("python", toJson ((o.witness?.getD []).map PyLit.toPyString))])

/-- `x`, with a resource-limit exception (heartbeats, recursion depth) turned into an ordinary error that
`try … catch` handles: one step running out of its budget must not end the whole target. -/
def budgeted {α : Type} (x : TermElabM α) : TermElabM α :=
  tryCatchRuntimeEx x fun e => do throwError (← e.toMessageData.toString)

/-- A judgement that ran out of its budget reads as an evaluation error, like any other failure to judge. -/
def budgetedJudge (x : TermElabM Json) : TermElabM Json :=
  tryCatchRuntimeEx x fun e => do return judgeJson none none (some (← e.toMessageData.toString))

/-- Run one target: both searches, then every witness through both worlds. -/
def runTarget (t : Target) (cfg : RefuteConfig) (extra : List (List PyLit)) : TermElabM Json := do
  let cfg := { cfg with allowed := t.allowed }
  let mut fields : Array (String × Json) := #[("id", toJson t.id)]
  let mut witnesses : Array (String × List PyLit) := #[]
  -- witnesses whose evaluation ran past the per-case deadline: judged `Timeout`, never re-evaluated
  let mut hung : Array (List PyLit) := #[]
  -- where the searches stalled: inputs closest to unreached branches, for `solvePlateau`
  let mut seeds : List (List PyLit) := []
  -- Provable world: the theorem if there is one (certifiable), else the exact-mode checker.
  let provTy? ← match t.theorem?, t.provChk? with
    | some thm, _ => pure (some ((← getConstInfo thm).type, true))
    | none, some chk => pure (some (← checkerStatement chk t.provPre?, false))
    | none, none => pure none
  -- Each world searches on its own: one that cannot be evaluated (e.g. a twin that does not elaborate)
  -- must not stop the other.
  if let some (ty, isThm) := provTy? then
    try
      let ty ← instantiateMVars ty
      let (o, names) ← budgeted (refuteType ty cfg)
      let cert ← match o.status, o.witness? with
        | .refuted, some ws => if isThm && !o.hang then budgeted (certify ty names ws) else pure none
        | _, _ => pure none
      fields := fields.push ("prov", ← searchJson o names cert)
      seeds := seeds ++ o.seeds
      if let some ws := o.witness? then
        witnesses := witnesses.push ("prov", ws)
        if o.hang then hung := hung.push ws
    catch e => fields := fields.push ("prov", Json.mkObj [("error", toJson (← e.toMessageData.toString))])
  -- The solver: `grind` on guards ∧ ¬body. A model is one more witness to judge (and certify); a proof
  -- means no input violates the provable obligation.
  if let some (ty, _) := provTy?.filter (fun _ => cfg.solver) then
    try
      let ty ← instantiateMVars ty
      match ← budgeted (solveObligation ty) with
      | .proved => fields := fields.push ("solver", Json.mkObj [("status", toJson "proved")])
      | .model vals =>
        let names ← obligationBinders ty
        let shown := Json.mkObj (vals.toList.map fun (n, v) => (n.eraseMacroScopes.toString, toJson (toString v)))
        match ← modelWitness names vals with
        | some ws =>
          witnesses := witnesses.push ("grind", ws)
          fields := fields.push ("solver", Json.mkObj [("status", toJson "model"), ("model", shown)])
        | none => fields := fields.push ("solver", Json.mkObj [("status", toJson "model-unusable"), ("model", shown)])
      | .unknown why =>
        fields := fields.push ("solver", Json.mkObj [("status", toJson "unknown"), ("why", toJson (why.take 300))])
    catch e => fields := fields.push ("solver", Json.mkObj [("status", toJson "unknown"),
      ("why", toJson ((← e.toMessageData.toString).take 300))])
  -- Runnable world: the `'rn` checker over its own types (Float, Array).
  if let some chk := t.runChk? then
    try
      let ty ← checkerStatement chk t.runPre?
      let (o, names) ← budgeted (refuteType ty { cfg with errorsFail := true })
      fields := fields.push ("run", ← searchJson o names none)
      seeds := seeds ++ o.seeds
      if let some ws := o.witness? then
        witnesses := witnesses.push ("run", ws)
        if o.hang then hung := hung.push ws
    catch e => fields := fields.push ("run", Json.mkObj [("error", toJson (← e.toMessageData.toString))])
  -- Nothing found: finish the stalled searches by solving for the integer leaves of their closest inputs.
  if !witnesses.any (fun (o, _) => o == "prov" || o == "run") && cfg.solver then
    if let some (ty, _) := provTy? then
      for seed in seeds.eraseDups.take 3 do
        if let some ws ← (try budgeted (solvePlateau (← instantiateMVars ty) seed) catch _ => pure none) then
          if !witnesses.any (·.2 == ws) then witnesses := witnesses.push ("plateau", ws)
  for ws in extra do witnesses := witnesses.push ("given", ws)
  -- Cross-check every witness in both worlds; certify the first one (from any engine) that refutes the
  -- theorem in the provable twin.
  let mut evals : Array Json := #[]
  let mut certified : Array (List PyLit × String) := #[]
  for (origin, ws) in witnesses do
    if hung.contains ws then
      let timeout := Json.mkObj [("guard", toJson true), ("exc", toJson "Timeout")]
      evals := evals.push (Json.mkObj [("origin", toJson origin), ("lits", toJson ws),
        ("python", toJson (ws.map PyLit.toPyString)), ("prov", timeout), ("provChk", timeout), ("run", timeout)])
      continue
    let provChk ← match t.provChk? with
      | some chk => budgetedJudge (judgeChecker chk t.provPre? ws (executes := false) t.allowed cfg.perCaseMs)
      | none => pure Json.null
    let prov ← match t.theorem? with
      | some thm => budgetedJudge (judgeTheorem thm ws t.allowed cfg.perCaseMs)
      | none => pure provChk
    let run ← match t.runChk? with
      | some chk => budgetedJudge (judgeChecker chk t.runPre? ws (allowed := t.allowed) (ms := cfg.perCaseMs))
      | none => pure Json.null
    evals := evals.push (Json.mkObj [("origin", toJson origin), ("lits", toJson ws),
      ("python", toJson (ws.map PyLit.toPyString)), ("prov", prov), ("provChk", provChk), ("run", run)])
    -- A few, so the report can show a certificate for the witness it leads with.
    if certified.size < 3 && (prov.getObjValAs? Bool "guard").toOption == some true
        && (prov.getObjValAs? Bool "holds").toOption == some false then
      if let some thm := t.theorem? then
        let ty ← instantiateMVars (← getConstInfo thm).type
        let names ← obligationBinders ty
        if let some line ← (try budgeted (certify ty names ws) catch _ => pure none) then
          certified := certified.push (ws, line)
  fields := fields.push ("witnesses", Json.arr evals)
  -- No witness violates anything (or loops): let `taste?` try to prove the obligation for every input.
  let violated := evals.any fun e => ["prov", "run"].any fun w =>
    ((e.getObjValD w).getObjValAs? Bool "holds").toOption == some false
      || ((e.getObjValD w).getObjValAs? String "exc").toOption == some "Timeout"
  let solverProved := fields.any fun (k, v) => k == "solver" && (v.getObjValAs? String "status").toOption == some "proved"
  if !violated && !solverProved && cfg.solver then
    if let some (ty, _) := provTy? then
      if ← tasteProves (← instantiateMVars ty) then
        fields := (fields.filter (·.1 != "solver")).push ("solver", Json.mkObj [("status", toJson "proved"), ("by", toJson "taste?")])
  if ← judgeHung.swap false then fields := fields.push ("judgeHang", toJson true)
  fields := fields.push ("certifiedAll", Json.arr (certified.map fun (ws, line) =>
    Json.mkObj [("lits", toJson ws), ("proof", toJson line)]))
  return Json.mkObj fields.toList

/-- The Python class a Lean structure stands for: its last name component, without the runnable twin's
`'rn` suffix. -/
def pyClassName (n : Name) : String :=
  let last := n.getString!
  if last.endsWith "'rn" then (last.dropEnd 3).toString else last

/-- The fields of structure `n` (flattened: inherited ones too) with their types; `none` when a field has
no projection to read its type from. -/
def fieldTypes (n : Name) : MetaM (Array (Name × Option Expr)) := do
  let env ← getEnv
  (getStructureFieldsFlattened env n (includeSubobjectFields := false)).mapM fun f => do
    -- an inherited field's projection belongs to the ancestor that declares it
    let proj? := (findField? env n f).bind (getProjFnForField? env · f)
    return (f, ← proj?.mapM fun p => do forallTelescopeReducing (← getConstInfo p).type fun _ r => pure r)

/-- Structures (user classes) among `e`'s constants, transitively through field types. -/
partial def structuresIn (e : Expr) (acc : NameSet := {}) : MetaM NameSet := do
  let env ← getEnv
  let mut acc := acc
  for c in e.getUsedConstants do
    if acc.contains c || !isStructure env c then continue
    -- program and library classes only, not Lean's own (`String` → `ByteArray` → `BitVec`)
    if !isProgramConst c then continue
    acc := acc.insert c
    for (_, ty?) in ← fieldTypes c do
      if let some ty := ty? then acc ← structuresIn ty acc
  return acc

/-- A `PyArb` instance, as a command, for every structure among the targets' inputs that has none:
built field by field, read back as the Python class with its fields. Self-referential
structures get a depth-bounded generator through `Option S` / `List S` fields. -/
def structInstanceCommands (targets : Array Target) : MetaM (Array String) := do
  let env ← getEnv
  let mut tys : Array Expr := #[]
  for t in targets do
    for n in [t.theorem?, t.provChk?, t.runChk?].filterMap id do
      if let some ci := env.find? n then tys := tys.push ci.type
  let mut structs : NameSet := {}
  for ty in tys do structs ← structuresIn ty structs
  -- dependency order: a structure after those its fields mention, whose instances it uses
  let deps (n : Name) : MetaM (List Name) := do
    let mut ds : NameSet := {}
    for (_, ty?) in ← fieldTypes n do
      if let some ty := ty? then ds ← structuresIn ty ds
    return ds.toList.filter (fun d => d != n && structs.contains d)
  let mut order : Array Name := #[]
  let mut seen : NameSet := {}
  let mut stack : List (Name × Bool) := structs.toList.map (·, false)
  while !stack.isEmpty do
    let (n, expanded) := stack.head!
    stack := stack.tail!
    if expanded then
      if !order.contains n then order := order.push n
    else if !seen.contains n then
      seen := seen.insert n
      stack := (← deps n).map (·, false) ++ [(n, true)] ++ stack
  let mut out := #[]
  for n in order.toList do
    let ci ← getConstInfo n
    if !ci.levelParams.isEmpty || ci.type.isForall then continue
    let existing ← try (some <$> synthInstance (← mkAppM ``PyArb #[mkConst n])) catch _ => pure none
    if existing.isSome then continue
    let ftys ← fieldTypes n
    let fields := ftys.map (·.1)
    -- Each field's shape: plain, or a reference back to the structure as `Option S` / `List S` (a tree,
    -- a linked list); any other self-reference is left without a generator.
    let shapes := ftys.map fun (_, ty?) => ty?.bind fun r =>
      if !r.getUsedConstants.contains n then some "plain"
      else if r.isAppOfArity ``Option 1 && r.appArg!.isConstOf n then some "opt"
      else if r.isAppOfArity ``List 1 && r.appArg!.isConstOf n then some "list"
      else none
    if shapes.any (·.isNone) then continue
    let shapes := shapes.map (·.getD "plain")
    let fs := fields.toList.zip shapes.toList
    let alts := "".intercalate (fields.toList.zipIdx.map fun (f, i) =>
      s!"\n    | {i} => return \{ s with «{f}» := ← PastaLean.Refute.PyArb.mutateField s.«{f}» }")
    let mutate := s!"\n  mutate s := do\n    match (← Plausible.Gen.choose Nat 0 {fields.size - 1} (by omega)).val with{alts}\n    | _ => return s"
    if shapes.all (· == "plain") then
      -- structure-instance notation, not the constructor: a class extending another takes its parent
      -- as one constructor argument, while the flattened fields name every slot
      let gens := ", ".intercalate (fields.toList.map fun f => s!"«{f}» := (← PastaLean.Refute.PyArb.arbField)")
      let lits := ", ".intercalate (fields.toList.map fun f =>
        s!"(\"{f}\", PastaLean.Refute.ToPyLit.toLit s.«{f}»)")
      out := out.push (s!"instance : PastaLean.Refute.PyArb {n} where\n  arb := do return (\{ {gens} } : {n})\n  toLit s := .obj \"{pyClassName n}\" [{lits}]"
        ++ (if fields.isEmpty then "" else mutate))
    else
      -- recursive: a depth-bounded generator and a recursive read-back
      let lits := ", ".intercalate (fs.map fun (f, sh) => match sh with
        | "opt" => s!"(\"{f}\", match s.«{f}» with | some c => {n}.pyLitRec c | none => .none)"
        | "list" => s!"(\"{f}\", .list (s.«{f}».map {n}.pyLitRec))"
        | _ => s!"(\"{f}\", PastaLean.Refute.ToPyLit.toLit s.«{f}»)")
      let gens := ", ".intercalate (fs.map fun (f, sh) => s!"«{f}» := " ++ match sh with
        | "opt" => s!"(← if d == 0 then pure none else do if (← Plausible.Gen.chooseAny Bool) then pure (some (← {n}.pyArbRec (d - 1))) else pure none)"
        | "list" => s!"(← do let k := if d == 0 then 0 else (← Plausible.Gen.choose Nat 0 2 (by omega)).val; (List.range k).mapM fun _ => {n}.pyArbRec (d - 1))"
        | _ => "(← PastaLean.Refute.PyArb.arbField)")
      out := out.push s!"partial def {n}.pyLitRec (s : {n}) : PastaLean.Refute.PyLit := .obj \"{pyClassName n}\" [{lits}]"
      out := out.push s!"partial def {n}.pyArbRec (d : Nat) : Plausible.Gen {n} := do return (\{ {gens} } : {n})"
      out := out.push s!"instance : PastaLean.Refute.PyArb {n} where\n  arb := {n}.pyArbRec 3\n  toLit := {n}.pyLitRec"
  return out

unsafe def evalLitUnsafe (e : Expr) : MetaM PyLit := do
  evalExpr PyLit (mkConst ``PyLit) (← instantiateMVars e)

@[implemented_by evalLitUnsafe]
opaque evalLit (e : Expr) : MetaM PyLit

/-- `fn` applied to one input, as a `PyLit` (an `Id` result is unwrapped). -/
def evalAt (fn : Name) (ws : List PyLit) : MetaM Json := do
  try
    forallTelescopeReducing (← inferType (← constZ fn)) fun xs res => do
      if xs.size != ws.length then return Json.mkObj [("error", toJson "arity mismatch")]
      let args ← (← xs.mapM inferType).toList.zip ws |>.mapM fun (τ, w) => litToExpr τ w
      let mut call := mkAppN (← constZ fn) args.toArray
      let mut τ := res.replaceFVars xs args.toArray
      if τ.isAppOfArity ``Id 1 then
        call ← mkAppM ``Id.run #[call]; τ := τ.appArg!
      let lit ← mkAppOptM ``ToPyLit.toLit #[τ, none, call]
      let (v, exc) ← withPyError (evalLit lit)
      return match exc with
        | some e => Json.mkObj [("exc", toJson e)]
        | none => Json.mkObj [("value", toJson v)]
  catch e => return Json.mkObj [("error", toJson (← e.toMessageData.toString))]

/-- `evals: [{id, fn, inputs}]`: each function's value at each input. -/
def runEvals (json : Json) : MetaM Json := do
  let reqs := (json.getObjValAs? (Array Json) "evals").toOption.getD #[]
  let out ← reqs.mapM fun r => do
    let some fn := nameOpt r "fn" | return Json.mkObj [("error", toJson "missing fn")]
    let inputs := ((r.getObjValAs? (Array Json) "inputs").toOption.getD #[]).toList.filterMap fun ls =>
      ((ls.getArr?).toOption.bind fun a => (a.toList.mapM PyLit.fromJson?).toOption)
    if !(← getEnv).contains fn then
      return Json.mkObj [("id", r.getObjValD "id"), ("error", toJson s!"unknown constant {fn}")]
    return Json.mkObj [("id", r.getObjValD "id"), ("values", Json.arr (← inputs.toArray.mapM (evalAt fn)))]
  return Json.arr out

unsafe def evalIOUnsafe (fn : Name) : MetaM (IO Unit) := do
  evalExpr (IO Unit) (mkApp (mkConst ``IO) (mkConst ``Unit)) (← constZ fn)

@[implemented_by evalIOUnsafe]
opaque evalIO (fn : Name) : MetaM (IO Unit)

/-- Run `act` with `input` as its stdin; what it printed, and the error it ended with. Streams are
per-thread, so this must run on the thread that runs `act`. -/
def runWithStdin (act : IO Unit) (input : String) : IO (String × Option String) := do
  let inRef ← IO.mkRef ({ data := input.toUTF8 } : IO.FS.Stream.Buffer)
  let outRef ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let errRef ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let oldIn ← IO.setStdin (IO.FS.Stream.ofBuffer inRef)
  let oldOut ← IO.setStdout (IO.FS.Stream.ofBuffer outRef)
  let oldErr ← IO.setStderr (IO.FS.Stream.ofBuffer errRef)
  discard <| pyErrorLog.swap none
  let r ← act.toBaseIO
  let pyErr ← pyErrorLog.swap none
  discard <| IO.setStdin oldIn
  discard <| IO.setStdout oldOut
  discard <| IO.setStderr oldErr
  let out := String.fromUTF8? (← outRef.get).data |>.getD ""
  -- A runtime error is a compiled panic that let the program go on; Python would have stopped there.
  return (out, match r, pyErr with
    | .error e, _ => some (toString e)
    | .ok _, some k => some s!"{k} (raised as a runtime panic; the program continued)"
    | .ok _, none => none)

/-- Each input through `act` on its own thread, under a deadline. After an overrun the thread is left
running, so the remaining inputs are skipped and the caller should restart the backend. -/
def runProgramInputs (act : IO Unit) (inputs : List String) (ms : Nat) : IO (Array Json) := do
  let mut out := #[]
  let mut hung := false
  for input in inputs do
    if hung then
      out := out.push (Json.mkObj [("skipped", Json.bool true)]); continue
    let work ← IO.asTask (prio := .dedicated) (runWithStdin act input)
    let start ← IO.monoMsNow
    repeat
      if ← IO.hasFinished work then break
      if (← IO.monoMsNow) - start > ms then break
      IO.sleep 2
    if !(← IO.hasFinished work) then
      hung := true
      out := out.push (Json.mkObj [("hang", Json.bool true)]); continue
    match work.get with
    | .ok (stdout, err) =>
      out := out.push (Json.mkObj ([("stdout", toJson stdout)] ++
        (match err with | some e => [("error", toJson e)] | none => [])))
    | .error e => out := out.push (Json.mkObj [("error", toJson (toString e))])
  return out

/-- `programs: [{id, fn, inputs}]`: run the `IO Unit` constant `fn` on each stdin text. -/
def runPrograms (json : Json) (ms : Nat) : MetaM Json := do
  let reqs := (json.getObjValAs? (Array Json) "programs").toOption.getD #[]
  let out ← reqs.mapM fun r => do
    let some fn := nameOpt r "fn" | return Json.mkObj [("error", toJson "missing fn")]
    let inputs := (r.getObjValAs? (Array String) "inputs").toOption.getD #[]
    if !(← getEnv).contains fn then
      return Json.mkObj [("id", r.getObjValD "id"), ("error", toJson s!"unknown constant {fn}")]
    try
      let act ← evalIO fn
      let runs ← runProgramInputs act inputs.toList ms
      return Json.mkObj [("id", r.getObjValD "id"), ("runs", Json.arr runs)]
    catch e =>
      return Json.mkObj [("id", r.getObjValD "id"), ("error", toJson (← e.toMessageData.toString))]
  return Json.arr out

/-- The task body: run every target of `json` in `env`. -/
def runRefuteTargets (json : Json) : TermElabM Json := do
  let targets := ((json.getObjValAs? (Array Json) "targets").toOption.getD #[]).map Target.ofJson
  let cfg := configOfJson ((json.getObjVal? "config").toOption.getD Json.null)
    { numInst := 200, maxSize := 30, timeMs := 5000, perCaseMs := 1000 }
  let given := (json.getObjValAs? (Array Json) "witnesses").toOption.getD #[]
  let mut out := #[]
  for t in targets do
    let extra := given.toList.filterMap fun w =>
      if (w.getObjValAs? String "target").toOption == some t.id then
        ((w.getObjValAs? (Array Json) "lits").toOption.bind fun ls =>
          (ls.toList.mapM PyLit.fromJson?).toOption)
      else none
    out := out.push (← try budgeted (runTarget t cfg extra)
      catch e => pure (Json.mkObj [("id", toJson t.id), ("error", toJson (← e.toMessageData.toString))]))
  return Json.mkObj [("result", Json.bool true), ("targets", Json.arr out), ("evals", ← runEvals json),
    ("programs", ← runPrograms json cfg.perCaseMs)]

end PastaLean.Refute
