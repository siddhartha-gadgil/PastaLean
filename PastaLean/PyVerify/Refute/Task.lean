import PastaLean.PyVerify.Refute.Tactic

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

def nameOpt (j : Json) (k : String) : Option Name :=
  match j.getObjValAs? String k with
  | .ok s => if s.isEmpty then none else some s.toName
  | .error _ => none

def Target.ofJson (j : Json) : Target :=
  { id := (j.getObjValAs? String "id").toOption.getD "",
    theorem? := nameOpt j "theorem", provPre? := nameOpt j "provPre", provChk? := nameOpt j "provChk",
    runPre? := nameOpt j "runPre", runChk? := nameOpt j "runChk" }

def configOfJson (j : Json) (base : RefuteConfig) : RefuteConfig :=
  let n (k : String) (d : Nat) : Nat := (j.getObjValAs? Nat k).toOption.getD d
  { base with numInst := n "numInst" base.numInst, maxSize := n "maxSize" base.maxSize,
              seed := n "seed" base.seed, timeMs := n "timeMs" base.timeMs,
              perCaseMs := n "perCaseMs" base.perCaseMs, enumDepth := n "enumDepth" base.enumDepth,
              enumMax := n "enumMax" base.enumMax }

/-- `∀ args, pre args = true → chk args = true` from a checker (and optional precondition) constant. -/
def checkerStatement (chk : Name) (pre? : Option Name) : MetaM Expr := do
  let chkTy ← inferType (mkConst chk)
  forallTelescopeReducing chkTy fun args _ => do
    let concl ← mkEq (mkAppN (mkConst chk) args) (toExpr true)
    let body ← match pre? with
      | some pre => mkArrow (← mkEq (mkAppN (mkConst pre) args) (toExpr true)) concl
      | none => pure concl
    mkForallFVars args body

/-- The argument types of a checker constant. -/
def checkerArgTypes (chk : Name) : MetaM (Array Expr) := do
  forallTelescopeReducing (← inferType (mkConst chk)) fun args _ => args.mapM inferType

/-- Evaluate a closed `Bool` term. -/
unsafe def evalBoolUnsafe (e : Expr) : MetaM Bool := do
  evalExpr Bool (mkConst ``Bool) (← instantiateMVars e)

@[implemented_by evalBoolUnsafe]
opaque evalBool (e : Expr) : MetaM Bool

/-- What a world says about a witness: does it pass the precondition, does the property hold, the Python
error the evaluation raised (`exc`), and a runtime error hit while the value stayed the logical default
(`panic`, provable twin only). -/
def judgeJson (pass holds : Option Bool) (err : Option String := none) (exc : Option String := none)
    (panic : Option String := none) : Json :=
  Json.mkObj ([("guard", toJson pass), ("holds", toJson holds)] ++
    (match err with | some e => [("error", toJson e)] | none => []) ++
    (match exc with | some e => [("exc", toJson e)] | none => []) ++
    (match panic with | some e => [("panic", toJson e)] | none => []))

/-- Run `x`, returning the Python error a runtime function hit meanwhile (see `pyErrorLog`). -/
def withPyError (x : MetaM α) : MetaM (α × Option String) := do
  discard <| (pyErrorLog.swap none : IO _)
  let a ← x
  return (a, ← (pyErrorLog.swap none : IO _))

/-- Evaluate a witness against a checker (and precondition) in one world. With `executes` (the runnable
twin) a runtime error is a raise, as under CPython: in the precondition it rejects the input, in the
property it violates it. Otherwise (the provable twin) the logical value stands and the error is noted. -/
def judgeChecker (chk : Name) (pre? : Option Name) (ws : List PyLit) (executes := true) : MetaM Json := do
  try
    let tys ← checkerArgTypes chk
    if tys.size != ws.length then return judgeJson none none (some "arity mismatch")
    let args ← (tys.toList.zip ws).mapM fun (τ, w) => litToExpr τ w
    let (guardOk, gexc) ← withPyError do match pre? with
      | some pre => evalBool (← mkAppM ``BEq.beq #[mkAppN (mkConst pre) args.toArray, toExpr true])
      | none => pure true
    if !guardOk || (executes && gexc.isSome) then return judgeJson (some false) none
    let (holds, exc) ← withPyError do
      evalBool (← mkAppM ``BEq.beq #[mkAppN (mkConst chk) args.toArray, toExpr true])
    if executes then return judgeJson (some true) (some (holds && exc.isNone)) none exc
    return judgeJson (some true) (some holds) none none (exc <|> gexc)
  catch e => return judgeJson none none (some (← e.toMessageData.toString))

/-- Evaluate a witness against the obligation theorem (its guards, then its body), by `decide`. -/
def judgeTheorem (thm : Name) (ws : List PyLit) : MetaM Json := do
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
        | .ok d => if !(← evalBool d) then return judgeJson (some false) none
      -- The theorem's own truth: a runtime error inside it is the logical default, noted as `panic`.
      match ← mkDecideRunnable (inst ob.body) with
      | .error e => return judgeJson (some true) none (some e)
      | .ok d =>
        let (holds, exc) ← withPyError (evalBool d)
        return judgeJson (some true) (some holds) none none exc
  catch e => return judgeJson none none (some (← e.toMessageData.toString))

def searchJson (o : SearchOutcome) (names : Array (Name × Expr)) (cert : Option String) : MetaM Json := do
  let binders ← names.mapM fun (n, τ) => do
    return Json.mkObj [("name", toJson n.eraseMacroScopes.toString), ("type", toJson (toString (← ppExpr τ)))]
  return o.toJson.mergeObj (Json.mkObj [("binders", Json.arr binders), ("kernel", toJson cert.isSome),
    ("proof", toJson (cert.getD "")),
    ("python", toJson ((o.witness?.getD []).map PyLit.toPyString))])

/-- Run one target: both searches, then every witness through both worlds. -/
def runTarget (t : Target) (cfg : RefuteConfig) (extra : List (List PyLit)) : TermElabM Json := do
  let mut fields : Array (String × Json) := #[("id", toJson t.id)]
  let mut witnesses : Array (String × List PyLit) := #[]
  -- Provable world: the theorem if there is one (certifiable), else the exact-mode checker.
  let provTy? ← match t.theorem?, t.provChk? with
    | some thm, _ => pure (some ((← getConstInfo thm).type, true))
    | none, some chk => pure (some (← checkerStatement chk t.provPre?, false))
    | none, none => pure none
  if let some (ty, isThm) := provTy? then
    let ty ← instantiateMVars ty
    let (o, names) ← refuteType ty cfg
    let cert ← match o.status, o.witness? with
      | .refuted, some ws => if isThm && !o.hang then certify ty names ws else pure none
      | _, _ => pure none
    fields := fields.push ("prov", ← searchJson o names cert)
    if let some ws := o.witness? then witnesses := witnesses.push ("prov", ws)
  -- Runnable world: the `'rn` checker over its own types (Float, Array).
  if let some chk := t.runChk? then
    let ty ← checkerStatement chk t.runPre?
    let (o, names) ← refuteType ty { cfg with errorsFail := true }
    fields := fields.push ("run", ← searchJson o names none)
    if let some ws := o.witness? then witnesses := witnesses.push ("run", ws)
  for ws in extra do witnesses := witnesses.push ("given", ws)
  -- Cross-check every witness in both worlds; certify the first one (from any engine) that refutes the
  -- theorem in the provable twin.
  let mut evals : Array Json := #[]
  let mut certified : Option (List PyLit × String) := none
  for (origin, ws) in witnesses do
    let prov ← match t.theorem?, t.provChk? with
      | some thm, _ => judgeTheorem thm ws
      | none, some chk => judgeChecker chk t.provPre? ws (executes := false)
      | none, none => pure Json.null
    let provChk ← match t.provChk? with
      | some chk => judgeChecker chk t.provPre? ws (executes := false)
      | none => pure Json.null
    let run ← match t.runChk? with
      | some chk => judgeChecker chk t.runPre? ws
      | none => pure Json.null
    evals := evals.push (Json.mkObj [("origin", toJson origin), ("lits", toJson ws),
      ("python", toJson (ws.map PyLit.toPyString)), ("prov", prov), ("provChk", provChk), ("run", run)])
    if certified.isNone && (prov.getObjValAs? Bool "guard").toOption == some true
        && (prov.getObjValAs? Bool "holds").toOption == some false then
      if let some thm := t.theorem? then
        let ty ← instantiateMVars (← getConstInfo thm).type
        let names ← withObligation ty fun ob => ob.data.mapM fun x => do
          return ((← x.fvarId!.getDecl).userName, ← inferType x)
        if let some line ← certify ty names ws then certified := some (ws, line)
  fields := fields.push ("witnesses", Json.arr evals)
  if let some (ws, line) := certified then
    fields := fields.push ("certified", Json.mkObj [("lits", toJson ws), ("proof", toJson line)])
  return Json.mkObj fields.toList

/-- The Python class a Lean structure stands for: its last name component, without the runnable twin's
`'rn` suffix. -/
def pyClassName (n : Name) : String :=
  let last := n.getString!
  if last.endsWith "'rn" then (last.dropEnd 3).toString else last

/-- Structures (user classes) among `e`'s constants, transitively through field types. -/
partial def structuresIn (e : Expr) (acc : NameSet := {}) : MetaM NameSet := do
  let env ← getEnv
  let mut acc := acc
  for c in e.getUsedConstants do
    if acc.contains c || !isStructure env c then continue
    acc := acc.insert c
    for f in getStructureFieldsFlattened env c (includeSubobjectFields := false) do
      if let some proj := getProjFnForField? env c f then
        let fieldTy ← forallTelescopeReducing (← getConstInfo proj).type fun _ r => pure r
        acc ← structuresIn fieldTy acc
  return acc

/-- A `PyArb` instance, as a command, for every structure among the targets' inputs that has none:
built through the constructor, read back as the Python class with its fields. Self-referential
structures are left out (their generator would not terminate). -/
def structInstanceCommands (targets : Array Target) : MetaM (Array String) := do
  let env ← getEnv
  let mut tys : Array Expr := #[]
  for t in targets do
    for n in [t.theorem?, t.provChk?, t.runChk?].filterMap id do
      if let some ci := env.find? n then tys := tys.push ci.type
  let mut structs : NameSet := {}
  for ty in tys do structs ← structuresIn ty structs
  let mut out := #[]
  for n in structs.toList do
    let ci ← getConstInfo n
    if !ci.levelParams.isEmpty || ci.type.isForall then continue
    let existing ← try (some <$> synthInstance (← mkAppM ``PyArb #[mkConst n])) catch _ => pure none
    if existing.isSome then continue
    let fields := getStructureFieldsFlattened env n (includeSubobjectFields := false)
    -- A field whose own type mentions the structure (its codomain, not the projection's domain).
    let selfRef ← fields.anyM fun f => do
      match getProjFnForField? env n f with
      | some proj => forallTelescopeReducing (← getConstInfo proj).type fun _ r =>
          return r.getUsedConstants.contains n
      | none => return true
    if selfRef then continue
    let ctor := getStructureCtor env n
    let gens := " ".intercalate (fields.toList.map fun _ => "(← PastaLean.Refute.PyArb.arb)")
    let lits := ", ".intercalate (fields.toList.map fun f =>
      s!"(\"{f}\", PastaLean.Refute.ToPyLit.toLit s.{f})")
    out := out.push s!"instance : PastaLean.Refute.PyArb {n} where\n  arb := do return {ctor.name} {gens}\n  toLit s := .obj \"{pyClassName n}\" [{lits}]"
  return out

unsafe def evalLitUnsafe (e : Expr) : MetaM PyLit := do
  evalExpr PyLit (mkConst ``PyLit) (← instantiateMVars e)

@[implemented_by evalLitUnsafe]
opaque evalLit (e : Expr) : MetaM PyLit

/-- `fn` applied to one input, as a `PyLit` (an `Id` result is unwrapped). -/
def evalAt (fn : Name) (ws : List PyLit) : MetaM Json := do
  try
    forallTelescopeReducing (← inferType (mkConst fn)) fun xs res => do
      if xs.size != ws.length then return Json.mkObj [("error", toJson "arity mismatch")]
      let args ← (← xs.mapM inferType).toList.zip ws |>.mapM fun (τ, w) => litToExpr τ w
      let mut call := mkAppN (mkConst fn) args.toArray
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

unsafe def evalIOUnsafe (fn : Name) : MetaM (IO Unit) :=
  evalExpr (IO Unit) (mkApp (mkConst ``IO) (mkConst ``Unit)) (mkConst fn)

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
    out := out.push (← try runTarget t cfg extra
      catch e => return Json.mkObj [("id", toJson t.id), ("error", toJson (← e.toMessageData.toString))])
  return Json.mkObj [("result", Json.bool true), ("targets", Json.arr out), ("evals", ← runEvals json),
    ("programs", ← runPrograms json cfg.perCaseMs)]

end PastaLean.Refute
