import PastaLean.PyVerify.Refute.Obligation
import PastaLean.PyAPI.TasteIngr

/-!
# `refute?`, `#refute` and `refute_at`

* `refute?` — search for a counterexample to the current goal. On one it fails with the input (as
  Python) and, when the kernel accepts it, the `refute_at` line that proves the goal false. Otherwise
  it reports how many inputs were tried and leaves the goal alone, so `refute?; taste?` composes.
* `#refute thm` — the same, for a declaration's statement.
* `refute_at w₁, …, wₙ` — proves `¬ ∀ x₁ … xₙ, P` by instantiating the statement at the witness and
  deciding the instance (never `native_decide`, so `#print axioms` stays clean).
-/

namespace PastaLean.Refute

open Lean Meta Elab Tactic Command

syntax (name := refuteAtStx) "refute_at " term,+ : tactic

macro_rules
  | `(tactic| refute_at $ts,*) =>
    `(tactic| (intro h; have hw := h $(ts.getElems)*; revert hw;
               first
                 | decide
                 | decide +kernel
                 | norm_num [taste_ingr]
                 | simp (config := { decide := true }) [taste_ingr]
                 | simp_all [taste_ingr]))

declare_config_elab elabRefuteConfig RefuteConfig
declare_command_config_elab elabRefuteCmdConfig RefuteConfig

/-- `x = …, y = …` with each value as Python. -/
def witnessPython (names : Array (Name × Expr)) (ws : List PyLit) : String :=
  ", ".intercalate ((names.toList.zip ws).map fun ((n, _), w) =>
    s!"{n.eraseMacroScopes} = {w.toPyString}")

/-- The `refute_at …` line for a witness, with each value ascribed its binder type. -/
def refuteAtSource (names : Array (Name × Expr)) (ws : List PyLit) : MetaM String := do
  let parts ← (names.toList.zip ws).mapM fun ((_, τ), w) => do
    let e ← litToExpr τ w
    let src ← withOptions (fun o => o.setBool `pp.fullNames true) do
      return toString (← ppExpr e)
    return s!"({src} : {← ppExpr τ})"
  return "refute_at " ++ ", ".intercalate parts

/-- Prove `¬ ty` with the witness, by elaborating exactly the `refute_at` line that will be emitted;
`some line` when the kernel accepts it. Data binders must lead the statement for this to apply. -/
def certify (ty : Expr) (names : Array (Name × Expr)) (ws : List PyLit) : TermElabM (Option String) := do
  let line ← refuteAtSource names ws
  let env ← getEnv
  let some stx := (Parser.runParserCategory env `tactic line).toOption | return none
  let goalTy := mkNot ty
  let mvar ← mkFreshExprMVar goalTy
  let saved ← saveState
  try
    let remaining ← Term.withoutErrToSorry <| Tactic.run mvar.mvarId! (evalTactic stx)
    if !remaining.isEmpty then saved.restore; return none
    let pf ← instantiateMVars mvar
    if pf.hasSorry || pf.hasSyntheticSorry then saved.restore; return none
    saved.restore
    return some line
  catch _ =>
    saved.restore
    return none

/-- The human-readable verdict for one search. -/
def describe (o : SearchOutcome) (names : Array (Name × Expr)) (cert : Option String) : String :=
  match o.status, o.witness? with
  | .refuted, some ws =>
      let what := if o.hang then "does not terminate (per-case deadline) on" else "is FALSE, counterexample:"
      s!"goal {what} {witnessPython names ws}" ++
        (match cert with
         | some line => s!"\nkernel-checked: {line}"
         | none => "\n(not kernel-checked)") ++
        s!"\n[{o.tested} tests, {o.shrinks} shrinks, seed {o.seed}]"
  | .untestable why, _ => s!"refute?: cannot test this goal — {why}"
  | .gaveUp, _ => s!"refute?: gave up — {o.discarded} draws failed the precondition, {o.tested} tested (seed {o.seed})"
  | .timeout, _ => s!"refute?: time budget exhausted after {o.tested} tests (seed {o.seed})"
  | _, _ => s!"refute?: no counterexample in {o.tested} tests ({o.discarded} discarded, seed {o.seed})"

syntax (name := refuteStx) "refute?" Lean.Parser.Tactic.optConfig : tactic

@[tactic refuteStx] def evalRefute : Tactic := fun stx => withMainContext do
  let cfg ← elabRefuteConfig stx[1]
  let goal ← getMainGoal
  -- Close over the local context, so the obligation is a statement about all its inputs.
  let lctx ← getLCtx
  let hyps := lctx.getFVarIds.filter fun f => !(lctx.get! f).isImplementationDetail
  let (_, closed) ← goal.revert hyps (preserveOrder := true)
  let ty ← instantiateMVars (← closed.getType)
  let (o, names) ← refuteType ty cfg
  match o.status with
  | .refuted =>
      let cert ← match o.witness? with
        | some ws => if o.hang then pure none else certify ty names ws
        | none => pure none
      throwError (describe o names cert)
  | _ => logInfo (describe o names none)

syntax (name := refuteCmd) "#refute " ident Lean.Parser.Tactic.optConfig : command

@[command_elab refuteCmd] def elabRefuteCmd : CommandElab := fun stx => do
  let cfg ← elabRefuteCmdConfig stx[2]
  liftTermElabM do
  let declName ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let ty ← instantiateMVars (← getConstInfo declName).type
  let (o, names) ← refuteType ty cfg
  match o.status, o.witness? with
  | .refuted, some ws =>
      let cert ← if o.hang then pure none else certify ty names ws
      logWarning (describe o names cert)
  | _, _ => logInfo (describe o names none)

/-! ### `taste?` runs this first

`taste?` asks for a counterexample before it searches for a proof: proving a false goal only burns the
budget, and the counterexample is the more useful answer. The pre-check is small and only looks at
closed obligations — a goal with local hypotheses is an mvcgen verification condition or an in-body
assert, whose free variables may take values the program never reaches. -/

register_option pastalean.taste.refute : Bool := {
  defValue := true
  descr := "taste? first searches for a counterexample (refute?) before trying to prove the goal" }

register_option pastalean.taste.skip : Bool := {
  defValue := false
  descr := "taste? admits every goal without searching (used when a file is elaborated only to run it)" }

register_option pastalean.taste.refuteMs : Nat := {
  defValue := 250
  descr := "wall-clock budget, in ms, of taste?'s counterexample pre-check" }

/-- Counterexamples `taste?` found, keyed by the byte offset of the `taste?` token, as JSON. -/
initialize tasteCounterexamplesRef : IO.Ref (Array (Nat × Json)) ← IO.mkRef #[]

def counterexampleJson (decl : Option Name) (o : SearchOutcome) (names : Array (Name × Expr))
    (cert : Option String) : MetaM Json := do
  let ws := o.witness?.getD []
  let binders ← names.mapM fun (n, τ) => do
    return Json.mkObj [("name", toJson n.eraseMacroScopes.toString), ("type", toJson (toString (← ppExpr τ)))]
  return Json.mkObj [
    ("decl", toJson ((decl.map toString).getD "")), ("binders", Json.arr binders),
    ("lits", toJson ws), ("python", toJson (ws.map PyLit.toPyString)),
    ("kernel", toJson cert.isSome), ("proof", toJson (cert.getD "")), ("hang", toJson o.hang),
    ("seed", toJson o.seed), ("tested", toJson o.tested), ("shrinks", toJson o.shrinks)]

/-- `true` when the goal is refuted with a kernel-checked counterexample: it is then admitted and
reported, and `taste?` skips proof search. -/
def tastePrecheck (stx : Syntax) : TacticM Bool := withMainContext do
  let opts ← getOptions
  if !pastalean.taste.refute.get opts then return false
  let goal ← getMainGoal
  let lctx ← getLCtx
  if lctx.getFVarIds.any (fun f => !(lctx.get! f).isImplementationDetail) then return false
  let ty ← instantiateMVars (← goal.getType)
  if ty.find? (fun e => e.isConstOf `Std.Do.Triple || e.isConstOf `Std.Do.SPred) |>.isSome then
    return false
  -- Opaque code (partial defs, while loops) cannot be refuted with a kernel certificate, so the
  -- pre-check could never admit it; it would only risk running a non-terminating loop.
  if ← reachesOpaque ty then return false
  let cfg : RefuteConfig := { numInst := 40, maxSize := 12, timeMs := pastalean.taste.refuteMs.get opts,
                              perCaseMs := 50, maxShrinks := 50, enumDepth := 3, enumMax := 400 }
  let saved ← saveState
  let r ← try some <$> refuteType ty cfg catch _ => pure none
  let some (o, names) := r | do saved.restore; return false
  let .refuted := o.status | do saved.restore; return false
  let some ws := o.witness? | do saved.restore; return false
  let cert ← if o.hang then pure none else certify ty names ws
  logWarning m!"taste?: {describe o names cert}"
  let some _ := cert | return false
  if let some pos := stx.getPos? then
    let j ← counterexampleJson (← Term.getDeclName?) o names cert
    tasteCounterexamplesRef.modify (·.push (pos.byteIdx, j))
  admitGoal goal
  return true

end PastaLean.Refute
