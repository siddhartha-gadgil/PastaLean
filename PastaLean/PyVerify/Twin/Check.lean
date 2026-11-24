import PastaLean.PyVerify.Twin.Bridge

/-!
# Checking the twins of a program: `twin_tac` and `#twin_check`

For every pair `f` / `f'rn` in the current file, `#twin_check` builds the refinement statement

  `∀ a₁ … aₙ, f'rn (up a₁) … (up aₙ) = up (f a₁ … aₙ)`

(`up` only where the two binder types differ, via `TwinRel`), proves it with `twin_tac`, and adds it
to the environment as `f._twin` plus the rewrite form `f._twin_eq : ∀ b, f'rn b = up (f (down b))`
tagged `@[twin]`, so callers' proofs reuse it (pairs are checked callee-first). A runnable class
`C'rn` gets its `TwinRel C'rn C` instance first. Nothing is ever an error: each pair gets a verdict,
reported in one `twin-report:` info message that PALC tallies. The theorems live only in the
elaborated environment; generated programs never contain them.

`partial def` twins are opaque constants in Lean's logic, so equality is not provable. For those we
prove the strongest available statement, **step equivalence**: the defining functionals (the bodies
of `f._unsafe_rec` / `f'rn._unsafe_rec`, recursive calls abstracted) are conjugate by `TwinRel`.
-/

open Lean Elab Command Term Meta

namespace PastaLean.Twin

/-- Verdict of one twin pair. -/
inductive Verdict where
  /-- `f'rn ∘ up = up ∘ f` proved. -/
  | proved
  /-- Proved assuming the twin equations of the listed `partial` callees (each step-equivalent). -/
  | provedModPartial (callees : List Name)
  /-- A `partial def` pair whose defining functionals are proved conjugate. -/
  | stepEquiv
  /-- Not proved; `cat` is the reason category. -/
  | failed (cat : String) (detail : String)
  deriving Inhabited

def Verdict.tag : Verdict → String
  | .proved => "proved"
  | .provedModPartial _ => "proved_mod_partial"
  | .stepEquiv => "partial_step_equiv"
  | .failed cat _ => cat

/-- The provable twin's name for a runnable name: drop `'rn` from each component (`f'rn ↦ f`,
`C'rn.m ↦ C.m`, `main''rn ↦ main'`). `none` if no component carried the suffix. -/
def provableName? (n : Name) : Option Name :=
  let rec go : Name → Option Name
    | .anonymous => none
    | .num p k => (go p).map (Name.num · k)
    | .str p s =>
      if s.endsWith "'rn" then some (Name.str ((go p).getD p) (s.dropEnd 3).toString)
      else (go p).map (Name.str · s)
  go n

private def mentions (e : Expr) (pred : Name → Bool) : Bool :=
  (e.find? fun t => t.isConst && pred t.constName!).isSome

private def nameHas (n : Name) (s : String) : Bool := (n.toString.splitOn s).length > 1

/-- Classify a statement-building failure from the two types. -/
private def classifyTypes (p : Name) (tp tr : Expr) : String :=
  let isFloat := fun n => n == ``Float
  let isExact := fun n => n == ``Rat || n == ``Real
  let isIO := fun n => n == ``IO || n == ``EIO || n == ``BaseIO
  let isProofM := fun n => n == ``PastaLean.ProofMode.PyProofM
  if mentions tr isFloat && (mentions tp isExact || !mentions tp isFloat) then "float"
  else if ((privateToUserName p).getString!.startsWith "main") && (mentions tr isIO || mentions tp isProofM) then "io_main"
  else if mentions tr isIO || mentions tp isProofM then "monad"
  else "type"

/-- `up x : β` for `x : α`, if `TwinRel β α` resolves (with `α` matching). -/
private def mkUp? (β α x : Expr) : MetaM (Option Expr) := do
  let some u ← mkRel? β α | return none
  return some (mkAppN (Lean.mkConst ``TwinRel.up) #[β, α, u, x])
where
  mkRel? (β α : Expr) : MetaM (Option Expr) := do
    unless (← inferType β).isType && (← inferType α).isType do return none
    let m ← mkFreshExprMVar (mkSort 1)
    let some inst ← synthInstance? (mkApp2 (Lean.mkConst ``TwinRel) β m) | return none
    unless ← isDefEq m α do return none
    return some (← instantiateMVars inst)

private def mkDown? (β α y : Expr) : MetaM (Option Expr) := do
  let some u ← mkUp?.mkRel? β α | return none
  return some (mkAppN (Lean.mkConst ``TwinRel.down) #[β, α, u, y])

/-- The refinement statement `∀ a, r (up a) = up (p a)` and its rewrite form
`∀ b, r b = up (p (down b))`, or a failure category. -/
def twinStatements (p r : Expr) (pName : Name) : MetaM (Except String (Expr × Expr)) := do
  let tp ← inferType p
  let tr ← inferType r
  let fail : MetaM (Except String (Expr × Expr)) := pure (.error (classifyTypes pName tp tr))
  forallTelescope tp fun xs ρ => do
    let mut rApp := r
    let mut trCur := tr
    let mut eqBinders : Array (Name × Expr × Option (Expr × Expr)) := #[]
    for x in xs do
      let trW ← whnfR trCur
      let .forallE bn β body _ := trW | return ← fail
      let α ← inferType x
      if ← isDefEq β α then
        rApp := mkApp rApp x; trCur := body.instantiate1 x
        eqBinders := eqBinders.push (bn, α, none)
      else
        let some u ← mkUp? β α x | return ← fail
        rApp := mkApp rApp u; trCur := body.instantiate1 u
        eqBinders := eqBinders.push (bn, β, some (β, α))
    if (← whnfR trCur).isForall then return ← fail
    let pApp := mkAppN p xs
    let (rhs, resRel) ← if ← isDefEq trCur ρ then pure (pApp, none) else
      match ← mkUp? trCur ρ pApp with
      | some e => pure (e, some (trCur, ρ))
      | none => return ← fail
    let stmt ← mkForallFVars xs (← mkEq rApp rhs)
    -- Rewrite form: the differing binders at their runnable types, `down` into the provable call;
    -- shared binders (type parameters included) stay the telescope's own variables.
    let diff := (xs.zip eqBinders).filter (·.2.2.2.isSome)
    let eqStmt ← withLocalDeclsD (diff.map fun (_, n, t, _) => (n, fun _ => pure t)) fun bs => do
      let mut pArgs := #[]
      let mut rArgs := #[]
      let mut binders := #[]
      let mut k := 0
      for x in xs, (_, _, rel) in eqBinders do
        match rel with
        | none => pArgs := pArgs.push x; rArgs := rArgs.push x; binders := binders.push x
        | some (β, α) =>
          let b := bs[k]!
          k := k + 1
          pArgs := pArgs.push (← mkDown? β α b).get!; rArgs := rArgs.push b; binders := binders.push b
      let pCall := mkAppN p pArgs
      let rhs ← match resRel with
        | none => pure pCall
        | some (β, α) => pure (← mkUp? β α pCall).get!
      mkForallFVars binders (← mkEq (mkAppN r rArgs) rhs)
    return .ok (stmt, eqStmt)

/-- The tactic run on a refinement goal: unfold the listed twins, normalise with `twin`, close. -/
def twinTacSyntax (unfold : Array Name) (hyps : Array Name := #[]) (extra : Array Term := #[]) :
    CoreM Syntax.Tactic := do
  let mut lemmas : Array (TSyntax ``Parser.Tactic.simpLemma) := #[]
  for n in unfold do
    lemmas := lemmas.push (← `(Parser.Tactic.simpLemma| $(mkCIdent n):ident))
  for h in hyps do
    lemmas := lemmas.push (← `(Parser.Tactic.simpLemma| $(mkIdent h):ident))
  for t in extra do
    lemmas := lemmas.push (← `(Parser.Tactic.simpLemma| $t:term))
  lemmas := lemmas.push (← `(Parser.Tactic.simpLemma| twin))
  let hs : Array (TSyntax `term) := hyps.map fun h => ⟨(mkIdent h).raw⟩
  if hs.isEmpty then
    `(tactic| (intros; (try simp only [$lemmas,*]); (try rfl)))
  else
    `(tactic| (intro $hs*; intros; (try simp only [$lemmas,*]); (try rfl)))

/-- The conditional twin equations of callees that assume `partial` twins, instantiated with the
caller's matching hypotheses `h_twin_i` (simp cannot discharge those premises itself). -/
private def instantiatedCalleeEqs (e : Expr) (hyps : Array (Name × Expr))
    (assumed : NameMap (List Name)) : CoreM (Array Term) := do
  let env ← getEnv
  let mut out := #[]
  for c in e.getUsedConstants.toList.eraseDups do
    let some cs := assumed.get? c | continue
    unless env.contains (c ++ `_twin_eq) do continue
    let some idxs := cs.mapM (fun n => hyps.findIdx? (·.1 == n)) | continue
    let args : Array Term := idxs.toArray.map fun i => ⟨(mkIdent (Name.mkSimple s!"h_twin_{i}")).raw⟩
    out := out.push (← `($(mkCIdent (c ++ `_twin_eq)) $args*))
  return out

/-- `twin_tac [f, f'rn]`: prove a twin refinement goal by unfolding the named definitions and
normalising with the `@[twin]` simp set (bridge lemmas + proved callee twins). -/
syntax (name := twinTac) "twin_tac" (" [" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| twin_tac $[[$ids,*]]?) => do
    let names ← match ids with
      | some ids => ids.getElems.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
      | none => pure #[]
    Tactic.evalTactic (← twinTacSyntax names)

/-- Heartbeat budget (thousands) of one proof attempt: a twin proof is a normalisation, so it either
closes fast or not at all. -/
register_option pastalean.twinHeartbeats : Nat := {
  defValue := 40000
  descr := "heartbeat budget (in thousands) of each twin proof attempt"
}

register_option pastalean.twinDebug : Bool := {
  defValue := false
  descr := "`#twin_check` logs the goal each failed twin proof is left with"
}

/-- Run `tac` on `goal`; the closed proof, or `none`. Runtime failures (heartbeats) count as `none`. -/
def proveWith (goal : Expr) (tac : Syntax.Tactic) : TermElabM (Option Expr) :=
  withCurrHeartbeats do
  let hb := pastalean.twinHeartbeats.get (← getOptions)
  withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
  let mvar ← mkFreshExprMVar goal
  let saved ← saveState
  let debug := pastalean.twinDebug.get (← getOptions)
  let (res, dbg) ← tryCatchRuntimeEx
    (do
      let rest ← Term.withoutErrToSorry <| Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
      if rest.isEmpty then
        let pf ← instantiateMVars mvar
        pure (if pf.hasSorry || pf.hasExprMVar then none else some pf, none)
      else
        let msg ← if debug then
            pure (some m!"twin-debug: {goal}\n{← rest.mapM fun g => do
              return m!"{← Meta.ppGoal g}"}")
          else pure none
        pure (none, msg))
    (fun e => pure (none, if debug then some m!"twin-debug: {goal}\n{e.toMessageData}" else none))
  if res.isNone then saved.restore
  if let some m := dbg then logInfo m
  return res

private def addTwinTheorem (name : Name) (stmt pf : Expr) : MetaM Unit := do
  let stmt ← instantiateMVars stmt
  let lparams := (collectLevelParams {} stmt).params.toList ++ (collectLevelParams {} pf).params.toList
  addDecl <| .thmDecl { name, levelParams := lparams.eraseDups, type := stmt, value := pf }

private def addToTwinSet (name : Name) : MetaM Unit := do
  let some ext ← getSimpExtension? `twin | return
  addSimpTheorem ext name (post := true) (inv := false) .global (prio := 1000)

/-- Decls worth pairing: user definitions, not auxiliaries / instances / structure plumbing. -/
private def auxPrefixes : List String :=
  ["match_", "eq_", "proof_", "_sunfold", "_unary", "_binary", "_mutual", "_cstage", "_spec",
   "_lambda", "_elambda", "_closed", "_redArg", "_boxed", "_unsafe_rec", "_override",
   "_flat_ctor", "_sizeOf"]

private def isUserDecl (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  !n.hasMacroScopes && !isInstanceCore env n && !isInstanceCore env n.getPrefix &&
  !env.isProjectionFn n && !isAuxRecursor env n && !isNoConfusion env n &&
  ((match n with | .str _ s => some s | _ => none).map (fun (s : String) =>
    !auxPrefixes.any (fun (q : String) => s.startsWith q) && s != "ctorIdx" && s != "noConfusionType" && s != "ctorElim")).getD false &&
  match ci with
  | .defnInfo d => d.safety == .safe
  | .opaqueInfo _ => true
  | _ => false

/-- The functional of a `partial def`: its `_unsafe_rec` body with self calls abstracted, and other
partial callees' `_unsafe_rec` replaced by their (opaque) public constants. -/
private def partialFunctional? (n : Name) : MetaM (Option Expr) := do
  let env ← getEnv
  let self := n ++ `_unsafe_rec
  let some (.defnInfo d) := env.find? self | return none
  let body := d.value.replace fun e =>
    if e.isConst then
      let c := e.constName!
      if c != self && (match c with | .str _ s => s == "_unsafe_rec" | _ => false) then
        some (Lean.mkConst c.getPrefix e.constLevels!)
      else none
    else none
  withLocalDeclD `rec d.type fun recv => do
    let f ← mkLambdaFVars #[recv] (body.replace fun e => if e.isConstOf self then some recv else none)
    if (f.find? fun e => e.isConstOf self).isSome then return none
    return some f

/-- From `thm : ∀ a, r (up a) = U (p a)` derive the rewrite form `∀ b, r b = U (p (down b))`:
instantiate `a := down b`, then transport each `up (down b)` to `b` along `up_down`. -/
private def deriveEqForm (thm eqStmt : Expr) : MetaM (Option Expr) :=
  forallTelescope eqStmt fun bs eqn => do
    let some (_, _, rhs) := eqn.eq? | return none
    let pCall := if rhs.isAppOfArity ``TwinRel.up 4 then rhs.appArg! else rhs
    let pArgs := pCall.getAppArgs
    unless pArgs.size == bs.size do return none
    let mut pf := mkAppN thm pArgs
    for i in [0:bs.size] do
      let ty ← instantiateMVars (← inferType pf)
      let some (_, lhs, rhs') := ty.eq? | return none
      let args := lhs.getAppArgs
      let a := args[args.size - bs.size + i]!
      if a == bs[i]! then continue
      unless a.isAppOfArity ``TwinRel.up 4 do return none
      let a' := a.getAppArgs
      let hEq := mkAppN (Lean.mkConst ``TwinRel.up_down) #[a'[0]!, a'[1]!, a'[2]!, bs[i]!]
      let motive ← withLocalDeclD `y (← inferType bs[i]!) fun y => do
        mkLambdaFVars #[y] (← mkEq (mkAppN lhs.getAppFn (args.set! (args.size - bs.size + i) y)) rhs')
      pf ← mkEqNDRec motive pf hEq
    let pfAll ← mkLambdaFVars bs pf
    unless ← isDefEq (← inferType pfAll) eqStmt do return none
    return some pfAll

/-- Twin equations (rewrite form) of the `partial` callees used by `e` — directly, or through a callee
whose twin theorem assumes them (`assumed`) — as hypotheses. -/
private def partialHyps (e : Expr) (self : Name) (partialPairs : NameMap Name)
    (assumed : NameMap (List Name)) : MetaM (Array (Name × Expr)) := do
  let env ← getEnv
  let used := e.getUsedConstants
  let direct := used.toList.filter fun c => c != self && partialPairs.contains c
  let viaCallees := used.toList.flatMap fun c => (assumed.get? c).getD []
  let names := ((direct ++ viaCallees).filter (· != self)).eraseDups.toArray.qsort
    (·.toString < ·.toString)
  let mut out := #[]
  for c in names do
    let some cr := partialPairs.get? c | continue
    let some cci := env.find? c | continue
    let some crci := env.find? cr | continue
    if let .ok (_, h) ← twinStatements (Lean.mkConst c (cci.levelParams.map mkLevelParam))
        (Lean.mkConst cr (crci.levelParams.map mkLevelParam)) c then
      out := out.push (c, h)
  return out

private def withHyps (hyps : Array (Name × Expr)) (stmt : Expr) : Expr :=
  hyps.size.foldRev (init := stmt) fun i _ acc =>
    mkForall (Name.mkSimple s!"h_twin_{i}") .default hyps[i]!.2 acc

private def hypIdents (n : Nat) : Array Name :=
  (List.range n).toArray.map fun i => Name.mkSimple s!"h_twin_{i}"

/-- One twin pair's check. Adds `p._twin` / `p._twin_eq` on success. -/
def checkPair (p r : Name) (partialPairs : NameMap Name) (assumed : NameMap (List Name)) :
    TermElabM Verdict := do
  let env ← getEnv
  let some pci := env.find? p | return .failed "type" "missing"
  let some rci := env.find? r | return .failed "type" "missing"
  -- The entry point: `main'` (state-monad IO model) vs `main''rn` (real `IO`), and the `main`
  -- wrappers around them. Their agreement is the IO model's, which is trusted, not proved.
  if p.getString! == "main" || p.getString! == "main'" then return .failed "io_main" ""
  let pe := Lean.mkConst p (pci.levelParams.map mkLevelParam)
  let re := Lean.mkConst r (rci.levelParams.map mkLevelParam)
  let isPartial := pci matches .opaqueInfo _ || rci matches .opaqueInfo _
  if isPartial then
    return ← checkPartial p r pe re partialPairs
  match ← twinStatements pe re p with
  | .error cat => return .failed cat ""
  | .ok (stmt, eqStmt) =>
    let usesMemo := mentions rci.value! fun n => nameHas n "'memo"
    let usesWhile := mentions rci.value! (· == ``Lean.Loop.mk)
    -- Partial callees are opaque: assume their twin equations (hypotheses of the theorem).
    let hyps ← partialHyps pci.value! p partialPairs assumed
    let stmtH := withHyps hyps stmt
    let tac ← twinTacSyntax #[p, r] (hypIdents hyps.size)
      (← instantiatedCalleeEqs pci.value! hyps assumed)
    match ← proveWith stmtH tac with
    | none =>
      let isF := fun n => n == ``Float
      let isExact := fun n => n == ``Rat || n == ``Real
      let usesFloat := mentions rci.value! isF && !mentions pci.value! isF && mentions pci.value! isExact
      let cat := if (privateToUserName p).getString!.startsWith "main" then "io_main"
        else if usesMemo then "memo" else if usesFloat then "float"
        else if !hyps.isEmpty then "partial_callee" else if usesWhile then "while" else "proof"
      return .failed cat ""
    | some pf =>
      let thmName := p ++ `_twin
      addTwinTheorem thmName stmtH pf
      -- Rewrite form (conditional on the same hypotheses), for callers' `simp`.
      let thm := Lean.mkConst thmName (pci.levelParams.map mkLevelParam)
      let eqStmtH := withHyps hyps eqStmt
      let pf2 ← forallBoundedTelescope eqStmtH hyps.size fun hs body => do
        match ← deriveEqForm (mkAppN thm hs) body with
        | some pf => some <$> mkLambdaFVars hs pf
        | none => pure none
      if let some pf2 := pf2 then
        addTwinTheorem (p ++ `_twin_eq) eqStmtH pf2
        addToTwinSet (p ++ `_twin_eq)
      return if hyps.isEmpty then .proved else .provedModPartial (hyps.map (·.1)).toList
where
  checkPartial (p r : Name) (pe re : Expr) (partialPairs : NameMap Name) : TermElabM Verdict := do
    let isMemo := ((← getEnv).find? r).any fun ci =>
      mentions (ci.value?.getD (Lean.mkConst ``Unit)) (nameHas · "'memo")
    let (some fp, some fr) := (← partialFunctional? p, ← partialFunctional? r)
      | return .failed (if isMemo then "memo" else "partial") "no functional"
    -- `∀ rec a, Fr (conj rec) (up a) = up (Fp rec a)`, conj rec := the rewrite form's RHS.
    let tp ← inferType pe
    match ← twinStatements pe re p with
    | .error cat => return .failed cat ""
    | .ok (_, eqStmt) =>
      -- conj rec = fun b => up (rec (down b)): reuse eqStmt's RHS with `p` replaced by `rec`.
      let goal ← withLocalDeclD `rec tp fun recv => do
        let conj ← forallTelescope eqStmt fun bs eqn => do
          let rhs := eqn.appArg!.replace fun e => if e.isConstOf p then some recv else none
          mkLambdaFVars bs rhs
        let lhsF := fr.beta #[conj]
        let rhsF := fp.beta #[recv]
        let s ← twinStatements rhsF lhsF p
        match s with
        | .ok (stmt, _) => some <$> mkForallFVars #[recv] stmt
        | .error _ => pure none
      let some goal := goal | return .failed "partial" "functional types"
      let hyps ← partialHyps fp p partialPairs assumed
      match ← proveWith (withHyps hyps goal)
          (← twinTacSyntax #[] (hypIdents hyps.size) (← instantiatedCalleeEqs fp hyps assumed)) with
      | some _ => return .stepEquiv
      | none =>
        let rci := (← getEnv).find? r
        if (rci.map fun ci => mentions (ci.value?.getD (Lean.mkConst ``Unit)) (nameHas · "'memo")).getD false
            || nameHas r "'memo" then return .failed "memo" ""
        return .failed "partial" ""

/-- Twin pairs among this file's declarations, callee-first. -/
def twinPairs : CoreM (Array (Name × Name)) := do
  let env ← getEnv
  let locals := env.constants.map₂.toList
  -- one twin may be `private` and the other not (a memoised `private partial def` helper)
  let byUser : NameMap Name := locals.foldl (init := {}) fun m (n, _) => m.insert (privateToUserName n) n
  let mut pairs : Array (Name × Name) := #[]
  for (r, rci) in locals do
    unless isUserDecl env r rci do continue
    let some pu := provableName? (privateToUserName r) | continue
    let some p := byUser.get? pu | continue
    let some pci := env.find? p | continue
    unless isUserDecl env p pci do continue
    pairs := pairs.push (p, r)
  -- callee-first: depth-first over the provable twins' use graph
  let provs : NameSet := pairs.foldl (fun s (p, _) => s.insert p) {}
  let byP : NameMap Name := pairs.foldl (fun m (p, r) => m.insert p r) {}
  let sorted := (pairs.map (·.1)).qsort (·.toString < ·.toString)
  let mut seen : NameSet := {}
  let mut out : Array (Name × Name) := #[]
  for root in sorted do
    let mut stack : List (Name × Bool) := [(root, false)]
    while !stack.isEmpty do
      let (n, post) := stack.head!
      stack := stack.tail!
      if post then
        out := out.push (n, (byP.get? n).get!)
      else if !seen.contains n then
        seen := seen.insert n
        stack := (n, true) :: stack
        let deps := ((env.find? n).bind (·.value?)).map (·.getUsedConstants) |>.getD #[]
        for d in deps do
          if provs.contains d && !seen.contains d then stack := (d, false) :: stack
  return out

/-- Structure pairs `C` / `C'rn` of this file. -/
def structPairs : CoreM (Array (Name × Name)) := do
  let env ← getEnv
  let mut out := #[]
  for (r, _) in env.constants.map₂.toList do
    unless isStructure env r do continue
    let some p := provableName? r | continue
    if isStructure env p then out := out.push (p, r)
  return out

/-- Elaborate `cmds` silently; `true` iff no error. Messages are discarded either way. -/
private def elabQuiet (cmds : String) : CommandElabM Bool := do
  let saved := (← get).messages
  let ok ← try
      let inputCtx := Parser.mkInputContext cmds "<twin>"
      let mut pstate : Parser.ModuleParserState := {}
      let mut ok := true
      let mut done := false
      while !done do
        let (stx, ps', msgs) :=
          Parser.parseCommand inputCtx { env := (← getEnv), options := (← getOptions) } pstate {}
        pstate := ps'
        if msgs.hasErrors then ok := false; done := true
        else if Parser.isTerminalCommand stx then done := true
        else
          withEnableInfoTree false (elabCommand stx)
          if (← get).messages.hasErrors then ok := false; done := true
      pure ok
    catch _ => pure false
  modify fun s => { s with messages := saved }
  return ok

/-- `TwinRel C'rn C` field-wise, plus its constructor/projection rewrite lemmas. -/
def deriveStructTwin (p r : Name) : CommandElabM Bool := do
  let env ← getEnv
  let fields := getStructureFieldsFlattened env p (includeSubobjectFields := false)
  let rfields := getStructureFieldsFlattened env r (includeSubobjectFields := false)
  unless fields == rfields do return false
  let some rctor := (getStructureCtor env r |>.name : Name) |> some | return false
  let pctor := (getStructureCtor env p).name
  let P := p.toString; let R := r.toString
  let ups := ", ".intercalate (fields.toList.map fun f => s!"{f} := PastaLean.Twin.up c.{f}")
  let downs := ", ".intercalate (fields.toList.map fun f => s!"{f} := PastaLean.Twin.down c.{f}")
  let binders := " ".intercalate (fields.toList.map fun f => s!"({f} : _)")
  let args := " ".intercalate (fields.toList.map fun f => s!"{f}")
  let dargs := " ".intercalate (fields.toList.map fun f => s!"(PastaLean.Twin.down {f})")
  let updargs := " ".intercalate (fields.toList.map fun f =>
    s!"(PastaLean.Twin.up (PastaLean.Twin.down {f}))")
  let inst := s!"twinRel_{R.replace "." "_"}".replace "'" "_"
  let mut cmds := s!"instance «{inst}» : PastaLean.Twin.TwinRel {R} {P} where
  up c := \{ {ups} }
  down c := \{ {downs} }
  down_up c := by cases c; simp only [PastaLean.Twin.TwinRel.down_up]
  up_down c := by cases c; simp only [PastaLean.Twin.TwinRel.up_down]
instance : PastaLean.Twin.TwinNontriv {R} := ⟨⟩
@[twin] theorem {r ++ `_twin_mk} {binders} :
    {rctor} {args} = PastaLean.Twin.up ({pctor} {dargs}) := by
  rw [show PastaLean.Twin.up ({pctor} {dargs}) = {rctor} {updargs} from rfl]
  simp only [PastaLean.Twin.TwinRel.up_down]
"
  for f in fields do
    cmds := cmds ++ s!"@[twin] theorem {r ++ (Name.mkSimple s!"_twin_{f}")} (c : {P}) :
    ({R}.{f} (PastaLean.Twin.up c)) = PastaLean.Twin.up ({P}.{f} c) := rfl
"
  elabQuiet cmds

/-- Check every twin pair of the file; one verdict per pair. -/
def checkTwins : CommandElabM (Array (Name × Name × Verdict)) := do
  let mut out := #[]
  let mut failedClasses : Array Name := #[]
  for (p, r) in ← liftCoreM structPairs do
    unless ← (try deriveStructTwin p r catch _ => pure false) do
      failedClasses := failedClasses.push p
      out := out.push (p, r, Verdict.failed "class" "no field-wise TwinRel (recursive class?)")
  let pairs ← liftCoreM twinPairs
  let env ← getEnv
  let partialPairs : NameMap Name := pairs.foldl (init := {}) fun m (p, r) =>
    if (env.find? p).any (· matches .opaqueInfo _) then m.insert p r else m
  let mut assumed : NameMap (List Name) := {}
  for (p, r) in pairs do
    let saved := (← get).messages
    let v ← try liftTermElabM <| checkPair p r partialPairs assumed
      catch e => pure (Verdict.failed "error" (← e.toMessageData.toString))
    unless pastalean.twinDebug.get (← getOptions) do modify fun s => { s with messages := saved }
    if let .provedModPartial cs := v then assumed := assumed.insert p cs
    -- a method or user of a class without a `TwinRel` fails for that reason
    let env ← getEnv
    let v := match v with
      | .failed _ _ =>
        let ci := env.find? p
        if (ci.map fun ci => mentions ci.type failedClasses.contains ||
              mentions (ci.value?.getD (Lean.mkConst ``Unit)) failedClasses.contains).getD false
        then Verdict.failed "class" "uses a class without TwinRel" else v
      | v => v
    out := out.push (p, r, v)
  return out

/-- `#twin_check`: check every twin pair declared in this file and log a `twin-report:` JSON
summary (`{"pairs": [{"f": …, "verdict": …}]}`) as one info message. Never an error. -/
elab "#twin_check" : command => do
  let res ← checkTwins
  let items := res.map fun (p, _, v) =>
    Json.mkObj [("f", toJson ((privateToUserName p).componentsRev.headD .anonymous |>.toString)),
      ("decl", toJson p.toString), ("verdict", toJson v.tag),
      ("detail", toJson (match v with | .failed _ d => d | .provedModPartial cs => toString cs | _ => ""))]
  logInfo m!"twin-report: {(Json.mkObj [("pairs", Json.arr items)]).compress}"

end PastaLean.Twin
