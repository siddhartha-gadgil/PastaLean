import PastaLean.PyVerify.Twin.Check
import PastaLean.PyVerify.Twin.Table

/-!
# Twin proofs reduced to the substitution table

* `twin% f`: the refinement statement for `f` and its runnable twin `f'rn`,
  `∀ a, f'rn (up a) = up (f a)`.
* `twin_table`: proves such a goal by normalisation, after turning everything it rests on into
  separate goals: a primitive substitution (`Twin/Table.lean`) without a proved bridge lemma, and a
  runnable callee whose own twin equation is not proved yet. What is left to the user is exactly the
  comparison of table entries (and of callees, each again provable by `twin_table`).
* `#twin_table`: reports on the table itself: whether each `prim` row has its bridge lemma
  `Twin.<run>_twin` in the `@[twin]` set, stating the runnable primitive in terms of the provable one,
  resting on no `sorry`. A row that does not is only reported: `twin_table` turns it into goals.
-/

open Lean Elab Command Term Meta Tactic

namespace PastaLean.Twin

/-- The bridge lemma of a `prim` row, `PastaLean.Twin.<run>_twin`. -/
def rowLemma (s : Subst) : Name :=
  `PastaLean.Twin ++ Name.mkSimple (s.run.lastComponentAsString ++ "_twin")

/-- Does constant `c` rest on `sorry`, directly or through what it uses (any namespace)? -/
def constRestsOnSorry (c : Name) : CoreM Bool := do
  return (← collectAxioms c).contains ``sorryAx

/-- Is `l` in the `@[twin]` simp set (so the normalisation uses it)? -/
def inTwinSet (l : Name) : CoreM Bool := do
  let some ext ← getSimpExtension? `twin | return false
  return (← ext.getTheorems).isLemma (.decl l)

/-- Why a `prim` row is not a proved refinement, or `none` when it is. -/
def rowProblem (s : Subst) : MetaM (Option String) := do
  let l := rowLemma s
  let some ci := (← getEnv).find? l | return some s!"missing bridge lemma {l}"
  unless ← inTwinSet l do return some s!"{l} is not in the @[twin] set"
  if ← constRestsOnSorry l then return some s!"{l} rests on sorry"
  let concl ← forallTelescope ci.type fun _ b => pure b
  let some (_, lhs, rhs) := concl.eq? | return some s!"{l} is not an equation"
  unless lhs.getAppFn.isConstOf s.run do return some s!"{l}: left side is not {s.run}"
  unless rhs.containsConst (· == s.prov) do return some s!"{l}: right side does not mention {s.prov}"
  return none

/-- `#twin_table`: list the substitution table and report on its `prim` rows (a warning for each one
that is not a proved refinement; `twin_table` leaves those as goals where they are used). -/
elab "#twin_table" : command => liftTermElabM do
  let mut lines : Array String := #[]
  let mut bad : Array String := #[]
  for s in substTable do
    let tag := match s.kind with
      | .prim => "prim" | .type => "type" | .erase => "erase" | .effect => "effect"
      | .transform => "transform"
    let pair := if s.prov.isAnonymous then "" else s!"{s.prov} ↦ {s.run}  "
    if s.kind == .prim then
      match ← rowProblem s with
      | some why => bad := bad.push why; lines := lines.push s!"✗ {tag}  {pair}{s.python}"
      | none => lines := lines.push s!"✓ {tag}  {pair}{s.python}"
    else lines := lines.push s!"  {tag}  {pair}{s.python}"
  logInfo m!"{"\n".intercalate lines.toList}"
  unless bad.isEmpty do logWarning m!"substitution table, not yet proved: {"; ".intercalate bad.toList}"

/-- The runnable twin of `p`: `p` with `'rn` on one or more components (`f ↦ f'rn`, `C.m ↦ C'rn.m`). -/
def runnableName? (p : Name) : CoreM (Option Name) := do
  let env ← getEnv
  let rec variants : Name → List Name
    | .str q s => (variants q).flatMap fun q' => [Name.str q' s, Name.str q' (s ++ "'rn")]
    | n => [n]
  return (variants p).find? fun r => r != p && env.contains r && provableName? r == some p

private def pairOf (p : Name) : TermElabM (Name × Name) := do
  let some r ← runnableName? p | throwError "no runnable twin of {p} (expected {p}'rn)"
  return (p, r)

/-- `twin% f`: the refinement statement `∀ a, f'rn (up a) = up (f a)`. -/
elab "twin%" i:ident : term => do
  let (p, r) ← pairOf (← realizeGlobalConstNoOverloadWithInfo i)
  match ← twinStatements (← mkConstWithLevelParams p) (← mkConstWithLevelParams r) p with
  | .ok (stmt, _) => return stmt
  | .error cat => throwError "twin%: the twins of {p} are not related by an equation ({cat})"

/-- The applications of constant `c` in `e` (maximal ones: not their partial prefixes). -/
partial def appsOf (c : Name) : Expr → Array Expr
  | e@(.app ..) =>
    let inArgs := e.getAppArgs.foldl (fun acc a => acc ++ appsOf c a) #[]
    if e.getAppFn.isConstOf c then inArgs.push e else appsOf c e.getAppFn ++ inArgs
  | .lam _ t b _ | .forallE _ t b _ => appsOf c t ++ appsOf c b
  | .letE _ t v b _ => appsOf c t ++ appsOf c v ++ appsOf c b
  | .mdata _ b | .proj _ _ b => appsOf c b
  | _ => #[]

/-- The provable counterpart of the runnable type `β` (`TwinRel β α`), or `none` when they coincide or
are unrelated. -/
def provType? (β : Expr) : MetaM (Option Expr) := do
  let α ← mkFreshExprMVar (mkSort levelOne)
  let some _ ← (try some <$> synthInstance (mkApp2 (mkConst ``TwinRel) β α) catch _ => pure none)
    | return none
  let α ← instantiateMVars α
  if ← isDefEq α β then return none
  return some α

/-- `a : α` as a runnable value of type `β`, in the `@[twin]` normal form: `l.toArray` for an array of
shared elements, else `up a`. -/
def upNormal (β α a : Expr) : MetaM Expr := do
  if β.isAppOfArity ``Array 1 && α.isAppOfArity ``List 1 && (← isDefEq β.appArg! α.appArg!) then
    return mkApp2 (mkConst ``List.toArray [levelZero]) α.appArg! a
  mkAppOptM ``TwinRel.up #[some β, some α, none, some a]

/-- The obligation for one use `fn args` of a runnable primitive standing for `prov`, at the types of
that use and in the shape of a bridge lemma, over provable values:
`∀ l i, pyArrayPopValue l.toArray i = pyPopValue l i`. `none` when an implicit argument of the use
mentions local variables, or the two sides cannot be related. -/
partial def useObligation (prov : Name) (fn : Expr) (args : Array Expr) : MetaM (Option Expr) := do
  let rec go (i : Nat) (ty : Expr) (runArgs provArgs xs : Array Expr) : MetaM (Option Expr) := do
    if i == args.size then
      if xs.isEmpty then return none
      let lhs := mkAppN fn runArgs
      let some pcall ← (try some <$> mkAppM prov provArgs catch _ => pure none) | return none
      let lt ← inferType lhs
      let pt ← inferType pcall
      let rhs ← if ← isDefEq lt pt then pure pcall else
        match ← (try some <$> upNormal lt pt pcall catch _ => pure none) with
        | some e => pure e
        | none => return none
      return some (← mkForallFVars xs (← mkEq lhs rhs))
    let .forallE n d b bi ← whnf ty | return none
    if bi.isExplicit then
      let d := d.cleanupAnnotations
      match ← provType? d with
      | some α =>
        withLocalDeclD n α fun a => do
          let r ← upNormal d α a
          go (i + 1) (b.instantiate1 r) (runArgs.push r) (provArgs.push a) (xs.push a)
      | none =>
        withLocalDeclD n d fun x => do
          go (i + 1) (b.instantiate1 x) (runArgs.push x) (provArgs.push x) (xs.push x)
    else
      let a := args[i]!
      if a.hasLooseBVars || a.hasFVar || a.hasMVar then return none
      go (i + 1) (b.instantiate1 a) (runArgs.push a) provArgs xs
  go 0 (← inferType fn) #[] #[] #[]

/-- What the runnable body of `r` rests on: table rows whose bridge lemma is not proved (one
obligation per distinct instantiation used, else one at the row's own types), and runnable callees
(`c'rn` of a provable `c`) whose twin equation is not proved; each with its statement. -/
def obligations (r : Name) : TermElabM (Array (Name × Expr)) := do
  let env ← getEnv
  let some body := (env.find? r).bind (·.value?) | return #[]
  let mut out := #[]
  for c in body.getUsedConstants.toList.eraseDups do
    if let some s := substTable.find? (fun s => s.kind == .prim && s.run == c) then
      if (← rowProblem s).isSome then
        let mut stmts : Array Expr := #[]
        for app in appsOf c body do
          if let some st ← useObligation s.prov app.getAppFn app.getAppArgs then
            unless ← stmts.anyM (isDefEq · st) do stmts := stmts.push st
        if stmts.isEmpty then
          if let .ok (_, eq) ← twinStatements (← mkConstWithLevelParams s.prov)
              (← mkConstWithLevelParams c) s.prov then stmts := #[eq]
        let base := c.lastComponentAsString
        for st in stmts, k in [0:stmts.size] do
          let tag := if stmts.size == 1 then base else s!"{base}_{k + 1}"
          out := out.push (`prim ++ Name.mkSimple tag, st)
    else if let some pc := provableName? c then
      if c != r && env.contains pc && !env.contains (pc ++ `_twin_eq) then
        if let .ok (_, eq) ← twinStatements (← mkConstWithLevelParams pc)
            (← mkConstWithLevelParams c) pc then
          out := out.push (`callee ++ Name.mkSimple pc.lastComponentAsString, eq)
  return out

/-- `twin_table` (or `twin_table f`): prove `twin% f` by unfolding both twins and normalising with the
`@[twin]` set, after splitting off, as named goals (`prim.<op>`, `callee.<g>`), every primitive
substitution and callee it rests on that is not already proved. -/
syntax (name := twinTableTac) "twin_table" (ppSpace colGt ident)? : tactic

elab_rules : tactic
  | `(tactic| twin_table $[$i]?) => withMainContext do
    let goal ← getMainGoal
    let (p, r) ← match i with
      | some i => pairOf (← realizeGlobalConstNoOverloadWithInfo i)
      | none =>
        let tgt ← instantiateMVars (← goal.getType)
        let lhsHead? ← forallTelescope tgt fun _ b => pure (b.eq?.map (·.2.1.getAppFn.constName?))
        let some (some r) := lhsHead? | throwError "twin_table: expected a goal `twin% f`"
        let some p := provableName? r | throwError "twin_table: {r} is not a runnable twin"
        pure (p, r)
    let obls ← obligations r
    let mut main := goal
    let mut sides : Array MVarId := #[]
    let mut hyps : Array Term := #[]
    for (tag, stmt) in obls do
      let side ← mkFreshExprSyntheticOpaqueMVar stmt tag
      let h := Name.mkSimple ("h_" ++ tag.toString.replace "." "_")
      let (_, g) ← (← main.assert h stmt side).intro1P
      main := g
      sides := sides.push side.mvarId!
      hyps := hyps.push ⟨(mkIdent h).raw⟩
    let tac ← twinTacSyntax #[p, r] (extra := hyps)
    let rest ← Term.withoutErrToSorry <| Tactic.run main (Tactic.evalTactic tac)
    unless rest.isEmpty do
      logInfo m!"twin_table: normalisation left {rest.length} goal(s) for {p} beyond the table"
    replaceMainGoal (sides.toList ++ rest)

end PastaLean.Twin
