import PastaLean.PyVerify.Refute.Obligation
import Lean.Elab.Tactic.Grind.Param

/-!
# Solving an obligation with `grind`

An obligation `∀ xs, G → B` is false exactly when `G ∧ ¬B` is satisfiable. We hand `G` and `¬B` to
`grind` as hypotheses of a `False` goal, after unfolding the program's own definitions and the Python
operators so it sees plain arithmetic. `grind` case-splits on the program's `if`s and runs its
linear-integer-arithmetic solver (cutsat) on each path, which is what a symbolic executor does with an
SMT solver:

* if it derives `False`, no input violates the obligation: it is **proved**;
* if it gets stuck, cutsat's assignment on the stuck path satisfies the guards and the negated body as
  far as arithmetic can tell — a **model** whose integer values are a candidate counterexample (the
  caller still evaluates it: functions `grind` treats as uninterpreted may make it spurious).
-/

namespace PastaLean.Refute

open Lean Meta Elab Tactic

inductive SolveResult where
  | proved
  | model (vals : Array (Name × Rat))
  | unknown (why : String)

/-- The translated program's definitions (`PastaLean.User`) that `e` reaches. -/
partial def userDefsGo (seen : IO.Ref NameSet) (out : IO.Ref (Array Name)) (e : Expr) : MetaM Unit := do
  for c in e.getUsedConstants do
    if !isProgramConst c (libraries := false) || (← seen.get).contains c then continue
    seen.modify (·.insert c)
    if let some (.defnInfo d) := (← getEnv).find? c then
      out.modify (·.push c)
      userDefsGo seen out d.value

def userDefs (es : Array Expr) : MetaM (Array Name) := do
  let seen ← IO.mkRef {}
  let out ← IO.mkRef #[]
  for e in es do userDefsGo seen out e
  out.get

theorem idRun_dite {α : Type u} (c : Prop) [Decidable c] (t : c → Id α) (e : ¬c → Id α) :
    (dite c t e).run = dite c (fun h => (t h).run) (fun h => (e h).run) := by
  split <;> rfl

theorem idRun_ite {α : Type u} (c : Prop) [Decidable c] (t e : Id α) :
    (ite c t e).run = ite c t.run e.run := by
  split <;> rfl

/-- Rewritten before solving: `Id.run` pushed through the program's `if`s and `do` steps down to
plain values, and the Python operator classes reduced to the underlying arithmetic. -/
def operatorUnfolds : List Name :=
  [``idRun_dite, ``idRun_ite, ``Id.run_pure, ``Id.run_bind, ``Id.run_map, ``Id.run_seqRight,
   ``PastaLean.PyHAdd.hAdd, ``PastaLean.PyHSub.hSub, ``PastaLean.PyHMul.hMul,
   ``PastaLean.PyHDiv.hDiv, ``PastaLean.PyModulo.hMod, ``PastaLean.PyFloorDiv.floorDiv,
   ``PastaLean.pyFloorDiv,
   -- list length and indexing, so a list of known length (a plateau seed's shape) exposes its elements
   ``PastaLean.pyLen, ``PastaLean.PyLen.pyLen, ``PastaLean.pyGetItem, ``PastaLean.PyGetItem.getItem,
   ``PastaLean.pyListGetItem, ``List.length_cons, ``List.length_nil, ``List.getElem?_cons_zero,
   ``List.getElem?_cons_succ, ``PastaLean.runPure_self]

/-- Runtime definitions `grind` may instantiate by their equations (Python `%` and `//` on ints). -/
def solverEquations : List Name := [``PastaLean.pyMod, ``PastaLean.pyRaiseOr]

/-- Solve `∀ data, guards → body` (see the module doc), within `maxHeartbeats` (thousands). -/
def solveObligation (ty : Expr) (maxHeartbeats : Nat := 400000) : TermElabM SolveResult :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := maxHeartbeats * 1000 }) do
  try
    withObligation ty fun ob => do
      let defs ← userDefs (#[ob.body] ++ (← ob.guards.mapM inferType))
      withLocalDeclD `hneg (mkNot ob.body) fun _ => do
        let goal ← mkFreshExprMVar (mkConst ``False)
        let lemmas ← (defs.toList ++ operatorUnfolds).filterM (fun n => return (← getEnv).contains n)
        let ids : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
          lemmas.toArray.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
        let simpStx ← `(tactic| simp only [$ids,*] at *)
        let goals ← try Term.TermElabM.run' (Tactic.run goal.mvarId! (evalTactic simpStx))
          catch _ => pure [goal.mvarId!]
        let some g := goals.head? | return .proved
        let mut params ← Grind.mkDefaultParams {}
        for n in solverEquations do
          if (← getEnv).contains n then
            params ← try Elab.Tactic.addEMatchTheorem params (mkIdent n) n (.default false) false (warn := false)
              catch _ => pure params
        let r ← Grind.main g params
        match r.failure? with
        | none => return .proved
        | some stuck =>
          let model ← Grind.Arith.Cutsat.mkModel stuck
          let lctx := (← stuck.mvarId.getDecl).lctx
          let vals := model.filterMap fun (e, v) =>
            match e with
            | .fvar id => (lctx.find? id).map fun d => (d.userName, v)
            | _ => none
          return .model vals
  catch e =>
    return .unknown (← e.toMessageData.toString)

/-! ### Finishing a stalled search

At a plateau the coverage-guided search hands over the inputs that came closest to the branches it
never reached. Each keeps its shape (lengths, keys, strings, classes) while up to `k` of its integer
leaves become unknowns; `grind`'s model for those is a new candidate, judged like any other witness. -/

/-- Up to `k` integer leaves of `l` replaced by symbolic sentinels (`symLeafBase + i`); the originals
are kept in order. Dict keys stay concrete. -/
partial def markLeaves (k : Nat) : PyLit → StateM (Array Int) PyLit
  | .int n => do
      let vs ← get
      if vs.size < k then set (vs.push n); return .int (symLeafBase + vs.size) else return .int n
  | .list xs => return .list (← xs.mapM (markLeaves k))
  | .tuple xs => return .tuple (← xs.mapM (markLeaves k))
  | .set xs => return .set (← xs.mapM (markLeaves k))
  | .dict kvs => return .dict (← kvs.mapM fun (a, b) => do return (a, ← markLeaves k b))
  | .obj c fs => return .obj c (← fs.mapM fun (n, v) => do return (n, ← markLeaves k v))
  | l => return l

/-- The sentinels of `markLeaves` replaced by `vals`. -/
partial def unmarkLeaves (vals : Array Int) : PyLit → PyLit
  | .int n => if n ≥ symLeafBase then .int (vals.getD (n - symLeafBase).toNat 0) else .int n
  | .list xs => .list (xs.map (unmarkLeaves vals))
  | .tuple xs => .tuple (xs.map (unmarkLeaves vals))
  | .set xs => .set (xs.map (unmarkLeaves vals))
  | .dict kvs => .dict (kvs.map fun (a, b) => (a, unmarkLeaves vals b))
  | .obj c fs => .obj c (fs.map fun (n, v) => (n, unmarkLeaves vals v))
  | l => l

/-- The obligation `ty` at `seed`'s shape: `∀ leaf₀ … leafₖ : Int, guards → body` with the data binders
replaced by the seed's values over the leaves. `none` when the seed does not fit or has no integer leaf. -/
def plateauStatement (ty : Expr) (seed : List PyLit) (marked : List PyLit) (n : Nat) : MetaM (Option Expr) :=
  withObligation ty fun ob => do
    if ob.data.size != seed.length || n == 0 then return none
    if ob.body.hasAnyFVar (fun f => ob.guards.any (·.fvarId! == f)) then return none
    let tys ← ob.data.mapM inferType
    -- a leaf inside a boxed value would not be read back through `litToExpr`
    if tys.any (fun τ => (τ.find? (·.isConstOf ``PastaLean.PyAny)).isSome) then return none
    let decls := (List.range n).toArray.map fun i => (Name.mkSimple s!"leaf{i}", fun (_ : Array Expr) => pure (mkConst ``Int))
    withLocalDeclsD decls fun xs => do
      symLeaves.set xs
      let vals ← try (tys.toList.zip marked).mapM (fun (τ, l) => litToExpr τ l) finally symLeaves.set #[]
      let inst (e : Expr) : Expr := e.replaceFVars ob.data vals.toArray
      let guards ← ob.guards.mapM fun g => do return inst (← inferType g)
      return some (← mkForallFVars xs (← guards.foldrM (fun g acc => mkArrow g acc) (inst ob.body)))

/-- A candidate witness near `seed`: its integer leaves solved by `grind` for a violation. -/
def solvePlateau (ty : Expr) (seed : List PyLit) (maxHeartbeats : Nat := 200000) : TermElabM (Option (List PyLit)) := do
  let (marked, orig) := (seed.mapM (markLeaves 8)).run #[]
  let some stmt ← (try plateauStatement ty seed marked orig.size catch _ => pure none) | return none
  match ← solveObligation stmt maxHeartbeats with
  | .model m =>
      let vals := orig.mapIdx fun i n =>
        ((m.find? (·.1.eraseMacroScopes == Name.mkSimple s!"leaf{i}")).map (·.2.floor)).getD n
      return some (marked.map (unmarkLeaves vals))
  | _ => return none

/-- Whether `taste?` (PastaLean's proof portfolio) proves `ty` outright, within `maxHeartbeats`
(thousands) per candidate. Invoked by its syntax kind, since `taste?` itself imports this library; its
own counterexample pre-check is switched off, and a proof leaning on `sorry` does not count. -/
def tasteProves (ty : Expr) (maxHeartbeats : Nat := 4000) : TermElabM Bool := do
  let stx := Syntax.node .none `PastaLean.tasteStx #[Syntax.atom .none "taste?"]
  withoutModifyingState do
    -- a candidate running out of heartbeats is a runtime exception, which plain `catch` lets through
    tryCatchRuntimeEx
      (withOptions (fun o => (o.setBool `pastalean.taste.refute false).set `maxHeartbeats maxHeartbeats) do
        let goal ← mkFreshExprMVar ty
        let gs ← Term.TermElabM.run' (Tactic.run goal.mvarId! (evalTactic stx))
        let pf ← instantiateMVars goal
        return gs.isEmpty && !pf.hasSorry && !pf.hasSyntheticSorry)
      (fun _ => return false)

/-- A model's values as a witness for the data binders `names`: integers from the model, and the
simplest value of each other carrier (empty list / string, `false`, zero) for binders it leaves free.
`none` when some binder's type has no such default. -/
def modelWitness (names : Array (Name × Expr)) (vals : Array (Name × Rat)) : MetaM (Option (List PyLit)) := do
  let mut out := #[]
  for (n, τ) in names do
    let τ ← whnfR τ
    let v? := (vals.find? (·.1.eraseMacroScopes == n.eraseMacroScopes)).map (·.2)
    let lit? : Option PyLit := match τ.getAppFn.constName?, v? with
      | some ``Int, some v => some (.int v.floor)
      | some ``Nat, some v => some (.int (max 0 v.floor))
      | some ``Int, none => some (.int 0)
      | some ``Nat, none => some (.int 0)
      | some ``Rat, some v => some (.rat v.num v.den)
      | some ``Rat, none => some (.int 0)
      | some ``Bool, _ => some (.bool false)
      | some ``String, _ => some (.str "")
      | some ``List, _ => some (.list [])
      | some ``Array, _ => some (.list [])
      | _, _ => none
    match lit? with
    | some l => out := out.push l
    | none => return none
  return some out.toList

end PastaLean.Refute
