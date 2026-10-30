import PastaLean.PyVerify.Refute.Search
import PastaLean.PyVerify.Refute.ArbPy

/-!
# From a goal to a search

An obligation `∀ x₁ … xₙ, G₁ → … → Gₘ → B` is split into its data binders (what the search draws),
its guards (the preconditions, used to discard draws) and its body (the property). The search itself is
a closed `IO SearchOutcome` term built here and evaluated with `evalExpr`, so it runs compiled code over
the user's own definitions.

A binder followed by a membership hypothesis (`∀ t, t ∈ xs → …`, Lean's bounded `∀ t ∈ xs, …`) is NOT
a free input: it stays in the body, where it is decided by iterating `xs`.
-/

namespace PastaLean.Refute

open Lean Meta

structure Obligation where
  /-- Every binder of the leading telescope, in order. -/
  xs : Array Expr
  /-- The data binders among `xs` — what gets generated. -/
  data : Array Expr
  /-- The Prop binders among `xs` — the guards. -/
  guards : Array Expr
  body : Expr

/-- Is `t` a membership statement about `x` (`x ∈ s`)? -/
def isMembershipOf (x t : Expr) : Bool :=
  t.isAppOfArity ``Membership.mem 5 && (t.getArg! 4 == x || t.getArg! 3 == x)

/-- Split `ty` into an obligation and continue with `k`, inside the binders' local context. -/
def withObligation {α} (ty : Expr) (k : Obligation → MetaM α) : MetaM α :=
  forallTelescope ty fun xs body => do
    -- Cut before the first data binder that opens a bounded quantifier.
    let mut cut := xs.size
    for i in [0:xs.size] do
      let t ← inferType xs[i]!
      if !(← isProp t) && i + 1 < xs.size then
        if isMembershipOf xs[i]! (← inferType xs[i+1]!) then
          cut := i
          break
    let lead := xs.extract 0 cut
    let body ← mkForallFVars (xs.extract cut xs.size) body
    let mut data := #[]
    let mut guards := #[]
    for x in lead do
      if ← isProp (← inferType x) then guards := guards.push x else data := data.push x
    k { xs := lead, data, guards, body }

/-- `τ₁ × (τ₂ × (… × Unit))`. The `Unit` terminator keeps a one-binder tuple unambiguous. -/
def tupleType (tys : Array Expr) : MetaM Expr :=
  tys.foldrM (fun t acc => mkAppM ``Prod #[t, acc]) (mkConst ``Unit)

/-- The `i`-th component of a value `t` of `tupleType`. -/
def tupleProj (t : Expr) (i : Nat) : MetaM Expr := do
  let mut e := t
  for _ in [0:i] do e ← mkAppM ``Prod.snd #[e]
  mkAppM ``Prod.fst #[e]

/-- Constants whose presence means a proposition is decided classically, hence cannot be run. -/
def classicalConsts : List Name :=
  [`Classical.propDecidable, `Classical.dec, `Classical.decEq, `Classical.decPred, `Classical.choice]

/-- `decide p`, refusing an instance that is classical (it would not evaluate). -/
def mkDecideRunnable (p : Expr) : MetaM (Except String Expr) := do
  let inst? ← try some <$> synthInstance (mkApp (mkConst ``Decidable) p) catch _ => pure none
  match inst? with
  | none => return .error s!"no Decidable instance for {← ppExpr p}"
  | some inst =>
      let inst ← instantiateMVars inst
      if inst.find? (fun e => classicalConsts.any e.isConstOf) |>.isSome then
        return .error s!"only a classical Decidable instance for {← ppExpr p}"
      return .ok (mkApp2 (mkConst ``Decidable.decide) p inst)

def mentionsReal (e : Expr) : Bool :=
  e.find? (fun c => c.isConstOf `Real) |>.isSome

/-- Does `e` reach a `partial` definition through the definitions it unfolds to (a user `partial def`,
or the `while` loop machinery, itself partial)? The kernel cannot unfold one, so a refutation could
never be certified, and running it on a generated input may not terminate. -/
partial def reachesOpaque (e : Expr) (fuel : Nat := 4000) : MetaM Bool := do
  let visited ← IO.mkRef ({} : NameSet)
  let budget ← IO.mkRef fuel
  let rec go (e : Expr) : MetaM Bool := do
    for c in e.getUsedConstants do
      if (← visited.get).contains c then continue
      visited.modify (·.insert c)
      let b ← budget.get
      if b == 0 then return false
      budget.set (b - 1)
      match (← getEnv).find? c with
      -- `partial def f` compiles to an opaque `f` beside its real recursion `f._unsafe_rec`; an opaque
      -- native primitive (`@[extern]`, e.g. `String.append`) always returns.
      | some (.opaqueInfo _) =>
          let env ← getEnv
          if !isExtern env c && (env.contains (c ++ `_unsafe_rec) || (Compiler.getImplementedBy? env c).isSome) then
            return true
      | some (.defnInfo d) => if ← go d.value then return true
      | _ => pure ()
    return false
  go e

/-- `RefuteConfig` as a term (it must reach the compiled search unchanged). -/
def configExpr (cfg : RefuteConfig) : Expr := toExpr cfg

/-- The search over an obligation as a closed `IO SearchOutcome`, or why it cannot be built. -/
def searchExpr (ob : Obligation) (cfg : RefuteConfig) : MetaM (Except String Expr) := do
  if mentionsReal ob.body || (← ob.guards.anyM fun g => return mentionsReal (← inferType g)) then
    return .error "involves ℝ, which is not computable"
  if ob.body.hasAnyFVar (fun f => ob.guards.any (·.fvarId! == f)) then
    return .error "the property depends on a proof of its precondition"
  let tys ← ob.data.mapM inferType
  let tupTy ← tupleType tys
  let some arbInst ← (try some <$> synthInstance (← mkAppM ``PyArb #[tupTy]) catch _ => pure none)
    | let missing ← tys.filterM fun t => do
          return (← try some <$> synthInstance (← mkAppM ``PyArb #[t]) catch _ => pure none).isNone
      return .error s!"no generator for {← missing.mapM ppExpr}"
  withLocalDeclD `t tupTy fun t => do
    let projs ← (List.range ob.data.size).toArray.mapM (tupleProj t)
    let inst (e : Expr) : Expr := e.replaceFVars ob.data projs
    let lits ← projs.toList.mapM fun p => mkAppM ``ToPyLit.toLit #[p]
    let litsList ← mkListLit (mkConst ``PyLit) lits
    let mut guardB := toExpr true
    for g in ob.guards do
      match ← mkDecideRunnable (inst (← inferType g)) with
      | .error e => return .error e
      | .ok d => guardB ← mkAppM ``and #[guardB, d]
    let bodyB ← match ← mkDecideRunnable (inst ob.body) with
      | .error e => return .error e
      | .ok d => pure d
    let litsF ← mkLambdaFVars #[t] litsList
    let guardF ← mkLambdaFVars #[t] guardB
    let bodyF ← mkLambdaFVars #[t] bodyB
    return .ok (mkAppN (mkConst ``runSearch) #[tupTy, arbInst, litsF, guardF, bodyF, configExpr cfg])

/-- Run the search over `ty`. -/
unsafe def refuteTypeUnsafe (ty : Expr) (cfg : RefuteConfig) :
    MetaM (SearchOutcome × Array (Name × Expr)) :=
  withObligation ty fun ob => do
    let names ← ob.data.mapM fun x => do return ((← x.fvarId!.getDecl).userName, ← inferType x)
    match ← searchExpr ob cfg with
    | .error why => return ({ status := .untestable why, seed := cfg.seed }, names)
    | .ok e =>
        let e ← instantiateMVars e
        let act ← evalExpr (IO SearchOutcome) (mkApp (mkConst ``IO) (mkConst ``SearchOutcome)) e
        return (← act, names)

@[implemented_by refuteTypeUnsafe]
opaque refuteType (ty : Expr) (cfg : RefuteConfig) : MetaM (SearchOutcome × Array (Name × Expr))

/-! ### Witnesses back into Lean -/

/-- A `PyLit` boxed as a `PyAny`. -/
partial def pyAnyExpr : PyLit → MetaM Expr
  | .int n => return mkApp (mkConst ``PastaLean.PyAny.int) (toExpr n)
  | .bool b => return mkApp (mkConst ``PastaLean.PyAny.bool) (toExpr b)
  | .str s => return mkApp (mkConst ``PastaLean.PyAny.str) (toExpr s)
  | .float k e => return mkApp (mkConst ``PastaLean.PyAny.float) (toExpr (mkRat k (2 ^ e)))
  | .none => return mkConst ``PastaLean.PyAny.none
  | .list xs => do
      let ty := mkConst ``PastaLean.PyAny
      return mkApp (mkConst ``PastaLean.PyAny.list) (← mkListLit ty (← xs.mapM pyAnyExpr))
  | l => throwError "refute: cannot box {repr l} as PyAny"


/-- A `PyLit` as a Lean term of type `τ`; the same literal lands as `ℚ` in one twin and `Float` in the
other because the target type decides. -/
partial def litToExpr (τ : Expr) (l : PyLit) : MetaM Expr := do
  let τ ← whnfR τ
  match τ.getAppFn.constName?, l with
  | some ``Int, .int n => return toExpr n
  | some ``Nat, .int n => return toExpr n.toNat
  | some ``Bool, .bool b => return toExpr b
  | some ``String, .str s => return toExpr s
  | some ``Unit, _ => return mkConst ``Unit.unit
  | some ``Rat, .float k e => return toExpr (mkRat k (2 ^ e))
  | some ``Rat, .int n => return toExpr (n : Rat)
  -- `k · 2^-e` by scaling (exact for every double, subnormals included; `2^e` itself overflows).
  | some ``Float, .float k e =>
      mkAppM ``Float.scaleB #[← mkAppM ``Float.ofInt #[toExpr k], toExpr (-(e : Int))]
  -- A Python int where a float is annotated.
  | some ``Float, .int n => mkAppM ``Float.ofInt #[toExpr n]
  | some ``Float, .double b => mkAppM ``Float.ofBits #[toExpr b]
  | some ``List, .list xs =>
      let α := τ.appArg!
      mkListLit α (← xs.mapM (litToExpr α))
  | some ``Array, .list xs =>
      let α := τ.appArg!
      mkArrayLit α (← xs.mapM (litToExpr α))
  | some ``Option, .none => mkAppOptM ``Option.none #[τ.appArg!]
  | some ``Option, l => mkAppM ``Option.some #[← litToExpr τ.appArg! l]
  | some ``Prod, .tuple (x :: rest) =>
      let α := τ.appFn!.appArg!
      let β := τ.appArg!
      let restLit := match rest with | [y] => y | ys => .tuple ys
      mkAppM ``Prod.mk #[← litToExpr α x, ← litToExpr β restLit]
  | some ``PastaLean.PyAny, l => pyAnyExpr l
  | some ``PastaLean.PySet, .set xs =>
      let α := τ.getArg! 0
      mkAppOptM ``PastaLean.pySetFromList #[α, none, none, ← mkListLit α (← xs.mapM (litToExpr α))]
  | some ``Std.HashMap, .dict kvs =>
      let κ := τ.getArg! 0
      let ν := τ.getArg! 1
      let pairTy ← mkAppM ``Prod #[κ, ν]
      let pairs ← kvs.mapM fun (k, v) => do mkAppM ``Prod.mk #[← litToExpr κ k, ← litToExpr ν v]
      mkAppOptM ``Std.HashMap.ofList #[κ, ν, none, none, ← mkListLit pairTy pairs]
  | some n, .obj _ fields =>
      -- A user class: its structure constructor, field by field (fields absent from the literal fail).
      let env ← getEnv
      let some info := getStructureInfo? env n | throwError "refute: {n} is not a structure"
      let ctor := getStructureCtor env n
      let params := τ.getAppArgs
      let fieldTys ← forallTelescopeReducing (← instantiateForall ctor.type params) fun xs _ =>
        xs.mapM fun x => do return ((← x.fvarId!.getDecl).userName, ← inferType x)
      let mut args := #[]
      for (fname, fty) in fieldTys do
        let some (_, v) := fields.find? (·.1 == fname.toString) | throwError "refute: missing field {fname}"
        if fty.hasLooseBVars then throwError "refute: dependent field {fname}"
        args := args.push (← litToExpr fty v)
      let _ := info
      return mkAppN (mkAppN (mkConst ctor.name τ.getAppFn.constLevels!) params) args
  | _, _ => throwError "refute: cannot place {repr l} at type {← ppExpr τ}"

end PastaLean.Refute
