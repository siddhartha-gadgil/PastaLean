import PastaLean.PyVerify.Refute.Search
import PastaLean.PyVerify.Refute.ArbPy
import PastaLean.PyVerify.Refute.RegexLang
import PastaLean.PyVerify.Refute.Instrument

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

/-- The obligation's inputs: binder names and types. -/
def Obligation.binders (ob : Obligation) : MetaM (Array (Name × Expr)) :=
  ob.data.mapM fun x => do return ((← x.fvarId!.getDecl).userName, ← inferType x)

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

/-- The inputs of the obligation `ty`: binder names and types. -/
def obligationBinders (ty : Expr) : MetaM (Array (Name × Expr)) := withObligation ty (·.binders)

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

/-- The `re` flags an argument names (`re.VERBOSE`, `re.I | re.X`). -/
def regexFlagsOf (e : Expr) : Int :=
  let named : List (Name × Int) := [(`IGNORECASE, 2), (`I, 2), (`MULTILINE, 8), (`M, 8), (`DOTALL, 16),
    (`S, 16), (`VERBOSE, 64), (`X, 64), (`ASCII, 256), (`A, 256)]
  e.getUsedConstants.foldl (fun acc c => match named.find? (`Libraries.re ++ ·.1 == c) with
    | some (_, f) => Libraries.re.orFlags acc f
    | none => acc) 0

/-- Collect literals of `e` and of the `PastaLean.User` definitions it reaches into the refs. -/
partial def literalsGo (visited : IO.Ref NameSet) (strs : IO.Ref (Array String)) (ints : IO.Ref (Array Int))
    (ctorLits : IO.Ref (Array (Name × Array Int))) (budget : IO.Ref Nat) (e : Expr) : MetaM Unit := do
  e.forEach fun
    | .lit (.strVal v) => if v.length ≤ 40 then strs.modify (·.push v) else pure ()
    | .lit (.natVal n) => if n ≤ 10 ^ 12 then ints.modify (·.push n) else pure ()
    | a@(.app ..) => do
        -- only `Libraries.re` calls and library constructors are read, so test the head first
        let some f := a.getAppFn.constName? | pure ()
        if (`Libraries.re).isPrefixOf f then
          match a.getAppArgs.toList with
          | .lit (.strVal pat) :: rest =>
              if (← getConstInfo f).type.getForallBinderNames.length == rest.length + 1 then
                strs.modify (· ++ (regexPoolStrings pat (rest.foldl (fun acc r => Libraries.re.orFlags acc (regexFlagsOf r)) 0)).toArray)
          | _ => pure ()
        match f with
        | .str (.str ns c) "new" =>
            -- `C.new` (or `C'rn.new`) of a library class, with leading integer literals
            if (`Libraries).isPrefixOf f then
              let args := a.getAppArgs
              let lits := (args.toList.takeWhile (·.int?.isSome)).filterMap (·.int?)
              if lits.length ≥ 2 && (← getConstInfo f).type.getForallBinderNames.length == args.size then
                ctorLits.modify (·.push (.str ns (c.replace "'rn" ""), lits.toArray))
        | _ => pure ()
    | _ => pure ()
  for c in e.getUsedConstants do
    if !isProgramConst c || (← visited.get).contains c then continue
    visited.modify (·.insert c)
    let b ← budget.get
    if b == 0 then return
    budget.set (b - 1)
    if let some d := defBody? (← getEnv) c then literalsGo visited strs ints ctorLits budget d.value

/-- String and natural-number literals in `e` and in the program definitions it reaches (the
translated program, `PastaLean.User`, and the Python-module libraries it calls, `Libraries` — so
`json.loads(s)` contributes `"null"`; never the runtime or Mathlib), for the literal pool. -/
def literalsOf (e : Expr) (fuel : Nat := 400) : MetaM (Array String × Array Int × Array (Name × Array Int)) := do
  let strs ← IO.mkRef (#[] : Array String)
  let ints ← IO.mkRef (#[] : Array Int)
  let ctorLits ← IO.mkRef #[]
  literalsGo (← IO.mkRef {}) strs ints ctorLits (← IO.mkRef fuel) e
  return ((← strs.get).toList.eraseDups.toArray, (← ints.get).toList.eraseDups.toArray,
    (← ctorLits.get).toList.eraseDups.toArray)

/-- `RefuteConfig` as a term (it must reach the compiled search unchanged). -/
def configExpr (cfg : RefuteConfig) : Expr := toExpr cfg

/-- The type a binder is searched over, and the value a searched `v` stands for: a function `α → β` is
searched as a `PyFn α β` (a table and a default) applied, everything else as itself. -/
def searchView (τ : Expr) : MetaM (Expr × (Expr → MetaM Expr)) := do
  match ← whnfR τ with
  | .forallE _ α β _ =>
      if β.hasLooseBVars then return (τ, pure)
      let ok ← try (synthInstance (← mkAppM ``BEq #[α]) *> pure true) catch _ => pure false
      if !ok then return (τ, pure)
      return (← mkAppM ``PyFn #[α, β], fun v => mkAppM ``PyFn.apply #[v])
  | _ => return (τ, pure)

/-- The search over an obligation as a closed `IO SearchOutcome`, or why it cannot be built. -/
def searchExpr (ob : Obligation) (cfg : RefuteConfig) : MetaM (Except String Expr) := do
  if mentionsReal ob.body || (← ob.guards.anyM fun g => return mentionsReal (← inferType g)) then
    return .error "involves ℝ, which is not computable"
  if ob.body.hasAnyFVar (fun f => ob.guards.any (·.fvarId! == f)) then
    return .error "the property depends on a proof of its precondition"
  let views ← ob.data.mapM fun x => do searchView (← inferType x)
  let tys := views.map (·.1)
  let tupTy ← tupleType tys
  let some arbInst ← (try some <$> synthInstance (← mkAppM ``PyArb #[tupTy]) catch _ => pure none)
    | let missing ← tys.filterM fun t => do
          return (← try some <$> synthInstance (← mkAppM ``PyArb #[t]) catch _ => pure none).isNone
      return .error s!"no generator for {← missing.mapM ppExpr}"
  withLocalDeclD `t tupTy fun t => do
    let projs ← (List.range ob.data.size).toArray.mapM (tupleProj t)
    let vals ← (projs.zip views).mapM fun (p, (_, f)) => f p
    let inst (e : Expr) : Expr := e.replaceFVars ob.data vals
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
    -- the search runs the instrumented program, whose probes steer it (branch coverage and distance)
    let (gb, _) ← if cfg.instrument then instrument #[← instantiateMVars guardB, ← instantiateMVars bodyB]
      else pure (#[guardB, bodyB], 0)
    let litsF ← mkLambdaFVars #[t] litsList
    let guardF ← mkLambdaFVars #[t] gb[0]!
    let bodyF ← mkLambdaFVars #[t] gb[1]!
    let strategy := mkApp2 (mkConst (if cfg.instrument then ``coverageStrategy else ``plainStrategy)) tupTy arbInst
    return .ok (mkAppN (mkConst ``runSearch) #[tupTy, arbInst, strategy, litsF, guardF, bodyF, configExpr cfg])

/-! ### Plausible: the primary engine

The obligation is handed to Plausible's own `Testable` machinery — property decomposition, sampling,
guard discarding, shrinking — as `∀ x : Lit τ, guard x.val = true → body x.val = true`, over the
runnable `Bool`s `mkDecideRunnable` builds (so every `Decidable` Plausible needs exists). `Lit τ` samples
through `PyArb τ` (literal-pool-biased, library-aware) and its `Repr` is the value's exact `PyLit` JSON,
so the `x := …` lines of Plausible's counterexample decode losslessly into a typed witness. -/

open Plausible in
/-- Plausible's configuration for one chunk of `n` tests. -/
def plausibleConfig (n maxSize seed : Nat) : Plausible.Configuration :=
  { numInst := n, maxSize, randomSeed := some seed, quiet := true }

/-- A value Plausible samples and prints as its `PyLit` JSON. -/
structure Lit (α : Type) where
  val : α

instance {α : Type} [PyArb α] : Repr (Lit α) := ⟨fun x _ => (PyLit.toJson (ToPyLit.toLit x.val)).compress⟩
instance {α : Type} [PyArb α] : Plausible.Shrinkable (Lit α) :=
  ⟨fun x => ((PyArb.shrink x.val).filter fun c => (ToPyLit.toLit c).measure < (ToPyLit.toLit x.val).measure).map Lit.mk⟩
/-- The random state the previous binder's value was drawn from. -/
initialize lastDraw : IO.Ref (Option StdGen) ← IO.mkRef none

@[never_extract, noinline]
unsafe def swapLastDrawImpl (g : StdGen) : Option StdGen := unsafeBaseIO (lastDraw.swap (some g))

@[never_extract, implemented_by swapLastDrawImpl]
opaque swapLastDraw (g : StdGen) : Option StdGen

/-- Plausible's latest draws (one value per binder, last binder last) and when the latest was made: a
chunk that stops drawing for longer than the per-case deadline is stuck evaluating those values. -/
initialize plausibleDraws : IO.Ref (Array PyLit × Nat) ← IO.mkRef (#[], 0)

@[never_extract, noinline]
unsafe def noteDrawImpl {α : Type} [ToPyLit α] (v : α) : α :=
  unsafeBaseIO do
    let now ← IO.monoMsNow
    plausibleDraws.modify fun (ds, _) => ((if ds.size ≥ 64 then ds.extract 32 ds.size else ds).push (ToPyLit.toLit v), now)
    pure v

/-- `v`, noted as Plausible's latest draw (see `plausibleDraws`). -/
@[never_extract, implemented_by noteDrawImpl]
def noteDraw {α : Type} [ToPyLit α] (v : α) : α := v

/-- A fifth of the time a binder is drawn from the previous binder's random state: for two binders of
one type that is the same value (`compare_version_strings(v, v)`), otherwise just another draw. -/
instance {α : Type} [PyArb α] : Plausible.Arbitrary (Lit α) where
  arbitrary := do
    let replay := (← Plausible.Gen.choose Nat 0 4 (by omega)).val == 0
    let prev := swapLastDraw (← get).down
    if replay then if let some p := prev then set (ULift.up p)
    return Lit.mk (noteDraw (← PyArb.arb))
instance {α : Type} [PyArb α] : Plausible.SampleableExt (Lit α) := { proxy := Lit α, interp := id }

/-- Plausible's verdict, with the proposition erased so it can leave compiled code. -/
inductive PlausibleOutcome where
  | passed
  | gaveUp (n : Nat)
  | failed (vars : List String) (shrinks : Nat)
  deriving Inhabited

def PlausibleOutcome.ofResult {p : Prop} : Plausible.TestResult p → PlausibleOutcome
  | .success _ => .passed
  | .gaveUp n => .gaveUp n
  | .failure _ vs n => .failed vs n

private unsafe def raiseCheckImpl (allowed : List String) (errorsFail : Bool) (b : Unit → Bool) : Bool :=
  match unsafeEIO (do
      discard <| PastaLean.pyErrorLog.swap none
      let r ← IO.lazyPure b
      let e ← PastaLean.pyErrorLog.swap none
      return e.any (errAllowed allowed) || (r && !(errorsFail && e.isSome)) : IO Bool) with
  | .ok r => r
  | .error _ => false

/-- The property `b ()` under the contract's `raises:`: a recorded runtime error of an allowed kind
passes; any other one fails when `errorsFail` (the runnable twin executes). -/
@[implemented_by raiseCheckImpl]
def raiseCheck (_allowed : List String) (_errorsFail : Bool) (b : Unit → Bool) : Bool := b ()

/-- `b ()`, except that a Python runtime error recorded while computing it (`pyErrorLog`) makes it
`false`: the runnable twin executes, so an error there is a raise, as under CPython (`errorsFail`). -/
def raiseFree (b : Unit → Bool) : Bool := raiseCheck [] true b

/-- The obligation as the decorated proposition Plausible tests, or why it cannot be. -/
def plausibleProp (ob : Obligation) (errorsFail : Bool) (allowed : List String := []) :
    MetaM (Except String Expr) := do
  let views ← ob.data.mapM fun x => do searchView (← inferType x)
  -- plain positional names: Plausible prints them, and hygienic binder names do not round-trip
  let decls := (views.mapIdx fun i (τ, _) => (Name.mkSimple s!"x{i}", fun (_ : Array Expr) => mkAppM ``Lit #[τ]))
  withLocalDeclsD decls fun ys => do
    let vals ← (ys.zip views).mapM fun (y, (_, f)) => do f (← mkAppM ``Lit.val #[y])
    let inst (e : Expr) : Expr := e.replaceFVars ob.data vals
    let mut props : Array Expr := #[]
    for g in ob.guards do
      match ← mkDecideRunnable (inst (← inferType g)) with
      | .error e => return .error e
      | .ok d =>
          let d := if errorsFail then mkApp (mkConst ``raiseFree) (mkLambda `_ .default (mkConst ``Unit) d) else d
          props := props.push (← mkEq d (toExpr true))
    let body ← match ← mkDecideRunnable (inst ob.body) with
      | .error e => return .error e
      | .ok d =>
          let d := if errorsFail || !allowed.isEmpty then
              mkAppN (mkConst ``raiseCheck) #[toExpr allowed, toExpr errorsFail, mkLambda `_ .default (mkConst ``Unit) d]
            else d
          mkEq d (toExpr true)
    let prop ← props.foldrM (fun g acc => mkArrow g acc) body
    return .ok (← Plausible.Decorations.addDecorations (← mkForallFVars ys prop))

/-- Decode Plausible's `x{i} := json` lines into a witness, in binder order. -/
def decodePlausible (arity : Nat) (vars : List String) : Option (List PyLit) := do
  let found : List (String × PyLit) := vars.filterMap fun line =>
    match line.splitOn " := " with
    | n :: rest => match Json.parse (" := ".intercalate rest) with
        | .ok j => (PyLit.fromJson? j).toOption.map (n, ·)
        | .error _ => none
    | [] => none
  (List.range arity).mapM fun i => found.lookup s!"x{i}"

/-- Tests per Plausible run: the budget is spent as a sequence of short runs with fresh seeds, so a run
never outlives the deadline by more than one chunk (a Lean task cannot be cancelled). -/
def plausibleChunk : Nat := 200

/-- Run Plausible over the obligation within half the time budget. `none`: not testable this way. -/
unsafe def runPlausible (ob : Obligation) (names : Array Name) (cfg : RefuteConfig) :
    MetaM (Option SearchOutcome) := do
  let .ok prop ← plausibleProp ob cfg.errorsFail cfg.allowed | return none
  let some inst ← try some <$> synthInstance (mkApp (mkConst ``Plausible.Testable) prop) catch _ => pure none
    | return none
  let chunk := min cfg.numInst plausibleChunk
  let run ← withLocalDeclD `seed (mkConst ``Nat) fun seed => do
    let pcfg := mkAppN (mkConst ``plausibleConfig) #[toExpr chunk, toExpr cfg.maxSize, seed]
    let act := mkAppN (mkConst ``Functor.map [0, 0]) #[mkConst ``IO, (← synthInstance (← mkAppM ``Functor #[mkConst ``IO])),
      ← mkAppM ``Plausible.TestResult #[prop], mkConst ``PlausibleOutcome,
      ← mkAppOptM ``PlausibleOutcome.ofResult #[prop],
      mkAppN (mkConst ``Plausible.Testable.checkIO) #[prop, inst, pcfg]]
    mkLambdaFVars #[seed] act
  let runTy := mkForall `seed .default (mkConst ``Nat) (mkApp (mkConst ``IO) (mkConst ``PlausibleOutcome))
  let io ← evalExpr (Nat → IO PlausibleOutcome) runTy (← instantiateMVars run)
  let started ← IO.monoMsNow
  let deadline := started + cfg.timeMs / 2
  let mut tested := 0
  let mut discarded := 0
  let mut round := 0
  while tested < cfg.numInst && (← IO.monoMsNow) < deadline do
    plausibleDraws.set (#[], ← IO.monoMsNow)
    let task ← IO.asTask (io (cfg.seed + round * 7919))
    round := round + 1
    let mut stuck : Option (List PyLit) := none
    while !(← IO.hasFinished task) && (← IO.monoMsNow) < deadline do
      let (ds, lastMs) ← plausibleDraws.get
      -- no draw for a per-case deadline: the property is stuck on the latest draws
      if (← IO.monoMsNow) - lastMs > cfg.perCaseMs && ds.size ≥ names.size then
        stuck := some (ds.extract (ds.size - names.size) ds.size).toList
        break
      IO.sleep 2
    let ms := (← IO.monoMsNow) - started
    if let some ws := stuck then
      return some { status := .refuted, witness? := some ws, hang := true, tested, discarded, ms,
                    seed := cfg.seed, engine := "plausible" }
    -- An unfinished run keeps its thread busy: flag it so the driver restarts the backend.
    if !(← IO.hasFinished task) then
      return some { status := .timeout, tested, discarded, ms, seed := cfg.seed, engine := "plausible", hang := true }
    match task.get with
    | .error _ => return none
    | .ok .passed => tested := tested + chunk
    | .ok (.gaveUp n) => discarded := discarded + n; tested := tested + (chunk - min chunk n)
    | .ok (.failed vars shrinks) =>
        match decodePlausible names.size vars with
        | some ws => return some { status := .refuted, witness? := some ws, shrinks, tested, discarded, ms,
                                   seed := cfg.seed, engine := "plausible" }
        | none => return none
  let ms := (← IO.monoMsNow) - started
  let status := if tested == 0 && discarded > 0 then SearchStatus.gaveUp else .noCounterexample
  return some { status, tested, discarded, ms, seed := cfg.seed, engine := "plausible" }

/-- Run `act` with the search's pools filled from the obligation's literals (`literalsOf`) and its draw
state reset; the pools are emptied afterwards. -/
def withPools {α} (pools : Array String × Array Int × Array (Name × Array Int)) (cfg : RefuteConfig)
    (act : MetaM α) : MetaM α := do
  let (s, i, c) := pools
  literalPool.set (s, i)
  ctorPool.set c
  cmpPool.set (#[], #[])
  intCapRef.set cfg.intCap
  -- a warm backend serves many searches: a seed must give the same search every time
  lastDraw.set none
  try act finally
    literalPool.set (#[], #[])
    ctorPool.set #[]
    cmpPool.set (#[], #[])
    intCapRef.set 0

/-- Run the search over `ty`: Plausible first; the enumeration/random search when Plausible finds
nothing (small exhaustive cases, per-case deadlines for loops) or cannot test the obligation. -/
unsafe def refuteTypeUnsafe (ty : Expr) (cfg : RefuteConfig) :
    MetaM (SearchOutcome × Array (Name × Expr)) :=
  withObligation ty fun ob => do
    let names ← ob.binders
    let pools ← literalsOf ty
    let viaPlausible ← if !cfg.plausible then pure none
      else withPools pools cfg do try runPlausible ob (names.map (·.1)) cfg catch _ => pure none
    if let some o := viaPlausible then
      if o.status == .refuted then return (o, names)
    let plausibleHung := viaPlausible.any (·.hang)
    let build (cfg : RefuteConfig) : MetaM (Except String (IO SearchOutcome)) := do
      match ← searchExpr ob cfg with
      | .error why => return .error why
      | .ok e =>
          -- the instrumented copies are `unsafe` definitions
          return .ok (← evalExpr (IO SearchOutcome) (mkApp (mkConst ``IO) (mkConst ``SearchOutcome))
            (← instantiateMVars e) (safety := .unsafe))
    -- instrumentation only steers the search: if the instrumented program does not compile, search the
    -- program as it is
    let built ← try build cfg catch e => if cfg.instrument then build { cfg with instrument := false } else throw e
    match built with
    | .error why => return ({ status := .untestable why, seed := cfg.seed }, names)
    | .ok act =>
        let out ← withPools pools cfg act
        return ({ out with hang := out.hang || plausibleHung }, names)

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


/-- An `.int` literal at or above this offset stands for a symbolic integer (`symLeaves`): the solver
finishes a witness by solving for its integer leaves while its shape stays concrete. -/
def symLeafBase : Int := 10 ^ 40

initialize symLeaves : IO.Ref (Array Expr) ← IO.mkRef #[]

/-- A `PyLit` as a Lean term of type `τ`; the same literal lands as `ℚ` in one twin and `Float` in the
other because the target type decides. -/
partial def litToExpr (τ : Expr) (l : PyLit) : MetaM Expr := do
  let τ ← whnfR τ
  if let .int n := l then
    if n ≥ symLeafBase then
      if let some v := (← symLeaves.get)[(n - symLeafBase).toNat]? then
        match τ.getAppFn.constName? with
        | some ``Int => return v
        | some ``Nat => return ← mkAppM ``Int.toNat #[v]
        | some ``Rat => return ← mkAppOptM ``Int.cast #[mkConst ``Rat, none, v]
        | some ``Float => return ← mkAppM ``Float.ofInt #[v]
        | _ => pure ()
  if let (.forallE _ α β _, .fn table d) := (τ, l) then
    let pairTy ← mkAppM ``Prod #[α, β]
    let pairs ← table.mapM fun (k, v) => do mkAppM ``Prod.mk #[← litToExpr α k, ← litToExpr β v]
    let f ← mkAppOptM ``PyFn.mk #[α, β, ← mkListLit pairTy pairs, ← litToExpr β d]
    return ← mkAppM ``PyFn.apply #[f]
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
      unless isStructure env n do throwError "refute: {n} is not a structure"
      let ctor := getStructureCtor env n
      let params := τ.getAppArgs
      let fieldTys ← forallTelescopeReducing (← instantiateForall ctor.type params) fun xs _ =>
        xs.mapM fun x => do return ((← x.fvarId!.getDecl).userName, ← inferType x)
      let mut args := #[]
      for (fname, fty) in fieldTys do
        if fty.hasLooseBVars then throwError "refute: dependent field {fname}"
        -- A library class keeps Python's public names in its literal (`year` for the field `_year`); an
        -- `Option` field the literal omits (a naive `datetime`'s `_tzinfo`) is `none`.
        let name := fname.toString
        -- a parent class (`toBase`) is built from the same literal: its fields are the object's
        if (isSubobjectField? env n fname).isSome then
          args := args.push (← litToExpr fty l); continue
        match fields.find? (fun (k, _) => k == name || "_" ++ k == name) with
        | some (_, v) => args := args.push (← litToExpr fty v)
        | none =>
            if fty.isAppOfArity ``Option 1 then args := args.push (← mkAppOptM ``Option.none #[fty.appArg!])
            else throwError "refute: missing field {fname}"
      return mkAppN (mkAppN (mkConst ctor.name τ.getAppFn.constLevels!) params) args
  | _, _ => throwError "refute: cannot place {repr l} at type {← ppExpr τ}"

end PastaLean.Refute
