import PastaLean.PyAPI.PyPanic
import PastaLean.PyAPI.Core
import PastaLean.PyVerify.Refute.Arb
import PastaLean.PyVerify.Refute.Coverage

/-!
# The search loop

Draw inputs of a growing size, keep those that satisfy the guards (the preconditions), and stop at the
first one the property rejects; then shrink it greedily to a smaller input that still passes the guards
and still fails. Seeded, so a run reproduces exactly. Each evaluation runs as a task with a deadline:
a buggy loop that never terminates on a generated input is itself worth reporting, and must not hang
the search.
-/

namespace PastaLean.Refute

open Plausible Lean

structure RefuteConfig where
  /-- Test count cap; the time budget normally ends the search first. -/
  numInst : Nat := 100000
  maxSize : Nat := 30
  seed : Nat := 0x5EED
  /-- Wall-clock budget for the whole search, in milliseconds. -/
  timeMs : Nat := 1000
  /-- Deadline for one evaluation of the property, in milliseconds. -/
  perCaseMs : Nat := 200
  /-- Give up once this many draws per requested test failed the guards. -/
  maxDiscardRatio : Nat := 10
  shrink : Bool := true
  maxShrinks : Nat := 200
  /-- A runtime Python error (`pyErrorLog`) during the property counts as failing it: the runnable
  twin executes; the provable twin keeps the logical (default) value. -/
  errorsFail : Bool := false
  /-- Exhaustive phase first: every input up to this depth, smallest first. `0` disables it. -/
  enumDepth : Nat := 4
  /-- Cap on inputs the exhaustive phase may check before random search takes over. -/
  enumMax : Nat := 3000
  /-- Run Plausible first (the primary engine). Off for `taste?`'s quick pre-check, where compiling a
  Plausible run per obligation costs more than the check is worth. -/
  plausible : Bool := true
  /-- Exceptions the contract allows (`raises:`): a runtime error of one of these kinds is a pass. -/
  allowed : List String := []
  /-- Run `grind` on guards ∧ ¬body for a model or a proof. -/
  solver : Bool := true
  /-- Search the instrumented program (coverage-guided). Off for `taste?`'s quick pre-check, where
  copying and compiling the program per obligation costs more than the check is worth. -/
  instrument : Bool := true
  /-- Magnitude bound on generated integers (`0`: none): set on the retry after the backend ran out of
  memory (a pool constant such as `10**9 + 7` drawn as a table size). -/
  intCap : Nat := 0
  deriving Repr, Inhabited, Lean.ToExpr

inductive SearchStatus where
  | refuted
  | noCounterexample
  | gaveUp
  | timeout
  | untestable (why : String)
  deriving Repr, Inhabited, BEq

def SearchStatus.toString : SearchStatus → String
  | .refuted => "refuted"
  | .noCounterexample => "noCounterexample"
  | .gaveUp => "gaveUp"
  | .timeout => "timeout"
  | .untestable _ => "untestable"

structure SearchOutcome where
  status : SearchStatus
  tested : Nat := 0
  discarded : Nat := 0
  shrinks : Nat := 0
  ms : Nat := 0
  witness? : Option (List PyLit) := none
  /-- The witness made the property loop past `perCaseMs` instead of answering. -/
  hang : Bool := false
  seed : Nat := 0
  /-- Which engine produced the outcome: `plausible` (primary) or `search` (enumeration/random fallback). -/
  engine : String := "search"
  /-- Branch directions the search reached in the instrumented program. -/
  covered : Nat := 0
  /-- Where the search stalled: the inputs that came closest to branch directions it never reached,
  nearest first, for the solver to finish (`solvePlateau`). -/
  seeds : List (List PyLit) := []
  deriving Repr, Inhabited

/-- What one evaluation of guard-then-property said. -/
inductive CaseResult where
  | discard
  | pass
  | fail
  | hang

/-- The case being evaluated right now and when it started — what the watchdog reads. -/
structure Inflight where
  lits : List PyLit
  startMs : Nat

/-- Run a generator at a size with an explicit random state, so the search is reproducible. -/
def runGen (g : Gen α) (size : Nat) (st : StdGen) : Except String (α × StdGen) :=
  match ReaderT.run (StateT.run g (ULift.up st)) ⟨size⟩ with
  | Except.ok (a, st') => Except.ok (a, st'.down)
  | Except.error e => Except.error (toString (repr e))

/-- A recorded runtime error (its kind, `pyErrorLog`) of a kind the contract allows. -/
def errAllowed (allowed : List String) (kind : String) : Bool := allowed.any (PastaLean.pyKindIsA kind ·)

/-- A coverage goal: branch, direction, and whether *every* hit of the branch in one evaluation must go
that way (a branch in a loop: `all(5 <= t <= 17 for t in times)` needs each iteration in range). -/
abbrev Goal := Nat × Bool × Bool

/-- Inputs that came closest to each goal not reached yet: distance and input. -/
abbrev Targets (α : Type) := Std.HashMap Goal (Nat × α)

/-- How the search picks its next input and learns from an evaluation: coverage-guided over an
instrumented program, or plain (fresh draws, nothing learnt). Passed in, so a plain search does not
compile the coverage machinery when `evalExpr` specialises it to the input type. -/
structure Strategy (α : Type) where
  next : Array α → Targets α → Gen α
  observe : α → Array α → Std.HashSet Goal → Targets α → IO (Array α × Std.HashSet Goal × Targets α)

/-- The next input of the coverage-guided search: a few times in ten, climb toward a branch direction
not reached yet (mutate the input that came closest); otherwise mutate an input that reached new
coverage, cross two of them, or draw a fresh one. -/
def nextInput {α : Type} [PyArb α] (corpus : Array α) (targets : Targets α) : Gen α := do
  let k := (← Gen.choose Nat 0 9 (by omega)).val
  let mutateN (x : α) : Gen α := do
    let mut y := x
    for _ in [0:(← Gen.choose Nat 1 3 (by omega)).val] do y ← PyArb.mutate y
    return y
  if k < 4 && !targets.isEmpty then
    -- among the closest few, so one unreachable branch does not absorb every step
    let best := (targets.toArray.qsort (fun a b => a.2.1 < b.2.1)).extract 0 8
    let i ← Gen.choose Nat 0 (best.size - 1) (by omega)
    -- climb by steps scaled to the distance left, now and then a plain mutation
    if let some (_, (d, x)) := best[i.val]? then
      return ← if ← Gen.chooseAny Bool then PyArb.climb x d else mutateN x
  if k < 8 && !corpus.isEmpty then
    let i ← Gen.choose Nat 0 (corpus.size - 1) (by omega)
    if let some x := corpus[i.val]? then return ← mutateN x
  -- two inputs that reached different goals, combined (a conjunction neither reaches alone)
  if k < 9 && corpus.size ≥ 2 && (← Gen.chooseAny Bool) then
    let i ← Gen.choose Nat 0 (corpus.size - 1) (by omega)
    let j ← Gen.choose Nat 0 (corpus.size - 1) (by omega)
    if let (some x, some y) := (corpus[i.val]?, corpus[j.val]?) then return ← PyArb.crossover x y
  PyArb.arb

/-- Fold the coverage the last evaluation of `x` logged into the search state, and add the operands its
comparisons logged to the literal pool (`x == 8314` makes `8314` drawable). -/
def observeCoverage {α : Type} (x : α) (corpus : Array α) (seen : Std.HashSet Goal) (targets : Targets α) :
    IO (Array α × Std.HashSet Goal × Targets α) := do
  let (log, (ss, is)) ← takeCoverage
  -- each goal this evaluation reached, and for each goal it did not, how far it was
  let mut reached : Array Goal := #[]
  let mut near : Array (Goal × Nat) := #[]
  -- per branch: hits each way, and the distance summed over the hits going the other way
  let mut agg : Std.HashMap Nat (Nat × Nat × Nat × Nat) := {}
  for (id, dir, d) in log do
    reached := reached.push (id, dir, false)
    near := near.push ((id, !dir, false), d)
    let (t, f, dt, df) := agg.getD id (0, 0, 0, 0)
    agg := agg.insert id (if dir then (t + 1, f, dt, df + d) else (t, f + 1, dt + d, df))
  for (id, (t, f, dt, df)) in agg do
    if t + f ≥ 2 then
      if f == 0 then reached := reached.push (id, true, true) else near := near.push ((id, true, true), dt)
      if t == 0 then reached := reached.push (id, false, true) else near := near.push ((id, false, true), df)
  let mut corpus := corpus
  let mut seen := seen
  let mut targets := targets
  let mut fresh := false
  for g in reached do
    if !seen.contains g then
      seen := seen.insert g
      targets := targets.erase g
      fresh := true
  for (g, d) in near do
    if !seen.contains g && targets[g]?.all (d < ·.1) then targets := targets.insert g (d, x)
  if fresh && corpus.size < 512 then corpus := corpus.push x
  if !ss.isEmpty || !is.isEmpty then
    cmpPool.modify fun (ps, pi) =>
      (ss.foldl (fun a w => if a.size < 400 && !a.contains w then a.push w else a) ps,
       is.foldl (fun a n => if a.size < 400 && !a.contains n then a.push n else a) pi)
  return (corpus, seen, targets)

/-- The closest inputs to the `k` nearest unreached branch directions. -/
def plateauSeeds {α : Type} (lits : α → List PyLit) (targets : Targets α) (k : Nat := 3) : List (List PyLit) :=
  ((targets.toArray.qsort (fun a b => a.2.1 < b.2.1)).toList.map (lits ·.2.2)).eraseDups.take k

def coverageStrategy {α : Type} [PyArb α] : Strategy α := ⟨nextInput, observeCoverage⟩

def plainStrategy {α : Type} [PyArb α] : Strategy α := ⟨fun _ _ => PyArb.arb, fun _ c s t => pure (c, s, t)⟩

def searchLoop {α : Type} [PyArb α] (strategy : Strategy α) (lits : α → List PyLit) (guard body : α → Bool)
    (cfg : RefuteConfig) (inflight : IO.Ref (Option Inflight)) : IO SearchOutcome := do
  let start ← IO.monoMsNow
  let elapsed : IO Nat := do return (← IO.monoMsNow) - start
  let check (x : α) : IO CaseResult := do
    inflight.set (some { lits := lits x, startMs := ← IO.monoMsNow })
    -- `lazyPure` pins the evaluation between the two writes.
    discard <| PastaLean.pyErrorLog.swap none
    let g ← IO.lazyPure fun _ => guard x
    -- a precondition that raises puts the input outside the function's domain, as under CPython
    let gErr ← PastaLean.pyErrorLog.swap none
    let r ← if !g || (cfg.errorsFail && gErr.isSome) then pure CaseResult.discard
      else IO.lazyPure fun _ => if body x then CaseResult.pass else .fail
    let err ← PastaLean.pyErrorLog.swap none
    inflight.set none
    return if err.any (errAllowed cfg.allowed) && !(r matches .discard) then .pass
      else if cfg.errorsFail && err.isSome && r matches .pass then .fail else r
  let mut st := mkStdGen cfg.seed
  let mut tested := 0
  let mut discarded := 0
  let mut found : Option (α × Bool) := none
  -- Coverage feedback from the instrumented program: inputs that reached a new branch direction, and
  -- for each direction not reached yet the input that came closest (smallest branch distance).
  let mut corpus : Array α := #[]
  let mut seen : Std.HashSet Goal := {}
  let mut targets : Targets α := {}
  discard takeCoverage
  -- Small-scope exhaustive phase: deterministic, finds the smallest counterexample there is up to the
  -- depth, and a sparse precondition cannot starve it the way it starves random draws.
  let mut enumerated := 0
  for d in [1:cfg.enumDepth + 1] do
    if found.isSome || enumerated ≥ cfg.enumMax || (← elapsed) > cfg.timeMs / 2 then break
    for x in (PyArb.enum d (cfg.enumMax - enumerated) : List α) do
      if enumerated ≥ cfg.enumMax || (← elapsed) > cfg.timeMs / 2 then break
      enumerated := enumerated + 1
      let res ← check x
      (corpus, seen, targets) ← strategy.observe x corpus seen targets
      match res with
      | .discard => discarded := discarded + 1
      | .pass => tested := tested + 1
      | .fail => tested := tested + 1; found := some (x, false); break
      | .hang => tested := tested + 1; found := some (x, true); break
  let discardedBeforeRandom := discarded
  let mut i := 0
  while tested < cfg.numInst + enumerated && found.isNone do
    let stopped (status : SearchStatus) : IO SearchOutcome := do
      return { status, tested, discarded, ms := ← elapsed, seed := cfg.seed, covered := seen.size,
               seeds := plateauSeeds lits targets }
    if (← elapsed) > cfg.timeMs then return ← stopped .timeout
    if discarded - discardedBeforeRandom > cfg.maxDiscardRatio * cfg.numInst then return ← stopped .gaveUp
    -- Sizes ramp up over the run, as in Plausible's own suite.
    let size := (cfg.maxSize * (i % (cfg.numInst + 1))) / cfg.numInst + 1
    i := i + 1
    match runGen (strategy.next corpus targets) size st with
    | .error _ => discarded := discarded + 1
    | .ok (x, st') =>
      st := st'
      let res ← check x
      (corpus, seen, targets) ← strategy.observe x corpus seen targets
      match res with
      | .discard => discarded := discarded + 1
      | .pass => tested := tested + 1
      | .fail => tested := tested + 1; found := some (x, false)
      | .hang => tested := tested + 1; found := some (x, true)
  let covered := seen.size
  let some (x₀, hang) := found
    | return { status := .noCounterexample, tested, discarded, ms := ← elapsed, seed := cfg.seed, covered,
               seeds := plateauSeeds lits targets }
  -- Greedy shrink: take the first smaller candidate that still passes the guards and still fails.
  let cost (y : α) : Nat := ((lits y).map (·.toPyString.length)).foldl (· + ·) 0
  -- Only strictly shorter candidates are taken, which also guarantees the loop ends.
  let greedy (x₀ : α) (shrinks₀ : Nat) : IO (α × Nat) := do
    let mut x := x₀
    let mut shrinks := shrinks₀
    let mut progress := true
    while progress && shrinks < cfg.maxShrinks && (← elapsed) ≤ cfg.timeMs * 2 do
      progress := false
      for y in PyArb.shrink x do
        if cost y < cost x && (← check y) matches .fail then
          x := y
          shrinks := shrinks + 1
          progress := true
          break
    return (x, shrinks)
  let mut x := x₀
  let mut shrinks := 0
  if cfg.shrink && !hang then
    (x, shrinks) ← greedy x 0
    -- Greedy steps stall under a sparse precondition (halving one element breaks the guard), so also
    -- re-sample at small sizes and keep any failing input that reads shorter, then shrink that.
    for size in [1:cfg.maxSize / 2 + 2] do
      if (← elapsed) > cfg.timeMs * 2 then break
      for _ in [0:20] do
        match runGen (PyArb.arb : Gen α) size st with
        | .error _ => pure ()
        | .ok (y, st') =>
          st := st'
          if cost y < cost x then
            if (← check y) matches .fail then
              (x, shrinks) ← greedy y (shrinks + 1)
  return { status := .refuted, tested, discarded, shrinks, ms := ← elapsed,
           witness? := some (lits x), hang, seed := cfg.seed, covered }

/-- Run the search on its own thread under one watchdog. Checks run synchronously; the watchdog polls
the case in flight, and one that outlives `perCaseMs` is reported as non-terminating on that input.
A stuck evaluation cannot be cancelled and keeps its thread. -/
def runSearch {α : Type} [PyArb α] (strategy : Strategy α) (lits : α → List PyLit) (guard body : α → Bool)
    (cfg : RefuteConfig) : IO SearchOutcome := do
  let inflight ← IO.mkRef none
  let work ← IO.asTask (prio := .dedicated) (searchLoop strategy lits guard body cfg inflight)
  let start ← IO.monoMsNow
  let budget := 3 * cfg.timeMs + cfg.perCaseMs
  repeat
    if ← IO.hasFinished work then break
    let now ← IO.monoMsNow
    if let some c ← inflight.get then
      if now - c.startMs > cfg.perCaseMs then
        return { status := .refuted, witness? := some c.lits, hang := true, ms := now - start,
                 seed := cfg.seed }
    if now - start > budget then
      return { status := .timeout, ms := now - start, seed := cfg.seed }
    IO.sleep 2
  match work.get with
  | .ok o => return o
  | .error e => throw e

def SearchOutcome.toJson (o : SearchOutcome) : Json :=
  Json.mkObj ([
    ("status", Lean.toJson o.status.toString),
    ("tested", Lean.toJson o.tested), ("discarded", Lean.toJson o.discarded), ("shrinks", Lean.toJson o.shrinks),
    ("ms", Lean.toJson o.ms), ("seed", Lean.toJson o.seed), ("hang", Lean.toJson o.hang),
    ("engine", Lean.toJson o.engine), ("covered", Lean.toJson o.covered)] ++
    (match o.status with | .untestable why => [("reason", Lean.toJson why)] | _ => []) ++
    (match o.witness? with | some ws => [("lits", Lean.toJson ws)] | none => []))

end PastaLean.Refute
