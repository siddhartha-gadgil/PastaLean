import PastaLean.PyAPI.PyPanic
import PastaLean.PyVerify.Refute.Arb

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
  numInst : Nat := 100
  maxSize : Nat := 30
  seed : Nat := 0x5EED
  /-- Wall-clock budget for the whole search, in milliseconds. -/
  timeMs : Nat := 2000
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

def searchLoop {α : Type} [PyArb α] (lits : α → List PyLit) (guard body : α → Bool)
    (cfg : RefuteConfig) (inflight : IO.Ref (Option Inflight)) : IO SearchOutcome := do
  let start ← IO.monoMsNow
  let elapsed : IO Nat := do return (← IO.monoMsNow) - start
  let check (x : α) : IO CaseResult := do
    inflight.set (some { lits := lits x, startMs := ← IO.monoMsNow })
    -- `lazyPure` pins the evaluation between the two writes.
    discard <| PastaLean.pyErrorLog.swap none
    let r ← IO.lazyPure fun _ =>
      if !guard x then CaseResult.discard else if body x then .pass else .fail
    let err ← PastaLean.pyErrorLog.swap none
    inflight.set none
    return if cfg.errorsFail && err.isSome && r matches .pass then .fail else r
  let mut st := mkStdGen cfg.seed
  let mut tested := 0
  let mut discarded := 0
  let mut found : Option (α × Bool) := none
  -- Small-scope exhaustive phase: deterministic, finds the smallest counterexample there is up to the
  -- depth, and a sparse precondition cannot starve it the way it starves random draws.
  let mut enumerated := 0
  for d in [1:cfg.enumDepth + 1] do
    if found.isSome || enumerated ≥ cfg.enumMax || (← elapsed) > cfg.timeMs / 2 then break
    for x in (PyArb.enum d (cfg.enumMax - enumerated) : List α) do
      if enumerated ≥ cfg.enumMax || (← elapsed) > cfg.timeMs / 2 then break
      enumerated := enumerated + 1
      match ← check x with
      | .discard => discarded := discarded + 1
      | .pass => tested := tested + 1
      | .fail => tested := tested + 1; found := some (x, false); break
      | .hang => tested := tested + 1; found := some (x, true); break
  let discardedBeforeRandom := discarded
  let mut i := 0
  while tested < cfg.numInst + enumerated && found.isNone do
    if (← elapsed) > cfg.timeMs then
      return { status := .timeout, tested, discarded, ms := ← elapsed, seed := cfg.seed }
    if discarded - discardedBeforeRandom > cfg.maxDiscardRatio * cfg.numInst then
      return { status := .gaveUp, tested, discarded, ms := ← elapsed, seed := cfg.seed }
    -- Sizes ramp up over the run, as in Plausible's own suite.
    let size := (cfg.maxSize * (i % (cfg.numInst + 1))) / cfg.numInst + 1
    i := i + 1
    match runGen (PyArb.arb : Gen α) size st with
    | .error _ => discarded := discarded + 1
    | .ok (x, st') =>
      st := st'
      match ← check x with
      | .discard => discarded := discarded + 1
      | .pass => tested := tested + 1
      | .fail => tested := tested + 1; found := some (x, false)
      | .hang => tested := tested + 1; found := some (x, true)
  let some (x₀, hang) := found
    | return { status := .noCounterexample, tested, discarded, ms := ← elapsed, seed := cfg.seed }
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
           witness? := some (lits x), hang, seed := cfg.seed }

/-- Run the search on its own thread under one watchdog. Checks run synchronously; the watchdog polls
the case in flight, and one that outlives `perCaseMs` is reported as non-terminating on that input.
A stuck evaluation cannot be cancelled and keeps its thread. -/
def runSearch {α : Type} [PyArb α] (lits : α → List PyLit) (guard body : α → Bool)
    (cfg : RefuteConfig) : IO SearchOutcome := do
  let inflight ← IO.mkRef none
  let work ← IO.asTask (prio := .dedicated) (searchLoop lits guard body cfg inflight)
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
    ("ms", Lean.toJson o.ms), ("seed", Lean.toJson o.seed), ("hang", Lean.toJson o.hang)] ++
    (match o.status with | .untestable why => [("reason", Lean.toJson why)] | _ => []) ++
    (match o.witness? with | some ws => [("lits", Lean.toJson ws)] | none => []))

end PastaLean.Refute
