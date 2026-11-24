import Lean
import PastaLean
import TypeInfer
import PALC

/-!
# PastaCheck — the example-program test runner (`lake test`)

Two things run under `lake test`:

1. **`#guard_msgs` / `#guard` unit tests** in the `PALC` library — these fire at *build* time, so
   importing `PALC` above makes `lake build` of this executable fail if any of them fail.
2. **Every Python program in `example_scripts/`** — all are translated in one warm pass
   (`pastalean batch --emit-lean`; the Python front end still owns AST→JSON), then each is
   **compile-checked in-process** by elaborating the generated Lean in the already-booted Mathlib
   environment (no `lake env lean` per file). A program passes when it converts, carries no
   unexpected `pyUnsupported`, and elaborates clean.

Generated `.lean` is written next to the `.py` for the "showcase" directories (so the output is
reviewable), and checked-then-discarded for the rest.
-/

open Lean Lean.Elab

def backendModules : Array Import :=
  #[{ module := `PastaLean }, { module := `Mathlib }, { module := `Libraries },
    { module := `Std.Tactic.Do }]

unsafe def bootEnv : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules (loadExts := true) backendModules {}

/-- Drop `import …` lines: the environment already has everything imported. -/
def stripImports (code : String) : String :=
  String.intercalate "\n" ((code.splitOn "\n").filter (fun l => ¬ l.trimAscii.startsWith "import "))

/-- Whether to run the twin-refinement check (`#twin_check`, `PastaLean/PyVerify/Twin/Check.lean`) on each
program after it elaborates. Off with `--no-twin`. -/
initialize twinCheckEnabled : IO.Ref Bool ← IO.mkRef true

/-- Per-pair twin verdicts (`{f, decl, verdict, detail}`) of the last checked program. -/
initialize lastTwinReport : IO.Ref (Array Json) ← IO.mkRef #[]

/-- Elaborate a generated program in `env`; `none` on success, else the first error message. With
the twin check on, `#twin_check` is appended IN MEMORY (never written to the generated file) and its
verdicts are left in `lastTwinReport`. -/
def checkProgram (env : Environment) (code : String) : IO (Option String) := do
  lastTwinReport.set #[]
  let twin ← twinCheckEnabled.get
  let src := stripImports code ++ (if twin then "\n\n#twin_check\n" else "")
  let inputCtx := Parser.mkInputContext src "<check>"
  let cmdState := Command.mkState env {} {}
  let frontendState ← Lean.Elab.IO.processCommands inputCtx {} cmdState
  let msgs := frontendState.commandState.messages
  unless msgs.hasErrors do
    if twin then
      for msg in msgs.toList do
        let s ← msg.data.toString
        if let some j := s.dropPrefix? "twin-report: " then
          if let .ok r := Json.parse j.toString then
            lastTwinReport.set ((r.getObjValAs? (Array Json) "pairs").toOption.getD #[])
    return none
  for msg in msgs.toList do
    if msg.severity == .error then
      let s := (← msg.data.toString).trimAscii.toString
      return some ((s.replace "\n" " ").take 160).toString
  return some "elaboration error"

/-- Translate every `.py` under `dir` through ONE warm backend (`pastalean batch --emit-lean`), and
return the parsed summary records `{file, status, error?, unsupported?, lean?}`. This is the single
expensive step (one Mathlib boot); the compile-checks that follow are all in-process. -/
def translateAll (pyBin : String) (dir : System.FilePath)
    (extraArgs : Array String := #[])
    (summaryPath : System.FilePath := "/tmp/pastacheck_summary.json") : IO (Array Json) := do
  let out ← IO.Process.output {
    cmd := pyBin,
    -- `--prove-asserts`: the CLI/API default is now opt-in (fast, leaves `:= by taste?`), but the
    -- test suite must exercise the full proof-search + splice path so a regression in taste?/proving
    -- fails `lake test`.
    args := #["-m", "pastalean", "batch", dir.toString, "--recursive", "--mode", "both",
              "--prove-asserts",
              "--emit-lean", "--summary", summaryPath.toString, "--quiet"] ++ extraArgs }
  unless (← summaryPath.pathExists) do
    throw (IO.userError s!"pastalean batch produced no summary:\n{out.stderr}")
  match Json.parse (← IO.FS.readFile summaryPath) with
  | .ok j => return (j.getObjValAs? (Array Json) "files").toOption.getD #[]
  | .error e => throw (IO.userError s!"could not parse batch summary: {e}")

/-- Files where a `pyUnsupported` placeholder is expected (best-effort degradation demos). -/
-- `pk_simulation.py` is KNOWN-DEGRADED: its `odeint(system, …)` callback captures and is passed as
-- a value, and `system(state, t)` has no inferred param types, so the whole body becomes a
-- placeholder. It passed silently until the `degraded` check below started reading the emitted Lean.
def expectUnsupported : List String := ["unsupported_demo.py", "pk_simulation.py"]

/-- Directories whose generated `.lean` is written next to the `.py` (reviewable output). -/
def writeInPlaceDirs : List String := ["showcase", "mvcgen_playground", "random", "general", "typing", "terms", "proof_mode",  "commands"]

/-- Non-program helper scripts (drivers/figures), not transpiler inputs. -/
def skipNames : List String := ["run_showcase.py", "fetch_data.py"]

/-- Directories skipped by the per-file checker: `terms/` are single expressions (`--target term`),
`imports/` is a cross-file import test that needs the imported module elaborated first, and `heap/`
holds `--heap`-only examples (reference semantics) that intentionally exceed value-semantics support
in the default sweep — they are checked separately with `--heap`. -/
def skipDirs : List String := ["terms", "imports", "heap"]

/-- The verdict for one program. -/
inductive Verdict | ok | convertFail (msg : String) | unsupported (msg : String) | compileFail (msg : String)

def Verdict.tag : Verdict → String
  | .ok => "OK" | .convertFail _ => "CONVERT_FAIL"
  | .unsupported _ => "UNSUPPORTED" | .compileFail _ => "COMPILE_FAIL"

def Verdict.detail : Verdict → String
  | .ok => "" | .convertFail m | .unsupported m | .compileFail m => m

/-- Verdict for one already-translated summary record. -/
def checkRecord (env : Environment) (rec : Json) (bypassSkip : Bool := false) : IO (Option Verdict) := do
  let file := (rec.getObjValAs? String "file").toOption.getD ""
  let name := (System.FilePath.mk file).fileName.getD ""
  if skipNames.contains name then return none          -- driver/figure scripts, not programs
  -- `bypassSkip` lets the dedicated `--heap` pass check the `heap/` dir that the value sweep skips.
  if !bypassSkip && skipDirs.any (fun d => (file.splitOn s!"/{d}/").length > 1) then return none
  let status := (rec.getObjValAs? String "status").toOption.getD "convert_fail"
  if status == "convert_fail" then
    return some (.convertFail ((rec.getObjValAs? String "error").toOption.getD "convert failed"))
  let hasUnsup := (rec.getObjVal? "unsupported").toOption.isSome
  let expects := expectUnsupported.contains name
  if hasUnsup && !expects then
    return some (.unsupported "unexpected pyUnsupported placeholder(s) — real logic degraded")
  if expects && !hasUnsup then
    return some (.unsupported "expected pyUnsupported placeholder(s) but found none")
  let code := (rec.getObjValAs? String "lean").toOption.getD ""
  -- Write `.lean` next to the `.py` for the reviewable showcase directories.
  if writeInPlaceDirs.any (fun d => (file.splitOn s!"/{d}/").length > 1) then
    IO.FS.writeFile ((System.FilePath.mk file).withExtension "lean") code
  match ← checkProgram env code with
  | some err => return some (.compileFail err)
  | none => return some .ok

/-! ### Warm evaluation backend (`lake exe palc eval`) for cp_harness

`lake env lean --run <harness>` reloads Mathlib (~5 s) per problem. This mode boots the environment
ONCE, then reads harness `.lean` paths on stdin and runs each harness's `main` in-process, capturing
what it prints (`PASSED p/t` / `FAIL i: got …`). A non-terminating harness would hang the shared
process, so the driver reads each block under a timeout and restarts on a miss. -/

/-- Elaborate a cp_harness `.lean` in `env` and run its `main`, returning captured stdout, or
`ERROR …` on an elaboration/eval failure. -/
unsafe def evalHarness (env : Environment) (code : String) : IO String := do
  let src := stripImports code
  let inputCtx := Parser.mkInputContext src "<harness>"
  let cmdState := Command.mkState env {} {}
  let frontendState ← Lean.Elab.IO.processCommands inputCtx {} cmdState
  let msgs := frontendState.commandState.messages
  if msgs.hasErrors then
    for msg in msgs.toList do
      if msg.severity == .error then
        return s!"ERROR {(((← msg.data.toString).replace "\n" " ").take 200)}"
    return "ERROR elaboration"
  match frontendState.commandState.env.evalConst (IO Unit) {} `main with
  | .error e => return s!"ERROR eval {e}"
  | .ok act => return (← IO.FS.withIsolatedStreams act).1

/-- Boot once, then loop: read a harness path per stdin line, print its run output delimited. -/
unsafe def runEvalLoop : IO UInt32 := do
  IO.println "Booting Mathlib environment for warm evaluation…"
  let env ← bootEnv
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "===PACEVAL-READY===\n"; stdout.flush
  let mut done := false
  while !done do
    let line ← stdin.getLine
    if line.isEmpty then done := true
    else
      let path := line.trimAscii.toString
      unless path.isEmpty do
        let out ← try evalHarness env (← IO.FS.readFile path)
                  catch e => pure s!"ERROR {toString e}"
        stdout.putStr s!"===PACEVAL-BEGIN===\n{out}\n===PACEVAL-END===\n"; stdout.flush
  return 0

/-- Twin coverage: one line per verdict category, and every pair's verdict in
`/tmp/pastacheck_twins.json`. Informational — a twin that is not proved never fails the suite. -/
def reportTwins (twins : Array (String × Json)) : IO Unit := do
  let tag (j : Json) := (j.getObjValAs? String "verdict").toOption.getD "?"
  let mut counts : Std.HashMap String Nat := {}
  for (_, j) in twins do counts := counts.insert (tag j) (counts.getD (tag j) 0 + 1)
  let n (k : String) := counts.getD k 0
  let inScope := ["proved", "proved_mod_partial", "partial_step_equiv", "type", "proof"]
  let outLabel := [("float", "float"), ("io_main", "IO entry point"), ("monad", "monad"), ("class", "class"),
    ("memo", "memo"), ("while", "while over Array state"), ("partial", "partial"),
    ("partial_callee", "partial callee")]
  let others := (counts.toList.map (·.1)).filter fun k => !inScope.contains k && !(outLabel.map (·.1)).contains k
  let outs := (outLabel.filter (n ·.1 > 0)).map (fun (k, l) => s!"{l} {n k}") ++ others.map (fun k => s!"{k} {n k}")
  IO.println s!"=== twins: {twins.size} function pairs (f, f'rn); each checked in Lean for f'rn ≡ f on all inputs ==="
  IO.println s!"    in scope ({inScope.foldl (fun a k => a + n k) 0} pairs, types related by TwinRel): proved {n "proved" + n "proved_mod_partial"} ({n "proved"} outright, {n "proved_mod_partial"} assuming partial callees), step-equivalent {n "partial_step_equiv"} (partial def), unproved {n "type" + n "proof"}"
  IO.println s!"    out of scope (equality is not the relation): {", ".intercalate outs}"
  for (f, j) in twins do
    if tag j == "proof" || tag j == "type" then
      IO.println s!"    unproved: {f} :: {(j.getObjValAs? String "f").toOption.getD "?"}"
  let arr := twins.map fun (f, j) => Json.mkObj [("file", toJson f), ("pair", j)]
  IO.FS.writeFile "/tmp/pastacheck_twins.json" (Json.arr arr).pretty

/-- Sort records by file path, for stable output. -/
def byFile (recs : Array Json) : Array Json :=
  recs.qsort (fun a b => (a.getObjValAs? String "file").toOption.getD "" < (b.getObjValAs? String "file").toOption.getD "")

unsafe def main (args : List String) : IO UInt32 := do
  -- `palc eval`: warm evaluation backend for cp_harness (stdin-driven). Otherwise: example checks.
  if args.head? == some "eval" then return (← runEvalLoop)
  if args.contains "--no-twin" then twinCheckEnabled.set false
  let args := args.filter (!·.startsWith "--")
  let base : System.FilePath := "example_scripts"
  let g := args.head?                                   -- optional subdirectory (`lake exe palc typing`)
  let dir := match g with | some d => base / d | none => base
  let pyBin := if (← (System.FilePath.mk ".venv/bin/python3").pathExists) then ".venv/bin/python3" else "python3"
  IO.println "Booting Mathlib environment for in-process compile-checks…"
  let env ← bootEnv
  -- Collect (file, verdict) across both passes, then tally once.
  let mut results : Array (String × Verdict) := #[]
  let mut twins : Array (String × Json) := #[]
  -- Value-semantics sweep (skips heap/, imports/, terms/). Skipped when targeting heap only.
  unless g == some "heap" do
    IO.println "Translating every example (value semantics, one warm backend)…"
    for rec in byFile (← translateAll pyBin dir) do
      if let some v ← checkRecord env rec then
        let file := (rec.getObjValAs? String "file").toOption.getD ""
        results := results.push (file, v)
        twins := twins ++ (← lastTwinReport.get).map (file, ·)
  -- Reference-semantics sweep: `heap/` under `--heap --mode both` (exact + runnable twins in ONE
  -- program). Runs on the full suite or when targeting heap; the value sweep can't check these.
  if g == none || g == some "heap" then
    let heapDir := base / "heap"
    if (← heapDir.pathExists) then
      IO.println "Translating heap examples (--heap --mode both)…"
      -- the heap model's twins share one `Val` universe; the twin relation does not cover it yet
      let twin ← twinCheckEnabled.get
      twinCheckEnabled.set false
      let hrecords ← translateAll pyBin heapDir #["--heap"] "/tmp/pastacheck_heap_summary.json"
      for rec in byFile hrecords do
        if let some v ← checkRecord env rec (bypassSkip := true) then
          let file := (rec.getObjValAs? String "file").toOption.getD ""
          results := results.push (file, v)
          twins := twins ++ (← lastTwinReport.get).map (file, ·)
      twinCheckEnabled.set twin
  let mut ok := 0
  let mut fails := 0
  for (rel, v) in results do
    match v with
    | .ok => ok := ok + 1; IO.println s!"  OK            {rel}"
    | _ => fails := fails + 1; IO.println s!"  {v.tag}  {rel}: {v.detail}"
  IO.println s!"\n=== {ok} OK, {fails} FAILED ==="
  if ← twinCheckEnabled.get then reportTwins twins
  return if fails == 0 then 0 else 1
