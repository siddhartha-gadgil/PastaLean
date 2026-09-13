import Lean
import PastaLean
import TypeInfer
open Lean Meta Elab Term Qq Std
open PastaLean

def backendModules : Array Import := #[
  { module := `PastaLean },
  { module := `Mathlib },
  -- `Libraries` is imported so the `proveFile` pass can elaborate generated programs that
  -- `open Libraries` (numpy/scipy shims) without a second cold import of Mathlib.
  { module := `Libraries }
]

unsafe def initBackend : IO (Core.Context × Environment) := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (loadExts := true) backendModules {}
  let ctx : Core.Context := {
    fileName := "<py2lean>"
    fileMap := default
  }
  pure (ctx, env)

def errorResponse (message : String) : Json :=
  Json.mkObj [("result", Json.bool false), ("error", Json.str message)]

def sanitizeLeanOutput (code : String) : String :=
  code.replace "✝" ""

def successResponse (target : String) (code : Format) : Json :=
  Json.mkObj [("result", Json.bool true), ("lean_" ++ target, Json.str <| sanitizeLeanOutput code.pretty)]

def ensureTarget (jsonTask : Json) (target : String) : Json :=
  match jsonTask.getObjVal? "target" with
  | .ok _ => jsonTask
  | .error _ => (Json.mkObj [("target", Json.str target)]).mergeObj jsonTask

def runTranslateTask (jsonTask : Json) (ctx : Core.Context) (env : Environment) : IO Json := do
  let target := jsonTask.getObjValAs? String "target" |>.toOption.getD "term"
  let checkCode := jsonTask.getObjValAs? Bool "check" |>.toOption.getD true
  -- Per-request numeric mode (default exact = ℚ). Set before codegen so the literal/annotation
  -- sites lower `float` to `ℚ` or `Float` accordingly.
  let mode := jsonTask.getObjValAs? String "numericMode" |>.toOption.getD "exact"
  PastaLean.numericModeRef.set (if mode == "approx" then .approx else .exact)
  -- Run-twin suffixing (`--mode both`): when emitting the runnable twin, `runSuffix` is `'rn` and
  -- `userNames` lists the user's functions/classes whose references should also be suffixed.
  PastaLean.runSuffixRef.set (jsonTask.getObjValAs? String "runSuffix" |>.toOption.getD "")
  PastaLean.userNamesRef.set ((jsonTask.getObjValAs? (Array String) "userNames" |>.toOption.getD #[]).toList)
  -- Best-effort: degrade a single failing statement to `pyUnsupported` (keep the rest of the function).
  PastaLean.bestEffortRef.set (jsonTask.getObjValAs? Bool "best_effort" |>.toOption.getD false)
  -- `getObjVal?`, not `getObjValAs? Json`: the latter reads a missing key as `null` and defers the
  -- failure to codegen, which then reports a confusing "no 'node_type' field" instead.
  let .ok json := jsonTask.getObjVal? "ast"
    | return errorResponse "Invalid JSON: missing 'ast' field"
  -- Reference semantics (`--heap`): opt-in via the task flag only. Off keeps the value-semantics path.
  PastaLean.heapModeRef.set (jsonTask.getObjValAs? Bool "heap" |>.toOption.getD false)
  -- The whole-module `inferTypes` pass (run by the driver) marks each statement `_inferred`; only fall
  -- back to the context-free per-statement stamp when it did not run (a bare term, or on failure).
  let alreadyInferred := (json.getObjVal? "_inferred").toOption.isSome
  -- Generators (`yield`) materialise to a list-building function before anything else, so the
  -- synthesised `append`/`extend`/`return` flow through desugaring and codegen; see
  -- `PyGens/Transform/GeneratorLower.lean`.
  -- When the driver pre-ran the `inferTypes` task, generators + desugaring already happened there
  -- (before inference), so re-running them here would double-desugar; skip straight to codegen.
  let json ← if alreadyInferred then pure json else match PastaLean.lowerGenerators json with
    | .ok lowered => pure lowered
    | .error message => return errorResponse s!"Error generating code: {message}"
  -- Syntactic desugaring (nested `for` targets, walrus, chained assign) runs before codegen; see
  -- `PyGens/Transform/Desugar.lean`.
  let json ← if alreadyInferred then pure json else match PastaLean.desugarAst json with
    | .ok desugared => pure desugared
    | .error message => return errorResponse s!"Error generating code: {message}"
  -- Type inference stamps `_ty` on binders whose Lean type the code generator would otherwise
  -- leave for Lean to guess (and get stuck on). See `TypeInfer/`.
  let json := if alreadyInferred then json else TypeInfer.stampNode (TypeInfer.ssaModule json)
  let code? ← getCodeIO json target.toName ctx env checkCode
  pure <| match code? with
    | .ok code => successResponse target code
    | .error err => errorResponse err

/-- Drop `import …` lines from generated Lean text. The backend has already imported everything at
boot, so the `proveFile` pass elaborates only the *commands* (opens, set_options, defs, theorems). -/
def stripImports (code : String) : String :=
  String.intercalate "\n" <|
    (code.splitOn "\n").filter (fun l => ¬ l.trimAscii.startsWith "import ")

/-- Elaborate an already-generated program (with `:= by taste?` proof obligations) into the warm
boot `env`, letting the `taste?` tactic search each assert and record its winning tactic string into
`PastaLean.tasteWinnersRef`. Returns the winners in elaboration order (one per `taste?`), so the
Python driver can splice each back over the matching `taste?` token. No Mathlib re-import. -/
def runProveFileTask (jsonTask : Json) (env : Environment) : IO Json := do
  let .ok code := jsonTask.getObjValAs? String "code"
    | return errorResponse "proveFile: missing 'code' field or it is not a string"
  PastaLean.tasteWinnersRef.set #[]
  let src := stripImports code
  -- `stripImports` drops the leading `import …` lines, so byte offsets recorded against `src` are
  -- shifted left by exactly those removed prefix bytes. Add them back so each winner's `pos` is an
  -- offset into the *original* `code` the Python splicer walks.
  let shift := code.toUTF8.size - src.toUTF8.size
  let inputCtx := Parser.mkInputContext src "<proveFile>"
  let cmdState := Command.mkState env {} {}
  let frontendState ← Lean.Elab.IO.processCommands inputCtx {} cmdState
  let winners ← PastaLean.tasteWinnersRef.get
  let hasErrors := frontendState.commandState.messages.hasErrors
  pure <| Json.mkObj [
    ("result", Json.bool true),
    ("winners", Json.arr (winners.map (fun (off, p) =>
      Json.mkObj [("pos", toJson (off + shift)), ("proof", Json.str p)]))),
    ("hasErrors", Json.bool hasErrors)
  ]

/-- Whole-module type inference: stamp `_ty` on binders using interprocedural (return-type) flow,
so a later per-statement `translate` sees types a single statement couldn't reveal. Returns the
stamped AST for the driver to send back one node at a time. -/
def runInferTypesTask (jsonTask : Json) : IO Json := do
  let .ok ast := jsonTask.getObjVal? "ast"
    | return errorResponse "inferTypes: missing 'ast' field"
  -- Materialise generators (`yield`) to list-builders AND run syntactic desugaring (chained assign,
  -- walrus, nested for-targets) BEFORE inferring — otherwise inference sees the un-split
  -- `a = b = expr` (a multi-`targets` node it can't learn per-target from) and later desugaring
  -- strips the stamps it would have produced. Codegen skips both passes when `_inferred` is set.
  match PastaLean.lowerGenerators ast with
  | .error message => pure <| errorResponse message
  | .ok ast =>
    match PastaLean.desugarAst ast with
    | .error message => pure <| errorResponse message
    | .ok ast => pure <| Json.mkObj [("result", Json.bool true), ("ast", TypeInfer.inferModule (TypeInfer.ssaModule ast))]

def handleTaskJson (jsonTask : Json) (ctx : Core.Context) (env : Environment) : IO Json := do
  let .ok task := jsonTask.getObjValAs? String "task"
    | return errorResponse "Invalid JSON: missing 'task' field or it is not a string"
  match task with
  | "translate" => runTranslateTask jsonTask ctx env
  | "inferTypes" => runInferTypesTask jsonTask
  | "proveFile" => runProveFileTask jsonTask env
  -- Library facts the Python driver needs but that must not be duplicated there.
  | "libraryInfo" =>
      pure <| Json.mkObj [
        ("result", Json.bool true),
        ("ioEffectfulLibraries", Json.arr (Libraries.ioEffectfulLibraries.toArray.map Json.str))]
  | _ => pure <| errorResponse s!"Unknown task: {task}"

def handleTaskString (payload : String) (ctx : Core.Context) (env : Environment) : IO Json := do
  match Json.parse payload with
  | .ok jsonTask => handleTaskJson jsonTask ctx env
  | .error err => pure <| errorResponse s!"Error parsing JSON: {err}"

partial def runServerLoop (stdin stdout : IO.FS.Stream) (ctx : Core.Context) (env : Environment) : IO UInt32 := do
  -- `getLine` keeps the trailing newline, so only end-of-stream yields `""`. A hand-rolled
  -- byte-at-a-time reader that strips the newline cannot tell a blank line from EOF, and would
  -- shut the server down on one.
  let rawLine ← stdin.getLine
  if rawLine.isEmpty then
    return 0
  let line := rawLine.trimAscii.toString
  if line.isEmpty then
    runServerLoop stdin stdout ctx env
  else
    let response ← handleTaskString line ctx env
    stdout.putStr <| Lean.Json.compress response ++ "\n"
    stdout.flush
    runServerLoop stdin stdout ctx env

def runSingleTask (payload : String) (defaultTarget : String) (ctx : Core.Context)
    (env : Environment) : IO UInt32 := do
  let stdout ← IO.getStdout
  match Json.parse payload with
  | .ok jsonTask =>
      let response ← handleTaskJson (ensureTarget jsonTask defaultTarget) ctx env
      stdout.putStr <| Lean.Json.compress response ++ "\n"
      stdout.flush
      return 0
  | .error err =>
      IO.eprintln s!"Error parsing JSON: {err}"
      return 1

unsafe def main(args : List String) : IO UInt32 := do
  let (ctx, env) ← initBackend
  match args with
  | "--server" :: _ =>
      let stdin ← IO.getStdin
      let stdout ← IO.getStdout
      runServerLoop stdin stdout ctx env
  | jsStr :: rest =>
      runSingleTask jsStr (rest.headD "term") ctx env
  | [] =>
      IO.eprintln "No JSON input provided"
      return 1
