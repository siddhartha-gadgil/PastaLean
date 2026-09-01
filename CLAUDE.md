# PastaLean — orientation for AI sessions

PastaLean is a **Python → Lean 4 transpiler**. It takes ordinary Python source and emits
Lean 4 code that elaborates against a hand-written runtime (`PastaLean.PyAPI`) modelling
Python's semantics. The motivating use case is the "logic side of data science" /
competitive-programming-style code: ints, strings, lists, dicts, loops, comprehensions,
functions, exceptions.

This file is a map so you don't have to re-derive the architecture. Read it first, then open
only the files you actually need.

## Working rules (read first)

- **NEVER `git commit` (or push) until the user explicitly tells you to in that moment.** Permission
  is per-commit and does NOT carry forward — a "commit" earlier in the session does not authorise the
  next one. Make and stage changes freely; leave committing to the user's explicit say-so.
- **Run the full regression gate (`lake exe palc`) only when finishing a feature/amendment, or when
  fixing a regression it would catch — not routinely.** During a batch, verify with a single targeted
  `pastalean translate <the file you're fixing>`, not PALC.
- **Batch builds.** `lake build` is slow (Mathlib); group related edits, build once, test once.
- **Comments: minimal and precise** (see Code writing tips below).

---

## The pipeline (Python text → Lean text)

Three stages, orchestrated by **`src/transpile/driver.py`**. Don't call the stages by hand — go
through the CLI or the `Session` API below.

```
Python source
  │
  ├─ src/transpile/annotate_python.py  pre-pass: walks the Python AST, attaches type/scope
  │                                    annotations (inferred param types, mutated-name sets).
  │
  ├─ src/transpile/node_visitor.py     Python AST → a JSON IR. Each node is {"node_type": "...", ...}.
  │                                    Holds the operator/compare maps (BINOP_MAP, COMPAREOP_MAP, ...).
  │
  ├─ src/transpile/toplevel_state.py   further IR annotations for top-level state threading and
  │                                    if/loop scope analysis (Lean has no top-level mutation).
  │
  └─ Lean backend (exe `py2lean`)      JSON IR → Lean Syntax → pretty-printed Lean text.
```

The driver boots **one persistent Lean backend process** and streams JSON translation requests to
it (one per top-level statement), so Lean isn't restarted per node.

- `--target term` emits an expression; `--target command` emits top-level declarations
  (this is what you want for whole programs — it produces `def main : IO Unit := ...` when the
  source has a `main`/`__main__`).
- `--verbose` dumps the intermediate JSON IR and Lean syntax — invaluable when debugging.

---

## The Python side: `src/` (the `pastalean` package)

`src/` *is* the package: `import pastalean` loads `src/__init__.py`. (It cannot sit at the repo
root — `PastaLean/`, the Lean library, is already there, and the two names collide on
case-insensitive filesystems.) Install it with `uv pip install -e '.[server]'`.

- `main.py` — **start here.** The `pastalean` console script / `python -m pastalean`; one thin
  `cmd_*` per subcommand, delegating to `api` and `backend`.
- `api.py` — `Session` (warm backend, many files), `translate`/`translate_file` (one-shot),
  `TranslationResult`.
- `server.py` — `pastalean serve`: a FastAPI app over one `Session`, serving the `static/` web
  playground at `/` and its generated reference at `/api`.
- `pyexec.py` — runs the *original* Python, so the UI can diff it against the Lean twin.
- `backend/` — everything that talks to Lean: `client.py` (the persistent `py2lean --server`
  process) and `lean.py` (`compile_check` / `run_program` via `lake env lean`).
- `transpile/` — everything that manipulates Python AST/IR (the three stages above, plus
  `normalize_loops.py`, `contract_passta.py`, `llm.py`).
- `prepasses.py` — the optional LLM source rewrites (`--contracts`, `--redesign`).
- `paths.py` — every filesystem location, resolved from `__file__`. Never derive paths from the cwd.

```bash
pastalean translate <file.py>                      # Lean on stdout, then compile-check it
pastalean translate <file.py> --no-check           # codegen only (skip `lake env lean`) — faster
pastalean translate <file.py> -v                   # + intermediate stages
pastalean run <file.py> < input.txt                # translate, compile, execute
pastalean json <file.py>                           # dump the JSON IR
pastalean batch example_scripts/commands --check   # many files, one warm backend
pastalean serve                                    # web UI at /, API reference at /api
```

`uv run pastalean ...` works without installing anything. `uv run src/main.py` does not — the
package uses relative imports.

```python
from pastalean import Session
with Session(target="command", mode="run") as s:      # one Lean boot for all of them
    for result in s.translate_files(paths):
        print(result.lean_code if result.ok else result.error)
```

The low-level backend is the Lean executable defined by `py2lean.lean`; it takes a JSON task
string directly (`lake exe py2lean '{"task":"translate","ast":{...}}' term`). You rarely call
this directly — `backend/client.py` drives it.

---

## The Lean side: `PastaLean/`

Two layers, with its own `PastaLean/README.md` giving the detailed "what goes where".

### `PastaLean/PyAPI/` — the runtime
Lean implementations of Python-like behavior. Generated code calls into these. If you are
implementing *what a Python operation does*, it goes here.

- `Core.lean` — shared runtime types (`PyException`, `PyExcept`), `pyRange`, string-index
  helpers (`pyStringGetItem`, `pyStringSlice`), small cross-cutting helpers.
- `Operators.lean` — the operator typeclasses and notation: `+ₚ -ₚ *ₚ /ₚ %ₚ ^ₚ` backed by
  `PyHAdd / PyHSub / PyHMul / PyHDiv / PyModulo / PyHPow` (each with an `outParam` result type
  so mixed-numeric results reduce). Instances cover Int/Nat/Rat/Float/String mixes.
- `Strings.lean`, `Lists.lean`, `Dicts.lean`, `Sets.lean` — per-container helpers
  (`pyStringSplit`, `pyAppend`, `pyItems`, set ops, ...).
- `Input.lean`, `PyPrint.lean` — `pyInputIO`, `pyPrintIO`, `PyPrintable`/`pyStringify`.
- `Builtins/` — Python builtins: `Casting.lean` (`pyInt`/`pyStr`/`pyFloat`/`pyList` casts),
  `Character.lean` (`chr`/`ord`), `Functional.lean` (`map`/`filter`/`sum`/`min`/`max`/`zip`),
  `Math.lean` (`pow`). Registered for call dispatch in `BuiltinRegistry.lean`
  (`pythonBuiltinMap?` maps a Python builtin name → a Lean runtime name).
- `CommonProtocols/` — intentionally-extensible typeclasses, one file each: `Length` (`pyLen`),
  `Iterable` (`pyIter`), `GetItem`/`SetItem` (`x[i]`, `x[i]=v`), `Membership` (`pyContains`),
  `Sorting` (`pySort`), `Pop`, `Count`, `Find`, `Index`, `Truthy` (`pyTruthy`), `Bool`,
  `Reversed`, `Clear`, `AnyFunc`. **Convention:** a protocol whose result type varies per
  instance carries that type as an `outParam` class parameter, never an associated-type field
  — associated-type projections stay "stuck" and break downstream instance resolution.

### `PastaLean/PyGens/` — the code generator
JSON-IR-node → Lean `Syntax`. If you are deciding *how a Python AST node emits Lean syntax*,
it goes here. Each generator is a function tagged `@[pygen "NodeType"]` returning
`PygenM (TSyntax kind)`; `getCode json kind` dispatches to the registered generator by
`node_type`. The monad `PygenM` (`Codegen.lean`) is `StateT PyGen.State TermElabM` and carries
codegen state — notably `varNames` (which names are in scope / declared `let mut`).

- `Codegen.lean` — the `@[pygen ...]` attribute machinery, `getCode`, and state combinators:
  `withFixedVariables` (scope a block's var registrations), `hasVar`/`addVar`, `freshName`.
- `Basic.lean` — leaf/expression nodes: `Constant`, `Name`, `List`, `Tuple`, `BinOp`,
  `UnaryOp`, `BoolOp`, `Compare`, `IfExp`. Operator/compare lowering lives here.
- `Core/` — `Assign.lean` (assignment, return, tuple-unpack), `Subscript.lean` (`x[i]` reads),
  `Utils.lean` (body-flattening `appendDoElems`, `monadicFunctionBodySyntax`, helpers).
- `UseCases/` — `ControlFlow.lean` (`If`/`For`/`While`/`AugAssign` + top-level state
  threading), `FuncDef.lean` (`Module`/`FunctionDef`/body threading), `LambdaExpr.lean`,
  `ListComp.lean`, `Match.lean`, `Exceptions.lean` (`Try`/`Raise`), `Imports.lean`,
  `Comments.lean`.
- `Calls/` — call lowering. `CallExpr.lean` is the main path; `CallEffects.lean` handles
  IO-effectful calls and `inlineIOTerm` (inlining `← input()` awaits into pure positions);
  `SpecialCalls/` for special-cased builtins.
- `Attributes.lean` — **dispatch glue only.** Maps Python method names (`"split"`, `"append"`)
  to runtime functions (`pyStringSplit`, `pyAppend`) via `pythonMethodMap`. No implementations.

### Effects / IO model
A Lean program's entry point is `IO Unit`. `input()`/`print()` are `IO`. Pure expressions that
contain an IO sub-term (e.g. `int(input()) + 5`) are handled by hoisting/inlining the `←`
await into the pure position rather than letting a raw `IO _` leak — see `inlineIOTerm` and the
`jsonUsesIOEffect` / `basicJsonUsesMonadicEffect` predicates.

---

## Other top-level pieces

- `Libraries/` (lean lib `Libraries`) — a small standard-library surface that generated code
  `open`s alongside `PastaLean` (e.g. numpy-like shims under `Libraries/numpy`).
- `example_scripts/` — sample Python inputs, one directory per theme (`terms/` are single
  expressions, `commands/` whole programs, `heap/` the `--heap` examples, `typing/`,
  `proof_mode/`, `mvcgen_playground/`, ...). These *are* the test corpus — see Tests below.
- `PastaBench/` (lean lib `PastaBench`, **not** a default target) — the shipped verification
  benchmark: ~300 leetcode/stdlib problems, each a `Generated.lean` (regenerated by
  `pastabench.py`) plus hand-written `Proofs.lean`/`solution_contracts.py`. Build explicitly.
- `HeapProofs/` (lean lib `HeapProofs`, **not** a default target) — separation-logic specs proved
  against verbatim `--heap` translator output (see `PastaLean/PyAPI/Heap/Proof.lean`). Each module
  is its own compilation unit so their root-namespace `Val` inductives never collide.
- `docs/phases.md` — design notes on the translation phases.

## Tests

- **PALC** (`PALC/`, lean lib + exe `palc`, `testDriver = "palc"`) — the gate, run by `lake test`.
  `PALC/PastaCheck.lean` is the runner; it does two things:
  1. importing the `PALC` library runs its **`#guard_msgs` / `#guard` unit tests** at build time
     (`PALC/PyAPI/`, `PALC/TypeInfer/`, `PALC/Libraries/`, `PALC/PyGens/`);
  2. it translates **every `.py` under `example_scripts/`** in one warm `pastalean batch` pass and
     **compile-checks each program in-process** against an already-booted Mathlib environment (no
     `lake env lean` per file). A program passes when it converts, carries no unexpected
     `pyUnsupported`, and elaborates clean. There is a second sweep over `heap/` with `--heap
     --mode both`, since the value-semantics pass skips it (`skipDirs`).
  There are no `# CHECK:` directives — the assertion is "converts and elaborates", so this catches
  broken *elaboration*, not emitted syntax. Two gotchas: `writeInPlaceDirs` makes the runner
  **overwrite `<name>.lean` next to the `.py`** for the reviewable directories (`showcase`,
  `mvcgen_playground`, `random`, `general`, `typing`, `terms`, `proof_mode`, `commands`), so a full
  run destroys any hand-written proof living there; and paths are relative to `example_scripts/`
  (`lake exe palc typing`, not `lake exe palc example_scripts/typing`).
- **`cp_harness/`** — an end-to-end harness over real competitive-programming Python solutions
  (`cp_harness/dataset*/<problem>/solutions/sol_*.py`). `cpasta_eval.py` wraps bare top-level code
  in a `__main__` guard, translates it through one warm `Session`, compile-checks the Lean, and
  tallies `ok | convert_fail | compile_fail` into `<dataset>/convert_summary.json`. The convert
  stage is slow; treat `convert_summary.json` as the source of truth for coverage.
  `lake exe palc eval` is its warm in-process evaluation backend (stdin-driven, boots Mathlib once).

## Build / run quick reference

```bash
lake build                  # build PastaLean + py2lean (default targets)
lake build py2lean          # just the transpiler backend
lake test                   # == `lake exe palc`: unit tests + every example_scripts program
lake exe palc <subdir>      # same, restricted (path relative to example_scripts/)
lake build PastaBench       # the ~300-problem benchmark (slow, not a default target)
lake build HeapProofs       # the separation-logic proofs (not a default target)
```

- Toolchain pinned by `lean-toolchain`; deps in `lakefile.toml` (Mathlib, lean-regex).
- The Python side uses a uv venv at `.venv/`; `uv pip install -e '.[server]'` puts the `pastalean`
  console script on PATH. The `server` extra (fastapi/uvicorn) is only needed for `pastalean serve`.

## Conventions worth knowing

- **Runtime vs codegen split is load-bearing.** New Python *behavior* → `PyAPI/`. New decision
  about *which syntax a node emits* → `PyGens/`. Method-name→function mapping → `Attributes.lean`
  (glue) + the implementation in `PyAPI/`.
- **Extensible protocols use `outParam`, not associated types** (see `CommonProtocols/`).
- **`def main` appears only when the source has a `main`/`__main__`.** The general transpiler
  never auto-wraps bare code; only `cp_harness/cpasta_eval.py` adds a `__main__` guard for the
  harness.
- Generated programs start with `import PastaLean` / `import Libraries` and `open` both.

## Code writing tips

- **Comments: minimal and precise.** Most edits need NO comment. Only add one for a genuinely
  non-obvious invariant or gotcha, and keep it to one line. Do NOT narrate what the code plainly
  does, do NOT add a comment on every edit, and never write multi-line rationale/history blocks.
  Also any pre-existing comment, don't remove it either.
- Think about robustness solution for the same, touching a generic problem, then just a temporary solution for the same. This will help in future bugs, to avoid code duplication and will help in maintainability of the code.
- If you find some python code very nice/hard/typical, add them within pre-existing regression tests for those files testing them, or make new ones. Add those examples which really test the boundaries of PastaLean, and which are likely to be bugs if not handled properly.
