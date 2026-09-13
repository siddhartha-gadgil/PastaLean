# Reproducing the PastaLean paper results

This file lists the exact commands that regenerate every table and figure in the
paper. Each experiment names the paper artifact it produces and the file it writes,
so a result can be checked number by number.

All paths are relative to the repository root. Every number in the paper was
measured on a single machine (32-core AMD Ryzen Threadripper PRO 5975WX, 128 GiB,
Linux 6.8.0 x86_64); absolute times and memory vary on other hardware, but the
ranking of the tools does not.

## 0. Setup

```bash
# Python side: uv virtualenv + editable install of the `pastalean` package
uv venv                                 # creates .venv/ (the harnesses source it)
uv pip install -e '.[server]'           # installs the `pastalean` console script

# Lean side: toolchain is pinned by lean-toolchain; deps (Mathlib, ...) by lakefile.toml
lake build py2lean                      # the transpiler backend the harnesses drive
lake build typeinfer                    # standalone Mathlib-free inference binary
lake build PastaBench                   # the verification library (proving experiment only)
```

`uv run pastalean ...` also works without installing. The type-inference and
repository benchmarks use the standalone `typeinfer` binary, which starts in about
30 ms because it never loads the Mathlib image.

## 1. Code generation and execution (Table `tab:codegen`)

Harness: `PastaBench/pastaeval.py`. The dataset for HumanEval is bundled; the two
competitive-programming sets are reached through the `cp` subcommand, which forwards
to `cp_harness/cpasta_eval.py`.

```bash
# HumanEval — "Elaborated" (translate + compile-check) and, with --run, "Tests"/"Passed"
python3 PastaBench/pastaeval.py humaneval            # elaboration
python3 PastaBench/pastaeval.py humaneval --run      # run the 'rn twin against tests.json

# LeetCode and LiveCodeBench columns
python3 PastaBench/pastaeval.py cp --source leetcode      --num max
python3 PastaBench/pastaeval.py cp --source livecodebench --num max
```

Outputs: `PastaBench/pastaeval_report.json` (HumanEval, with per-problem Lean under
`PastaBench/_eval_out/`); `cp_harness/dataset_leetcode/` and
`cp_harness/dataset_livecodebench/` each get a `convert_summary.json`,
`eval_report.json`, and `eval_divergences.json` (the per-case divergence log used to
attribute every mismatch to a specific runtime function).

The competitive-programming stages can be run and re-run separately. `fetch`
downloads once; `--skip-convert` reuses already-translated Lean and only re-runs the
test comparison:

```bash
python3 cp_harness/cpasta_eval.py run --source leetcode --num max --dataset cp_harness/dataset_leetcode
python3 cp_harness/cpasta_eval.py run --skip-fetch --skip-convert --dataset cp_harness/dataset_leetcode
```

## 2. Type inference: TypeEvalPy (Tables `tab:static-micro`, `tab:static-auto`, `tab:checkers-micro`, `tab:checkers-auto`)

Harness: `PastaBench/typeinfer_bench/`. Fetch the benchmark once:

```bash
git clone --depth 1 https://github.com/secure-software-engineering/TypeEvalPy /tmp/TypeEvalPy
```

```bash
# PastaLean on the micro-benchmark (850 facts)
python3 PastaBench/pastaeval.py typeinfer            # -> typeinfer_bench/typeinfer_summary.json

# PastaLean on the autogen set (5453 snippets, 77268 facts)
bash PastaBench/typeinfer_bench/run_autogen.sh       # -> typeinfer_bench/autogen_summary.json

# The production type checkers on the same facts (mypy, ty, pyright, pyrefly, zuban)
uv run python PastaBench/typeinfer_bench/bench_checkers.py --bench <micro-or-autogen dir>
```

`typeinfer_eval.py` takes `--bench DIR`, `--out FILE`, `--engine {typeinfer,backend}`,
and `--jobs`. `bench_checkers.py` takes `--tools` (default
`ty,pyrefly,pyright,mypy,zuban`). The autogen thread-scaling numbers (Table
`tab:ti-threads`) come from running the autogen command above with `--jobs` set to
each pool size.

## 3. Type inference: TypyBench, repository level (Table `tab:typybench`)

Harness: `PastaBench/typybench_bench/`. Datasets are laid out as
`<dataset>/<repo>/repo_without_types/`.

```bash
# Generate PastaLean predictions for the whole dataset
python3 PastaBench/typybench_bench/run_predictions.py <dataset_dir> ./predictions

# Score each tool in Lean (TypeSim / Exact / Coverage) and the summed time.
# By default score.py runs the fifty projects one at a time, each using the whole
# machine (full throttle), and reports the SUM of the per-project times (the Time
# column of Table `tab:typybench`) alongside the slot-weighted totals.
python3 PastaBench/typybench_bench/score.py <dataset_dir> --tool pastalean
python3 PastaBench/typybench_bench/score.py <dataset_dir> --tool pyrefly
python3 PastaBench/typybench_bench/score.py <dataset_dir> --tool pyre

# Memory (Mem column): peak PSS on the largest project, measured the same way for all three.
python3 PastaBench/typybench_bench/measure_mem.py --repo vllm --tool pastalean <dataset_dir>
```

`score.py` prints the per-project table (with a per-project Time column), the summed
prediction time, and the slot-weighted totals reported in the paper. `--parallel-repos N`
scores N projects at once (default 1; this is a project count, NOT a thread count, so the
default gives each project the whole machine); `--repo NAME` restricts the run to one project.

## 4. LLM baseline: prompting a model to write Lean directly (Table `tab:llm`)

Harness: `PastaBench/llm_bench/llm_eval.py`. This asks `claude-opus-4-8` for the Lean
directly, five samples per problem at temperature 1.0, and scores compilation and
test agreement against CPython.

```bash
python3 PastaBench/llm_bench/llm_eval.py all --datasets humaneval,livecodebench --k 5
```

Stages `generate`, `eval`, `report` can be run separately. This step needs an API key
for the model provider.

## 5. Verification: contracts and proofs (Appendix `app:contracts`)

The HumanEval problems we wrote contracts for and worked proofs through this path live
in the `PastaBench` Lean library. The generated code is produced from the contract-carrying
Python, and the hand proofs are checked by the Lean build; any proof that drifts
fails the build.

```bash
python3 PastaBench/pastabench.py regen        # re-generate Lean from solution_contracts.py
lake build PastaBench                          # type-check generated code + every proof
python3 PastaBench/pastabench.py status        # proof progress
```

Single-file proving through the CLI uses the same flags:

```bash
pastalean translate <file.py> --contracts --prove-asserts
```

`--contracts` runs the LLM contract pre-pass (`Requires`/`Ensures`/`Invariant`);
`--prove-asserts` searches for a tactic and splices the winning proof over
`:= by taste?`.

## 6. Regression suite (codegen coverage)

Every program under `example_scripts/` is translated and compile-checked in one warm
pass; any failure fails the build.

```bash
lake test                    # PALC over the whole example corpus
lake exe palc <dir|file>     # run PALC on a subset
```

## Output-file map

| Paper artifact | Command | Output |
| --- | --- | --- |
| Table `tab:codegen` (HumanEval) | `pastaeval.py humaneval [--run]` | `PastaBench/pastaeval_report.json` |
| Table `tab:codegen` (LeetCode, LiveCodeBench) | `pastaeval.py cp --source ...` | `<dataset>/convert_summary.json`, `eval_report.json`, `eval_divergences.json` |
| Tables `tab:static-*`, `tab:checkers-*` | `pastaeval.py typeinfer`, `run_autogen.sh`, `bench_checkers.py` | `typeinfer_bench/typeinfer_summary.json`, `autogen_summary.json`, stdout |
| Table `tab:ti-threads` | `run_autogen.sh` with varying `--jobs` | `autogen_summary.json` + log |
| Table `tab:typybench` | `run_predictions.py`, `score.py --tool ...` | stdout table |
| Table `tab:llm` | `llm_bench/llm_eval.py all` | `PastaBench/llm_bench/out/` |
| Appendix `app:contracts` | `pastabench.py regen` + `lake build PastaBench` | build pass/fail (self-checking) |
| Regression | `lake test` | build pass/fail |
