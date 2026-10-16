---
name: verify-python
description: Prove that Python logic is correct by translating it to Lean 4 with PastaLean and proving its contracts. Use when asked to verify, prove, or formally check a Python function (numerical code, data-processing logic, algorithms, agent-generated scripts), or when a result computed by Python must be trusted on all inputs rather than tested on a few.
---

# Verify Python with PastaLean

PastaLean deterministically translates Python into Lean 4: a **provable twin** (exact arithmetic,
for proofs) and a **runnable twin** (Float, for execution). Contracts written in the Python become
Lean theorems. Proving them shows the Python is correct on *all* inputs that satisfy the
preconditions.

Use the `pastalean` MCP tools if they are connected. Otherwise run the same steps from the repo root
with the CLI (`uv run pastalean translate f.py -o f.lean`, `lake env lean f.lean`).

## Workflow

1. **Understand the intent.** Decide what the function is *for* (e.g. "returns n!", "result is
   sorted and a permutation of the input"). That property is what gets proved.

2. **Write contracts** in the Python. Read `get_guide("contracts")` (or
   `docs/contract-prompt-system.md`) the first time. In short:
   - `from contracts import *` at the top.
   - `Requires(p)` and `Ensures(p)` at the top of the body. `Result()` is the return value.
   - `Invariant(p)` as the first statement of each loop; `Decreases(e)` for `while`.
   - Quantify with `all(... for x in xs)` / `any(...)`; write implication as `not a or b`.
   - Never use `Forall`, `Implies`, or `Old`. They are vacuous.
   - State the purpose, not bookkeeping. A shallow bound like `Result() >= 0` proves almost
     nothing.

3. **Translate**: `translate_python(source=..., name="f")`. Check:
   - `degraded: true` means some logic became `pyUnsupported`. You cannot verify it as written.
     Restructure the Python (`get_guide("verifiable_design")`) and translate again.
   - `compile.errors` should be empty. `open_obligations` lists the theorems to prove.

4. **Prove** each obligation by editing `lean_path`, **only the proof after `:= by`**.
   - Start from `get_guide("proving")` and the closest worked example: `list_proved_examples("mvcgen")`,
     then `get_example("CountUpTo")` or `get_example("playground/factorial")`.
   - For loops: `mvcgen [f, pyRange_forIn, pyRange_forIn_start] invariants`, one
     `· ⇓⟨cur, vars…⟩ => ⌜…⌝` bullet per loop, invariant restated over `(cur.prefix.length : Int)`,
     then `all_goals simp_all [taste_ingr]` and a closer battery
     (`omega | nlinarith | (ring_nf; omega) | grind`).
   - **Dig into the repo when stuck.** For each runtime function in a goal (`pyLen`, `pyAppend`,
     `pySetItem`, …), run `find_definition` to see what it computes and `search_lemmas` /
     `grep_source` for facts already proved about it. Read the surrounding file with `read_source`.
     With file access, read `PastaLean/PyAPI/` and `PastaLean/PyVerify/` directly. Missing facts
     become helper lemmas in your file.
   - Iterate with `check_lean(lean_path=...)`.

5. **Verify**: `verify_theorems(lean_path=...)`. This is the only verdict:
   - `verified: true` requires every theorem `"status": "proved"`, meaning no `sorryAx`, no
     `native_decide`, no extra axioms.
   - It also requires `fidelity.ok`: every `def` and theorem statement is exactly as translated. Never
     edit a definition or a statement to make a proof go through. Adding `def`, `instance` or
     `notation` is rejected.

6. **Cross-check execution** with `run_differential`. Add an `if __name__ == "__main__":` block that
   prints the function on edge cases. CPython and the runnable twin must agree.

7. **Report honestly**, per function, one of:
   - **Proved**, with the property in plain words.
   - **False**: the contract does not hold. Give the counterexample; that is a bug found in the
     Python (or in its spec).
   - **Not proved yet**: say which obligation remains and what was tried.

   Never call something verified on the strength of tests, a compiling file, or `sorry`.

## When a proof will not close

First test the claim. Evaluate the runnable twin (`#eval f'rn …` in `check_lean`) or run
`run_differential` on edge cases (0, negatives, empty lists, duplicates). False postconditions are
the most common failure. If the claim holds, the invariant is usually too weak: add the missing
bound, length, or relation to the loop index. If it only holds for some inputs, add a `Requires` to
the Python and re-translate.

## Scope

Supported: arithmetic, loops, mutation, early return, multiple returns, exceptions, closures, memo
dictionaries, comprehensions, generators, `match`, classes (value semantics), and parts of numpy,
pandas, `math`, `heapq`, `bisect`, `itertools` and `collections`.

Not supported: dynamic dispatch, multiple inheritance, `eval`/`exec`, monkey-patching,
async/threads. Proof automation is best-effort, so expect to write invariants and some proof steps
yourself.
