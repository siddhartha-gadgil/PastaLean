# Refute: counterexamples (and proofs) for Python contracts, in Lean

Refute takes a claim about a Python program — a property function, a contract (`Requires` / `Ensures`,
PEP 316 docstrings, icontract decorators) or a Lean goal — and either finds an input that breaks it or
shows that none exists. All search happens in Lean, over the translated program; CPython only replays the
inputs Lean found, so every reported counterexample is checked against the real Python.

## Three ways to use it

**In a Lean proof** — `refute?` decides the goal in front of it:

```lean
example : ∀ xs : List Int, xs.length ≤ 3 → xs.sum ≠ 7 := by
  refute?            -- error: goal is FALSE, counterexample: xs = [7]  (kernel-checked: refute_at ([7] : List ℤ))

example : ∀ a b : Int, a + b = b + a := by
  refute?            -- closes the goal: no counterexample exists, grind proves it

example : ∀ n : Nat, n * n ≠ 1764 := by
  refute? (config := { timeMs := 8000, seed := 7 })   -- n = 42
```

A false goal is an error carrying the witness and, when the kernel can check it, a `refute_at` proof of
`¬ goal`. A true goal is closed by the proof that showed it (`grind` or `taste?`). Otherwise `refute?`
reports how many inputs it tried and leaves the goal. `#refute thm` does the same for a declaration.
`taste?` runs a quick refute pre-check first, so proof search never burns time on a false goal.

**From the shell** — the full three-world check of every obligation in a Python file:

```bash
pastalean refute file.py            # verdict per obligation, witness, which worlds violate it
pastalean refute file.py --json     # machine-readable
pastalean refute file.py --time 30000 --tests 1000000000 --seed 1
```

Verdicts: `REFUTED` (fails in the provable twin, the runnable twin and CPython), `PROVED`, `FLOAT_ONLY`
/ `ROUNDING_SENSITIVE` (holds over exact ℚ, fails in IEEE floats), `PARTIALITY_GAP` (CPython raises where
the exact model returns a default), `FIDELITY_BUG` (the Lean twins disagree with CPython: a translation
bug), `NONTERMINATION`, `PRECONDITION_MISMATCH`, `INCONCLUSIVE`.

**From Python** — `pastalean.refute.refute_file(path, session=…)`; pass one `Session` for many files.

## Speed

| | time |
|---|---|
| `refute?` / `#refute`, false goal (typical) | 30–300 ms |
| `refute?`, true goal (search budget, then a proof attempt) | ~1–1.5 s |
| `pastalean refute`, first call (boots the Lean backend) | ~3.6 s |
| `pastalean refute`, later calls (warm daemon) | ~0.3 s |

The first `pastalean refute` starts a background daemon (one per backend binary, exits after 10 idle
minutes) that later calls reuse; `PASTALEAN_NO_DAEMON=1` runs cold. It serves requests in parallel, one
warm backend per concurrent caller, up to `PASTALEAN_DAEMON_POOL` (default 1, ~7 GB per backend): with a
pool of 4, four simultaneous refutations take ~0.5 s each once warm. The benchmark harnesses below set the
pool to their `--jobs`, so they run warm.

## How it searches

1. **Plausible** over typed generators (`PyArb`) seeded with a literal pool mined from the program and the
   libraries it calls — strings, integers, members of its `re` patterns, `date`/`datetime` literals.
2. **Coverage-guided search** over an instrumented copy of the program: every decision logs its branch, how
   far it was from flipping (`|a − b|`, edit distance), and the values it compared. Inputs that reach new
   branches are kept and mutated; the input closest to an unreached branch is climbed toward it; compared
   values are spliced into inputs; two inputs are crossed for conjunctions; branches in loops also get
   "every iteration" goals.
3. **`grind`** on the obligation (a proof, or a model to try), and at a plateau on the closest inputs'
   integer leaves; **`taste?`** proves what no input breaks.

Configuration (`refute? (config := { … })`, or the CLI's `--time`/`--tests`/`--seed`): `timeMs`
(budget, default 1000), `numInst` (test cap), `seed`, `plausible`, `instrument`, `solver`, `intCap`. For
engine experiments from the shell: `PASTALEAN_REFUTE_CONFIG='{"plausible": false, "solver": false}'`.

## Benchmarks

All in `PastaBench/pbt_bench/`:

```bash
uv run python run.py --tools refute,crosshair --timeout 60   # CrossHair's 32-problem benchmark
uv run python heldout.py --timeout 20 --crosshair             # CrossHair's own examples (held out)
uv run python mutants.py --limit 80 --per 2 --timeout 30      # mutation benchmark, HumanEval/LeetCode
uv run python contract_gaps.py                                # refute every contracted solution
```

Current results: 30/32 on CrossHair's benchmark (CrossHair 29–30); 9 bugs and 0 false alarms on CrossHair's
own examples (CrossHair 13 and 2); 56/58 contract-detectable mutants killed (median 3.8 s), 0 false alarms
on the unmutated solutions; 33 of 464 corpus contracts refuted, each a missing precondition or a wrong
contract (`results/contract_gaps.json`).
