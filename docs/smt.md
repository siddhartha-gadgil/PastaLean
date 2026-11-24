# SMT solvers in PastaLean, with every answer re-checked in Lean

Status: research notes and a prototype (Nov 2026, Lean 4.36.0, Mathlib v4.36.0). The rule: an SMT
solver may be faster than Lean's own search, but nothing it says counts until Lean has checked it.

* **sat → counterexample.** A model is only a candidate witness. Refute evaluates it in both twins and
  certifies it with `refute_at` (the kernel decides the instance), exactly as for a `grind` model. A
  wrong model, a translation slip or a solver bug costs time and nothing else.
* **unsat → proof.** Only counts if the solver's proof is rebuilt as a Lean term and the kernel checks it.

## 1. What exists (checked 2026-11-23)

| project | what it does | trusts the solver? | Lean version on its default branch | on 4.36 |
|---|---|---|---|---|
| [lean-smt](https://github.com/ufmg-smite/lean-smt) (ufmg-smite) | `smt [h₁, …]` tactic: goal → SMT-LIB → cvc5 (FFI through [lean-cvc5](https://github.com/abdoo8080/lean-cvc5)) → replays cvc5's CPC proof as a Lean term | no: the kernel checks the replayed proof; steps it cannot replay come back as goals | v4.35.0 (main, 2026-11-09; no v4.36 tag yet) | **builds and works** after a one-line patch to lean-auto (§3) |
| [lean-auto](https://github.com/leanprover-community/lean-auto) | monomorphisation (dependent types → HOL/FOL) and front end for external provers | its SMT (z3/cvc5) and TPTP modes do **no** reconstruction (README); proofs only through native backends such as Duper | tag v4.35.0 | fails at one line on 4.36 (`Core.Context` gained `optionFlags`); patched locally |
| [Duper](https://github.com/leanprover-community/duper) | superposition prover written in Lean, proof-producing | n/a (no external solver) | tag v4.35.0 | not tried |
| [LeanHammer](https://github.com/JOSHCLUNE/LeanHammer) | premise selection + lean-auto + Duper (+ `grind`/`aesop`) | reconstructs | v4.35.0 | not tried |
| Lean core `bv_decide` | bit-blasts `BitVec`/`Bool` goals to CNF, CaDiCaL returns an LRAT certificate, a verified LRAT checker checks it | no: the checker is proved correct in Lean, but it runs by `Lean.ofReduceBool` (the compiler is trusted, as with `native_decide`) | core | yes (built in) |
| z3 → Lean (Lev Nachmanson's PRs to Z3: [#11017](https://github.com/Z3Prover/z3/pull/11017), [#11224](https://github.com/Z3Prover/z3/pull/11224), [#11276](https://github.com/Z3Prover/z3/pull/11276), [#11424](https://github.com/Z3Prover/z3/pull/11424); [reports](https://levnach.github.io/z3/)) | Python exporter turns Z3's proof log into a Lean file (`omega`/`grind` per theory lemma), checked by `lean` | no, but the SMT-LIB parser / Python translation are trusted; offline (a file), not a tactic | its own pinned workspace | not tried; not a tactic, so not usable as a `taste?` closer |
| [pmatos/z3-to-lean](https://github.com/pmatos/z3-to-lean) | parses Z3's `sat.euf` proof log in Lean | proof terms are future work | — | — |
| QuerySMT ([Clune, Barbosa, Avigad, "Hint-Based SMT Proof Reconstruction", arXiv 2601.14495](https://arxiv.org/abs/2601.14495)) | cvc5's intermediate facts become hints; `grind`/Duper re-prove the goal | no | [repo](https://github.com/JOSHCLUNE/QuerySMT) on v4.29.0 | not tried |

lean-smt's paper ([CAV 2025, arXiv 2505.15796](https://arxiv.org/abs/2505.15796)): about 200 of cvc5's
662 CPC rules are reconstructed (163 by lemmas, 37 by tactics, 5 by verified reflection, e.g. a verified
polynomial normaliser); 71% of 21,595 cvc5 proofs re-checked by the kernel. Its README lists UF and
linear integer/real arithmetic (with quantifiers) as supported, bit-vectors as experimental. There is no
Z3 counterpart for Lean as a tactic: Isabelle's Sledgehammer replays Z3 proofs, Lean does not.

What I could not verify: Duper, LeanHammer and QuerySMT on 4.36; the z3 → Lean exporter's state
outside the PR descriptions; lean-smt's string theory (no reconstruction rules for strings appear in its
`Reconstruct/` tree, so I assume none).

## 2. SAT side: `pastalean refute --smt` (prototype, off by default)

`PastaLean/PyVerify/Refute/Smt.lean`, a sibling of `Solve.lean`:

1. the obligation is split and unfolded exactly as for `grind` (program definitions, Python operators,
   `Id.run` through `if`s);
2. every hypothesis and the negated body go to SMT-LIB: linear and nonlinear `Int`/`Nat`/`ℚ` arithmetic
   (Lean's `/`, `%` and Python's floor `//`, `%` encoded exactly), `Bool`/`Prop` connectives,
   `if`/`dite`, and `String` length, `++`, `startswith`/`endswith`, `in`, `replace`, `find`, slicing and
   indexing with Python's negative-index rules. Anything else becomes a fresh constant, so the query is an
   over-approximation (a model may be spurious; it is never lost to an untranslatable side condition);
3. z3 or cvc5 runs as a subprocess (`$PASTALEAN_SMT`, else `z3`/`cvc5` on `PATH` or `~/.local/bin`);
4. the model becomes `List PyLit` and joins the witnesses that `runTarget` judges in both twins and in
   CPython and certifies with `refute_at`. Plateau seeds (the coverage search's closest inputs) are also
   solved this way. `unsat` is reported as `unsat-untrusted` and changes nothing.

Switch it on with `pastalean refute --smt FILE`, `PASTALEAN_REFUTE_CONFIG='{"smt": true}'`, or
`refute? (config := { smt := true })` / `#refute thm (config := { smt := true })`.
`PASTALEAN_SMT_DUMP=<dir>` saves each query.

Installing the solvers without sudo (what was done here):

```bash
gh release download z3-5.3.3 -R Z3Prover/z3 -p 'z3-5.3.3-x64-glibc-2.39.zip'      # or z3-solver from pip
gh release download cvc5-1.4.2 -R cvc5/cvc5 -p 'cvc5-Linux-x86_64-static.zip'
unzip … -d ~/.local/opt && ln -s ~/.local/opt/…/bin/{z3,cvc5} ~/.local/bin/
```

### Measurements

Solver step alone (`PastaBench/smt/bench_sat.py solver`: Plausible, enumeration and coverage search off, so
witnesses come only from `grind` or the SMT model; z3 5.3.3; the 52 contract obligations of
`example_scripts/refute/` and CrossHair's 32-problem benchmark):

| | model that Lean confirms as a counterexample | proved / unsat | median time |
|---|---|---|---|
| `grind` (cutsat model) | 2 | 1 proved (a Lean proof) | 21 ms |
| SMT (z3 model) | 8 (a superset of grind's 2) | 1 `unsat` (not trusted, not used) | 86 ms |

The 6 extra are exactly the nonlinear and string obligations of `example_scripts/refute/nonlinear_smt.py`
(Pythagorean triple with a sum, semiprime, taxicab, quadratic root, `x % 97 == 13 ∧ x² % 101 == 5`,
a string with prefix/suffix/length tied to `n * n == 49`); `grind`'s models there are spurious (`n * n`
is an opaque atom to cutsat). On the CrossHair problems neither solver produces a usable model: regexes,
`date`/`datetime`, dicts and loops are outside both fragments, and the values are found by the search
engines instead. SMT's median is dominated by starting a solver process per query (~70-100 ms);
cvc5 1.4.2 instead of z3 returned `unknown` on 3 of the 7 nonlinear obligations (pythag, taxicab,
mod_square) where z3 answers in ~0.1-0.3 s.

End to end (`PastaBench/smt/bench_sat.py full`: default refute vs `--smt`, 8 s per obligation, 4 files in parallel on a
warm daemon): 38 vs 39 of 53 obligations refuted. `--smt` adds pythag and mod_square (the other
nonlinear ones are already reached by the literal-pool/coverage search: `17 * 23`, `9³ + 15³`, `2013`);
it lost version_compare once, which was budget noise (re-run alone: refuted with and without `--smt`).
The regex problems need the 60 s budget of the published benchmark, so their counts at 8 s are noisy.


## 3. UNSAT side: lean-smt as a `taste?` closer (prototype, worktree only)

**It builds on 4.36.** lean-smt `main` (cbec5bd, toolchain v4.35.0) with Mathlib v4.36.0: the only
failure is lean-auto v4.35.0's `Auto/Lib/ExprExtra.lean:365`, which builds a `Core.Context` with a new
`options` but not the `optionFlags` field 4.36 added. One-line patch:

```diff
-    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
+    withOptions (fun o => o.setBool `smartUnfolding false) do
```

lean-cvc5's FFI (`ffi.cpp`) compiles with the clang that ships in the Lean toolchain (put
`~/.elan/toolchains/leanprover--lean4---v4.36.0/bin` on `PATH`; no system clang needed) against the
static cvc5 1.3.2 it downloads from its own fork's release. Tactics run under `lake lean FILE` (or
`lake build`), which loads cvc5's shared library; plain `lake env lean` fails with "Could not find native
implementation of external declaration 'cvc5.TermManager.new'".

Sanity checks (all with axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`/`ofReduceBool`):
`x < y → x + 1 ≤ y`, `n * n = 1764 → n > 0 → n = 42`, `x > 0 → y > 0 → x * y > 0`. A parity goal over
`%` failed ("Failed to reconstruct sort Real") without `import Smt.Real`. On the false
`x³ + y³ ≠ 1729` it answers sat (no proof, as it should).

**The closer** (`PastaSmt/Closer.lean`, a separate `lean_lib`, not a default target, not imported by
`PastaLean`): `taste_smt` = `intros; try simp_all [taste_ingr]; try push_cast at *; all_goals smt [*]`
(timeout 10 s), so the Python operators are lowered first; `taste_smt_raw` skips the lowering. On
`n *ₚ n = 1764 → n > 0 → n = 42`, `taste?` fails after 9.5 s and `taste_smt` proves it in 42 ms.

**Against `taste?` on real obligations** (`PastaBench/smt/gen_cmp.py`, `run_cmp.py`, `summ_cmp.py`): 80 contract solutions
sampled from PastaBench (40 HumanEval, 40 LeetCode, seed 7), translated with every `taste?` replaced by
`taste_cmp`, which runs each closer on each goal from the same state (200k heartbeats each; a proof
counts only if no goal remains and it does not rest on `sorry`, transitively). 79 files, 168 goals
(one file timed out at 15 min; 8-10 have elaboration errors unrelated to the closers):

| | goals closed | median ms (closed) | median ms (failed) | total |
|---|---|---|---|---|
| `taste?` | 58 | 198 | 34,300 | 81 min |
| `taste_smt` | 25 | 28 | 68 | 1.5 min |
| `taste_smt_raw` (no lowering) | 1 | | | |
| `taste_smt` preprocessing alone (`… ; done`) | 23 | | | |
| closed by `taste_smt` and not by `taste?` | **0** | | | |

So the solver itself closed 2 goals (HarshadNumber, MagicalString) beyond what its own `simp_all`
does, and `taste?` closes both. PastaBench's obligations are loop invariants over lists, strings and
`HashMap`s, `pyLen`/`foldl`/indexing facts: after lowering, cvc5 sees them as uninterpreted functions and
cannot refute the negation. Nonlinear integer facts, where cvc5 does beat `nlinarith`/`grind`, are rare
in this corpus. The one real advantage is failing fast (68 ms vs 34 s), which only matters if the
closer runs before the slow `taste?` candidates.

**Dependency cost** (measured in the worktree):

* three new packages: `smt` (cbec5bd), `auto` (v4.35.0 + the patch), `cvc5` (lean-cvc5 d19a134, which
  downloads an 86 MB static `libcvc5.a`); 0.8 GB on disk with builds (smt 179 MB, auto 432 MB, cvc5
  226 MB);
* cold build of the stack on top of a built Mathlib: 81 s wall (24 cores, 594 jobs, 2.9 GB peak RSS);
* Mathlib and its dependencies resolve to exactly the revisions PastaLean already pins, as long as
  `require mathlib` stays last in the lakefile (otherwise lean-auto drags in older batteries/aesop/Qq);
* version pinning: no lean-smt/lean-auto/lean-cvc5 release targets 4.36 yet; the patch lives in
  `.lake/packages/auto` and `lake update` would discard it (lake warns "auto: repository has local
  changes"). Merging needs a fork with the patch or upstream v4.36 tags (lean-auto/Duper have so far
  tagged each Lean release within weeks);
* if `taste?` itself used it, `PastaLean` (and so every generated program, `py2lean` and PALC) would
  import lean-smt and link cvc5 (a 33 MB shared library at elaboration time), and every bump of the
  Lean toolchain would wait for three more projects.


## 4. Recommendation

* **SAT side: merge, off by default** (`Refute/Smt.lean`, the hooks in `Task.lean`/`Tactic.lean`, the
  `smt` config field and `--smt`). No new Lean dependency, an external binary only when asked for, and
  nothing it returns is trusted: every model goes through the existing judging and `refute_at`. It
  refutes nonlinear-integer and string obligations `grind` cannot (6 of 52 in the solver-only bench, 2 of
  53 end to end beyond what the search already finds), for ~0.1 s per obligation. Next: a persistent
  solver process, sequences for list binders, z3 first (cvc5 was weaker on NIA here).
* **UNSAT side: do not merge lean-smt now.** It works on 4.36 and its proofs are genuinely
  kernel-checked, but on 168 PastaBench goals it closed nothing `taste?` does not, and it costs three
  pinned dependencies (one needing a patch) plus cvc5 linked into everything that imports `PastaLean`.
  Revisit if (a) lean-smt/lean-auto publish 4.36+ tags, and (b) a corpus with nonlinear integer
  obligations appears (the `n * n = 1764` shape, where it wins outright). If it is ever wanted, keep it
  as an opt-in library (`PastaSmt`) whose closer a user adds explicitly, not inside `taste?`.
* **Found on the way and fixed:** `tasteProves` and `certify` accepted proofs that use `sorry`
  *transitively*. In a refute module every theorem is admitted, so `grind +locals +suggestions` could
  "prove" a false obligation from its own admitted spec lemma, and refute would report `PROVED` whenever
  the search missed (`slug` in `nonlinear_smt.py` with the engines off). Both now reject any proof whose
  constants depend on `sorryAx` (`restsOnSorry`, `Solve.lean`).
* z3 → Lean certificates (Nachmanson's exporter) are worth watching: QF_LIA/QF_UFLIA through `omega`/
  `grind` per theory lemma would suit PastaLean's goals better than cvc5's CPC, but today it is an
  offline Python pipeline, not a tactic.

