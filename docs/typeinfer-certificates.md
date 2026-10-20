# TypeInfer certificates — a checker that shows its work

## Why

`pastalean typeinfer --check` runs the `checkTypes` task over a module and reports type errors. Its
entire *positive* output was one boolean:

```lean
-- typeinfer_exe.lean
/-- ... `ok` is the per-program certificate: this module has no reportable type error. -/
```

`ok := diags.isEmpty`, and nothing even persisted it — `src/typeinfer/check.py` dropped the field.
So when the checker said a file was clean, there was no artifact, nothing to re-check, and nothing
for a benchmark run to write down: `PastaBench/typecheck_bench/check_corpus.py` computed a per-file
verdict and discarded it; `bench_checkers.py` computed which seeded mutants each tool caught and threw
that away too.

Meanwhile the proof layer already held the lemma a certificate would need, in a module **nothing
imported, so no build ever compiled it** (`TypeInfer/Theorem/Requirements.lean`):

```lean
theorem hasType_commit {evidence : List PyType} {t : PyType} {v : PyType.Val}
    (hc : (Req.ofEvidenceAll evidence).commit? = some t) (hv : PyType.HasType v t) :
    ∀ u ∈ evidence, u ≠ .unknown → PyType.HasType v u
```

**The goal:** make the checker emit a *certificate* — a per-file record of the evidence behind every
slot it judged — re-checkable by a small validator that never runs the inference engine, with one
Lean theorem saying what the validator's acceptance means.

## The shape of the idea

The certificate is the **witness**; the theorem is the **guarantee**. You prove one theorem, once,
and every accepted certificate is an instance of it. That is the verified-validator pattern
(CompCert's validators, Necula's proof-carrying code): no proof per file, and it still runs over
millions of lines.

What makes it cheap here is an asymmetry:

* **Producing** a certificate needs the whole engine — the fixpoint, the interprocedural pass, the
  1,662-line stamper, `usageEvidence`.
* **Checking** one needs none of it. Every judgment in `Diagnostics/Basic.lean` is a total function
  of a slot's evidence, so replaying `checkUses` / `checkAnnotation` over the recorded evidence
  reproduces the verdict or refutes it.

So the trusted base for "this module has no type error" shrinks from ~8,000 lines of engine to the
requirement algebra plus a ~240-line validator.

## What is in a certificate

```jsonc
{ "file": "real_conflict.py",
  "summary": "4 slots checked, 1 type error",
  "ok": false,
  "slots": [
    { "slot": "buf", "scope": "mangle", "kind": "local-var", "line": 2, "col": 5,
      "says": "uses require both str and int, which no type satisfies",
      "verdict":  { "verdict": "conflict", "expected": "str", "actual": "int" },
      "judgment": { "judgment": "uses" },
      "evidence": [ { "origin": "body-use", "req": "str" },
                    { "origin": "body-use", "req": "int" } ] }
  ],
  "diagnostics": [ /* one per failing slot */ ],
  "version": 1,
  "ir_hash": "10465593179643896654" }   // names the program this is about
```

Key order is chosen for a reader: the Lean side builds its JSON through `Json.mkObj`, which sorts
keys, so `slot` and `verdict` came out buried mid-alphabet. `file`, `summary` and `says` are added on
write and ignored on read — `Cert.ofCertJson?` looks up what it needs by name, so a re-ordered,
annotated certificate still verifies (checked: 165/165 and 16/16 read back from disk).

Five verdicts, split across two judgments:

| judgment | verdict | meaning |
|---|---|---|
| `uses` | `commits t` | the slot's uses narrow to exactly `t` |
| `uses` | `unconstrained` | no use constrained it |
| `uses` | `conflict a b` | two uses no single type satisfies |
| `declared ann` | `agrees` | every piece of evidence is consistent with the written type |
| `declared ann` | `rejects a b` | this evidence contradicts the written type |

Five slot kinds: `param`, `return`, `local` (an annotated `x: T = e`), `call-arg`, and `local-var`.
That last one is new with this work — the pass used to judge only a function's *boundary*
(parameters, return, call arguments) plus annotated locals, so an ordinary `i = 1` was never looked
at. Locals now get the judgment an unannotated parameter gets, which both extends the checker and
makes a certificate describe the whole function rather than its signature. On `example_scripts` that
is 884 local-variable slots out of 1,910, where there were none.

It is a real extension, not just extra reporting — this was previously undetectable, because `buf` is
a local:

```python
def mangle(items):
    buf = items[0]
    k = buf.isalpha()    # buf must be a str
    m = buf << 1         # ... and an int. No type is both.
```

```
real_conflict.py:2:5: error: unsatisfiable constraints
  mangle.buf
one use requires
  Int     -- python: int
another use requires
  String  -- python: str
no type satisfies both
```

Precision did not move: still 0 false positives over `example_scripts`. One wrinkle the validator
caught rather than I did — an annotated `x: T = e` was briefly getting two slots, one per judgment,
and the grounding rule refused the second.

## What the validator checks

`TypeInfer/Certificate/Check.lean`. **Its import list is the point**: `Certificate.Basic` and
`Annotation`, and nothing from `Solve/`, `Rules` or `Repo`. The three JSON helpers it needs are
re-declared locally rather than taken from `Solve/Env.lean`, so an engine dependency cannot creep in.

1. **Identity** — the certificate names this program (`ir_hash`) and this format version.
2. **Replay** — every verdict is what `checkUses` / `checkAnnotation` actually compute on the
   recorded evidence. *This is what the theorem is about.*
3. **Reporting** — every failing slot produced a diagnostic, and every diagnostic has a failing slot
   behind it. A certificate can neither hide an error behind a clean `ok` nor manufacture one.
4. **Grounding** — every *declared* type is the type the source really writes at that slot, and a
   slot judged by its uses really is an unannotated parameter.

## The theorems

`TypeInfer/Theorem/Certificate.lean`, both `sorry`-free and depending only on `propext`,
`Classical.choice`, `Quot.sound` — no `native_decide`.

```lean
theorem validate_sound (ast : Json) (c : Cert) (h : validate ast c = true) : CertSound c
```

If the validator accepts, then wherever the certificate says a slot's uses narrow to `t`, **every
runtime value of type `t` satisfies every one of those uses**. Discharged by `hasType_commit`.

```lean
theorem validate_error_sound (ast : Json) (c : Cert) (h : validate ast c = true) :
    ∀ d ∈ c.diagnostics, isScalar d.expected = true → isScalar d.actual = true →
      ∀ v : Val, ¬ (HasType v d.expected ∧ HasType v d.actual)
```

Every reported error between two scalars is a **real** error: no runtime value inhabits both types.
Not "the checker disagreed" — a value-level impossibility. This is exactly the claim the seeded-error
corpus in `typecheck_bench/negative/` measures.

Supporting these needed two new facts, both finite case analyses over the five scalars and seven
value shapes — the *introduction* direction of `Theorem/Meet.lean`'s `hasType_meet`, which only had
elimination:

```lean
theorem hasType_meet_intro_scalar : HasType v a → HasType v b → HasType v (meet a b)
theorem scalar_inconsistent_uninhabited : consistent a b = false → ¬ (HasType v a ∧ HasType v b)
```

### What the theorems do *not* say

Three limits, all load-bearing; they are in the module docstring and should travel with any
description of this work.

* **The evidence is taken as recorded.** Replay confirms the verdict follows from the evidence, and
  grounding confirms a *declared* type against the source — but a `bodyUse` requirement cannot be
  traced to the expression it was read from, because `usageEvidence` yields a bare `List PyType` with
  no positions. A certificate that invents a plausible body-use requirement is accepted. Grounding
  every requirement in its syntax node, and proving the rule that read it, is the next tier.
* **`HasType` is a model, not Python.** `PyType.Val` has seven constructors and no set, dict, tuple
  or closure inhabitant, so those lattice heads denote the empty set and claims about them are
  vacuous. `isScalar` is exactly the fragment where the model has content, which is why
  `validate_error_sound` is stated over it.
* **Nothing here verifies the inference algorithm.** No theorem connects `ofValue`, `typeOfExpr` or
  `inferFunction` to `HasType` — they are `partial def`s with no equation lemmas. The certificate
  routes around that; it does not close it.

## A fact that had to be proved first

`PyType` had no `DecidableEq` (`deriving` does not apply — `tuple`/`fn` recurse through
`List PyType`) and its hand-rolled `BEq` had **no lawfulness lemma**: `beq a b = true ↔ a = b` was
nowhere proved. A validator built on `==` would hand the theorem a `Bool` claim with nothing behind
it. So `TypeInfer/PyTypeEq.lean` proves `LawfulBEq PyType` and derives `DecidableEq` from it —
Mathlib-free and on the default build path, because the validator ships in the Mathlib-free
`typeinfer` binary. `beq_refl` and `zip_self_eq` moved there from `Theorem/Consistency.lean`, which
now imports them.

## Status

| Step | State |
|---|---|
| 0. Unblock the orphan proof modules (`Meet`, `Requirements`) | **done** — they still elaborate; now imported by `TypeInfer/Theorem.lean`, so `lake test` compiles them |
| 1. `Certificate/Basic.lean` — the record and its hand-written JSON | **done** |
| 2. `Certificate/Check.lean` — `validate`, no engine imports | **done** |
| 3. `Theorem/Certificate.lean` — `validate_sound`, `validate_error_sound` | **done** |
| 4. Producer + binary tasks + Python client | **done** — `certify` / `verifyCert` / `certifyBatch` / `verifyBatch`; `certify_ast` / `verify_cert` |
| 5. Kernel-checked `.lean` certificate for showcase files | **done** — `--emit-proof` |
| 6. `typecheck_bench` writes and re-verifies certificates | **done** |

The pass itself was **inverted rather than duplicated**: `Diagnostics/Pass.lean` now yields `Slot`s
and reads the diagnostics off them (`Slot.diagnostic?`). That is sound because every judgment reports
at most one diagnostic, built from the verdict's own two types — so a slot and its diagnostic are the
same fact in two shapes, and the slot additionally keeps what the old pass discarded: the evidence
weighed, and the verdicts on slots that *passed*.

## The kernel-checked form

`pastalean typeinfer f.py --emit-proof f_cert.lean` writes a file whose *compilation* is its
certificate check:

```lean
def fCert : Cert := { ... }
theorem fCert_replay : replayOk fCert = true := by cert_replay fCert
theorem fCert_sound  : CertSound fCert := replay_sound fCert fCert_replay
```

Two things had to be settled to make this work.

**`decide` and `rfl` do not reduce.** `PyType.meet`, `consistent` and `beq` are well-founded
recursions, so kernel reduction gets stuck on `WellFounded.fix`. Their *equation lemmas* do reduce,
so the `cert_replay` tactic is a `simp` over those — still an ordinary kernel-checked proof term.
`native_decide` is not used: `TypeInfer/` is free of `sorry`, `axiom` and `native_decide`, and that is
worth more than a convenience.

**`validate` had to be split.** The identity hash (`String.hash` is an `extern`) and the declaration
grounding (`Std.HashMap` lookups) cannot evaluate in the kernel at all. So `validate` is now
`replayOk c && groundedIn ast c`: the first half depends on the certificate alone and is what both
theorems are proved about; the second ties it to a program and stays with `--verify-cert`. The
generated file states that boundary in its own header rather than letting a reader assume more.

## Evidence so far

* `lake build TypeInfer.Theorem.Certificate` — green; `#print axioms` shows only the three standard
  axioms.
* 136 files (`example_scripts` sample + the full negative corpus): **zero diagnostic drift** against
  the old `checkTypes`, and **zero certificates rejected** by the validator.
* `example_scripts` (165 files): **0 false positives**, 165/165 certificates verified, 0.3 s,
  **1,910 slots** (683 params, 884 locals, 186 returns, 154 call args, 3 annotated locals).
* `typecheck_bench/negative` (16 files): **0 missed seeded errors**, 16/16 certificates verified.
* `mutate.py` over `example_scripts`: **169/204 mutants caught, 0 clean flagged** — the documented
  baseline, unchanged by the refactor, and the per-mutant catch set is now written to disk.
* **Every** emitted `.lean` across both corpora (181 files, up to 181 slots each) compiles, each
  depending only on `propext`, `Classical.choice`, `Quot.sound`. Two emitter bugs surfaced that way
  and are fixed: a file named `01_counter.py` produced `def 01_counterCert`, which is not a Lean
  identifier, and the largest certificate exhausted the default `maxRecDepth`.
* The readable on-disk JSON round-trips: 165/165 and 16/16 re-verified by reading the written files
  rather than the in-memory certificates.
* Mutation recall unchanged at 169/204 with 0 clean flagged — as expected, since `mutate.py` flips
  *annotations* on parameters and returns, which local coverage does not touch.
* `PALC/TypeInfer/TestCertificate.lean`: eight tamper cases, each required to be refused.
* Tamper tests, each of which must be refused — all refused, with a reason naming the failure:

  | tamper | validator's reason |
  |---|---|
  | wrong program | `certificate is for a different program (hash 12345, expected 10465593179643896654)` |
  | wrong version | `certificate format version 99, expected 1` |
  | flipped `ok` | `ok = true with 1 diagnostics` |
  | retyped declaration | `is_word.<return>: recorded verdict is not what the evidence yields` |

A validator that accepted everything would pass every other test here, so the tamper suite is the one
that actually tests the validator.

## Benchmarks

### Differential recall against the production checkers

`mutate.py` flips an annotation in known-good code, one mutant per seeded error, and a tool is
credited only when it flags the mutant *and* not its untouched original — so nothing is scored for
pre-existing noise. 204 mutants of 77 files, all six tools on the same machine (16 cores):

| Tool | Caught | Flagged clean | Time |
|---|---|---|---|
| **pastalean** | **169 (82.8%)** | **0 (0.0%)** | 0.8 s |
| ty | 149 (73.0%) | 47 (23.0%) | 0.1 s |
| pyright | 143 (70.1%) | 54 (26.5%) | 5.5 s |
| pyrefly | 140 (68.6%) | 56 (27.5%) | 0.5 s |
| zuban | 132 (64.7%) | 42 (20.6%) | 1.6 s |
| mypy | 119 (58.3%) | 80 (39.2%) | 1.5 s |

Read the second column with the first: the others flag a fifth to two fifths of the *unmutated*
files, which here are known-good. One honest caveat — those originals are `example_scripts`, the
corpus PastaLean's own filters were written against, so the zero has home advantage. The differential
rule protects the *caught* column from that; it does not protect the *flagged clean* one.

### Precision at scale: mypy_primer

158 projects, every file attempted, nothing skipped for size. Every diagnostic here is a candidate
false positive, because a project is on mypy_primer's list only if it already type-checks in its own
CI.

```
mypy_primer corpus: 158 projects, 68,542 .py files CHECKED
  diagnostics       294 (4.29 per 1000 files)
  front-end failed  6,221 (IR could not be built; excluded from the rate above)
  timed out         8 files (> 90s, bisected)
  wall              2,343s (29 files/s)
```

**These numbers are not comparable to the 238 / 72,923 in `README.md`, and neither is better or
worse than the other.** That figure was computed over a denominator that counted every file handed
to the checker, including the ~6,000 whose IR never built, and over a numerator that counted one
inlined definition once per module that inlined it. Both of those are fixed below. Saying whether
precision improved would need the old code re-run under the corrected harness, which has not been
done.

What *can* be said, because each was measured on its own:

* the use-conflict gate cut 310 to 213 under the old accounting, with no project getting worse
  (`scipy` 24→0, `spark` 13→0, `scikit-learn` 7→0);
* skipping inlined code cut `graphql-core` 36 to 12 **with the same 342 files checked**, and turned
  `sympy/core`'s eight line-0 duplicates of one `Float.__new__` into three diagnostics at real lines
  in their own files;
* the ellipsis fix recovered 38 of 354 files in `graphql-core` that were never being read.

The sweep earned its keep three times over, and none of what it found was in the certificate work.

### Three other things the sweep found

None of them have anything to do with certificates; all were pre-existing.

**`...` crashed the serializer — fixed.** `Ellipsis` is a real constant (`def f(): ...`,
`Callable[..., T]`, `a[...]`) and is not JSON-serializable, so `visit_Constant` raised `TypeError` and
the whole file was dropped. It is now carried as a null tagged `python_literal_kind: "ellipsis"`, and
both type readers answer `unknown` for it rather than `none` — `Callable[..., T]` says nothing about
its argument list, and `None` is a different type. On `graphql-core` alone this recovers **38 of 354
files** that were never being read.

**The harness was counting dropped files as checked — fixed.** `primer.py` reported "front-end
failed" only for whole-chunk crashes, while a file whose IR could not be built was counted in the
denominator and contributed zero diagnostics. Its docstring claimed "nothing is silently dropped",
which was not true: `graphql-core` was losing 50 of 354 that way. `check_paths_report` now returns
the split and the rate is computed over files actually read. **This means the older numbers in this
document and in `README.md` are not comparable to the new ones** — they were measured over a
denominator that included files nothing had parsed.

**Import inlining recurses into itself — diagnosed, not fixed.** `resolve_local_imports`' two halves
are mutually recursive: `_Rewriter.visit_Attribute` resolves `mod.f` by calling `load_module`, and
`load_module` rewrites every node it loads. The `loading` set stops a *cycle* but not a deep chain of
distinct modules, and a large package has those — `bokeh/src/bokeh/io/browser.py` spends **148.9 s**
nesting and then dies with `RecursionError` inside the rewriter, which is what pushed eight files past
the 90 s chunk ceiling.

Bounding the nesting depth and the module count does fix it — 148.9 s to 0.2 s, timeouts 8 to 0, and
the whole sweep 4.2x faster — but it is **not a free win and was reverted**: less inlined context
means weaker inference, and the diagnostic count rose sharply (`sympy` 5 to 107, `graphql-core` 12 to
53). Measuring the alternative showed no clean threshold either, because uncapped inlining over
`sympy/core` is itself slow enough to time out, so sympy's legitimate need for context and bokeh's
pathology are not separable by volume. The real fix is to phase-separate loading from rewriting —
discover and parse every reachable module with a worklist, then rewrite against the finished table —
which removes the recursion without giving up any context. That is a front-end change with its own
precision risk, so it is written down here rather than taken unilaterally.

### Is the checker parallel? Yes — and here is where it stops

Already parallel on both halves: IR building forks across a process pool (the `ast` walk is pure
Python, so threads would queue on the GIL), and the checks then fan across the Lean exe's task
scheduler and, past one process's ceiling, across several exe processes (`_fan`, sharded at 32
modules). So the question is not whether to parallelise it but how far it actually goes. Measured
over 2,000 `sympy` files on 16 cores:

| jobs | check (s) | certify (s) | files/s | speedup | certificate overhead |
|---|---|---|---|---|---|
| 1 | 296.6 | 304.4 | 7 | 1.00x | +2.7% |
| 2 | 158.9 | 162.0 | 13 | 1.87x | +1.9% |
| 4 | 92.0 | 90.5 | 22 | 3.22x | −1.7% |
| 8 | 57.0 | 56.6 | 35 | 5.20x | −0.7% |
| 16 | 56.2 | 55.6 | 36 | 5.27x | −1.1% |

Two things to read off it. **Certificates are free**: producing one is within noise of not producing
one, because it is the same pass — the verdict was already computing everything the record holds.
And the speedup **plateaus at 8 jobs**, reaching 5.3x rather than 16x.

That plateau is not the sharding formula. Splitting the Lean half into 1, 2, 4, 8 or 16 shards moves
it between 20.7 s and 24.2 s with no trend, so `_fan`'s conservative `jobs // 8` is not what caps
anything and tuning it would be noise. The work is split almost evenly instead — at 16 jobs, 45.6%
is Python building the IR (263 MB of it for 1,609 files) and 54.4% is Lean checking it — so there is
no single bottleneck to remove, and a real gain would have to come from cheaper IR generation or less
per-file work in Lean, not from more processes.

## What is left

* **Ground the body-use evidence.** The one real gap: a `bodyUse` requirement cannot be traced to the
  expression it was read from, because `usageEvidence` returns a bare `List PyType`. Closing it means
  carrying `(rule, position)` through `Solve/Usage.lean` and proving the rule table — the Tier-B work
  deliberately excluded here.
* **Certify inference, not just checking.** TypeEvalPy and TypyBench score *inferred* types; those
  facts carry no evidence today. That needs evidence threaded through the fixpoint, the
  interprocedural pass and the stamper.
* **Scale.** Certificates are ~2x source size as indented JSON. `mypy_primer` (72,923 files) has not
  been run with `--certs` yet; a compact encoding may be wanted there.
* **Widen the model.** `PyType.Val` has no `set`/`dict`/`tuple`/closure inhabitant, so
  `validate_error_sound` is stated over scalars. Extending the denotation would widen it.

## Files

| File | Change |
|---|---|
| `TypeInfer/PyTypeEq.lean` | **new** — `LawfulBEq PyType`, `DecidableEq PyType`, Mathlib-free |
| `TypeInfer/Certificate/Basic.lean` | **new** — `Cert`/`Slot`/`Evidence`/`Judgment`/`Verdict` + JSON |
| `TypeInfer/Certificate/Check.lean` | **new** — `validate`; no engine imports |
| `TypeInfer/Certificate.lean` | **new** — re-export |
| `TypeInfer/Theorem/Certificate.lean` | **new** — `validate_sound`, `validate_error_sound` |
| `TypeInfer/Theorem.lean` | imports `Meet`, `Requirements`, `Certificate` |
| `TypeInfer/Theorem/Consistency.lean` | `beq_refl`/`zip_self_eq` moved out to `PyTypeEq.lean` |
| `TypeInfer/Diagnostics/Pass.lean` | yields slots; diagnostics read off them; `certifyModule` |
| `typeinfer_exe.lean` | `certify`, `verifyCert`, `certifyBatch`, `verifyBatch` tasks |
| `src/backend/typeinfer.py`, `src/typeinfer/check.py`, `src/typeinfer/cli.py` | client, batching, flags |
| `src/typeinfer/proof.py` | **new** — render a certificate as a checkable `.lean` file |
| `PALC/TypeInfer/TestCertificate.lean` | **new** — unit checks, incl. eight tamper cases |
| `PastaBench/typecheck_bench/{check_corpus,bench_checkers}.py` | persist certificates and per-mutant results |
| `TypeInfer/README.md`, `REPRODUCE.md` | document it; three stale README facts corrected |
