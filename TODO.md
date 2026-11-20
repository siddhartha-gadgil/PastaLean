# TODO

Open work, newest concerns first within each section. Delete an item when it is done; add one when
something is found to be missing.

## Refute (counterexample search)

Roadmap (from the CrossHair / search-based testing / hybrid fuzzing research). Done: coverage-guided
search over an instrumented copy (`Coverage.lean`, `Instrument.lean`, `PyArb.mutate`, branch distance +
operand splicing), `partial def`s instrumented as unsafe copies (one mutual block), distances for floats,
list `==`, set `==` and list membership, plateau solving (`solvePlateau`: the closest inputs to unreached
branches keep their shape, `grind` solves their integer leaves) and `taste?` proving obligations no
witness violates (`tasteProves`, also in `refute?`/`#refute`). Next:
- **Plateau solving mid-search.** Seeds are solved after the search ends; feeding solved seeds back
  into the running loop (corpus) would let it continue from them. Seeds with no integer leaf (strings,
  booleans) are skipped: solve string leaves too (length constraints first).
- **Aggregate properties beyond loops.** Branches in a loop get "every hit goes this way" goals (summed
  distance), which solved `find_5_times`; a property over a whole collection with no branch per element
  (`sorted(xs) == xs`, a `sum`) still has only the final comparison's distance.
- **Structurally/well-founded recursive definitions** are still called uninstrumented (their compiled
  code is not in the environment); only `partial` ones are copied.
- **Distances must not change the program's observable behaviour.** `a and b` / `a or b` distances now
  short-circuit like the program, and errors a distance records are discarded; a distance over a
  comparison whose operands are expensive (a library call) still re-evaluates them: cache the operands
  the decision computed instead of recomputing them in the thunk.
- **Choice-sequence shrinking and mutation** (Hypothesis/Zest): one representation for generate,
  mutate and shrink.
- **Distances for more operators.** `≠` (`Ne`) had none, so every inequality was a blind search
  (`n * n ≠ 1764`: 70k tests → 78 once added, with distance-scaled `PyArb.climb` moves). Check the other
  decision shapes the same way: `Nat.ble`/`Int.decLe` forms, `%`, membership in a `Std.HashMap`/`PySet`.
- **Mutation benchmark** (`PastaBench/pbt_bench/mutants.py`): the main measure from now on — kill rate
  over mutants whose contract a test input violates (78% at 80 problems × 2), and originals refuted
  (3/80, all real contract gaps: missing `Requires` such as "adjacent elements differ"). Misses:
  - `ValidDate`'s slicing type errors (translation);
  - `FaultyKeyboard`: a search miss at the full budget.
- **Crossover** (`PyArb.crossover`, used by the coverage search) solved a conjunction no single branch
  steers toward (`FileNameCheck`: three digits AND a valid name → `'b207.exe'`); structures other than
  strings, lists and tuples still use the default (keep the first value).
- **Fix the PastaBench contracts refute broke** (`PastaBench/pbt_bench/contract_gaps.py`, report in
  `PastaBench/pbt_bench/results/contract_gaps.json`): 33 of 464 solutions. Most lack a `Requires` the
  problem states (distinct / positive elements, a rotated sorted input, a digit string, untyped parameters
  that admit `None`); some are wrong outright (`MirrorReflection`: "result 2 whenever p != 1";
  `CountTestedDevices`; `MaxSumOfAPairWithEqualSumOfDigits`: "always -1").
- **Held-out evaluation**: `PastaBench/pbt_bench/heldout.py` (CrossHair's own examples). Misses:
  `getattr` with a computed name, contracts on methods (`__eq__` with `self` symbolic) and `abc.ABC`
  bases, aliasing inputs (the same list twice; value semantics cannot express it).
- **Per-type compilation of the search.** `evalExpr` specialises `runSearch`/`checkIO` to each binder
  type, which costs up to seconds per obligation for heavy instances (the `taste?` pre-check now passes
  `plainStrategy` so it compiles only the small loop). Running the precompiled generic code instead
  (`@[nospecialize]`, or the instance behind a `@[noinline]` call) made generators miss the
  per-search pools (`ctorPool`): the unspecialised path apparently reads a different copy of the
  `initialize`d refs. Find out which copy each path reads; with one shared copy the search could skip
  per-type compilation entirely.

- **Relational inputs.** Binders are drawn independently, except that a binder replays the previous
  one's random state a fifth of the time (equal values of one type), dates/timedeltas derive from
  constructor literals, and dict keys from pool strings. Still open: a list and a valid index into it,
  a value derived from another by an operation (`b == a + 1`), relations across different types.
- **Plausible coverage.** Plausible is the primary engine; obligations it cannot take (no runnable
  `Decidable`, no `PyArb` for a binder type) fall back to the enumeration/random search. Give every
  input type a `PyArb` (user classes get generated instances already; check `PyAny`, nested dicts,
  sets, tuples) so the fallback is only for per-case deadlines.
- **Per-case deadlines in Plausible.** Plausible now runs in chunks of 200 tests until its half-budget
  deadline, so it never outlives the deadline by more than one chunk; a single non-terminating case
  still flags `hang` and leaves a spinning thread until the backend restarts. Run each case under a
  deadline, or through a fuel-bounded twin.
- **Stdin mode input generation** is still Python-side (`src/refute/stdin.py`); move it to Lean.
- **`taste?` pre-check cost**: PALC went ~89 s → ~120 s with the grind pre-check (now ~117 s, with
  Plausible off in the pre-check); tune its budget.
- **Guard-directed generation** beyond lengths: string/list lengths are drawn from pool integers
  (`len(v) == 3`), but other guard shapes (`sorted`, ranges `a < x < b`, non-empty, membership) are
  still left to chance; read them off the guard and generate inside them.
- **`assert` in the runnable twin**: dropped, so `pastalean run` ignores a failing assert that CPython
  raises on. A pure runtime check is erased as dead code (`let _ := check x`), so it must travel as a
  value (`PyExcept`); refute does this only for the helpers its preconditions call (`_asserts_raise`).

## Libraries

- **`zoneinfo`**: `ZoneInfo("America/New_York")` via `Std.Time`'s tz database. Needs `datetime`'s
  time zone to become "offset at an instant" (a `tzinfo` with rules), `utcoffset(dt)`/`tzname(dt)`
  taking the datetime, `fold` for ambiguous local times, and an opaque rules value in the provable twin.
- **`datetime`**: `strptime`; float arguments to `timedelta` (`timedelta(hours=1.5)`); `isocalendar()`,
  `fromisocalendar`, `fromtimestamp`, `utcfromtimestamp`; `%U %W %G %V %c %x %X %z %Z` in `strftime`.
- **`json`**: `load`/`dump` (file objects), `object_hook`/`object_pairs_hook`/`default`/`cls`,
  `NaN`/`Infinity` (floats are exact rationals; reals with infinities are not modelled), a user `dict`
  passed to `dumps` comes out in `Std.HashMap` order rather than insertion order.
- **`re`**: possessive quantifiers and atomic groups, Unicode classes beyond ASCII, callable `repl` in
  `sub`, `finditer`, `subn`, `Pattern.groups`/`groupindex`, `Match.groupdict`, `re.error` details.
- Class-library declarations (`Libraries/datetime/Mapping.lean`) are JSON written by hand-maintained
  tooling; a checker that they agree with the Lean signatures would catch drift.

## Translator

- **Mutating a container's elements through a loop variable** (`for ls in lists: ls.append(42)`) does
  not write back under value semantics (refute reports it as `FIDELITY_BUG`).
- **A list literal for an `Optional[list]` parameter** (`count([])` with `xs: Optional[List[int]]`):
  the `[]` coercion to `Option` gets stuck on the element type.
- **`getattr(obj, computed_name)`** is not translated (dispatch over the class's method names).

- **Callee parameter types do not flow back to callers** in TypeInfer: `def g(d): return f(d)` leaves
  `d` untyped even when `f`'s `d` is inferred `dict[str, int]` (refute works around it for its checkers
  with `refine_params`). Interproc only flows argument types into callee parameters.

- **Lambdas whose body raises** (`lambda: timedelta(days=10**9)`): the lambda is not lowered as an
  action, so calling it neither awaits nor propagates the exception.
- **User exception classes** (`class MyError(ValueError)`): the hierarchy table in `Core.lean`
  (`pyExcParent`) covers builtins and modelled libraries only.
- **Insertion-ordered dicts**: typed `dict[K, V]` is `Std.HashMap`, so iteration order differs from
  CPython; boxed (`PyAny`) dicts already keep insertion order.
- `x is not None` narrowing on attributes (`if self._tz is not None: self._tz.f()`) — only names are
  narrowed; the code has to bind a local first.
