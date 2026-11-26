# Counterexample search vs CrossHair and Hypothesis

[crosshair-benchmark](https://github.com/pschanely/crosshair-benchmark) is CrossHair's own performance
suite: 32 Python functions, each with one false contract (docstring `pre:`/`post:`/`raises:` or
icontract), chosen to take CrossHair "5 seconds to 5 minutes". `run.py` gives each tool the same
wall-clock budget per problem, as a separate process:

| tool | how it runs |
|---|---|
| CrossHair | `crosshair check`, exactly as the suite's own runner invokes it (0.0.112) |
| CrossHair + TypeInfer | the same, on a copy annotated with TypeInfer's inferred parameter types (`crosshair_typed.py`) |
| Hypothesis | `hyp_driver.py`: `st.from_type` strategies, `assume(pre)`, allowed `raises:` (6.170) |
| refute | `pastalean refute`: translation, then the search in Lean only (Plausible over `PyArb` generators seeded with a literal pool, then enumeration/random draws and `grind` on guards ∧ ¬body); CPython only executes the witnesses Lean finds |

Every reported counterexample is re-executed against the contract by `validate.py`, independently of
the tool that found it; only confirmed ones count (with two documented exceptions for the other tools,
marked `*`: a witness the validator cannot re-parse, and a CrossHair witness for a function that
mutates its argument, since CrossHair prints arguments after the call).

## Result (60 s per problem and tool)

| | solved |
|---|---|
| CrossHair | 29–30 / 32 |
| CrossHair + TypeInfer annotations | 30 / 32 |
| Hypothesis | 11–14 / 32 |
| refute (Lean only) | 30 / 32 |

`json`, `re` and `datetime` are Lean libraries (`Libraries/{json,re,datetime}`), so the problems that
use them are translated and searched. What reaches the bugs, all in Lean:

- falsey regex (14): every `re.compile` pattern in the program is expanded into strings it matches
  (`0`, `-0`, `0e0`, `{ }`, …) and those are edited with the pattern's own characters, so `0.0`,
  `0E-0` and `0e00` are a few edits away;
- dates (10): constructor literals (`date(2022, 10, 6)`) are mined, so a `timedelta` is drawn as the
  gap between two of them and a `date`/`datetime` as one shifted by a program integer (`- 8314` days);
- untyped dicts (2): TypeInfer reads `dict[str, int]` off `d["age"] += 1`, and dicts are drawn keyed by
  the program's strings;
- `compare_version_strings`: lengths drawn from the program's integers (`len(v) == 3`), numeral
  strings, a binder sometimes replaying the previous one's draw (equal strings), and the contract's
  `raises: ValueError` honoured for `int("1 c")`;
- `str_replace`, `find_in_long_string`, `find_5_times`: the literal pool and the set generator.

Unsolved: the dataframe problem (pandas) and the assertion gauntlet (icontract decorators over classes
with optional nested lists and a non-BMP Unicode regex).

**Held-out check** (`heldout.py`): CrossHair's own bundled examples, which refute was never tuned on —
`bugs_detected/` (each refuted function counts) and `correct_code/` (any refutation is a false alarm).
CrossHair finds 13 bugs there with 2 false alarms; refute finds 9 with none. The misses: `getattr` with
a computed name, a contract on a method (`__eq__`), and two aliasing bugs (the same list passed twice,
which value semantics cannot express).

**Mutation benchmark** (`mutants.py`, ETNA-style): the contracted HumanEval/LeetCode solutions with one
small mutation in the body (contracts untouched); a mutant counts only if CPython shows it failing one
of the problem's tests. It reports false alarms on the unmutated (proved) solutions and the kill rate on
test-confirmed buggy mutants, with time to kill.

An earlier version of refute also searched on the CPython side (32/32 here); that search was removed by
design — all searching now happens in Lean over the translated program.

```bash
uv sync --all-extras                       # crosshair-tool, hypothesis, icontract
uv run python PastaBench/pbt_bench/run.py  # --timeout 60 --jobs 12 --tools crosshair,hypothesis,pastalean
```
