"""A mutation benchmark for `pastalean refute` (ETNA-style): the contracted HumanEval/LeetCode solutions
(`PastaBench/{humaneval,leetcode}/*/solution_contracts.py`), each mutated by one small change to its
body (the contracts are left alone). A mutant counts only if CPython shows it is wrong: it fails at
least one of the problem's `tests.json`. Reported:

* refutations of the unmutated solutions — each a contract weaker than the problem (a missing
  `Requires`, e.g. LeetCode's "adjacent elements differ") or a false alarm; inspect them;
* kill rate — over the mutants whose contract a test input violates under CPython (a mutant can fail
  the tests yet satisfy a weak contract, and then there is nothing to find), and how fast.

    uv run python PastaBench/pbt_bench/mutants.py [--limit 40] [--per 2] [--timeout 30] [--jobs 4]

Set `PASTALEAN_REFUTE_CONFIG` (e.g. '{"plausible": false, "solver": false}') to measure one engine.
"""

from __future__ import annotations

import argparse
import ast
import copy
import json
import os
import random
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from pastalean.refute import obligations as O  # noqa: E402

CORPORA = [ROOT / "PastaBench" / "humaneval", ROOT / "PastaBench" / "leetcode"]
SWAPS = {ast.Lt: ast.LtE, ast.LtE: ast.Lt, ast.Gt: ast.GtE, ast.GtE: ast.Gt, ast.Eq: ast.NotEq,
         ast.NotEq: ast.Eq, ast.Add: ast.Sub, ast.Sub: ast.Add, ast.Mult: ast.FloorDiv,
         ast.And: ast.Or, ast.Or: ast.And}


def _is_marker(stmt: ast.stmt) -> bool:
    return O._marker(stmt) is not None


def _code_nodes(node: ast.AST):
    """`node` and its descendants, skipping contract statements (`Invariant(...)` in a loop too)."""
    if isinstance(node, ast.stmt) and _is_marker(node):
        return
    yield node
    for child in ast.iter_child_nodes(node):
        yield from _code_nodes(child)


def _sites(fn: ast.FunctionDef) -> list[ast.AST]:
    """Mutable nodes in `fn`'s body outside contract statements."""
    out = []
    for stmt in fn.body:
        for n in _code_nodes(stmt):
            if isinstance(n, ast.Compare) or isinstance(n, (ast.BinOp, ast.BoolOp)) and type(n.op) in SWAPS:
                out.append(n)
            elif isinstance(n, ast.Constant) and type(n.value) is int:
                out.append(n)
    return out


def _mutate(node: ast.AST, rng: random.Random) -> str:
    if isinstance(node, ast.Compare):
        i = rng.randrange(len(node.ops))
        op = type(node.ops[i])
        if op not in SWAPS:
            return ""
        node.ops[i] = SWAPS[op]()
        return f"{op.__name__}->{type(node.ops[i]).__name__}"
    if isinstance(node, (ast.BinOp, ast.BoolOp)):
        op = type(node.op)
        node.op = SWAPS[op]()
        return f"{op.__name__}->{type(node.op).__name__}"
    d = rng.choice([1, -1])
    node.value += d
    return f"const{d:+d}"


def mutants(source: str, method: str, per: int, rng: random.Random) -> list[tuple[str, str]]:
    tree = ast.parse(source)
    fn = next((n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == method), None)
    if fn is None:
        return []
    n_sites = len(_sites(fn))
    out = []
    for i in rng.sample(range(n_sites), min(per * 3, n_sites)):
        t = copy.deepcopy(tree)
        f = next(n for n in t.body if isinstance(n, ast.FunctionDef) and n.name == method)
        desc = _mutate(_sites(f)[i], rng)
        if desc:
            out.append((ast.unparse(t), desc))
        if len(out) >= per:
            break
    return out


def fails_tests(source: str, method: str, tests: list[dict]) -> bool:
    """CPython ground truth: the program (contract markers stripped) fails some test."""
    prog = O.cpython_module(source, []) + "\n" + "import json as _j, sys as _s\n" + f"""
_bad = False
for _t in _j.loads(_s.stdin.read()):
    _env = {{}}
    try:
        exec(_t["input"], globals(), _env)
        _got = {method}(**_env)
        _bad = _bad or _got != eval(_t["output"])
    except Exception:
        _bad = True
print("BAD" if _bad else "OK")
"""
    try:
        p = subprocess.run([sys.executable, "-c", prog], input=json.dumps(tests), capture_output=True, text=True,
                           timeout=20)
    except subprocess.TimeoutExpired:
        return True
    return "BAD" in p.stdout


def contract_violated_on_tests(source: str, tests: list[dict]) -> bool:
    """Whether some test input violates the mutant's contract under CPython (the checkers refute uses): the
    mutants refute can be judged on, since a contract may be too weak to notice a test-failing mutant."""
    obs = O.collect(source)
    if not obs:
        return False
    calls = "\n".join(
        f"""    try:
        _args = [_env[_n] for _n in {[n for n, _ in ob.params]!r}]
        if {ob.pre_fn}(*_args) and not {ob.chk_fn}(*_args):
            _bad = True
    except Exception:
        _bad = True""" for ob in obs)
    prog = O.cpython_module(source, obs) + "\nimport json as _j, sys as _s\n" + f"""
_bad = False
for _t in _j.loads(_s.stdin.read()):
    _env = {{}}
    exec(_t["input"], globals(), _env)
{calls}
print("BAD" if _bad else "OK")
"""
    try:
        p = subprocess.run([sys.executable, "-c", prog], input=json.dumps(tests), capture_output=True, text=True,
                           timeout=30)
    except subprocess.TimeoutExpired:
        return False
    return "BAD" in p.stdout


def refute(source: str, timeout: int) -> tuple[bool, float]:
    """Whether refute finds a CPython-confirmed violation, and the seconds it took."""
    with tempfile.NamedTemporaryFile("w", suffix=".py", delete=False) as f:
        f.write(source)
    t0 = time.monotonic()
    p = subprocess.run([sys.executable, "-m", "pastalean", "refute", f.name, "--json", "--tests", str(10 ** 9),
                        "--time", str(timeout * 1000)], capture_output=True, text=True, timeout=timeout * 10)
    dt = time.monotonic() - t0
    Path(f.name).unlink(missing_ok=True)
    try:
        report = json.loads(p.stdout)
    except json.JSONDecodeError:
        return False, dt
    hit = any(o.get("witness") and o["witness"].get("py") == "violates" for o in report.get("obligations", []))
    return hit, dt


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=40, help="problems sampled")
    ap.add_argument("--per", type=int, default=2, help="mutants per problem")
    ap.add_argument("--timeout", type=int, default=30, help="refute budget per program, seconds")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--dump", type=Path, default=None, help="write the mutants here and stop (for study)")
    args = ap.parse_args()
    # refute runs warm: the daemon keeps one warm backend per parallel job (`refute/daemon.py`)
    os.environ["PASTALEAN_DAEMON_POOL"] = str(args.jobs)
    rng = random.Random(args.seed)
    problems = sorted(p for c in CORPORA for p in c.iterdir() if (p / "solution_contracts.py").exists())
    problems = rng.sample(problems, min(args.limit, len(problems)))
    originals, cases = [], []
    buggy = 0
    for p in problems:
        meta = json.loads((p / "meta.json").read_text())
        src = (p / "solution_contracts.py").read_text()
        tests = json.loads((p / "tests.json").read_text())
        originals.append((p.name, src))
        for m, desc in mutants(src, meta["method"], args.per, rng):
            if fails_tests(m, meta["method"], tests):
                buggy += 1
                if contract_violated_on_tests(m, tests):
                    cases.append((p.name, desc, m))
    if args.dump:
        args.dump.mkdir(parents=True, exist_ok=True)
        for i, (name, desc, m) in enumerate(cases):
            (args.dump / f"{name}__{i}__{desc.replace('->', '_to_').replace('+', 'p').replace('-', 'm')}.py").write_text(m)
        print(f"{len(cases)} mutants written to {args.dump}")
        return 0
    with ThreadPoolExecutor(args.jobs) as ex:
        orig = list(ex.map(lambda o: (o[0], *refute(o[1], args.timeout)), originals))
        muts = list(ex.map(lambda c: (c[0], c[1], *refute(c[2], args.timeout)), cases))
    alarms = [n for n, hit, _ in orig if hit]
    killed = [(n, d, t) for n, d, hit, t in muts if hit]
    for n, d, hit, t in muts:
        print(f"{'KILL' if hit else 'miss'} {n:40} {d:16} {t:6.1f}s")
    times = sorted(t for _, _, t in killed)
    print(f"originals refuted (contract gap or false alarm): {len(alarms)}/{len(orig)} {alarms}")
    print(f"{buggy} mutants fail the tests; {len(muts)} of them violate their contract on a test input")
    print(f"killed: {len(killed)}/{len(muts)} contract-detectable mutants"
          + (f", median {times[len(times) // 2]:.1f}s" if times else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
