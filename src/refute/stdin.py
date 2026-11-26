"""Counterexamples for stdin programs: inputs on which worlds or programs print different things.

`refute_stdin(source)` generates well-formed inputs (`stdin_harness.generate`, or mutations of given
examples), then compares, per input, what CPython, the runnable twin (`main'rn`) and the provable twin
(`main`, over an `IOStream`) print. With `against=` a second program (e.g. a brute-force reference), it
looks for inputs on which the two programs print differently under CPython, shrinks one, and confirms
the difference in both Lean worlds of both programs (`PROGRAM_DIFF`).

Outputs are compared the way judges do: trailing whitespace per line and trailing blank lines ignored.
"""

from __future__ import annotations

import ast
import json
import random
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

__all__ = ["refute_stdin", "StdinReport", "StdinFinding"]

HARNESS = Path(__file__).with_name("stdin_harness.py")
NS = "PastaLean.User.Root."


def norm(s: str | None) -> str | None:
    if s is None:
        return None
    return "\n".join(l.rstrip() for l in s.rstrip().split("\n"))


@dataclass
class Outcome:
    """What one world did with one input."""
    stdout: str | None
    error: str | None = None
    hang: bool = False
    unavailable: bool = False
    violation: str | None = None    # how the input breaks the inferred format (CPython replays only)

    @property
    def clean(self) -> bool:
        return self.error is None and self.violation is None

    @property
    def key(self):
        if self.unavailable:
            return ("unavailable",)
        if self.hang:
            return ("hang",)
        if self.error:
            return ("error", _exc_kind(self.error))
        return ("out", norm(self.stdout))

    def show(self) -> str:
        if self.unavailable:
            return "not evaluable (see notes)"
        if self.hang:
            return "did not finish"
        if self.error:
            return f"raised {_exc_kind(self.error)}" + (f" after printing {self.stdout!r}" if self.stdout else "")
        return repr(self.stdout)


def _exc_kind(err: str) -> str:
    m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_]*)", err or "")
    return m.group(1) if m else err


@dataclass
class StdinFinding:
    verdict: str
    input: str
    worlds: dict[str, Outcome]
    note: str = ""


@dataclass
class StdinReport:
    findings: list[StdinFinding] = field(default_factory=list)
    tested: int = 0
    rejected: int = 0
    error: str | None = None
    shapes: dict = field(default_factory=dict)
    notes: list[str] = field(default_factory=list)

    @property
    def found(self) -> bool:
        return bool(self.findings)


def _harness(req: dict, timeout: float) -> dict:
    try:
        p = subprocess.run([sys.executable, str(HARNESS)], input=json.dumps(req), capture_output=True,
                           text=True, timeout=timeout, cwd=str(HARNESS.parent))
    except subprocess.TimeoutExpired:
        return {"error": "CPython stdin harness timed out"}
    if p.returncode != 0:
        return {"error": (p.stderr or p.stdout).strip()[-1500:]}
    return json.loads(p.stdout)


def _replay(source: str, inputs: list[str], ms: int, check: str | None = None) -> list[Outcome]:
    if not inputs:
        return []
    res = _harness({"mode": "replay", "source": source, "inputs": inputs, "ms": ms, "check": check},
                   60 + len(inputs) * ms / 1000)
    if "error" in res:
        raise RuntimeError(res["error"])
    return [Outcome(r["stdout"], r["exc"], r["exc"] == "Timeout", violation=r.get("violation"))
            for r in res["runs"]]


class _Twins:
    """Both Lean worlds of one program, run through the warm backend."""

    def __init__(self, session, source: str, heap: bool = False):
        self.session = session
        res = session.translate(source, prove_asserts=False, heap=heap)
        if not res.ok:
            raise RuntimeError(f"translation failed: {res.error}")
        self.code = res.lean_code
        if "def main'rn" not in self.code:
            raise RuntimeError("the program has no `main` / `__main__` entry point")
        self.unavailable: dict[str, str] = {}   # world -> why it cannot be run

    def run(self, inputs: list[str], ms: int) -> tuple[list[Outcome], list[Outcome]]:
        progs = [{"id": "prov", "fn": NS + "main", "inputs": inputs},
                 {"id": "run", "fn": NS + "main'rn", "inputs": inputs}]
        res = self.session.client._long_task({"task": "refute", "code": self.code, "targets": [], "witnesses": [],
                                              "config": {"perCaseMs": ms}, "programs": progs},
                                             120 + len(inputs) * ms / 500) or {}
        by_id = {p.get("id"): p for p in res.get("programs", [])}
        out = []
        if not res.get("result"):
            raise RuntimeError(f"Lean run failed: {res.get('error')}")
        for w in ("prov", "run"):
            p = by_id.get(w, {})
            if p.get("error"):
                # e.g. this twin does not elaborate; the other world is still compared.
                self.unavailable[w] = p["error"]
                out.append([Outcome(None, unavailable=True) for _ in inputs])
                continue
            runs = p.get("runs", [])
            # Inputs after an overrun are skipped, not hung: they were never evaluated.
            out.append([Outcome(r.get("stdout"), r.get("error"), bool(r.get("hang")),
                                unavailable=bool(r.get("skipped"))) for r in runs])
        if any(o.hang for os_ in out for o in os_):
            # A run that overran leaves its thread spinning in the backend.
            self.session.client.close()
        return out[0], out[1]


def classify(py: Outcome, run: Outcome, prov: Outcome) -> str | None:
    """Verdict for one input of one program (CPython is the reference)."""
    twins = [o for o in (run, prov) if not o.unavailable]
    differ = [o for o in twins if o.key != py.key]
    if not differ:
        return None
    if any(o.hang for o in differ):
        return "NONTERMINATION"
    if len(differ) == len(twins):
        return "FIDELITY_BUG"
    return "RUN_TWIN_BUG" if run in differ else "PROVABLE_TWIN_DIVERGENCE"


# ---------------------------------------------------------------------------------------------------
# Inputs

_INT = re.compile(r"-?\d+")


def mutate(examples: list[str], n: int, seed: int) -> list[str]:
    """Token-level mutations of example inputs. A lone integer on its line is usually a count, so it
    changes rarely; data tokens change often (CPython and the format check reject the ill-formed)."""
    rng = random.Random(seed)
    out = list(examples)
    for _ in range(20 * n):
        if len(out) >= n or not examples:
            break
        # Mutants are mutated again, so several coordinated changes (e.g. every sign) become reachable.
        lines = rng.choice(out).split("\n")
        new = []
        for line in lines:
            toks = line.split(" ")
            rate = 0.08 if len(toks) == 1 else 0.35
            for i, t in enumerate(toks):
                if _INT.fullmatch(t) and rng.random() < rate:
                    v = int(t)
                    toks[i] = str(rng.choice([-v, -v, 0, 1, v + 1, v - 1, 2 * v, rng.randint(-2 * abs(v) - 2, 2 * abs(v) + 2)]))
            new.append(" ".join(toks))
        text = "\n".join(new)
        if text not in out:
            out.append(text)
    return out[:n]


def shrink_candidates(text: str) -> list[str]:
    """Smaller variants of an input: truncate, drop a line, drop a line's last token (with its count),
    drop a record (with its count), lower an integer."""
    lines = text.rstrip("\n").split("\n")
    cands = [lines[:k] for k in range(1, len(lines))]
    for i in range(len(lines)):
        cands.append(lines[:i] + lines[i + 1:])
        toks = lines[i].split()
        if toks:
            dropped = lines[:i] + [" ".join(toks[:-1])] + lines[i + 1:]
            cands.append(dropped)
            # Keep a list and the count before it in step: drop a token and lower the count.
            for j in range(i - 1, -1, -1):
                if _INT.fullmatch(lines[j].strip() or "x") and int(lines[j]) == len(toks):
                    cands.append(dropped[:j] + [str(len(toks) - 1)] + dropped[j + 1:])
                    break
        for j, t in enumerate(toks):
            if _INT.fullmatch(t) and t not in ("0", "1"):
                v = int(t)
                for w in dict.fromkeys([0, 1, v // 2, v - 1 if v > 0 else v + 1]):
                    cands.append(lines[:i] + [" ".join(toks[:j] + [str(w)] + toks[j + 1:])] + lines[i + 1:])
    # Drop a whole record (e.g. one test case) together with one from the count that announced it.
    for j, line in enumerate(lines):
        if _INT.fullmatch(line.strip() or "x") and int(line) > 0:
            for i in range(j + 1, len(lines)):
                for n in (1, 2, 3):
                    if i + n <= len(lines):
                        cands.append(lines[:j] + [str(int(line) - 1)] + lines[j + 1:i] + lines[i + n:])
    out = ["".join(l + "\n" for l in c) for c in cands]
    return sorted(dict.fromkeys(o for o in out if o != text), key=len)


def _size(text: str) -> tuple:
    return (len(text.split()), sum(abs(int(t)) for t in _INT.findall(text)), len(text))


def _shrink(text: str, still_fails, rounds: int) -> str:
    """Greedy: the smallest candidate that still fails, repeated. `still_fails` takes a batch of candidates
    and returns those that still fail (so one round costs one batch)."""
    for _ in range(rounds):
        cands = sorted((c for c in shrink_candidates(text) if _size(c) < _size(text)), key=_size)[:80]
        good = still_fails(cands)
        if not good:
            break
        text = min(good, key=_size)
    return text


# ---------------------------------------------------------------------------------------------------

def _has_guard(tree) -> bool:
    return any(isinstance(n, ast.If) and isinstance(n.test, ast.Compare) and isinstance(n.test.left, ast.Name)
               and n.test.left.id == "__name__" for n in ast.walk(tree))


def with_main_entry(source: str) -> str:
    """The module with an entry point PastaLean turns into `main`: a `def main()` nothing calls gets an
    `if __name__ == "__main__": main()`, and bare top-level code is moved under that guard (imports stay
    at module scope). A module that already has a guard is unchanged."""
    tree = ast.parse(source)
    if _has_guard(tree):
        return source
    if any(isinstance(n, ast.FunctionDef) and n.name == "main" for n in tree.body):
        return source.rstrip() + '\n\n\nif __name__ == "__main__":\n    main()\n'
    import_lines = {ln for node in tree.body if isinstance(node, (ast.Import, ast.ImportFrom))
                    for ln in range(node.lineno, (node.end_lineno or node.lineno) + 1)}
    imports, body = [], []
    for i, line in enumerate(source.splitlines(), start=1):
        (imports if i in import_lines else body).append(line)
    indented = "\n".join(("    " + ln) if ln.strip() else ln for ln in body)
    return "\n".join(imports + ['if __name__ == "__main__":', indented]) + "\n"


def refute_stdin(source: str, *, session=None, against: str | None = None, examples: list[str] | None = None,
                 tests: int = 150, seed: int = 24301, per_case_ms: int = 2000, negative: bool = False,
                 shrink_rounds: int = 6, heap: bool = False) -> StdinReport:
    from ..api import Session

    report = StdinReport()
    source = with_main_entry(source)
    against = with_main_entry(against) if against else None
    check = "strict"
    if examples:
        try:
            if not all(o.clean for o in _replay(source, examples, per_case_ms, "strict")):
                # The examples break the "a list is as long as the last count" guess: check kinds only.
                check = "loose"
        except RuntimeError as e:
            report.error = str(e)
            return report
        inputs = mutate(examples, 3 * tests, seed)
    else:
        gen = _harness({"mode": "generate", "source": source, "n": tests, "seed": seed, "negative": negative,
                        "ms": min(per_case_ms, 500)}, 120 + tests)
        if "error" in gen:
            report.error = gen["error"]
            return report
        inputs = [g["input"] for g in gen["inputs"]]
        report.rejected, report.shapes = gen.get("rejected", 0), gen.get("shapes", {})
    try:
        py = _replay(source, inputs, per_case_ms, check)
        ref_py = _replay(against, inputs, per_case_ms) if against else None
    except RuntimeError as e:
        report.error = str(e)
        return report
    # Only inputs every CPython program accepts are well-formed.
    keep = [i for i, o in enumerate(py) if o.clean and (ref_py is None or ref_py[i].error is None)]
    report.rejected += len(inputs) - len(keep)
    keep = keep[:tests]
    inputs = [inputs[i] for i in keep]
    py = [py[i] for i in keep]
    ref_py = [ref_py[i] for i in keep] if ref_py else None
    report.tested = len(inputs)
    if not inputs:
        report.error = "no well-formed input: every generated input made CPython raise (try --stdin-examples)"
        return report

    own = session is None
    sess = session or Session(target="command", mode="both")
    try:
        try:
            twins = _Twins(sess, source, heap)
            ref_twins = _Twins(sess, against, heap) if against else None
        except RuntimeError as e:
            report.error = str(e)
            return report

        try:
            _compare(report, source, against, inputs, py, ref_py, twins, ref_twins, per_case_ms,
                     shrink_rounds, check)
        except RuntimeError as e:
            report.error = str(e)
        if len(twins.unavailable) == 2:
            report.error = "neither Lean twin of the program can be evaluated (see notes)"
        names = {"prov": "provable", "run": "runnable"}
        for label, t in (("", twins), ("reference ", ref_twins)):
            for w, why in (t.unavailable.items() if t else []):
                report.notes.append(f"{label}{names[w]} twin not evaluable: {why[:300]}")
    finally:
        if own:
            sess.close()
    return report


def _compare(report, source, against, inputs, py, ref_py, twins, ref_twins, ms, rounds, check):
    """Program differences (with a reference) on all inputs, then this program's fidelity."""
    if against:
        _program_diff(report, source, against, inputs, py, ref_py, twins, ref_twins, ms, rounds, check)
        inputs, py = inputs[:60], py[:60]
    _fidelity(report, source, inputs, py, twins, ms, rounds, check)


def _fidelity(report, source, inputs, py, twins, ms, rounds, check):
    """Inputs on which this program's twins print something other than CPython."""
    prov, run = twins.run(inputs, ms)
    first: dict[str, int] = {}
    for i, (p, r, c) in enumerate(zip(py, run, prov)):
        v = classify(p, r, c)
        if v and v not in first:
            first[v] = i
    for v, i in first.items():
        def still(cands, v=v):
            ok = [(c, o) for c, o in zip(cands, _replay(source, cands, ms, check)) if o.clean]
            if not ok:
                return []
            cp, cr = twins.run([c for c, _ in ok], ms)
            return [c for (c, o), r, p in zip(ok, cr, cp) if classify(o, r, p) == v]
        text = inputs[i] if v == "NONTERMINATION" else _shrink(inputs[i], still, rounds)
        (o,) = _replay(source, [text], ms)
        cp, cr = twins.run([text], ms)
        note = "the two twins also differ from each other" if v == "FIDELITY_BUG" and cr[0].key != cp[0].key \
            and not (cr[0].unavailable or cp[0].unavailable) else ""
        report.findings.append(StdinFinding(v, text, {"cpython": o, "runnable": cr[0], "provable": cp[0]}, note))


def _program_diff(report, source, against, inputs, py, ref_py, twins, ref_twins, ms, rounds, check):
    """Inputs on which the two programs print differently under CPython, confirmed in both Lean worlds."""
    diff = [i for i in range(len(inputs)) if py[i].key != ref_py[i].key]
    if not diff:
        return

    def still(cands):
        a, b = _replay(source, cands, ms, check), _replay(against, cands, ms)
        return [c for c, x, y in zip(cands, a, b) if x.clean and y.error is None and x.key != y.key]

    text = _shrink(min((inputs[i] for i in diff), key=_size), still, rounds * 3)
    (a,), (b,) = _replay(source, [text], ms), _replay(against, [text], ms)
    ap, ar = twins.run([text], ms)
    bp, br = ref_twins.run([text], ms)
    worlds = {"cpython": a, "reference cpython": b, "runnable": ar[0], "reference runnable": br[0],
              "provable": ap[0], "reference provable": bp[0]}
    confirmed = [w for w, x, y in (("runnable", ar[0], br[0]), ("provable", ap[0], bp[0])) if x.key != y.key]
    note = "confirmed in " + (" and ".join(confirmed) if confirmed else "neither Lean world") + " twins"
    report.findings.insert(0, StdinFinding("PROGRAM_DIFF", text, worlds, note))
