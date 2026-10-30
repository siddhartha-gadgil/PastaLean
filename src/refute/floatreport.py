"""How faithfully PastaLean's two twins model a program's float functions, measured against IEEE.

For every top-level function annotated `-> float`, sample dyadic inputs and compare four results with
the IEEE enclosure of the exact result (`fi.py`, proved sound in `PyAPI/FloatInterval.lean`):

* **CPython**: IEEE exactly, so it must always lie inside; any miss is a flaw in the enclosure itself;
* **runnable twin** (`f'rn`, Lean `Float`): expected bit-identical to CPython;
* **provable twin** (`f`, exact `ℚ`): the exact value, inside unless its model departs from real
  arithmetic (e.g. `x/0 = 0`);
* how wide the enclosure is, in ulps: how far the exact (provable) value can drift from the float one.
"""

from __future__ import annotations

import ast
import json
import math
import statistics
import struct
from dataclasses import dataclass, field
from fractions import Fraction

from . import obligations as O
from . import HARNESS, NS
from .fi import FI

__all__ = ["float_report", "FunctionReport"]


@dataclass
class FunctionReport:
    name: str
    samples: int = 0
    enclosed: int = 0                 # samples with a finite-or-infinite enclosure
    rounding: int = 0                 # a branch inside the computation depends on rounding
    unsupported: int = 0              # leaves the modelled operations (sqrt, //, int(), ...)
    py_in: int = 0
    py_raised: dict = field(default_factory=dict)   # exception kind -> count
    run_silent: int = 0               # CPython raised, the runnable twin returned a value
    prov_silent: int = 0              # CPython raised, the provable twin's total model gave a value
    run_same: int = 0                 # runnable twin bit-identical to CPython
    run_compared: int = 0
    run_in: int = 0
    run_enclosed: int = 0
    prov_in: int = 0
    prov_compared: int = 0
    prov_exact: int = 0               # the exact value already is CPython's double: no rounding at all
    widths: list[float] = field(default_factory=list)
    outside: list[dict] = field(default_factory=list)
    error: str | None = None

    def pct(self, k: int, n: int) -> str:
        return f"{100 * k / n:5.1f}%" if n else "    –"

    @property
    def median_width(self) -> float | None:
        return statistics.median(self.widths) if self.widths else None


def _float_functions(source: str) -> list[tuple[str, list[tuple[str, str | None]]]]:
    tree = ast.parse(source)
    out = []
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and not node.name.startswith(O.CHECKER_PREFIX) \
                and node.returns is not None and ast.unparse(node.returns) == "float" \
                and not node.args.vararg and not node.args.kwarg:
            out.append((node.name, O._params(node)))
    return out


def _lit_value(lit):
    """A numeric `PyLit` as an exact `Fraction`, or a non-finite `float`."""
    (tag, v), = lit.items()
    if tag == "float":
        return Fraction(v[0], 2 ** v[1])
    if tag == "rat":
        return Fraction(v[0], v[1])
    if tag == "int":
        return Fraction(v)
    if tag == "double":
        return struct.unpack("<d", struct.pack("<Q", v))[0]
    raise ValueError(f"not a number: {lit}")


def _frac(s):
    if s is None:
        return None
    n, d = s.split("/")
    return Fraction(int(n), int(d))


def _same(a, b) -> bool:
    if isinstance(a, float) or isinstance(b, float):
        return isinstance(a, float) and isinstance(b, float) and (a == b or (math.isnan(a) and math.isnan(b)))
    return a == b


def _inside(enc: FI, v) -> bool:
    if isinstance(v, float):
        # ±∞ is a possible IEEE result exactly when the enclosure is unbounded on that side.
        return (v > 0 and enc.hi is None) or (v < 0 and enc.lo is None)
    return (enc.lo is None or enc.lo <= v) and (enc.hi is None or v <= enc.hi)


def float_report(source: str, *, session=None, samples: int = 200, seed: int = 24301) -> list[FunctionReport]:
    import subprocess
    import sys

    from ..api import Session

    # The exact twin's values can outgrow the default int <-> str limit (e.g. repeated squaring).
    sys.set_int_max_str_digits(0)
    fns = _float_functions(source)
    if not fns:
        return []
    module = O.cpython_module(source, [])
    req = {"module": module, "values": [{"fn": f, "params": ps, "n": samples, "seed": seed} for f, ps in fns]}
    p = subprocess.run([sys.executable, str(HARNESS)], input=json.dumps(req), capture_output=True, text=True,
                       timeout=60 + samples * len(fns), cwd=str(HARNESS.parent))
    if p.returncode != 0:
        return [FunctionReport(f, error="CPython: " + (p.stderr or p.stdout).strip().splitlines()[-1]) for f, _ in fns]
    # Lean evaluation has no deadline: only inputs CPython finished on in time go to the twins.
    sampled = {v["fn"]: [r for r in v["rows"] if r.get("pyExc") not in ("Timeout", "MemoryError", "RecursionError")]
               for v in json.loads(p.stdout)["values"]}

    own = session is None
    sess = session or Session(target="command", mode="both")
    try:
        res = sess.translate(source, prove_asserts=False)
        if not res.ok:
            return [FunctionReport(f, error=f"translation failed: {res.error}") for f, _ in fns]
        evals = []
        for f, _ in fns:
            inputs = [r["lits"] for r in sampled[f]]
            evals += [{"id": f"{f}:prov", "fn": NS + f, "inputs": inputs},
                      {"id": f"{f}:run", "fn": NS + f + "'rn", "inputs": inputs}]
        lean = sess.client.refute(res.lean_code, [], evals=evals) or {}
    finally:
        if own:
            sess.close()
    by_id = {e.get("id"): e for e in lean.get("evals", [])}

    reports = []
    for f, _ in fns:
        rep = FunctionReport(f)
        prov = by_id.get(f"{f}:prov", {})
        run = by_id.get(f"{f}:run", {})
        if not lean.get("result"):
            rep.error = f"Lean evaluation failed: {lean.get('error')}"
        elif prov.get("error") or run.get("error"):
            rep.error = prov.get("error") or run.get("error")
        pvals, rvals = prov.get("values", []), run.get("values", [])
        for i, row in enumerate(sampled[f]):
            rep.samples += 1
            py = _lit_value(row["py"]) if row.get("py") else None
            pv = _lit_value(pvals[i]["value"]) if i < len(pvals) and "value" in pvals[i] else None
            rv = _lit_value(rvals[i]["value"]) if i < len(rvals) and "value" in rvals[i] else None
            if py is not None and rv is not None:
                rep.run_compared += 1
                rep.run_same += _same(py, rv)
            if py is not None and pv is not None and _same(py, pv):
                rep.prov_exact += 1
            if "pyExc" in row:
                # A raising computation has no float result to enclose.
                rep.py_raised[row["pyExc"]] = rep.py_raised.get(row["pyExc"], 0) + 1
                rep.run_silent += rv is not None
                # The provable twin is total: a runtime error there is still a (default) value.
                rep.prov_silent += pv is not None or (i < len(pvals) and "exc" in pvals[i])
                continue
            enc = row["enc"]
            if enc == "rounding":
                rep.rounding += 1
                continue
            if isinstance(enc, str):
                rep.unsupported += 1
                continue
            e = FI(_frac(enc[0]), _frac(enc[1]))
            rep.enclosed += 1
            if (w := e.width_ulps()) is not None:
                rep.widths.append(w)
            miss = {}
            if py is not None:
                if _inside(e, py):
                    rep.py_in += 1
                else:
                    miss["cpython"] = str(py)
            if rv is not None:
                rep.run_enclosed += 1
                rep.run_in += _inside(e, rv)
                if not _inside(e, rv):
                    miss["runnable"] = str(rv)
            if pv is not None:
                rep.prov_compared += 1
                if _inside(e, pv):
                    rep.prov_in += 1
                else:
                    miss["provable"] = str(pv)
            if miss and len(rep.outside) < 5:
                rep.outside.append({"input": row["lits"], "enclosure": repr(e), **miss})
        reports.append(rep)
    return reports
