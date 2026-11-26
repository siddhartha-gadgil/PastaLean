"""How faithfully PastaLean's two twins reproduce Python's float semantics, operation by operation.

Each operation is a one-line Python function. It is translated once (`both` mode) and evaluated on the
same inputs by CPython, the runnable twin (`f'rn`, Lean `Float`) and the provable twin (`f`, exact `ℚ`):

* runnable: does it produce the *same double* (bit for bit; any NaN equals any NaN) or raise the same
  exception as CPython?
* provable: is the exact value equal to CPython's double, and if not, how many ulps away is it? Inputs
  ℚ cannot represent (`nan`, `±inf`, `-0.0`) are skipped; where CPython raises, the total ℚ model
  returning a value is counted separately.

Inputs come in four classes: small dyadics (what `pastalean refute` draws), short decimals (`0.1`,
`2.675`, ...), arbitrary finite doubles (any exponent), and IEEE edge values.

    uv run python PastaBench/float_fidelity/bench.py [--samples N] [--json out.json]
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
import struct
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from pastalean import Session  # noqa: E402
from pastalean.refute.pylit import encode  # noqa: E402

NS = "PastaLean.User.Root."

# name, signature, expression, return annotation, input kinds per parameter ("f" float, "i" int, "s" small int)
OPS = [
    ("add", "a: float, b: float", "a + b", "float", "ff"),
    ("sub", "a: float, b: float", "a - b", "float", "ff"),
    ("mul", "a: float, b: float", "a * b", "float", "ff"),
    ("truediv", "a: float, b: float", "a / b", "float", "ff"),
    ("floordiv", "a: float, b: float", "a // b", "float", "ff"),
    ("mod", "a: float, b: float", "a % b", "float", "ff"),
    ("pow", "a: float, b: float", "a ** b", "float", "ff"),
    ("square", "a: float", "a * a", "float", "f"),
    ("cube", "a: float", "a ** 3", "float", "f"),
    ("recip", "a: float", "1 / a", "float", "f"),
    ("neg", "a: float", "-a", "float", "f"),
    ("abs", "a: float", "abs(a)", "float", "f"),
    ("lt", "a: float, b: float", "a < b", "bool", "ff"),
    ("eq", "a: float, b: float", "a == b", "bool", "ff"),
    ("max", "a: float, b: float", "max(a, b)", "float", "ff"),
    ("int", "a: float", "int(a)", "int", "f"),
    ("round", "a: float", "round(a)", "int", "f"),
    ("round2", "a: float", "round(a, 2)", "float", "f"),
    ("repr", "a: float", "str(a)", "str", "f"),
    ("sqrt", "a: float", "math.sqrt(a)", "float", "f"),
    ("floor", "a: float", "math.floor(a)", "int", "f"),
    ("ceil", "a: float", "math.ceil(a)", "int", "f"),
    ("exp", "a: float", "math.exp(a)", "float", "f"),
    ("log", "a: float", "math.log(a)", "float", "f"),
    ("sin", "a: float", "math.sin(a)", "float", "f"),
    ("atan2", "a: float, b: float", "math.atan2(a, b)", "float", "ff"),
    ("hypot", "a: float, b: float", "math.hypot(a, b)", "float", "ff"),
    ("mod_int", "a: float, k: int", "a % k", "float", "fs"),
    ("int_truediv", "i: int, j: int", "i / j", "float", "ii"),
    ("int_floordiv", "i: int, j: int", "i // j", "int", "ii"),
    ("int_mod", "i: int, j: int", "i % j", "int", "ii"),
    ("int_to_float", "i: int", "float(i)", "float", "i"),
    ("parse", "s: str", "float(s)", "float", "t"),
]

EDGE = [0.0, -0.0, math.inf, -math.inf, math.nan, 5e-324, 2.2250738585072014e-308, 1.7976931348623157e308,
        1e16, 2.0 ** 53, 0.5, 1.5, 2.5, -2.5, 0.1, 1 / 3, -1.0, 1.0, 3.0, -7.0]


def draw(kind, cls, rng):
    if kind == "t":
        r = rng.random()
        if r < 0.1:
            return rng.choice(["abc", "", "1.2.3", "1e", "--1", "1__0", "_1", "0x10", " nan ", "-Infinity", "1_000.5"])
        if r < 0.4:
            return "".join(rng.choice("0123456789") for _ in range(rng.randint(15, 30))) + "e" + str(rng.randint(-330, 300))
        return f"{rng.randint(-99999, 99999)}.{rng.randint(0, 99999):05d}e{rng.randint(-20, 20)}"
    if kind == "s":
        return rng.choice([-7, -3, -2, -1, 0, 1, 2, 3, 5, 10])
    if kind == "i":
        r = rng.random()
        if r < 0.1:
            return 0
        if r < 0.3:
            return rng.choice([-1, 1]) * rng.randint(2 ** 52, 2 ** 64)
        return rng.randint(-60, 60)
    if cls == "dyadic":
        return math.ldexp(rng.randint(-200, 200), -rng.randint(0, 4))
    if cls == "decimal":
        return float(f"{rng.randint(-999, 999)}e{rng.randint(-3, 2)}")
    if cls == "wide":
        while True:
            v = struct.unpack("<d", struct.pack("<Q", rng.getrandbits(64)))[0]
            if math.isfinite(v):
                return v
    return rng.choice(EDGE)


def module() -> str:
    lines = ["import math", ""]
    for name, sig, expr, ret, _ in OPS:
        lines += [f"def op_{name}({sig}) -> {ret}:", f"    return {expr}", "", ""]
    return "\n".join(lines)


def py_outcome(fn, args):
    try:
        return ("value", fn(*args))
    except Exception as e:  # noqa: BLE001
        return ("exc", type(e).__name__)


def lit_value(lit):
    (tag, v), = lit.items()
    if tag == "float":
        return Fraction(v[0], 2 ** v[1])
    if tag == "rat":
        return Fraction(v[0], v[1])
    if tag == "double":
        return struct.unpack("<d", struct.pack("<Q", v))[0]
    return v


def same_double(x: float, lit) -> bool:
    """`lit` (a Lean result) is the double `x`, bit for bit (any NaN matches any NaN)."""
    y = lit_value(lit)
    if isinstance(y, Fraction):
        return math.isfinite(x) and not (x == 0 and math.copysign(1, x) < 0) and Fraction(x) == y
    if isinstance(y, float):
        return (math.isnan(x) and math.isnan(y)) or struct.pack("<d", x) == struct.pack("<d", y)
    return False


def ulps(q: Fraction, x: float) -> float:
    ulp = math.ulp(x) if x != 0 else 5e-324
    return float(abs(q - Fraction(x)) / Fraction(ulp))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=int, default=150, help="Inputs per operation and input class.")
    ap.add_argument("--seed", type=int, default=24301)
    ap.add_argument("--json", help="Write the full results here.")
    args = ap.parse_args()
    sys.set_int_max_str_digits(0)

    src = module()
    ns: dict = {}
    exec(src, ns)  # noqa: S102
    rng = random.Random(args.seed)
    classes = ["dyadic", "decimal", "wide", "edge"]
    cases = {}
    for name, _, _, _, kinds in OPS:
        for cls in classes:
            if cls != "dyadic" and set(kinds) <= {"i", "s", "t"}:
                continue
            seen, rows = set(), []
            for _ in range(args.samples * 3):
                if len(rows) >= args.samples:
                    break
                a = [draw(k, cls, rng) for k in kinds]
                key = struct.pack(f"<{len(a)}d", *[float(x) for x in a]) if all(isinstance(x, float) for x in a) \
                    else repr(a)
                if key in seen:
                    continue
                seen.add(key)
                rows.append(a)
            cases[(name, cls)] = rows

    with Session(target="command", mode="both") as s:
        res = s.translate(src, prove_asserts=False)
        if not res.ok:
            print("translation failed:", res.error)
            return 2
        evals = []
        for (name, cls), rows in cases.items():
            inputs = [[encode(x) for x in a] for a in rows]
            evals += [{"id": f"{name}|{cls}|prov", "fn": NS + f"op_{name}", "inputs": inputs},
                      {"id": f"{name}|{cls}|run", "fn": NS + f"op_{name}'rn", "inputs": inputs}]
        out = s.client.refute(res.lean_code, [], evals=evals, timeout=3600) or {}
    if not out.get("result"):
        print("Lean evaluation failed:", out.get("error"))
        return 2
    by_id = {e["id"]: e for e in out.get("evals", [])}

    report, total = [], {"run_ok": 0, "run_n": 0, "prov_exact": 0, "prov_n": 0}
    print(f"{'op':13} {'class':8} {'n':>4}  {'runnable = CPython':>18}  {'ℚ exact':>8}  {'ℚ ulps med/max':>15}  notes")
    for (name, cls), rows in cases.items():
        fn = ns[f"op_{name}"]
        prov = by_id.get(f"{name}|{cls}|prov", {})
        run = by_id.get(f"{name}|{cls}|run", {})
        r_ok = p_exact = p_n = p_na = p_partial = n_complex = 0
        dists, bad = [], []
        for i, a in enumerate(rows):
            kind, val = py_outcome(fn, a)
            if isinstance(val, complex):
                # Python's `**` returns a complex number here; PastaLean has no complex type.
                p_na += 1
                n_complex += 1
                continue
            rv = (run.get("values") or [{}] * len(rows))[i] if run.get("values") else {"error": run.get("error")}
            pv = (prov.get("values") or [{}] * len(rows))[i] if prov.get("values") else {"error": prov.get("error")}
            # runnable
            if kind == "exc":
                ok = rv.get("exc") == val
            elif "value" in rv:
                ok = same_double(val, rv["value"]) if isinstance(val, float) else lit_value(rv["value"]) == val
            else:
                ok = False
            r_ok += ok
            if not ok and len(bad) < 3:
                want = repr(val) if kind == "value" else "raises " + val
                got = repr(lit_value(rv["value"])) if "value" in rv else \
                    ("raises " + rv["exc"] if rv.get("exc") else str(rv.get("error", ""))[:80])
                bad.append(f"{name}{tuple(a)}: CPython {want}, runnable {got}")
            # provable
            if "error" in pv:
                p_na += 1
            elif kind == "exc":
                p_partial += 1
            elif "value" in pv and isinstance(val, float):
                if not math.isfinite(val):
                    p_na += 1
                    continue
                q = lit_value(pv["value"])
                if isinstance(q, Fraction):
                    p_n += 1
                    if q == Fraction(val):
                        p_exact += 1
                    else:
                        dists.append(ulps(q, val))
            elif "value" in pv:
                p_n += 1
                p_exact += lit_value(pv["value"]) == val
        n = len(rows) - n_complex
        total["run_ok"] += r_ok
        total["run_n"] += n
        total["prov_exact"] += p_exact
        total["prov_n"] += p_n
        med = f"{statistics.median(dists):.2f}/{max(dists):.3g}" if dists else "–"
        notes = []
        if n_complex:
            notes.append(f"{n_complex} complex results skipped")
        if p_na:
            notes.append(f"ℚ n/a {p_na}")
        if p_partial:
            notes.append(f"ℚ total-model value where Python raises {p_partial}")
        print(f"{name:13} {cls:8} {n:4}  {r_ok:7}/{n:<4} {100 * r_ok / n:5.1f}%  "
              f"{(f'{100 * p_exact / p_n:5.1f}%' if p_n else '   –'):>8}  {med:>15}  {', '.join(notes)}")
        for b in bad:
            print(f"{'':28}{b}")
        report.append({"op": name, "class": cls, "n": n, "runnable_same": r_ok, "provable_exact": p_exact,
                       "provable_compared": p_n, "provable_ulps": dists, "provable_na": p_na,
                       "provable_partial": p_partial, "examples": bad})
    print(f"\nrunnable bit-identical to CPython: {total['run_ok']}/{total['run_n']} "
          f"({100 * total['run_ok'] / total['run_n']:.1f}%); provable exactly CPython's double: "
          f"{total['prov_exact']}/{total['prov_n']} ({100 * total['prov_exact'] / max(total['prov_n'], 1):.1f}%)")
    if args.json:
        Path(args.json).write_text(json.dumps(report, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
