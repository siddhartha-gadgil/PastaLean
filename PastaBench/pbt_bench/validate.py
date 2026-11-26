"""Re-check a reported counterexample against the problem's contract, independently of the tool.

    python validate.py PROBLEM.py TOOL WITNESS   →  prints CONFIRMED / REJECTED / UNPARSEABLE

A witness counts only if the precondition holds and the function then raises an exception the contract
does not allow, or returns a value breaking the postcondition.
"""

from __future__ import annotations

import ast
import datetime  # noqa: F401  (witness reprs mention it)
import importlib.util
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from pastalean.refute.obligations import collect  # noqa: E402
from pastalean.refute.pylit import decode  # noqa: E402


def call_args(tool: str, witness: str, env: dict, name: str):
    if tool == "crosshair":
        i = witness.find(f"when calling {name}(")
        if i < 0:
            return None
        text = witness[i + len(f"when calling {name}"):]
        depth = 0
        for j, c in enumerate(text):
            depth += c == "("
            depth -= c == ")"
            if depth == 0:
                return list(eval(f"({text[1:j]},)", env))  # noqa: S307
        return None
    if tool == "hypothesis":
        body = witness.removeprefix("FOUND ").split(" raised ")[0].split(": postcondition")[0]
        return list(eval(body, env))  # noqa: S307
    lits = json.loads(witness)
    classes = {k: v for k, v in env.items() if isinstance(v, type)}
    return [decode(l, classes) for l in lits]


def main(path: str, tool: str, witness: str) -> str:
    ob = collect(Path(path).read_text())[0]
    spec = importlib.util.spec_from_file_location("problem", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["problem"] = mod
    spec.loader.exec_module(mod)
    env = dict(vars(mod))
    env["datetime"] = datetime
    try:
        args = call_args(tool, witness, env, ob.name)
    except Exception:  # noqa: BLE001
        args = None
    if args is None:
        return "UNPARSEABLE"
    fn = getattr(mod, ob.name)
    fn = getattr(fn, "__wrapped__", fn)
    allowed = tuple(c for c in (eval(r, env) for r in ob.raises) if isinstance(c, type))  # noqa: S307
    env.update(zip([n for n, _ in ob.params], args))
    if ob.pre:
        try:
            if not eval(ob.pre, env):  # noqa: S307
                return "REJECTED"
        except Exception:  # noqa: BLE001
            return "REJECTED"
    try:
        env["pl_result"] = fn(*args)
    except allowed:
        return "REJECTED"
    except Exception:  # noqa: BLE001
        return "CONFIRMED"
    try:
        return "REJECTED" if eval(ob.chk, env) else "CONFIRMED"  # noqa: S307
    except Exception:  # noqa: BLE001
        return "CONFIRMED"


if __name__ == "__main__":
    print(main(sys.argv[1], sys.argv[2], sys.argv[3]))
