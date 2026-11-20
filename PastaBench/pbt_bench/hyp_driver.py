"""The plain-Hypothesis baseline: one problem file's contract as a `@given` test.

Strategies come from the annotations (`st.from_type`); an unannotated parameter draws ints or strings
(what CrossHair realises such a value as). The precondition is an `assume`, exceptions the contract
lists under `raises:` are allowed, and the test runs until it fails or the caller's timeout kills it.

    python hyp_driver.py PROBLEM.py
Prints `FOUND <args>` on a counterexample, nothing otherwise.
"""

from __future__ import annotations

import ast
import importlib.util
import sys
import typing
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from hypothesis import HealthCheck, assume, given, settings, strategies as st  # noqa: E402

from pastalean.refute.obligations import collect  # noqa: E402


def main(path: str) -> int:
    source = Path(path).read_text()
    obs = collect(source)
    if not obs:
        print("NO_CONTRACT")
        return 2
    ob = obs[0]
    spec = importlib.util.spec_from_file_location("problem", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["problem"] = mod
    spec.loader.exec_module(mod)
    fn = getattr(mod, ob.name)
    fn = getattr(fn, "__wrapped__", fn)          # icontract wraps; check the contract ourselves
    hints = typing.get_type_hints(fn)
    names = [n for n, _ in ob.params]
    strategies = [st.from_type(hints[n]) if n in hints else st.one_of(st.integers(), st.text())
                  for n in names]
    allowed = tuple(c for c in (eval(r, vars(mod)) for r in ob.raises) if isinstance(c, type))  # noqa: S307
    pre = compile(ast.parse(ob.pre, mode="eval"), "<pre>", "eval") if ob.pre else None
    post = compile(ast.parse(ob.chk, mode="eval"), "<post>", "eval")

    class Violation(Exception):
        """The function under test broke its contract (or raised something it does not allow)."""

    @settings(max_examples=10 ** 9, deadline=None, database=None, suppress_health_check=list(HealthCheck),
              derandomize=False)
    @given(st.tuples(*strategies))
    def test(args):
        env = dict(vars(mod))
        env.update(zip(names, args))
        if pre is not None:
            try:
                ok = eval(pre, env)  # noqa: S307
            except Exception:  # noqa: BLE001
                ok = False
            assume(ok)
        try:
            env["pl_result"] = fn(*args)
        except allowed:
            return
        except Exception as e:  # noqa: BLE001
            raise Violation(f"{args!r} raised {type(e).__name__}") from e
        try:
            ok = eval(post, env)  # noqa: S307
        except Exception as e:  # noqa: BLE001
            raise Violation(f"{args!r}: postcondition raised {type(e).__name__}") from e
        if not ok:
            raise Violation(repr(args))

    try:
        test()
    except Violation as e:
        print("FOUND", e.args[0])
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1]))
