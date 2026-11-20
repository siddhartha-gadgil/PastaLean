"""The CPython side of `pastalean refute`, run as a subprocess (`python -I harness.py < request.json`).

It never searches: every input comes from the Lean side. Over one module (the program with contract
markers stripped, plus the `pl_pre_*`/`pl_chk_*` checkers) it

* **judges** each witness the Lean search found, under CPython (the ground truth the twins are checked
  against): precondition, property, the exception raised if any, what the function returned and which
  `Ensures` that breaks, and for floats the IEEE-enclosure verdict (`lift.py`);
* **samples values** for `--float-report` (a measurement of the float model, not a search).

An exception inside `chk` is a violation (an observable result); one inside `pre` discards the input.
"""

from __future__ import annotations

import ast
import copy
import json
import math
import random
import signal
import sys

sys.setrecursionlimit(10000)

from pylit import decode, encode  # noqa: E402  (harness runs with its own directory on sys.path)
import fi  # noqa: E402
from fi import FI, RoundingSensitive, Unmodelled, enclose  # noqa: E402
from lift import lifted_namespace  # noqa: E402
import limits  # noqa: E402
import typing  # noqa: E402
import domains  # noqa: E402

# witnesses travel as JSON text: an exact big integer (`fib(100000)`) must not hit the 4300-digit limit
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)



FLOAT_EXP = 4


class Timeout(Exception):
    pass


def _alarm(_sig, _frame):
    raise Timeout()


signal.signal(signal.SIGALRM, _alarm)


def call_with_deadline(fn, args, ms):
    signal.setitimer(signal.ITIMER_REAL, ms / 1000.0)
    try:
        return fn(*args)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


# ---------------------------------------------------------------------------------------------------
# Types from annotations

def parse_type(ann: str | None, ns: dict):
    """An annotation string as a small type tree: ('int',), ('list', T), ('tuple', [T…]), …"""
    if ann is None:
        return ("int",)
    try:
        node = ast.parse(ann, mode="eval").body
    except SyntaxError:
        return ("int",)
    return _type_of(node, ns)


def _type_of(node, ns):
    if isinstance(node, ast.Constant) and node.value is None:
        return ("none",)
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return _type_of(ast.parse(node.value, mode="eval").body, ns)
    if isinstance(node, ast.Name):
        n = node.id
        if n in ("int", "float", "str", "bool"):
            return (n,)
        if n in ("list", "List"):
            return ("list", ("int",))
        if n in ("dict", "Dict"):
            return ("dict", ("int",), ("int",))
        if n in ("set", "Set"):
            return ("set", ("int",))
        cls = ns.get(n)
        if isinstance(cls, type):
            return ("obj", cls)
        return ("int",)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        l, r = _type_of(node.left, ns), _type_of(node.right, ns)
        if l == ("none",):
            return ("opt", r)
        if r == ("none",):
            return ("opt", l)
        return l
    if isinstance(node, ast.Subscript):
        head = node.value.id if isinstance(node.value, ast.Name) else getattr(node.value, "attr", "")
        args = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
        ts = [_type_of(a, ns) for a in args]
        if head in ("list", "List", "Sequence", "Iterable"):
            return ("list", ts[0])
        if head in ("set", "Set", "frozenset"):
            return ("set", ts[0])
        if head in ("dict", "Dict", "Mapping"):
            return ("dict", ts[0], ts[1] if len(ts) > 1 else ("int",))
        if head in ("tuple", "Tuple"):
            return ("tuple", [t for t in ts if t != ("ellipsis",)])
        if head == "Optional":
            return ("opt", ts[0])
    return ("int",)


# ---------------------------------------------------------------------------------------------------
# Typed generation and enumeration (mirrors `PastaLean/PyVerify/Refute/Arb.lean`)

MAX_LEN = 64


def _length(rng: random.Random, size: int) -> int:
    """A collection length for `size`, bounded however large the numbers get."""
    return rng.randint(0, min(size, 3 * MAX_LEN) // 3 + 1)


def gen(t, rng: random.Random, size: int):
    tag = t[0]
    if tag == "int":
        r = rng.randrange(10)
        if r == 0:
            return 0
        if r in (1, 2):
            return rng.choice([1, -1])
        if r == 3:
            # Powers of two stay within reach of the size: a huge one sent to a counting loop never returns.
            return rng.choice([1, -1]) * 2 ** rng.randrange(1, min(62, 2 * size + 2) + 1)
        return rng.randint(-size, size)
    if tag == "bool":
        return rng.random() < 0.5
    if tag == "float":
        e = rng.randrange(FLOAT_EXP + 1)
        b = size * 2 ** e + 1
        return math.ldexp(rng.randint(-b, b), -e)
    if tag == "str":
        n = rng.randint(0, min(size, 2 * MAX_LEN) // 2)
        return "".join(chr(rng.randint(32, 126)) if rng.random() < 0.2 else rng.choice("ababc01 ")
                       for _ in range(n))
    if tag == "date":
        return domains.gen_date(rng, None)
    if tag == "datetime":
        return domains.gen_datetime(rng, None)
    if tag == "timedelta":
        return domains.gen_timedelta(rng, None, size)
    if tag == "union":
        return gen(rng.choice(t[1]), rng, size)
    if tag == "any":
        return gen(rng.choice([("int",), ("str",)]), rng, size)
    if tag == "key":
        return gen(rng.choice([("int",), ("str",)]), rng, size)
    if tag == "none":
        return None
    if tag == "opt":
        return None if rng.random() < 0.25 else gen(t[1], rng, size)
    if tag == "list":
        return [gen(t[1], rng, size * 2 // 3) for _ in range(_length(rng, size))]
    if tag == "set":
        return {gen(t[1], rng, size * 2 // 3) for _ in range(_length(rng, size))}
    if tag == "dict":
        return {gen(t[1], rng, size // 2): gen(t[2], rng, size // 2) for _ in range(_length(rng, size))}
    if tag == "tuple":
        return tuple(gen(x, rng, size) for x in t[1])
    if tag == "obj":
        return gen_obj(t[1], rng, size)
    return 0


def gen_obj(cls, rng, size):
    """An instance built through `__init__`, its parameters drawn from their annotations."""
    import inspect
    try:
        hints = typing.get_type_hints(cls.__init__)
    except Exception:  # noqa: BLE001
        hints = {}
    raw = getattr(cls.__init__, "__annotations__", {})
    try:
        params = [p for p in inspect.signature(cls.__init__).parameters.values() if p.name != "self"]
    except (TypeError, ValueError):
        params = []
    args = []
    for p in params:
        if p.name in hints:
            sub = domains.type_of_hint(hints[p.name])
        else:
            ann = raw.get(p.name)
            sub = parse_type(ann if isinstance(ann, str) else getattr(ann, "__name__", None), {})
        # Recursive types shrink as they nest, so generation terminates.
        args.append(gen(sub, rng, max(0, size // 2)) if size > 0 or sub[0] in ("opt", "none") else None)
    return cls(*args)


def _param_types(ns, ob):
    """Parameter types from the function's resolved annotations (aliases, forward references and
    unions included), else from the annotation text; an unannotated parameter is an int or a str."""
    fn = ns.get(ob["name"])
    fn = getattr(fn, "__wrapped__", fn)
    try:
        hints = typing.get_type_hints(fn) if fn is not None else {}
    except Exception:  # noqa: BLE001
        hints = {}
    return [domains.type_of_hint(hints[n]) if n in hints else parse_type(a, ns) if a is not None else ("any",)
            for n, a in ob["params"]]


class Problem:
    def __init__(self, ns, ob, per_case_ms):
        self.ns = ns
        self.pre = ns[ob["pre_fn"]]
        self.chk = ns[ob["chk_fn"]]
        self.types = _param_types(ns, ob)
        self.names = [n for n, _ in ob["params"]]
        self.chk_ast = ast.parse(ob["chk"], mode="eval").body
        self.contract = ob["kind"] == "contract"
        self.fn = ns.get(ob["name"])
        self.ms = per_case_ms
        self.ensures = ob.get("ensures") or []
        self.lets = ob.get("lets") or []
        allowed = []
        for name in ob.get("raises") or []:
            try:
                cls = eval(name, ns)  # noqa: S307
            except Exception:  # noqa: BLE001
                continue
            if isinstance(cls, type) and issubclass(cls, BaseException):
                allowed.append(cls)
        self.allowed = tuple(allowed)   # exceptions the contract permits: not a violation

    def judge(self, args):
        """`(guard, holds, exc)` under CPython; `exc` is the exception kind when `chk` raised."""
        try:
            g = bool(call_with_deadline(self.pre, copy.deepcopy(args), self.ms))
        except Timeout:
            return None, None, "Timeout"
        except Exception:  # noqa: BLE001
            return False, None, None
        if not g:
            return False, None, None
        try:
            return True, bool(call_with_deadline(self.chk, copy.deepcopy(args), self.ms)), None
        except Timeout:
            return True, None, "Timeout"
        except MemoryError:
            # The input exhausted the memory cap: no verdict on it.
            return True, None, "MemoryError"
        except Exception as e:  # noqa: BLE001
            if self.allowed and isinstance(e, self.allowed):
                return False, None, None
            return True, False, type(e).__name__

    def judge_interval(self, iv, args, py_exc):
        """The same judgement in the lifted module `iv`, every float an IEEE enclosure: `holds` /
        `violates` when decided for every rounding-consistent execution, `rounding` when some comparison
        or zero test falls inside the rounding uncertainty, `unsupported:<why>` when the computation
        leaves the modelled operations, or `None` when it involves no float at all. An exception CPython
        raised too is the same violation."""
        if iv is None:
            return None
        before = fi.created
        fargs = [enclose(a, t) for a, t in zip(args, self.types)]
        try:
            try:
                g = bool(call_with_deadline(iv[self.pre.__name__], copy.deepcopy(fargs), self.ms))
            except (RoundingSensitive, Unmodelled, Timeout):
                raise
            except Exception:  # noqa: BLE001
                g = False
            if not g:
                out = "vacuous"
            else:
                try:
                    out = "holds" if bool(call_with_deadline(iv[self.chk.__name__], fargs, self.ms)) else "violates"
                except (RoundingSensitive, Unmodelled, Timeout):
                    raise
                except Exception as e:  # noqa: BLE001
                    out = "violates" if type(e).__name__ == py_exc else f"unsupported:{type(e).__name__}"
        except RoundingSensitive:
            out = "rounding"
        except Unmodelled as e:
            out = f"unsupported:{e}"
        except Timeout:
            out = "unsupported:timeout"
        return out if fi.created > before else None

    def explain(self, args):
        """For a contract: what the function returned and which `Ensures` clauses that breaks. For a
        property `a == b`: both sides."""
        if not self.contract:
            if isinstance(self.chk_ast, ast.Compare) and len(self.chk_ast.ops) == 1 \
                    and isinstance(self.chk_ast.ops[0], ast.Eq):
                env = dict(self.ns)
                env.update(zip(self.names, copy.deepcopy(args)))
                try:
                    for line in self.lets:
                        exec(line, env)  # noqa: S102
                    sides = [(ast.unparse(e), repr(eval(compile(ast.Expression(e), "<chk>", "eval"), env)))  # noqa: S307
                             for e in (self.chk_ast.left, self.chk_ast.comparators[0])]
                except Exception:  # noqa: BLE001
                    return None
                return {"sides": sides}
            return None
        if self.fn is None:
            return None
        try:
            call_with_deadline(self.fn, copy.deepcopy(args), self.ms)
        except Timeout:
            return None
        except Exception as e:  # noqa: BLE001
            return {"raised": type(e).__name__, "failed": []}
        try:
            env = self.env(args)
        except Exception:  # noqa: BLE001
            return None
        out = {"returned": repr(env.get("pl_result")), "failed": []}
        for orig, expr in self.ensures:
            try:
                if not eval(expr, env):  # noqa: S307
                    out["failed"].append(orig)
            except NameError:   # reads the function's locals: checked inside it (`pl_post_*`), not here
                out["failed"].append(f"{orig}  (over the function's locals)")
            except Exception as e:  # noqa: BLE001
                out["failed"].append(f"{orig}  (raised {type(e).__name__})")
        return out

    def env(self, args):
        env = dict(self.ns)
        env.update(zip(self.names, copy.deepcopy(args)))
        if self.contract and self.fn is not None:
            try:
                env["pl_result"] = self.fn(*copy.deepcopy(args))
            except Timeout:
                raise
            except Exception:  # noqa: BLE001
                env["pl_result"] = None
        return env


def _end(q):
    return None if q is None else f"{q.numerator}/{q.denominator}"


def sample_values(ns, iv, req):
    """For each float function: sampled inputs, CPython's result, and the IEEE enclosure of the exact
    result (`[lo, hi]` as fractions, `None` for an infinite end), or why there is none."""
    out = []
    for fr in req:
        fn = ns[fr["fn"]]
        types = [parse_type(a, ns) for _, a in fr["params"]]
        rng = random.Random(fr.get("seed", 24301))
        seen, rows = set(), []
        for i in range(fr.get("n", 200) * 4):
            if len(rows) >= fr.get("n", 200):
                break
            args = [gen(t, rng, 4 + i % 40) for t in types]
            key = repr(args)
            if key in seen:
                continue
            seen.add(key)
            row = {"lits": [encode(a) for a in args]}
            try:
                v = call_with_deadline(fn, copy.deepcopy(args), 200)
                row["py"] = encode(float(v)) if isinstance(v, (int, float)) else None
            except Exception as e:  # noqa: BLE001
                row["pyExc"] = type(e).__name__
            if "pyExc" in row:
                rows.append(row)
                continue
            try:
                r = call_with_deadline(iv[fr["fn"]], [enclose(a, t) for a, t in zip(args, types)], 200)
                r = FI.of(r)
                row["enc"] = [_end(r.lo), _end(r.hi)]
            except RoundingSensitive:
                row["enc"] = "rounding"
            except Unmodelled as e:
                row["enc"] = f"unsupported:{e}"
            except Exception as e:  # noqa: BLE001
                row["enc"] = f"unsupported:{type(e).__name__}"
            rows.append(row)
        out.append({"fn": fr["fn"], "rows": rows})
    return out


def main():
    limits.apply_memory_cap()
    req = json.load(sys.stdin)
    ns: dict = {"__name__": "pl_refute_module"}
    exec(compile(req["module"], "<program>", "exec"), ns)  # noqa: S102
    if "values" in req:
        json.dump({"values": sample_values(ns, lifted_namespace(req["module"]), req["values"])}, sys.stdout)
        return
    classes = {k: v for k, v in ns.items() if isinstance(v, type)}
    try:
        iv = lifted_namespace(req["module"])
    except Exception:  # noqa: BLE001
        iv = None
    iv_classes = {k: v for k, v in (iv or {}).items() if isinstance(v, type)}
    out = []
    for ob in req["obligations"]:
        res = {"id": ob["name"]}
        p = Problem(ns, ob, req.get("perCaseMs", 1000))
        judged = []
        for lits in ob.get("witnesses", []):
            try:
                args = [decode(l, classes) for l in lits]
            except Exception as e:  # noqa: BLE001
                judged.append({"lits": lits, "error": f"decode: {e}"})
                continue
            g, h, exc = p.judge(args)
            try:
                iv_args = [decode(l, iv_classes) for l in lits]
            except Exception:  # noqa: BLE001
                iv_args = None
            interval = p.judge_interval(iv, iv_args, exc) if iv_args is not None else None
            judged.append({"lits": lits, "guard": g, "holds": h, "exc": exc, "interval": interval,
                           "explain": p.explain(args) if g and (h is False or exc) else None})
        res["judged"] = judged
        out.append(res)
    json.dump({"obligations": out}, sys.stdout)


if __name__ == "__main__":
    main()
