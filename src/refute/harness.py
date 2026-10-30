"""The CPython side of `pastalean refute`, run as a subprocess (`python -I harness.py < request.json`).

Two jobs over one module (the program with contract markers stripped, plus the `pl_pre_*`/`pl_chk_*`
checkers), in one process so no case pays a process start:

* **judge** — run each given witness through `pre` and `chk` under CPython (the ground truth);
* **search** — look for a witness on the CPython side, with three engines:
  1. *typed generation*: small-scope enumeration, then random draws from the annotations;
  2. *precondition-directed search*: the precondition is turned into a branch distance (0 when it holds)
     and an alternating-variable hill climb walks inputs into it, then toward violating the property —
     the inputs that matter usually sit on the edge of a `Requires`;
  3. *Hypothesis* (`find` with its shrinker), when it is installed;
  4. *CrossHair* (symbolic execution over Z3), when it is installed — the engine for bugs behind a
     narrow branch or precondition that no amount of sampling reaches.

An exception inside `chk` is a violation (an observable result); one inside `pre` discards the input.
Stdlib only, besides the optional Hypothesis.
"""

from __future__ import annotations

import ast
import copy
import itertools
import json
import math
import random
import signal
import sys
import os
import re
import subprocess
import tempfile
import time

sys.setrecursionlimit(10000)

from pylit import decode, encode  # noqa: E402  (harness runs with its own directory on sys.path)
import fi  # noqa: E402
from fi import FI, RoundingSensitive, Unmodelled, enclose  # noqa: E402
from lift import lifted_namespace  # noqa: E402
from constraints import Plan  # noqa: E402

FLOAT_EXP = 4
BIG = 10.0 ** 9


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
        n = rng.randint(0, size // 2)
        return "".join(chr(rng.randint(32, 126)) if rng.random() < 0.2 else rng.choice("ababc01 ")
                       for _ in range(n))
    if tag == "none":
        return None
    if tag == "opt":
        return None if rng.random() < 0.25 else gen(t[1], rng, size)
    if tag == "list":
        return [gen(t[1], rng, size * 2 // 3) for _ in range(rng.randint(0, size // 3 + 1))]
    if tag == "set":
        return {gen(t[1], rng, size * 2 // 3) for _ in range(rng.randint(0, size // 3 + 1))}
    if tag == "dict":
        return {gen(t[1], rng, size // 2): gen(t[2], rng, size // 2) for _ in range(rng.randint(0, size // 3 + 1))}
    if tag == "tuple":
        return tuple(gen(x, rng, size) for x in t[1])
    if tag == "obj":
        return gen_obj(t[1], rng, size)
    return 0


def gen_obj(cls, rng, size):
    """An instance built through `__init__`, its parameters drawn from their annotations."""
    hints = getattr(cls.__init__, "__annotations__", {})
    import inspect
    try:
        params = [p for p in inspect.signature(cls.__init__).parameters.values() if p.name != "self"]
    except (TypeError, ValueError):
        params = []
    args = []
    for p in params:
        ann = hints.get(p.name)
        sub = parse_type(ann if isinstance(ann, str) else getattr(ann, "__name__", None), {})
        args.append(gen(sub, rng, size))
    return cls(*args)


def enum(t, d: int):
    """Every value up to depth `d`, smallest first (SmallCheck-style)."""
    tag = t[0]
    if tag == "int":
        return [0] + [s * i for i in range(1, d + 1) for s in (1, -1)]
    if tag == "bool":
        return [False, True]
    if tag == "float":
        return [float(x) for x in enum(("int",), d)] + [s * (2 * i + 1) / 2 for i in range(d) for s in (1, -1)]
    if tag == "str":
        return ["".join(p) for n in range(d // 2 + 1) for p in itertools.product("ab ", repeat=n)]
    if tag == "none":
        return [None]
    if tag == "opt":
        return [None] + enum(t[1], d)
    if tag == "list":
        es = enum(t[1], d - 1) if d > 0 else []
        return [list(p) for n in range(d + 1) for p in itertools.product(es, repeat=n)]
    if tag == "tuple":
        return [tuple(p) for p in itertools.product(*[enum(x, d) for x in t[1]])]
    return []


def enum_args(ts, d, cap):
    """Argument tuples up to depth `d`, at most `cap` of them, small ones first."""
    pools = [enum(t, d) for t in ts]
    if any(not p for p in pools):
        return []
    out = []
    for combo in itertools.product(*pools):
        out.append(list(combo))
        if len(out) >= cap:
            break
    return out


# ---------------------------------------------------------------------------------------------------
# Branch distance (precondition-directed search)

def _num(x):
    return isinstance(x, (int, float)) and not isinstance(x, bool) or isinstance(x, bool)


def _pair_true(op, a, b):
    """Distance to making `a op b` true (0 when it already is)."""
    try:
        if op is ast.Eq:
            return 0.0 if a == b else (abs(a - b) if _num(a) and _num(b) else 1.0)
        if op is ast.NotEq:
            return 0.0 if a != b else 1.0
        if op is ast.Lt:
            return 0.0 if a < b else (a - b + 1 if _num(a) and _num(b) else 1.0)
        if op is ast.LtE:
            return 0.0 if a <= b else (a - b if _num(a) and _num(b) else 1.0)
        if op is ast.Gt:
            return 0.0 if a > b else (b - a + 1 if _num(a) and _num(b) else 1.0)
        if op is ast.GtE:
            return 0.0 if a >= b else (b - a if _num(a) and _num(b) else 1.0)
        if op is ast.In:
            return 0.0 if a in b else 1.0
        if op is ast.NotIn:
            return 0.0 if a not in b else 1.0
        if op is ast.Is:
            return 0.0 if a is b else 1.0
        if op is ast.IsNot:
            return 0.0 if a is not b else 1.0
    except Exception:  # noqa: BLE001
        return BIG
    return 1.0


_NEG = {ast.Eq: ast.NotEq, ast.NotEq: ast.Eq, ast.Lt: ast.GtE, ast.LtE: ast.Gt, ast.Gt: ast.LtE,
        ast.GtE: ast.Lt, ast.In: ast.NotIn, ast.NotIn: ast.In, ast.Is: ast.IsNot, ast.IsNot: ast.Is}


def distance(node, env, want=True):
    """How far `node` is from evaluating to `want` (0 = already does)."""
    def ev(n):
        return eval(compile(ast.Expression(n), "<pl>", "eval"), env)  # noqa: S307
    try:
        if isinstance(node, ast.BoolOp):
            ds = [distance(v, env, want) for v in node.values]
            return sum(ds) if isinstance(node.op, ast.And) == want else min(ds)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return distance(node.operand, env, not want)
        if isinstance(node, ast.Compare):
            vals = [ev(node.left)] + [ev(c) for c in node.comparators]
            pairs = [(type(op), vals[i], vals[i + 1]) for i, op in enumerate(node.ops)]
            if want:
                return sum(_pair_true(op, a, b) for op, a, b in pairs)
            return min(_pair_true(_NEG[op], a, b) for op, a, b in pairs)
        v = bool(ev(node))
        return 0.0 if v == want else 1.0
    except Timeout:
        raise
    except Exception:  # noqa: BLE001
        return BIG


def leaves(v, path=()):
    """Paths to every mutable scalar in an input, and to every list (whose length can change)."""
    out = []
    if isinstance(v, bool):
        out.append((path, "bool"))
    elif isinstance(v, int):
        out.append((path, "int"))
    elif isinstance(v, float):
        out.append((path, "float"))
    elif isinstance(v, list):
        out.append((path, "list"))
        for i, x in enumerate(v):
            out.extend(leaves(x, path + (i,)))
    elif isinstance(v, (dict, set, frozenset)):
        out.append((path, "coll"))
    elif isinstance(v, tuple):
        for i, x in enumerate(v):
            out.extend(leaves(x, path + (i,)))
    return out


def get_at(v, path):
    for i in path:
        v = v[i]
    return v


def set_at(v, path, x):
    if not path:
        return x
    v = copy.deepcopy(v)
    cur = v
    for i in path[:-1]:
        cur = cur[i]
    if isinstance(cur, tuple):
        raise TypeError
    cur[path[-1]] = x
    return v


def neighbours(args, path, kind, step, elem_t):
    """Inputs one move away along one variable (alternating-variable method)."""
    cur = get_at(args, path)
    if kind == "int":
        return [set_at(args, path, cur + step), set_at(args, path, cur - step)]
    if kind == "float":
        return [set_at(args, path, cur + step / 2), set_at(args, path, cur - step / 2)]
    if kind == "bool":
        return [set_at(args, path, not cur)]
    if kind == "list":
        out = []
        if cur:
            out.append(set_at(args, path, cur[:-1]))
        if elem_t is not None:
            out.append(set_at(args, path, cur + [0 if elem_t[0] in ("int", "float") else gen(elem_t, random.Random(0), 3)]))
        return out
    return []


# ---------------------------------------------------------------------------------------------------

class Problem:
    def __init__(self, ns, ob, per_case_ms):
        self.ns = ns
        self.pre = ns[ob["pre_fn"]]
        self.chk = ns[ob["chk_fn"]]
        self.types = [parse_type(a, ns) for _, a in ob["params"]]
        self.names = [n for n, _ in ob["params"]]
        self.pre_ast = ast.parse(ob["pre"], mode="eval").body if ob.get("pre") else None
        self.chk_ast = ast.parse(ob["chk"], mode="eval").body
        self.contract = ob["kind"] == "contract"
        self.fn = ns.get(ob["name"])
        self.ms = per_case_ms
        self.plan = Plan(self.pre_ast, self.names, self.types)
        self.valid = self.rejected = 0
        self.samples: list = []        # valid inputs the property held on, for the Lean twins to re-check
        self.sample_rng = random.Random(0)
        self.ensures = ob.get("ensures") or []
        self.lets = ob.get("lets") or []

    def judge(self, args):
        """`(guard, holds, exc)` under CPython; `exc` is the exception kind when `chk` raised."""
        try:
            g = bool(call_with_deadline(self.pre, copy.deepcopy(args), self.ms))
        except Timeout:
            return None, None, "Timeout"
        except Exception:  # noqa: BLE001
            return False, None, None
        if not g:
            self.rejected += 1
            return False, None, None
        self.valid += 1
        try:
            return True, bool(call_with_deadline(self.chk, copy.deepcopy(args), self.ms)), None
        except Timeout:
            return True, None, "Timeout"
        except Exception as e:  # noqa: BLE001
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

    def failing(self, args):
        g, h, exc = self.judge(args)
        if g is True and h is True and len(self.samples) < 100 and self.sample_rng.random() < 0.2:
            self.samples.append(copy.deepcopy(args))
        return g is True and (h is False or exc is not None)

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
            env = self.env(args)
        except Exception:  # noqa: BLE001
            return None
        out = {"returned": repr(env.get("pl_result")), "failed": []}
        for orig, expr in self.ensures:
            try:
                if not eval(expr, env):  # noqa: S307
                    out["failed"].append(orig)
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

    def objective(self, args):
        """Precondition distance first (scaled), then distance to falsifying the property. The whole
        evaluation runs under the per-case deadline; one that overruns scores as far as possible."""
        signal.setitimer(signal.ITIMER_REAL, self.ms / 1000.0)
        try:
            env = self.env(args)
            dp = distance(self.pre_ast, env, True) if self.pre_ast is not None else 0.0
            if dp > 0:
                return BIG + dp
            return distance(self.chk_ast, env, False)
        except Timeout:
            return 2 * BIG
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)


def cost(args):
    """Smaller is simpler: shorter to write, then closer to zero."""
    mag = 0
    for path, kind in leaves(args):
        if kind in ("int", "float"):
            mag += abs(get_at(args, path))
    return (len(repr(args)), mag)


def shrink(p, args, budget_end):
    """Greedy: smaller inputs that still fail (drop list items, move numbers toward 0)."""
    improved = True
    while improved and time.monotonic() < budget_end:
        improved = False
        cands = []
        for path, kind in leaves(args):
            cur = get_at(args, path)
            if kind == "list":
                cands += [set_at(args, path, cur[:i] + cur[i + 1:]) for i in range(len(cur))]
            elif kind == "coll":
                items = list(cur.items()) if isinstance(cur, dict) else list(cur)
                mk = dict if isinstance(cur, dict) else type(cur)
                halves = [items[: len(items) // 2], items[len(items) // 2:]] if len(items) > 1 else []
                cands += [set_at(args, path, mk(h)) for h in halves]
                cands += [set_at(args, path, mk(items[:i] + items[i + 1:])) for i in range(min(len(items), 40))]
            elif kind in ("int", "float") and cur != 0:
                zero = 0 if kind == "int" else 0.0
                cands += [set_at(args, path, x) for x in {zero, cur // 2 if kind == "int" else cur / 2,
                                                          cur - (1 if cur > 0 else -1)}]
                # A congruence in the precondition (`x % 97 == 3`): step by the modulus to stay valid.
                var = p.plan.vars.get(p.names[path[0]]) if len(path) == 1 else None
                if kind == "int" and var is not None and var.mod:
                    cands.append(set_at(args, path, cur - var.mod[0] if cur > 0 else cur + var.mod[0]))
        for c in sorted(cands, key=cost):
            if cost(c) < cost(args) and p.failing(c):
                args, improved = c, True
                break
    return args


def engine_enumerate(p, end, depth=3, cap=3000):
    for d in range(1, depth + 1):
        for args in enum_args(p.types, d, cap):
            if time.monotonic() > end:
                return None
            if p.failing(args):
                return args
    return None


def engine_requires(p, rng, end, n_valid):
    """Draws from the precondition's plan until `n_valid` inputs have passed it (rejected ones do not
    count); sizes ramp up so small witnesses come first."""
    start = p.valid
    i = 0
    while p.valid - start < n_valid and time.monotonic() < end:
        size = 1 + (30 * (p.valid - start)) // max(n_valid, 1)
        i += 1
        args = p.plan.gen(rng, size, gen)
        if args is None:
            p.rejected += 1
            continue
        if p.failing(args):
            return args
    return None


def engine_random(p, rng, end, n=400):
    for i in range(n):
        if time.monotonic() > end:
            return None
        args = [gen(t, rng, 1 + (30 * i) // n) for t in p.types]
        if p.failing(args):
            return args
    return None


def engine_directed(p, rng, end, restarts=30):
    """Alternating-variable hill climbing on the objective: into the precondition, then out of the property.
    Restarts begin at random magnitudes, so a precondition like `n >= 1000` is reachable."""
    for r in range(restarts):
        if time.monotonic() > end:
            return None
        args = [gen(t, rng, 6 if r % 2 == 0 else 10 ** rng.randint(1, 6)) for t in p.types]
        if not leaves(args):
            return None             # nothing to climb on (e.g. objects): leave it to the other engines
        best = p.objective(args)
        stalled = 0
        while time.monotonic() < end and stalled < 3:
            if best == 0.0 and p.failing(args):
                return args
            moved = False
            for path, kind in leaves(args):
                if time.monotonic() > end:
                    break
                elem_t = None
                if kind == "list":
                    t = p.types[path[0]] if path else None
                    elem_t = t[1] if t and t[0] == "list" and len(path) == 1 else ("int",)
                step = 1
                while True:
                    try:
                        cands = neighbours(args, path, kind, step, elem_t)
                    except Exception:  # noqa: BLE001
                        break
                    scored = [(p.objective(c), c) for c in cands]
                    scored.sort(key=lambda s: s[0])
                    if scored and scored[0][0] < best:
                        best, args = scored[0]
                        step *= 2          # pattern move: keep going faster while it pays
                        moved = True
                        if best == 0.0 and p.failing(args):
                            return args
                    else:
                        break
                    if kind in ("bool", "list"):
                        break
            stalled = 0 if moved else stalled + 1
            if best < BIG and p.failing(args):
                return args
    return None


def strategy_for(t):
    from hypothesis import strategies as st
    tag = t[0]
    if tag == "int":
        return st.integers()
    if tag == "bool":
        return st.booleans()
    if tag == "float":
        return st.builds(lambda k, e: math.ldexp(k, -e), st.integers(-2 ** 20, 2 ** 20), st.integers(0, FLOAT_EXP))
    if tag == "str":
        return st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=126), max_size=20)
    if tag == "none":
        return st.none()
    if tag == "opt":
        return st.none() | strategy_for(t[1])
    if tag == "list":
        return st.lists(strategy_for(t[1]), max_size=20)
    if tag == "set":
        return st.sets(strategy_for(t[1]), max_size=20)
    if tag == "dict":
        return st.dictionaries(strategy_for(t[1]), strategy_for(t[2]), max_size=10)
    if tag == "tuple":
        return st.tuples(*[strategy_for(x) for x in t[1]])
    if tag == "obj":
        return st.builds(t[1])
    return st.integers()


def engine_hypothesis(p, end, n=500):
    try:
        from hypothesis import HealthCheck, find, settings
        from hypothesis import strategies as st
        from hypothesis.errors import NoSuchExample
    except ImportError:
        return None
    strat = st.tuples(*[strategy_for(t) for t in p.types]) if p.types else st.just(())
    try:
        found = find(strat, lambda a: time.monotonic() < end and p.failing(list(a)),
                     settings=settings(max_examples=n, database=None, derandomize=True, deadline=None,
                                       suppress_health_check=list(HealthCheck)))
        return list(found)
    except (NoSuchExample, Exception):  # noqa: BLE001
        return None


CROSSHAIR_CALL = re.compile(r"when calling (\w+)\((.*)\)\s*$")


def engine_crosshair(p, ob, module, end):
    """Hand the obligation to CrossHair as `assert pre; assert chk` (its "asserts" analysis: leading asserts
    are preconditions, any later failing assert is a counterexample) and read back the input it reports."""
    try:
        import crosshair  # noqa: F401
    except ImportError:
        return None
    budget = end - time.monotonic()
    if budget < 1:
        return None
    args = ", ".join(f"{n}: {a}" if a else n for n, a in ob["params"])
    call = ", ".join(n for n, _ in ob["params"])
    wrapper = (f"\n\ndef pl_cross_{ob['name']}({args}) -> None:\n"
               f"    assert {ob['pre_fn']}({call})\n"
               f"    assert {ob['chk_fn']}({call})\n")
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "pl_refute_mod.py")
        with open(path, "w", encoding="utf-8") as f:
            f.write(module + wrapper)
        try:
            out = subprocess.run([sys.executable, "-m", "crosshair", "check", "--analysis_kind=asserts",
                                  f"--per_condition_timeout={max(1, int(budget) - 1)}",
                                  f"pl_refute_mod.pl_cross_{ob['name']}"], capture_output=True, text=True,
                                 timeout=budget + 5, cwd=d)
        except subprocess.TimeoutExpired:
            return None
    for line in (out.stdout + out.stderr).splitlines():
        m = CROSSHAIR_CALL.search(line)
        if m and m.group(1) == f"pl_cross_{ob['name']}":
            try:
                call_ast = ast.parse(f"f({m.group(2)})", mode="eval").body
                vals = [ast.literal_eval(a) for a in call_ast.args]
                kw = {k.arg: ast.literal_eval(k.value) for k in call_ast.keywords}
                names = [n for n, _ in ob["params"]]
                vals += [kw[n] for n in names[len(vals):] if n in kw]
            except (ValueError, SyntaxError, KeyError):
                continue
            if len(vals) == len(names) and p.failing(vals):
                return vals
    return None


def search(p, seed, ms, ob=None, module=None, tests=1000):
    """Each engine in turn within the budget; a witness is shrunk before it is returned. `tests` is the
    number of precondition-satisfying inputs the plan-driven engine runs."""
    start = time.monotonic()
    end = start + ms / 1000.0
    rng = random.Random(seed)
    for name, run in (("enumerate", lambda: engine_enumerate(p, start + (end - start) * 0.15)),
                      ("requires", lambda: engine_requires(p, rng, start + (end - start) * 0.55, tests)),
                      ("directed", lambda: engine_directed(p, rng, start + (end - start) * 0.65)),
                      ("hypothesis", lambda: engine_hypothesis(p, start + (end - start) * 0.75)),
                      ("crosshair", lambda: engine_crosshair(p, ob, module, start + (end - start) * 0.97)),
                      ("random", lambda: engine_random(p, rng, end))):
        if time.monotonic() > end:
            break
        args = run()
        if args is not None:
            stats = (p.valid, p.rejected)
            w = shrink(p, args, end + 1.0)
            p.valid, p.rejected = stats      # shrinking re-judges; it is not testing
            return name, w
    return None, None


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
        if req.get("search", True):
            # Searching tries many inputs, so a slow one is abandoned sooner than a witness being judged.
            p = Problem(ns, ob, min(100, req.get("perCaseMs", 1000)))
            engine, w = search(p, req.get("seed", 24301), req.get("searchMs", 4000), ob, req["module"],
                               req.get("tests", 1000))
            samples = []
            for a in p.samples:
                try:
                    samples.append([encode(x) for x in a])
                except TypeError:
                    pass
            res["search"] = {"engine": engine, "lits": [encode(a) for a in w] if w is not None else None,
                             "valid": p.valid, "rejected": p.rejected, "plan": p.plan.describe(),
                             "samples": samples}
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
