"""Generators built from a precondition, so that drawn inputs already satisfy it.

`Plan(pre, names, types)` splits the `Requires` conjunction into atoms and keeps the ones it understands,
per parameter:

* bounds on a number, `lo <= x`, `x < hi`, `x != c` — the bound may mention other parameters
  (`0 <= i < len(xs)`), which are then generated first;
* bounds on a length, `len(xs) >= 1`, `len(a) == len(b)`;
* congruences, `x % 97 == 3`;
* element bounds, `all(0 <= v <= 9 for v in xs)`;
* `xs == sorted(xs)` (sorted), `len(set(xs)) == len(xs)` (distinct), `x in (1, 2, 3)` (choice).

Atoms it does not understand are left to the caller's full precondition check (rejection), so a plan
never changes which inputs are valid — only how often a draw is.
"""

from __future__ import annotations

import ast
import math
import random

LIMIT = 10 ** 6


class _Var:
    """What is known about one value (a parameter, or the elements of a list parameter)."""

    def __init__(self):
        self.lo: list[tuple[ast.expr, bool]] = []      # (bound, strict)
        self.hi: list[tuple[ast.expr, bool]] = []
        self.ne: list[ast.expr] = []
        self.mod: tuple[int, int] | None = None
        self.choices: ast.expr | None = None
        self.len = None                                # _Var for the length
        self.elem = None                               # _Var for list elements
        self.sorted = False
        self.distinct = False

    def length(self) -> "_Var":
        self.len = self.len or _Var()
        return self.len

    def element(self) -> "_Var":
        self.elem = self.elem or _Var()
        return self.elem

    def empty(self) -> bool:
        return not (self.lo or self.hi or self.ne or self.mod or self.choices or self.sorted or self.distinct
                    or (self.len and not self.len.empty()) or (self.elem and not self.elem.empty()))


def _conjuncts(e):
    if isinstance(e, ast.BoolOp) and isinstance(e.op, ast.And):
        for v in e.values:
            yield from _conjuncts(v)
    elif isinstance(e, ast.Compare) and len(e.ops) > 1:
        left = e.left
        for op, right in zip(e.ops, e.comparators):
            yield ast.Compare(left, [op], [right])
            left = right
    else:
        yield e


def _names(e) -> set[str]:
    return {n.id for n in ast.walk(e) if isinstance(n, ast.Name)}


_FLIP = {ast.Lt: ast.Gt, ast.LtE: ast.GtE, ast.Gt: ast.Lt, ast.GtE: ast.LtE, ast.Eq: ast.Eq, ast.NotEq: ast.NotEq}


class Plan:
    def __init__(self, pre: ast.expr | None, names: list[str], types: list):
        self.names, self.types = names, types
        self.vars = {n: _Var() for n in names}
        self.deps = {n: set() for n in names}
        self.recognised: list[str] = []
        if pre is not None:
            for atom in _conjuncts(pre):
                if self._atom(atom):
                    self.recognised.append(ast.unparse(atom))
        self.order = self._order()

    # -- reading the precondition ------------------------------------------------------------------

    def _target(self, e, local: str | None = None):
        """(parameter, `_Var`) that `e` denotes: a parameter, `len(p)`, or the element variable."""
        if isinstance(e, ast.Name) and e.id == local:
            return local, None
        if isinstance(e, ast.Name) and e.id in self.vars:
            return e.id, self.vars[e.id]
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) and e.func.id == "len" and len(e.args) == 1 \
                and isinstance(e.args[0], ast.Name) and e.args[0].id in self.vars:
            return e.args[0].id, self.vars[e.args[0].id].length()
        return None, None

    def _bound(self, var, op, bound) -> bool:
        if isinstance(op, (ast.GtE, ast.Gt)):
            var.lo.append((bound, isinstance(op, ast.Gt)))
        elif isinstance(op, (ast.LtE, ast.Lt)):
            var.hi.append((bound, isinstance(op, ast.Lt)))
        elif isinstance(op, ast.Eq):
            var.lo.append((bound, False))
            var.hi.append((bound, False))
        elif isinstance(op, ast.NotEq):
            var.ne.append(bound)
        else:
            return False
        return True

    def _atom(self, a, owner: str | None = None, local: str | None = None, elem: _Var | None = None) -> bool:
        if isinstance(a, ast.Call) and isinstance(a.func, ast.Name) and a.func.id == "all" and len(a.args) == 1 \
                and isinstance(a.args[0], ast.GeneratorExp) and owner is None:
            g = a.args[0]
            comp = g.generators[0]
            if len(g.generators) == 1 and not comp.ifs and isinstance(comp.target, ast.Name) \
                    and isinstance(comp.iter, ast.Name) and comp.iter.id in self.vars:
                p = comp.iter.id
                ok = [self._atom(x, p, comp.target.id, self.vars[p].element()) for x in _conjuncts(g.elt)]
                return all(ok) and bool(ok)
            return False
        if not isinstance(a, ast.Compare) or len(a.ops) != 1:
            return False
        left, op, right = a.left, a.ops[0], a.comparators[0]
        # `xs == sorted(xs)` / `len(set(xs)) == len(xs)`
        if owner is None and isinstance(op, ast.Eq):
            for x, y in ((left, right), (right, left)):
                if isinstance(x, ast.Name) and x.id in self.vars and isinstance(y, ast.Call) \
                        and isinstance(y.func, ast.Name) and y.func.id == "sorted" and len(y.args) == 1 \
                        and isinstance(y.args[0], ast.Name) and y.args[0].id == x.id and not y.keywords:
                    self.vars[x.id].sorted = True
                    return True
                for n in self.vars:
                    if ast.unparse(x) == f"len(set({n}))" and ast.unparse(y) == f"len({n})":
                        self.vars[n].distinct = True
                        return True
        # `x % m == r`
        if isinstance(op, ast.Eq) and isinstance(left, ast.BinOp) and isinstance(left.op, ast.Mod) \
                and isinstance(left.right, ast.Constant) and isinstance(left.right.value, int) and left.right.value > 0 \
                and isinstance(right, ast.Constant) and isinstance(right.value, int):
            p, var = self._target(left.left, local)
            var = elem if p == local and local is not None else var
            if var is not None:
                var.mod = (left.right.value, right.value % left.right.value)
                return True
            return False
        # `x in (1, 2, 3)`
        if isinstance(op, ast.In) and isinstance(right, (ast.Tuple, ast.List, ast.Set)):
            p, var = self._target(left, local)
            var = elem if p == local and local is not None else var
            if var is not None and all(isinstance(e, ast.Constant) for e in right.elts):
                var.choices = right
                return True
            return False
        for x, y, o in ((left, right, op), (right, left, _FLIP.get(type(op), type(op))())):
            p, var = self._target(x, local)
            if p is None:
                continue
            if p == local and local is not None:
                var = elem
            if local is not None and local in _names(y):
                continue
            free = _names(y) & set(self.vars)
            # A bound on the elements may only use other parameters, never their own list.
            if p in free or (owner is not None and owner in free):
                continue
            if self._bound(var, o, y):
                self.deps[owner or p] |= free
                return True
        return False

    def _order(self) -> list[str]:
        out, seen, busy = [], set(), set()

        def visit(n):
            if n in seen:
                return True
            if n in busy:
                return False
            busy.add(n)
            for d in self.deps[n]:
                if not visit(d):
                    # A cycle: drop the bounds that create it (rejection still enforces them).
                    self.deps[n].discard(d)
            busy.discard(n)
            seen.add(n)
            out.append(n)
            return True

        for n in self.names:
            visit(n)
        return out

    # -- drawing -----------------------------------------------------------------------------------

    def gen(self, rng: random.Random, size: int, fallback):
        """Arguments satisfying the recognised atoms, or `None` when a draw is infeasible.
        `fallback(t, rng, size)` draws a value of a type the plan has nothing to say about."""
        env: dict = {}
        for n in self.order:
            t = self.types[self.names.index(n)]
            v = self._value(self.vars[n], t, env, rng, size, fallback)
            if v is _NONE:
                return None
            env[n] = v
        return [env[n] for n in self.names]

    def _eval(self, bounds, env, strict_shift, pick):
        vals = []
        for e, strict in bounds:
            try:
                v = eval(compile(ast.Expression(e), "<pre>", "eval"), {"len": len, "abs": abs, "min": min,  # noqa: S307
                                                                         "max": max}, dict(env))
            except Exception:  # noqa: BLE001
                continue
            if isinstance(v, bool) or not isinstance(v, (int, float)):
                continue
            vals.append(v + strict_shift if strict and isinstance(v, int) else v)
        return pick(vals) if vals else None

    def _value(self, var: _Var, t, env, rng, size, fallback):
        tag = t[0]
        if var.choices is not None:
            return rng.choice([e.value for e in var.choices.elts])
        if tag in ("int", "float"):
            return self._number(var, tag, env, rng, size)
        if tag in ("list", "str", "set"):
            n = self._number(var.len, "int", env, rng, max(1, size // 3 + 1), nonneg=True) if var.len else None
            if n is _NONE:
                return _NONE
            if n is None:
                n = rng.randint(0, size // 3 + 1)
            if tag == "str":
                return "".join(rng.choice("ab") for _ in range(n))
            et = t[1]
            items = []
            for _ in range(n):
                v = self._value(var.elem, et, env, rng, size, fallback) if var.elem else fallback(et, rng, size)
                if v is _NONE:
                    return _NONE
                items.append(v)
            if var.distinct or tag == "set":
                seen, uniq = set(), []
                for x in items:
                    tries = 0
                    while x in seen and tries < 20:
                        x = self._value(var.elem, et, env, rng, size, fallback) if var.elem else fallback(et, rng, size)
                        tries += 1
                    if x in seen:
                        return _NONE
                    seen.add(x)
                    uniq.append(x)
                items = uniq
            if var.sorted:
                items.sort()
            return set(items) if tag == "set" else items
        return fallback(t, rng, size)

    def _number(self, var: _Var, tag, env, rng, size, nonneg=False):
        lo = self._eval(var.lo, env, 1, max)
        hi = self._eval(var.hi, env, -1, min)
        if nonneg:
            lo = 0 if lo is None else max(lo, 0)
        if tag == "float":
            # Strict float bounds: nudge inward by a dyadic step so the draw is exact in every world.
            if lo is not None and any(s for _, s in var.lo):
                lo = lo + 2 ** -4
            if hi is not None and any(s for _, s in var.hi):
                hi = hi - 2 ** -4
        span = (4 * size + 4) * (var.mod[0] if var.mod else 1)
        if lo is None and hi is None:
            lo, hi = -size, size
        elif lo is None:
            lo = hi - span
        elif hi is None:
            hi = lo + span
        if lo > hi or abs(lo) > LIMIT * 1000 or abs(hi) > LIMIT * 1000:
            return _NONE
        for _ in range(30):
            r = rng.random()
            if tag == "float":
                if r < 0.15:
                    v = float(lo)
                elif r < 0.3:
                    v = float(hi)
                else:
                    e = rng.randint(0, 4)
                    v = math.ldexp(rng.randint(math.ceil(lo * 2 ** e), math.floor(hi * 2 ** e)), -e) \
                        if math.ceil(lo * 2 ** e) <= math.floor(hi * 2 ** e) else float(lo)
            else:
                lo_i, hi_i = math.ceil(lo), math.floor(hi)
                if lo_i > hi_i:
                    return _NONE
                if var.mod:
                    m, rem = var.mod
                    first = lo_i + (rem - lo_i) % m
                    if first > hi_i:
                        return _NONE
                    v = first + m * rng.randint(0, (hi_i - first) // m)
                elif r < 0.15:
                    v = lo_i
                elif r < 0.3:
                    v = hi_i
                elif r < 0.4:
                    v = min(lo_i + 1, hi_i)
                else:
                    v = rng.randint(lo_i, hi_i)
            if not any(self._eval([(e, False)], env, 0, max) == v for e in var.ne):
                return v
        return _NONE

    def describe(self) -> list[str]:
        return self.recognised


_NONE = object()
