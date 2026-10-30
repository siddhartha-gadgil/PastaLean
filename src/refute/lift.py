"""Run a module with every float it creates kept as an IEEE enclosure (`fi.FI`).

Float-typed inputs are enclosed by the caller; this rewrites the module so that every *other* way a float
comes into being goes through the enclosure as well: `+ - * /` (int `/` int included), float literals
(widened when the decimal is not a double) and `float(...)`. Anything else that produces a float — `math`,
`**`, `//` or `%` on floats, a library — raises `Unmodelled`, and so does any plain float reaching the
arithmetic, so a result is either a sound enclosure or no answer at all.
"""

from __future__ import annotations

import ast
import builtins
import copy
import operator
import types
from fractions import Fraction

from fi import FI, Unmodelled

_OPS = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul", ast.Div: "truediv", ast.FloorDiv: "floordiv",
        ast.Mod: "mod", ast.Pow: "pow"}
_LIFTED = ("add", "sub", "mul", "truediv")


def _num(v) -> bool:
    return isinstance(v, (int, float, FI))


def _check(v):
    if isinstance(v, float):
        raise Unmodelled("a float computed outside the enclosure model")
    return v


def pl_arith(op: str, a, b):
    if not (_num(a) and _num(b)):
        return getattr(operator, op)(a, b)
    _check(a), _check(b)
    if isinstance(a, int) and isinstance(b, int) and op != "truediv":
        if op == "pow" and b < 0:
            raise Unmodelled("int ** negative int (a float)")
        return getattr(operator, op)(a, b)
    if op not in _LIFTED:
        raise Unmodelled(f"`{op}` on floats")
    return getattr(operator, op)(FI.of(a), FI.of(b))


def pl_aug(op: str, a, b):
    """`a op= b`: in place for containers (list `+=` extends), lifted for numbers."""
    if _num(a) and _num(b):
        return pl_arith(op, a, b)
    return getattr(operator, "i" + op)(a, b)


def pl_lit(text: str) -> FI:
    """A float literal as the program wrote it: the decimal, widened by one rounding unless exact."""
    q = Fraction(text.replace("_", ""))
    f = Fraction(float(q))
    return FI.point(f) if f == q else FI.rounded(q, q)


def pl_float(*args):
    if len(args) == 1 and isinstance(args[0], (int, FI)) and not isinstance(args[0], bool):
        return FI.of(args[0])
    if len(args) == 1 and isinstance(args[0], bool):
        return FI.point(int(args[0]))
    if len(args) == 1 and isinstance(args[0], str):
        v = float(args[0])
        # ±inf / nan parse exactly; a finite decimal rounds like a literal.
        return pl_lit(args[0].strip()) if v == v and abs(v) != float("inf") else v
    raise Unmodelled("float() of a non-number")


def _guard(fn):
    """A callable from outside the module: a float in its result is outside the model."""
    def call(*a, **k):
        r = fn(*a, **k)
        if isinstance(r, float):
            raise Unmodelled(f"float from {getattr(fn, '__name__', fn)}")
        return r
    return call


class _GuardedModule(types.ModuleType):
    def __init__(self, mod):
        super().__init__(mod.__name__)
        self._mod = mod

    def __getattr__(self, name):
        v = getattr(self._mod, name)
        if isinstance(v, float):
            raise Unmodelled(f"{self._mod.__name__}.{name}")
        return _guard(v) if callable(v) else v


class _Lift(ast.NodeTransformer):
    def __init__(self, source: str):
        self.source = source

    def _call(self, name, *args):
        return ast.Call(ast.Name(name, ast.Load()), list(args), [])

    def visit_BinOp(self, node):
        self.generic_visit(node)
        op = _OPS.get(type(node.op))
        if op is None:
            return node
        return ast.copy_location(self._call("pl_arith", ast.Constant(op), node.left, node.right), node)

    def visit_AugAssign(self, node):
        self.generic_visit(node)
        op = _OPS.get(type(node.op))
        if op is None:
            return node
        load = _as_load(node.target)
        value = self._call("pl_aug", ast.Constant(op), load, node.value)
        return ast.copy_location(ast.Assign([node.target], value), node)

    def visit_Constant(self, node):
        if isinstance(node.value, float):
            text = ast.get_source_segment(self.source, node) or repr(node.value)
            try:
                Fraction(text.replace("_", ""))
            except (ValueError, ZeroDivisionError):
                text = repr(node.value)
            return ast.copy_location(self._call("pl_lit", ast.Constant(text)), node)
        return node

    def visit_Call(self, node):
        self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id == "float":
            node.func = ast.copy_location(ast.Name("pl_float", ast.Load()), node.func)
        return node


def _as_load(target):
    t = copy.deepcopy(target)
    for n in ast.walk(t):
        if hasattr(n, "ctx"):
            n.ctx = ast.Load()
    return t


def lifted_namespace(source: str, name: str = "pl_refute_lifted") -> dict:
    """Execute `source` with its float arithmetic lifted; returns the module namespace."""
    tree = _Lift(source).visit(ast.parse(source))
    ast.fix_missing_locations(tree)
    guarded_builtins = dict(vars(builtins))
    guarded_builtins["pow"] = _guard(builtins.pow)
    ns: dict = {"__name__": name, "__builtins__": guarded_builtins, "pl_arith": pl_arith, "pl_aug": pl_aug,
                "pl_lit": pl_lit, "pl_float": pl_float}
    exec(compile(tree, "<lifted>", "exec"), ns)  # noqa: S102
    for k, v in list(ns.items()):
        if isinstance(v, types.ModuleType):
            ns[k] = _GuardedModule(v)
        elif isinstance(v, types.BuiltinFunctionType) and getattr(v, "__module__", None) not in (None, "builtins"):
            ns[k] = _guard(v)
    return ns
