"""Find the obligations in a Python source and write the checkers that test them.

An obligation is something PastaLean turns into a theorem: a *property function* (a body of `let`s and
one `assert`, optionally under an `if` guard — `def agree(xs): if len(xs) >= 1: assert f(xs) == g(xs)`)
or a *contract* (`Requires`/`Ensures` with `Result()`). For each one we write two ordinary Python
functions, `pl_pre_<name>` (the precondition) and `pl_chk_<name>` (the property, `Result()` replaced by
a call to the function). The same text then runs under CPython and is compiled into BOTH Lean twins, so
the three worlds judge the exact same predicate.
"""

from __future__ import annotations

import ast
import copy
from dataclasses import dataclass, field

CONTRACT_MARKERS = {"Requires", "Ensures", "Invariant", "Decreases", "Assume", "Assert"}
CHECKER_PREFIX = "pl_"


@dataclass
class Obligation:
    kind: str                      # "property" | "contract"
    name: str                      # the Python function
    params: list[tuple[str, str | None]]
    pre: str | None                # Python expression, or None
    chk: str                       # Python expression (contract: over `pl_result`)
    lets: list[str] = field(default_factory=list)
    theorem: str | None = None     # the Lean theorem PastaLean emits, when it has one
    ensures: list[tuple[str, str]] = field(default_factory=list)   # (as written, over `pl_result`)

    @property
    def pre_fn(self) -> str:
        return f"{CHECKER_PREFIX}pre_{self.name}"

    @property
    def chk_fn(self) -> str:
        return f"{CHECKER_PREFIX}chk_{self.name}"


def _marker(stmt: ast.stmt) -> str | None:
    """The contract marker a statement is (`Requires(...)` etc.), if any."""
    if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call) and isinstance(stmt.value.func, ast.Name):
        if stmt.value.func.id in CONTRACT_MARKERS:
            return stmt.value.func.id
    return None


def _strip_docstring(body: list[ast.stmt]) -> list[ast.stmt]:
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) \
            and isinstance(body[0].value.value, str):
        return body[1:]
    return body


def _params(fn: ast.FunctionDef) -> list[tuple[str, str | None]]:
    args = fn.args.posonlyargs + fn.args.args
    return [(a.arg, ast.unparse(a.annotation) if a.annotation is not None else None) for a in args]


class _ResultToVar(ast.NodeTransformer):
    def visit_Call(self, node: ast.Call):
        self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id == "Result" and not node.args:
            return ast.copy_location(ast.Name("pl_result", ast.Load()), node)
        return node


def _mentions_result(e: ast.AST) -> bool:
    return any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "Result"
               for n in ast.walk(e))


def _property(fn: ast.FunctionDef) -> Obligation | None:
    """`lets…; assert E` or `lets…; if G: assert E` — PastaLean's property-function shape."""
    body = _strip_docstring(fn.body)
    if not body or fn.args.vararg or fn.args.kwarg:
        return None
    *lets, last = body
    if not all(isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
               for s in lets):
        return None
    pre = None
    if isinstance(last, ast.If) and not last.orelse and len(last.body) == 1 and isinstance(last.body[0], ast.Assert):
        pre, last = ast.unparse(last.test), last.body[0]
    if not isinstance(last, ast.Assert):
        return None
    return Obligation("property", fn.name, _params(fn), pre, ast.unparse(last.test),
                      [ast.unparse(s) for s in lets], theorem=fn.name)


def _contract(fn: ast.FunctionDef) -> Obligation | None:
    body = _strip_docstring(fn.body)
    requires = [s.value.args[0] for s in body if _marker(s) in ("Requires", "Assume") and s.value.args]
    ensures = [s.value.args[0] for s in ast.walk(fn)
               if isinstance(s, ast.stmt) and _marker(s) in ("Ensures", "Assert")
               and s.value.args and _mentions_result(s.value.args[0])]
    if not ensures:
        return None
    pre = " and ".join(f"({ast.unparse(r)})" for r in requires) if requires else None
    clauses = [(ast.unparse(e), ast.unparse(_ResultToVar().visit(copy.deepcopy(e)))) for e in ensures]
    chk = " and ".join(f"({c})" for _, c in clauses)
    thm = f"{fn.name}_spec" if fn.name.startswith("_") else f"{fn.name}_correct"
    return Obligation("contract", fn.name, _params(fn), pre, chk, theorem=thm, ensures=clauses)


def collect(source: str) -> list[Obligation]:
    """Every testable obligation among the module's top-level functions."""
    tree = ast.parse(source)
    out: list[Obligation] = []
    for node in tree.body:
        if not isinstance(node, ast.FunctionDef) or node.name.startswith(CHECKER_PREFIX):
            continue
        ob = _property(node) or _contract(node)
        if ob is not None:
            out.append(ob)
    return out


def _signature(ob: Obligation) -> str:
    return ", ".join(f"{n}: {a}" if a else n for n, a in ob.params)


def checker_source(obs: list[Obligation]) -> str:
    """`pl_pre_*` / `pl_chk_*` for each obligation, as Python appended to the module."""
    blocks = []
    for ob in obs:
        sig = _signature(ob)
        lets = "".join(f"    {l}\n" for l in ob.lets)
        blocks.append(f"def {ob.pre_fn}({sig}) -> bool:\n{lets}    return {ob.pre or 'True'}\n")
        if ob.kind == "contract":
            call = f"{ob.name}({', '.join(n for n, _ in ob.params)})"
            blocks.append(f"def {ob.chk_fn}({sig}) -> bool:\n    pl_result = {call}\n    return {ob.chk}\n")
        else:
            blocks.append(f"def {ob.chk_fn}({sig}) -> bool:\n{lets}    return {ob.chk}\n")
    return "\n\n" + "\n\n".join(blocks)


class _StripMarkers(ast.NodeTransformer):
    """Remove contract marker statements (CPython cannot evaluate `Ensures(… Result() …)`)."""

    def _clean(self, body):
        kept = [s for s in body if _marker(s) is None]
        return kept or [ast.Pass()]

    def generic_visit(self, node):
        super().generic_visit(node)
        for attr in ("body", "orelse", "finalbody"):
            if isinstance(getattr(node, attr, None), list):
                setattr(node, attr, self._clean(getattr(node, attr)))
        return node


def cpython_module(source: str, obs: list[Obligation]) -> str:
    """The module as CPython should run it: markers stripped, a stub `contracts`, plus the checkers."""
    tree = _StripMarkers().visit(ast.parse(source))
    tree.body = [s for s in tree.body
                 if not (isinstance(s, ast.ImportFrom) and s.module in ("contracts", "contract_passta"))]
    ast.fix_missing_locations(tree)
    return ast.unparse(tree) + "\n" + checker_source(obs)


def lean_module(source: str, obs: list[Obligation]) -> str:
    """The module PastaLean translates: the original (so its theorems are emitted) plus the checkers."""
    return source.rstrip() + "\n" + checker_source(obs)


def reads_stdin(source: str) -> bool:
    """Whether the module reads standard input (`input()` or `sys.stdin`)."""
    tree = ast.parse(source)
    return any((isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "input")
               or (isinstance(n, ast.Attribute) and n.attr == "stdin") for n in ast.walk(tree))


def equiv_source(source: str, f: str, g: str) -> str:
    """A property function `equiv_f_g` asserting `f(x) == g(x)` on `f`'s parameters, under `f`'s
    `Requires` when it has any (`g` should agree wherever `f` is specified)."""
    fns = {n.name: n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef)}
    for name in (f, g):
        if name not in fns:
            raise ValueError(f"no top-level function `{name}`")
    fn = fns[f]
    params = _params(fn)
    sig = ", ".join(f"{n}: {a}" if a else n for n, a in params)
    args = ", ".join(n for n, _ in params)
    requires = [ast.unparse(s.value.args[0]) for s in _strip_docstring(fn.body)
                if _marker(s) in ("Requires", "Assume") and s.value.args]
    check = f"assert {f}({args}) == {g}({args})"
    body = (f"    if {' and '.join(f'({r})' for r in requires)}:\n        {check}\n" if requires
            else f"    {check}\n")
    return f"\n\ndef equiv_{f}_{g}({sig}):\n{body}"
