"""Python-AST facts shared by the translator (`transpile/driver.py`) and `pastalean refute`.

Dependency-free on purpose: `refute` imports it without loading the translator package.
"""

from __future__ import annotations

import ast
from collections import Counter

CONTRACT_MODULES = {"icontract", "deal"}


def is_contract_decorator(d: ast.expr, imported: set[str]) -> bool:
    """`@icontract.require(...)` / `@deal.pre(...)`, or a bare name imported from those modules."""
    if not isinstance(d, ast.Call):
        return False
    f = d.func
    if isinstance(f, ast.Attribute):
        return isinstance(f.value, ast.Name) and f.value.id in CONTRACT_MODULES
    return isinstance(f, ast.Name) and f.id in imported


def strip_contract_decorators(tree: ast.AST) -> None:
    """Remove icontract/deal contract decorators (`@require(lambda x: ...)`, `@icontract.ensure(...)`):
    they are specifications, which `pastalean refute` reads from the source, not code to translate."""
    imported = {a.asname or a.name for n in ast.walk(tree)
                if isinstance(n, ast.ImportFrom) and n.module in CONTRACT_MODULES for a in n.names}
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            n.decorator_list = [d for d in n.decorator_list if not is_contract_decorator(d, imported)]


def _loads(tree: ast.AST) -> Counter:
    return Counter(n.id for n in ast.walk(tree) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load))


def called_functions(module: ast.Module) -> set[str]:
    """The top-level functions the rest of the module refers to: a property-shaped one
    (`def check(x): assert …`) is then a helper to run, not a theorem to state."""
    total = _loads(module)
    return {fn.name for fn in module.body
            if isinstance(fn, ast.FunctionDef) and total[fn.name] > _loads(fn)[fn.name]}
