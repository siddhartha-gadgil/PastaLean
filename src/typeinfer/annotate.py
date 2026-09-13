"""Inject the engine's inferred types back into Python source as PEP 484 annotations.

`annotate_source` re-parses the original with `ast` (which has the positions the IR lacks), matches
the engine's records by qualified name, and `ast.unparse`s the result. `annotate_repo` does the same
across a whole directory, writing the annotated tree to an output directory."""

from __future__ import annotations

import ast as _ast
import re
from collections import defaultdict
from pathlib import Path

from .engine import infer_repo_dir
from .records import InferResult
from .report import count_annotations


def _type_expr(type_str: str):
    """Parse a rendered type string into an AST annotation expression, falling back to a string
    literal for anything unparseable."""
    try:
        return _ast.parse(type_str, mode="eval").body
    except SyntaxError:
        return _ast.Constant(value=type_str)


_TYPING_NAMES = ("Any", "Optional", "Callable")


def _note_typing(type_str: str, used: set[str]) -> None:
    for name in _TYPING_NAMES:
        if re.search(rf"\b{name}\b", type_str):
            used.add(name)


def _ensure_typing_imports(tree: _ast.Module, used: set[str]) -> None:
    """Add `from typing import ...` for any Any/Optional/Callable the annotations reference and that
    isn't imported already (extending an existing typing import, or inserting a new one after the
    module docstring / `__future__` imports)."""
    if not used:
        return
    existing = None
    imported: set[str] = set()
    for stmt in tree.body:
        if isinstance(stmt, _ast.ImportFrom) and stmt.module == "typing":
            existing = stmt
            imported |= {a.name for a in stmt.names}
    missing = sorted(used - imported)
    if not missing:
        return
    if existing is not None:
        existing.names += [_ast.alias(name=n) for n in missing]
        return
    idx = 0
    if (tree.body and isinstance(tree.body[0], _ast.Expr)
            and isinstance(tree.body[0].value, _ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        idx = 1  # keep a module docstring first
    while (idx < len(tree.body) and isinstance(tree.body[idx], _ast.ImportFrom)
           and tree.body[idx].module == "__future__"):
        idx += 1
    tree.body.insert(idx, _ast.ImportFrom(module="typing",
                                          names=[_ast.alias(name=n) for n in missing], level=0))


def annotate_source(source: str, result: InferResult, *, include_any: bool = True) -> str:
    """Return `source` with the inferred types injected as PEP 484 annotations. Re-parses the
    original with `ast` (which has the positions the IR lacks) and matches the engine's records by
    qualified name, then `ast.unparse`s the result — so comments and exact spacing are not preserved,
    but the code is a faithful annotated view. `include_any` (default True) also stamps bare `Any`
    and adds the needed `from typing import Any`; `--no-any` sets it False."""
    tree = _ast.parse(source)
    func_by_qual = {f.qualname: f for f in result.functions}
    var_by_scope: dict[str, dict[str, str]] = defaultdict(dict)
    for v in result.variables:
        var_by_scope[v.scope].setdefault(v.base or v.name, v.type)
    field_by_cls: dict[str, dict[str, str]] = defaultdict(dict)
    for f in result.fields:
        field_by_cls[f.cls].setdefault(f.name, f.type)

    scope: list[str] = []  # enclosing def/class names -> the collector's qualname
    annotated_vars: set[tuple[str, str]] = set()
    used_typing: set[str] = set()

    def qual() -> str:
        return ".".join(scope)

    def wanted(t: str | None) -> bool:
        return bool(t) and (include_any or t != "Any")

    def expr(t: str):
        _note_typing(t, used_typing)
        return _type_expr(t)

    class Annotator(_ast.NodeTransformer):
        def visit_FunctionDef(self, node: _ast.FunctionDef):
            scope.append(node.name)
            info = func_by_qual.get(qual())
            if info:
                for a in list(node.args.posonlyargs) + list(node.args.args) + list(node.args.kwonlyargs):
                    t = info.params.get(a.arg)
                    if a.annotation is None and wanted(t):
                        a.annotation = expr(t)
                if node.returns is None and wanted(info.returns):
                    node.returns = expr(info.returns)
            self.generic_visit(node)
            scope.pop()
            return node

        visit_AsyncFunctionDef = visit_FunctionDef

        def visit_ClassDef(self, node: _ast.ClassDef):
            scope.append(node.name)
            self.generic_visit(node)
            scope.pop()
            return node

        def visit_Assign(self, node: _ast.Assign):
            self.generic_visit(node)
            if len(node.targets) != 1:
                return node
            tgt = node.targets[0]
            # `self.x = ...` inside a method -> annotate the field.
            if (isinstance(tgt, _ast.Attribute) and isinstance(tgt.value, _ast.Name)
                    and tgt.value.id == "self" and len(scope) >= 2):
                cls = ".".join(scope[:-1])
                t = field_by_cls.get(cls, {}).get(tgt.attr)
                if wanted(t):
                    return _ast.AnnAssign(target=tgt, annotation=expr(t), value=node.value, simple=0)
                return node
            if isinstance(tgt, _ast.Name):
                key = (qual(), tgt.id)
                if key in annotated_vars:
                    return node
                t = var_by_scope.get(qual(), {}).get(tgt.id)
                if wanted(t):
                    annotated_vars.add(key)
                    return _ast.AnnAssign(target=tgt, annotation=expr(t), value=node.value, simple=1)
            return node

    Annotator().visit(tree)
    _ensure_typing_imports(tree, used_typing)
    _ast.fix_missing_locations(tree)
    return _ast.unparse(tree)


def annotate_repo(repo: Path, out_dir: Path, *, include_any: bool = True,
                  jobs: int | None = None) -> tuple[int, int, dict[str, int]]:
    """Copy `repo` to `out_dir` and overwrite each `.py` with its inferred-type-annotated version.
    Returns (files_annotated, total_repo_files, aggregate annotation counts)."""
    import shutil

    inferred = infer_repo_dir(repo, jobs=jobs)
    if out_dir.resolve() != repo.resolve():
        if out_dir.exists():
            shutil.rmtree(out_dir)
        shutil.copytree(repo, out_dir)
    n_files = 0
    totals = {"params": 0, "returns": 0, "variables": 0, "fields": 0}
    for _dotted, (src, result) in inferred.items():
        rel = src.relative_to(repo)
        try:
            annotated = annotate_source(src.read_text(encoding="utf-8"), result, include_any=include_any)
            (out_dir / rel).write_text(annotated, encoding="utf-8")
            n_files += 1
            for k, v in count_annotations(result, include_any=include_any).items():
                totals[k] += v
        except (SyntaxError, OSError):  # noqa: PERF203
            continue
    return n_files, len(inferred), totals
