"""Generate a `.pyi` stub from the engine's inferences (à la `stubgen`).

Walks the source AST's public surface — top-level functions, classes (and their methods/fields), and
module-level variables — and emits a type stub carrying the inferred types. Function *bodies* are not
descended into (a stub has none); class bodies are, for methods and fields."""

from __future__ import annotations

import ast as _ast
from collections import defaultdict

from .annotate import _note_typing
from .records import InferResult


def to_stub(source: str, result: InferResult, *, include_any: bool = False) -> str:
    """A `.pyi` for `source`. `include_any` (default False, unlike the annotator) also writes bare
    `Any` slots; otherwise an un-inferred slot is left unannotated in the stub."""
    tree = _ast.parse(source)
    func_by_qual = {f.qualname: f for f in result.functions}
    var_by_scope: dict[str, dict[str, str]] = defaultdict(dict)
    for v in result.variables:
        var_by_scope[v.scope].setdefault(v.base or v.name, v.type)
    field_by_cls: dict[str, dict[str, str]] = defaultdict(dict)
    for f in result.fields:
        field_by_cls[f.cls].setdefault(f.name, f.type)

    used_typing: set[str] = set()

    def wanted(t: str | None) -> bool:
        return bool(t) and (include_any or t != "Any")

    def ann(t: str | None) -> str:
        if wanted(t):
            _note_typing(t, used_typing)
            return t
        return ""

    def func_lines(node, qual: str, indent: str) -> list[str]:
        info = func_by_qual.get(qual)
        prefix = "async def" if isinstance(node, _ast.AsyncFunctionDef) else "def"
        parts: list[str] = []
        args = node.args
        for a in list(args.posonlyargs) + list(args.args):
            t = a.annotation and _ast.unparse(a.annotation) or (info and info.params.get(a.arg))
            parts.append(f"{a.arg}: {t}" if a.arg not in ("self", "cls") and wanted(t) else a.arg)
        if args.vararg:
            parts.append("*" + args.vararg.arg)
        if args.kwarg:
            parts.append("**" + args.kwarg.arg)
        ret = node.returns and _ast.unparse(node.returns) or (info and info.returns)
        ret_s = f" -> {ann(ret)}" if wanted(ret) else ""
        return [f"{indent}{prefix} {node.name}({', '.join(parts)}){ret_s}: ..."]

    def class_lines(node: _ast.ClassDef, qual: str, indent: str) -> list[str]:
        bases = ", ".join(_ast.unparse(b) for b in node.bases)
        header = f"{indent}class {node.name}" + (f"({bases})" if bases else "") + ":"
        body: list[str] = []
        inner = indent + "    "
        seen: set[str] = set()
        for stmt in node.body:
            if isinstance(stmt, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
                body += func_lines(stmt, f"{qual}.{stmt.name}", inner)
            elif isinstance(stmt, _ast.ClassDef):
                body += class_lines(stmt, f"{qual}.{stmt.name}", inner)
        for name, t in field_by_cls.get(qual, {}).items():
            if name not in seen and wanted(t):
                seen.add(name)
                body.append(f"{inner}{name}: {ann(t)}")
        if not body:
            body = [f"{inner}..."]
        return [header, *body]

    out: list[str] = []
    for stmt in tree.body:
        if isinstance(stmt, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            out += func_lines(stmt, stmt.name, "")
        elif isinstance(stmt, _ast.ClassDef):
            out += class_lines(stmt, stmt.name, "")
        elif isinstance(stmt, _ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], _ast.Name):
            name = stmt.targets[0].id
            t = var_by_scope.get("", {}).get(name)
            if wanted(t):
                out.append(f"{name}: {ann(t)}")
        elif isinstance(stmt, _ast.AnnAssign) and isinstance(stmt.target, _ast.Name):
            out.append(f"{stmt.target.id}: {_ast.unparse(stmt.annotation)}")

    header: list[str] = []
    if used_typing:
        header.append("from typing import " + ", ".join(sorted(used_typing)))
        header.append("")
    return "\n".join(header + out) + "\n"
