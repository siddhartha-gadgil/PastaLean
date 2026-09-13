"""Type-coverage measurement, à la a production checker's `--stats`.

`iter_slots` walks the *source* AST and, for every annotatable position (a parameter, a return, a
module/local variable, a class field), resolves it to one of three states: it already carries an
annotation in the source, the engine inferred a concrete type for it, or it is unresolved (no
annotation and either no inference or a bare `Any`). `coverage` tallies those into a per-dimension
report and an overall ratio; the CLI's `--check` / `--fail-under` gate on that ratio."""

from __future__ import annotations

import ast as _ast
from collections import defaultdict
from dataclasses import dataclass

from .records import InferResult

DIMENSIONS = ("params", "returns", "variables", "fields")


@dataclass
class Slot:
    kind: str          # one of DIMENSIONS (singular sense: "params" for a parameter slot)
    qualname: str      # dotted owner: function qual for a param/return/var scope, class for a field
    name: str          # parameter/variable/field name; "" for a return slot
    line: int
    col: int
    existing: str | None   # the annotation already present in the source, if any
    inferred: str | None   # the engine's inferred type, if any

    @property
    def resolved(self) -> str | None:
        """The type the slot ends up carrying: an existing source annotation wins over inference."""
        return self.existing or self.inferred

    @property
    def typed(self) -> bool:
        """Whether the slot has a concrete type (a bare `Any` does not count as typed)."""
        t = self.resolved
        return bool(t) and t != "Any"


def iter_slots(source: str, result: InferResult) -> list[Slot]:
    """Every annotatable slot in `source`, each resolved against the engine's `result`."""
    tree = _ast.parse(source)
    func_by_qual = {f.qualname: f for f in result.functions}
    var_by_scope: dict[str, dict[str, str]] = defaultdict(dict)
    for v in result.variables:
        var_by_scope[v.scope].setdefault(v.base or v.name, v.type)
    field_by_cls: dict[str, dict[str, str]] = defaultdict(dict)
    for f in result.fields:
        field_by_cls[f.cls].setdefault(f.name, f.type)

    slots: list[Slot] = []
    scope: list[str] = []
    seen_var: set[tuple[str, str]] = set()

    def qual() -> str:
        return ".".join(scope)

    def existing_ann(node) -> str | None:
        ann = getattr(node, "annotation", None)
        return _ast.unparse(ann) if ann is not None else None

    def visit(node: _ast.AST) -> None:
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            scope.append(node.name)
            info = func_by_qual.get(qual())
            for a in list(node.args.posonlyargs) + list(node.args.args) + list(node.args.kwonlyargs):
                if a.arg in ("self", "cls"):
                    continue
                slots.append(Slot("params", qual(), a.arg, a.lineno, a.col_offset,
                                  existing_ann(a), (info.params.get(a.arg) if info else None)))
            slots.append(Slot("returns", qual(), "", node.lineno, node.col_offset,
                              _ast.unparse(node.returns) if node.returns is not None else None,
                              (info.returns if info else None)))
            for child in node.body:
                visit(child)
            scope.pop()
            return
        if isinstance(node, _ast.ClassDef):
            scope.append(node.name)
            for child in node.body:
                visit(child)
            scope.pop()
            return
        if isinstance(node, _ast.AnnAssign) and isinstance(node.target, _ast.Attribute):
            tgt = node.target
            if isinstance(tgt.value, _ast.Name) and tgt.value.id == "self" and len(scope) >= 2:
                cls = ".".join(scope[:-1])
                slots.append(Slot("fields", cls, tgt.attr, node.lineno, node.col_offset,
                                  _ast.unparse(node.annotation), field_by_cls.get(cls, {}).get(tgt.attr)))
            return
        if isinstance(node, _ast.Assign) and len(node.targets) == 1:
            tgt = node.targets[0]
            if (isinstance(tgt, _ast.Attribute) and isinstance(tgt.value, _ast.Name)
                    and tgt.value.id == "self" and len(scope) >= 2):
                cls = ".".join(scope[:-1])
                if (cls, tgt.attr) not in seen_var:
                    seen_var.add((cls, tgt.attr))
                    slots.append(Slot("fields", cls, tgt.attr, node.lineno, node.col_offset,
                                      None, field_by_cls.get(cls, {}).get(tgt.attr)))
            elif isinstance(tgt, _ast.Name):
                key = (qual(), tgt.id)
                if key not in seen_var:
                    seen_var.add(key)
                    slots.append(Slot("variables", qual(), tgt.id, node.lineno, node.col_offset,
                                      None, var_by_scope.get(qual(), {}).get(tgt.id)))
        for child in _ast.iter_child_nodes(node):
            visit(child)

    for stmt in tree.body:
        visit(stmt)
    return slots


def coverage(source: str, result: InferResult) -> dict:
    """Per-dimension and overall type coverage: for each dimension `{typed, total}` where a slot is
    `typed` when it carries a concrete (non-`Any`) type, plus an overall count and ratio."""
    slots = iter_slots(source, result)
    dims: dict[str, dict[str, int]] = {d: {"typed": 0, "total": 0} for d in DIMENSIONS}
    for s in slots:
        d = dims[s.kind]
        d["total"] += 1
        if s.typed:
            d["typed"] += 1
    typed = sum(d["typed"] for d in dims.values())
    total = sum(d["total"] for d in dims.values())
    return {
        "dimensions": dims,
        "typed": typed,
        "total": total,
        "coverage": (typed / total) if total else 1.0,
    }


def format_coverage_report(path: str, cov: dict) -> str:
    """Human-readable coverage summary, one line per dimension plus the overall percentage."""
    label = {"params": "Parameters", "returns": "Returns", "variables": "Variables", "fields": "Fields"}
    lines = ["Type coverage", f"Path: {path}"]
    for d in DIMENSIONS:
        c = cov["dimensions"][d]
        pct = (100.0 * c["typed"] / c["total"]) if c["total"] else 100.0
        lines.append(f"  {label[d]:<11} {c['typed']}/{c['total']} ({pct:.1f}%)")
    pct = 100.0 * cov["coverage"]
    lines.append(f"  {'Overall':<11} {cov['typed']}/{cov['total']} ({pct:.1f}%)")
    return "\n".join(lines)
