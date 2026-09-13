"""Annotation counts and the human-readable / JSON output formats for an `InferResult`."""

from __future__ import annotations

from collections import defaultdict

from .records import MODULE_SCOPE, InferResult, VarInfo


def count_annotations(result: InferResult, *, include_any: bool = True) -> dict[str, int]:
    """How many annotations the engine produced per dimension — the ones the annotated source
    actually injects for the same `include_any` setting."""
    def wanted(t: str | None) -> bool:
        return bool(t) and (include_any or t != "Any")
    return {
        "params": sum(1 for f in result.functions for t in f.params.values() if wanted(t)),
        "returns": sum(1 for f in result.functions if wanted(f.returns)),
        "variables": sum(1 for v in result.variables if wanted(v.type)),
        "fields": sum(1 for f in result.fields if wanted(f.type)),
    }


def format_stats_report(path: str, counts: dict[str, int], elapsed: float,
                        files: tuple[int, int] | None = None) -> str:
    """The `--report` summary: annotation counts per dimension and wall-clock time."""
    lines = ["TypeInfer Report", f"Path: {path}"]
    if files is not None:
        lines.append(f"Files annotated: {files[0]}/{files[1]}")
    lines += [
        f"Function Parameter Types: {counts['params']}",
        f"Function Return Types: {counts['returns']}",
        f"Local Variable Types: {counts['variables']}",
        f"Class Field Types: {counts['fields']}",
        f"Total Annotations: {sum(counts.values())}",
        f"Time Taken: {elapsed:.3f}s",
    ]
    return "\n".join(lines)


def to_json_obj(result: InferResult, path: str | None = None) -> dict:
    obj: dict = {}
    if path is not None:
        obj["file"] = path
    obj["functions"] = [
        {"name": f.qualname, "params": f.params, "returns": f.returns} for f in result.functions
    ]
    obj["variables"] = [
        {"name": v.name, "scope": v.scope or MODULE_SCOPE, "type": v.type} for v in result.variables
    ]
    obj["fields"] = [{"class": f.cls, "name": f.name, "type": f.type} for f in result.fields]
    return obj


def to_report(result: InferResult, path: str | None = None) -> str:
    lines: list[str] = []
    if path:
        lines.append(f"Type inference for {path}")
        lines.append("=" * len(lines[-1]))
        lines.append("")

    if result.functions:
        lines.append("Functions")
        for f in result.functions:
            sig = ", ".join(f"{n}: {t}" for n, t in f.params.items())
            ret = f" -> {f.returns}" if f.returns else ""
            lines.append(f"  {f.qualname}({sig}){ret}")
        lines.append("")

    if result.fields:
        lines.append("Class fields")
        for f in result.fields:
            lines.append(f"  {f.cls}.{f.name}: {f.type}")
        lines.append("")

    if result.variables:
        lines.append("Variables")
        by_scope: dict[str, list[VarInfo]] = defaultdict(list)
        for v in result.variables:
            by_scope[v.scope or MODULE_SCOPE].append(v)
        for scope in sorted(by_scope, key=lambda s: (s != MODULE_SCOPE, s)):
            lines.append(f"  [{scope}]")
            for v in by_scope[scope]:
                lines.append(f"    {v.name}: {v.type}")
        lines.append("")

    if not (result.functions or result.fields or result.variables):
        lines.append("(no types inferred)")
    return "\n".join(lines).rstrip()
