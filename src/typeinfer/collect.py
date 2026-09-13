"""Walk a type-stamped AST into scope-keyed `InferResult` records.

The engine stamps each assignment target / parameter / class field with a `_ty` (or `_bench_ty`)
annotation node and each function with a return-type stamp (`_ret_ty` / `_bench_ret_ty` /
`_ret_float`); `collect_types` turns that stamped AST into the records the formatters read."""

from __future__ import annotations

from .records import FieldInfo, FuncInfo, InferResult, VarInfo, _base, _display_name
from .render import render_pytype


def _ann_of(node: dict):
    return node.get("_ty") or node.get("_bench_ty")


def collect_types(stamped: dict) -> InferResult:
    """Walk a type-stamped AST into `InferResult`. Variables are first-write-wins within a scope
    (the type at the point a name is introduced), matching how the annotated source reads."""
    res = InferResult()
    seen_var: set[tuple[str, str]] = set()

    def add_var(raw: str, ann, scope: str) -> None:
        t = render_pytype(ann)
        if not t:
            return
        display = _display_name(raw)
        key = (scope, display)
        if key in seen_var:
            return
        seen_var.add(key)
        res.variables.append(VarInfo(display, t, scope, _base(raw)))

    def collect_target(t, scope: str, cls: str | None) -> None:
        if not isinstance(t, dict):
            return
        nt = t.get("node_type")
        if nt == "Name":
            add_var(t.get("id") or "", _ann_of(t), scope)
        elif nt == "Attribute":
            ann = _ann_of(t)
            v = t.get("value")
            base_id = v.get("id") if isinstance(v, dict) else None
            if ann and base_id == "self" and cls and t.get("attr"):
                res.fields.append(FieldInfo(cls, t["attr"], render_pytype(ann) or "Any"))
        elif nt == "Starred":
            collect_target(t.get("value"), scope, cls)
        elif nt in ("Tuple", "List"):
            for e in t.get("elts", []):
                collect_target(e, scope, cls)

    def walk(o, scope: str, cls: str | None) -> None:
        if isinstance(o, dict):
            nt = o.get("node_type")
            if nt in ("FunctionDef", "AsyncFunctionDef"):
                qual = (scope + "." if scope else "") + _base(o.get("name") or "")
                info = FuncInfo(qual)
                for a in o.get("args", {}).get("args", []):
                    pname = _base(a.get("arg") or "")
                    if pname in ("self", "cls"):
                        continue
                    t = render_pytype(_ann_of(a))
                    if t:
                        info.params[pname] = t
                if o.get("_ret_float") is True:
                    info.returns = "float"
                else:
                    info.returns = render_pytype(o.get("_ret_ty") or o.get("_bench_ret_ty"))
                res.functions.append(info)
                for v in o.values():
                    walk(v, qual, cls)  # a nested def/var is scoped under this function
                return
            if nt == "ClassDef":
                name = (scope + "." if scope else "") + (o.get("name") or "")
                for f in o.get("fields", []):
                    if not isinstance(f, dict) or not f.get("name"):
                        continue
                    ann = _ann_of(f) or f.get("annotation")
                    t = render_pytype(ann) if isinstance(ann, dict) else None
                    if t:
                        res.fields.append(FieldInfo(name, f["name"], t))
                for v in o.values():
                    walk(v, name, name)
                return
            if nt in ("Assign", "AnnAssign", "AugAssign", "For"):
                collect_target(o.get("target"), scope, cls)
                for tg in o.get("targets", []):
                    collect_target(tg, scope, cls)
            for v in o.values():
                walk(v, scope, cls)
        elif isinstance(o, list):
            for v in o:
                walk(v, scope, cls)

    walk(stamped, "", None)
    # De-dup fields (a field can be stamped both class-level and in __init__); keep the first.
    seen_field: set[tuple[str, str]] = set()
    deduped = []
    for f in res.fields:
        if (f.cls, f.name) not in seen_field:
            seen_field.add((f.cls, f.name))
            deduped.append(f)
    res.fields = deduped
    return res
