"""Render a TypeInfer `_ty` annotation node into a Python type string.

The engine stamps each slot with an annotation node (`{"node_type": "Name", "id": "Int"}`,
`Subscript` for containers, `Tuple`, ...). `render_pytype` maps one such node to the Python type a
user expects to read (`list[int]`, `Optional[str]`, `Callable`, `Any`).
"""

from __future__ import annotations

# Lean runtime type names -> the Python type a user expects to read.
_SCALAR_PY = {
    "Int": "int", "Nat": "int", "int": "int",
    "String": "str", "Char": "str", "str": "str",
    "Bool": "bool", "bool": "bool",
    "Float": "float", "Rat": "float", "Real": "float", "float": "float", "complex": "complex",
    "None": "None", "NoneType": "None", "Nonetype": "None", "Unit": "None",
    "bytes": "bytes",
}
_CONTAINER_PY = {
    "List": "list", "list": "list",
    "Dict": "dict", "dict": "dict", "Std.HashMap": "dict",
    "PyDefaultDict": "defaultdict", "Counter": "Counter",
    "Set": "set", "set": "set", "frozenset": "frozenset",
    "Tuple": "tuple", "tuple": "tuple",
    "deque": "deque",
}


def render_pytype(node) -> str | None:
    """A TypeInfer `_ty` annotation node -> a Python type string, or None when it carries no
    information (an un-inferred `PyAny` reads as `Any`; a truly empty node is None)."""
    if not isinstance(node, dict):
        return None
    nt = node.get("node_type")
    if nt == "Name":
        rid = node.get("id")
        if not rid:
            return None
        if rid in ("PyAny", "Any"):
            return "Any"
        if rid in ("Callable", "callable", "function"):
            return "Callable"
        if rid in _SCALAR_PY:
            return _SCALAR_PY[rid]
        if rid in _CONTAINER_PY:
            return _CONTAINER_PY[rid]
        return rid.split(".")[-1]  # a user class name (strip any namespace)
    if nt == "Constant":
        return "None" if node.get("value") is None else None
    if nt == "Attribute":
        return node.get("attr")
    if nt == "Tuple":
        parts = [render_pytype(e) or "Any" for e in node.get("elts", [])]
        return "tuple[" + ", ".join(parts) + "]" if parts else "tuple"
    if nt == "Subscript":
        base = node.get("value")
        sl = node.get("slice")
        bid = base.get("id") if isinstance(base, dict) else None
        if bid in ("Optional", "Option"):
            return f"Optional[{render_pytype(sl) or 'Any'}]"
        base_str = render_pytype(base) or (bid.split(".")[-1] if bid else None)
        if base_str is None:
            return None
        if isinstance(sl, dict) and sl.get("node_type") == "Tuple":
            args = ", ".join(render_pytype(e) or "Any" for e in sl.get("elts", []))
        else:
            args = render_pytype(sl) or "Any"
        return f"{base_str}[{args}]"
    return None
