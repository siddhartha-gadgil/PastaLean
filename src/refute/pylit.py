"""`PyLit` on the Python side: the JSON value shape shared with `PastaLean/PyVerify/Refute/PyLit.lean`.

Every finite float is dyadic (`as_integer_ratio` has a power-of-two denominator), so `float k e` is exact
in CPython, in Lean's `Float` and in `ℚ`.
"""

from __future__ import annotations

import math
import struct


def encode(v):
    """A Python value as a `PyLit` JSON object."""
    if v is None:
        return {"none": None}
    if isinstance(v, bool):
        return {"bool": v}
    if isinstance(v, int):
        return {"int": v}
    if isinstance(v, float):
        if not math.isfinite(v) or (v == 0 and math.copysign(1.0, v) < 0):
            return {"double": struct.unpack("<Q", struct.pack("<d", v))[0]}
        k, d = v.as_integer_ratio()
        return {"float": [k, d.bit_length() - 1]}
    if isinstance(v, str):
        return {"str": v}
    if isinstance(v, list):
        return {"list": [encode(x) for x in v]}
    if isinstance(v, tuple):
        return {"tuple": [encode(x) for x in v]}
    if isinstance(v, dict):
        return {"dict": [[encode(k), encode(x)] for k, x in v.items()]}
    if isinstance(v, (set, frozenset)):
        return {"set": [encode(x) for x in v]}
    if hasattr(v, "__dict__"):
        return {"obj": {"cls": type(v).__name__, "fields": {k: encode(x) for k, x in vars(v).items()}}}
    raise TypeError(f"no PyLit for {type(v).__name__}")


def decode(lit, classes=None):
    """A `PyLit` JSON object as a Python value (`classes` resolves `obj` by name)."""
    (tag, v), = lit.items()
    if tag == "none":
        return None
    if tag in ("int", "bool", "str"):
        return v
    if tag == "float":
        return math.ldexp(v[0], -v[1])
    if tag == "rat":
        return v[0] / v[1]
    if tag == "double":
        return struct.unpack("<d", struct.pack("<Q", v))[0]
    if tag == "list":
        return [decode(x, classes) for x in v]
    if tag == "tuple":
        return tuple(decode(x, classes) for x in v)
    if tag == "dict":
        return {decode(k, classes): decode(x, classes) for k, x in v}
    if tag == "set":
        return {decode(x, classes) for x in v}
    if tag == "obj":
        cls = (classes or {}).get(v["cls"])
        if cls is None:
            raise KeyError(f"unknown class {v['cls']}")
        o = object.__new__(cls)
        o.__dict__.update({k: decode(x, classes) for k, x in v["fields"].items()})
        return o
    if tag == "exc":
        raise ValueError("an exception is a result, not an input")
    raise ValueError(f"unknown PyLit tag {tag}")


def py_repr(lit) -> str:
    """How a `PyLit` reads as Python source (a class instance as `Cls(field=…)`, no class needed)."""
    (tag, v), = lit.items()
    if tag == "obj":
        return f"{v['cls']}(" + ", ".join(f"{k}={py_repr(x)}" for k, x in v["fields"].items()) + ")"
    if tag == "list":
        return "[" + ", ".join(py_repr(x) for x in v) + "]"
    if tag == "tuple":
        return "(" + ", ".join(py_repr(x) for x in v) + ("," if len(v) == 1 else "") + ")"
    if tag == "dict":
        return "{" + ", ".join(f"{py_repr(k)}: {py_repr(x)}" for k, x in v) + "}"
    if tag == "set":
        return "{" + ", ".join(py_repr(x) for x in v) + "}" if v else "set()"
    try:
        return repr(decode(lit))
    except Exception:  # noqa: BLE001
        return str(lit)
