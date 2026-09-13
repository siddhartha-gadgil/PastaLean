"""The scope-keyed records `collect_types` produces, plus SSA-name helpers.

TypeInfer versions a variable on each type change (`total`, `total₀`, `total'v1`); `_base` strips
that back to the original Python identifier (for matching the untouched source) and `_display_name`
renders it as a distinct readable name (`total₀` -> `total__0`)."""

from __future__ import annotations

from dataclasses import dataclass, field

MODULE_SCOPE = "<module>"


@dataclass
class FuncInfo:
    qualname: str
    params: dict[str, str] = field(default_factory=dict)
    returns: str | None = None


@dataclass
class VarInfo:
    name: str          # display name (SSA version rendered as `__N`)
    type: str
    scope: str
    base: str = ""     # the original Python identifier, for matching the untouched source


@dataclass
class FieldInfo:
    cls: str
    name: str
    type: str


@dataclass
class InferResult:
    functions: list[FuncInfo] = field(default_factory=list)
    variables: list[VarInfo] = field(default_factory=list)
    fields: list[FieldInfo] = field(default_factory=list)


_SUBSCRIPTS = "₀₁₂₃₄₅₆₇₈₉"
_SUB_TO_ASCII = str.maketrans(_SUBSCRIPTS, "0123456789")


def _base(name: str) -> str:
    """Strip TypeInfer's SSA version suffix (`total'v1`, `total₀` -> `total`) so a name aligns with
    the original Python identifier — used to match the untouched source."""
    if not isinstance(name, str):
        return name
    return name.split("'")[0].rstrip(_SUBSCRIPTS)


def _display_name(name: str) -> str:
    """A readable display name: the SSA subscript version suffix becomes ASCII `__N` (`total₀` ->
    `total__0`), so distinct type-versions of one Python variable stay visible and distinct."""
    if not isinstance(name, str):
        return name
    name = name.split("'")[0]
    i = len(name)
    while i > 0 and name[i - 1] in _SUBSCRIPTS:
        i -= 1
    return name[:i] + "__" + name[i:].translate(_SUB_TO_ASCII) if i < len(name) else name
