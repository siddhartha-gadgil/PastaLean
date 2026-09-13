"""Project configuration for `pastalean typeinfer`, read from `[tool.typeinfer]` in pyproject.toml.

`load_config` walks up from a start path to the nearest pyproject.toml carrying a `[tool.typeinfer]`
table and returns its keys. CLI flags override whatever the config sets. Recognised keys mirror the
flags: `format`, `fail-under`, `no-any`, `include`, `exclude`, `output`."""

from __future__ import annotations

import tomllib
from pathlib import Path

# key -> (attr on argparse namespace, coercion). Hyphens in the TOML key map to underscores.
_KEYS = {
    "format": ("format", str),
    "fail-under": ("fail_under", float),
    "no-any": ("no_any", bool),
    "output": ("output", str),
    "include": ("include", list),
    "exclude": ("exclude", list),
}


def find_config(start: Path) -> Path | None:
    """The nearest pyproject.toml at or above `start` that has a `[tool.typeinfer]` table."""
    start = start.resolve()
    for d in [start, *start.parents] if start.is_dir() else [start.parent, *start.parent.parents]:
        cand = d / "pyproject.toml"
        if cand.is_file():
            try:
                data = tomllib.loads(cand.read_text(encoding="utf-8"))
            except (OSError, tomllib.TOMLDecodeError):
                continue
            if isinstance(data.get("tool", {}).get("typeinfer"), dict):
                return cand
    return None


def load_config(start: Path) -> dict:
    """The `[tool.typeinfer]` table nearest `start`, normalised to argparse-attr keys; `{}` if none."""
    cfg = find_config(start)
    if cfg is None:
        return {}
    data = tomllib.loads(cfg.read_text(encoding="utf-8"))
    table = data.get("tool", {}).get("typeinfer", {})
    out: dict = {}
    for key, (attr, coerce) in _KEYS.items():
        if key in table:
            out[attr] = coerce(table[key])
    return out
