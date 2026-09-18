#!/usr/bin/env python3
"""Seed type errors into a corpus of ANNOTATED Python, one mutant per seeded error.

A hand-written negative corpus measures a checker against the errors its author thought of. A
mutation corpus does not: every annotated parameter/return in the corpus is a candidate, the flip is
mechanical (`int` -> `str`, and back), and the same mutants are handed to every tool.

Each mutant is written next to a copy of its unmutated ORIGINAL under the same name, so a scoring
harness can require `flagged(mutant) and not flagged(original)` — a tool gets credit only for an
error the seeding introduced, never for pre-existing noise it would have reported anyway.

    uv run PastaBench/typecheck_bench/mutate.py example_scripts -o /tmp/tcbench --per-file 3
"""
from __future__ import annotations

import argparse
import ast
import json
from pathlib import Path

# The flip for each annotation we mutate. Chosen so the mutant is genuinely ill-typed wherever the
# slot is used at all: no Python type is both a `str` and an `int`, and neither supports the other's
# methods.
FLIP = {
    "int": "str", "float": "str", "bool": "str", "complex": "str",
    "str": "int",
    "list[int]": "str", "list[str]": "int", "List[int]": "str", "List[str]": "int",
    "list[float]": "str", "list[list[int]]": "str", "List[List[int]]": "str",
    "dict": "int", "set[int]": "str", "Set[int]": "str",
}


def _uses(name: str, fn: ast.AST) -> int:
    """How many times a parameter is READ in the body. A slot nothing reads cannot contradict its
    annotation, so mutating it would seed a non-error."""
    return sum(1 for n in ast.walk(fn)
               if isinstance(n, ast.Name) and n.id == name and isinstance(n.ctx, ast.Load))


def candidates(tree: ast.AST) -> list[tuple[ast.expr, str, str]]:
    """Every annotation worth flipping: `(node, original, replacement)`."""
    out = []
    for fn in ast.walk(tree):
        if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for a in fn.args.args + fn.args.posonlyargs + fn.args.kwonlyargs:
            if a.annotation is None or a.arg in ("self", "cls"):
                continue
            src = ast.unparse(a.annotation)
            if src in FLIP and _uses(a.arg, fn) > 0:
                out.append((a.annotation, src, FLIP[src]))
        if fn.returns is not None:
            src = ast.unparse(fn.returns)
            # A return annotation is only contradicted if the body actually returns a value.
            if src in FLIP and any(isinstance(n, ast.Return) and n.value is not None
                                   for n in ast.walk(fn)):
                out.append((fn.returns, src, FLIP[src]))
    return out


def _replace(source: str, node: ast.expr, new: str) -> str:
    lines = source.splitlines(keepends=True)
    starts = [0]
    for ln in lines:
        starts.append(starts[-1] + len(ln))
    a = starts[node.lineno - 1] + node.col_offset
    b = starts[node.end_lineno - 1] + node.end_col_offset
    return source[:a] + new + source[b:]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus", type=Path)
    ap.add_argument("-o", "--out", type=Path, required=True)
    ap.add_argument("--per-file", type=int, default=3, help="at most this many mutants per source file")
    args = ap.parse_args()

    orig_dir, mut_dir = args.out / "orig", args.out / "mut"
    for d in (orig_dir, mut_dir):
        d.mkdir(parents=True, exist_ok=True)
        for old in d.glob("*.py"):
            old.unlink()

    manifest = []
    files = sorted(args.corpus.rglob("*.py")) if args.corpus.is_dir() else [args.corpus]
    for py in files:
        source = py.read_text(encoding="utf-8")
        try:
            tree = ast.parse(source)
        except SyntaxError:
            continue
        for i, (node, old, new) in enumerate(candidates(tree)[: args.per_file]):
            ident = f"{py.stem}__{i}"
            (orig_dir / f"{ident}.py").write_text(source, encoding="utf-8")
            (mut_dir / f"{ident}.py").write_text(_replace(source, node, new), encoding="utf-8")
            manifest.append({"id": ident, "source": str(py), "line": node.lineno,
                             "from": old, "to": new})

    (args.out / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(f"{len(manifest)} mutants from {len(files)} files -> {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
