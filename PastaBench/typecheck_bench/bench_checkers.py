#!/usr/bin/env python3
"""Head-to-head TYPE CHECKING: PastaLean vs the production checkers (mypy, pyright, pyrefly, ty,
zuban) on the same seeded-error corpus.

Scored differentially, which is what makes the comparison fair across tools that check wildly
different amounts of Python. `mutate.py` writes each mutant beside an untouched copy of its
original (a mutation never changes line numbers), and a tool is credited with a CATCH when the
mutant has a diagnostic — keyed by `(line, rule)` — that its original does not. Errors the tool
reports anyway cancel out without making the file's mutants uncatchable, so a stricter tool is not
penalised on recall for its strictness.

Two numbers per tool:

  * **caught**              — seeded errors detected, the recall side.
  * **errors on originals** — distinct original files the tool reports any error on. The corpus is
    meant to be well-typed, but this counts strictness (e.g. `Optional` narrowing) as well as bugs,
    so it is not a false-positive rate.

    uv run PastaBench/typecheck_bench/mutate.py example_scripts -o /tmp/tcbench
    uv run PastaBench/typecheck_bench/bench_checkers.py /tmp/tcbench
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

VENV_BIN = Path(__file__).resolve().parents[2] / ".venv" / "bin"
# (file, line, rule) from each text format. mypy / zuban: `path:line[:col]: error: msg  [rule]`;
# ty concise: `path:line:col: error[rule] msg`; pyrefly min-text: `ERROR path:line:col-[line:]col: msg [rule]`.
LINE_RES = (
    re.compile(r"^(?P<f>[^\s:][^:]*\.py):(?P<l>\d+)(?::\d+)?: error: .*?(?:\[(?P<r>[\w-]+)\])?$"),
    re.compile(r"^(?P<f>[^\s:][^:]*\.py):(?P<l>\d+):\d+: error\[(?P<r>[\w-]+)\]"),
    re.compile(r"^ERROR (?P<f>[^\s:][^:]*\.py):(?P<l>\d+):\d+(?:-\d+(?::\d+)?)?: .*?(?:\[(?P<r>[\w-]+)\])?$"),
)

Diags = dict[str, set[tuple[int, str]]]


def _exe(name: str) -> str | None:
    cand = VENV_BIN / name
    if cand.exists():
        return str(cand)
    from shutil import which
    return which(name)


def _run(cmd: list[str], cwd: Path) -> str:
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=1800)
    except (subprocess.TimeoutExpired, OSError):
        return ""
    return p.stdout + "\n" + p.stderr


def _from_lines(out: str, root: Path) -> Diags:
    hits: Diags = {}
    for line in out.splitlines():
        for rx in LINE_RES:
            m = rx.match(line.strip())
            if m:
                hits.setdefault(Path(m["f"]).name, set()).add((int(m["l"]), m["r"] or ""))
                break
    return hits


def run_mypy(exe: str, d: Path) -> Diags:
    return _from_lines(_run([exe, "--no-error-summary", "--ignore-missing-imports",
                             "--no-incremental", "--cache-dir", "/dev/null", "."], d), d)


def run_zuban(exe: str, d: Path) -> Diags:
    return _from_lines(_run([exe, "check", "--no-error-summary", "--ignore-missing-imports", "."], d), d)


def run_ty(exe: str, d: Path) -> Diags:
    return _from_lines(_run([exe, "check", "--output-format", "concise", "."], d), d)


def run_pyrefly(exe: str, d: Path) -> Diags:
    # Without a config pyrefly silently checks nothing, so drop a minimal one into the corpus dir.
    (d / "pyrefly.toml").write_text('project-includes = ["**/*.py"]\n', encoding="utf-8")
    return _from_lines(_run([exe, "check", "--output-format=min-text"], d), d)


def run_pyright(exe: str, d: Path) -> Diags:
    out = _run([exe, "--outputjson", "."], d)
    try:
        doc = json.loads(out[out.index("{"):out.rindex("}") + 1])
    except ValueError:
        return {}
    hits: Diags = {}
    for g in doc.get("generalDiagnostics", []):
        if g.get("severity") == "error":
            hits.setdefault(Path(g["file"]).name, set()).add(
                (g["range"]["start"]["line"] + 1, g.get("rule", "")))
    return hits


def run_pastalean(_exe: str, d: Path) -> Diags:
    from pastalean.typeinfer.check import check_dir
    hits: Diags = {}
    for f, diag in check_dir(d):
        hits.setdefault(Path(f).name, set()).add((diag.get("line", 0), diag.get("kind", "")))
    return hits


TOOLS = [
    ("pastalean", "typeinfer", run_pastalean),
    ("mypy", "mypy", run_mypy),
    ("pyright", "pyright", run_pyright),
    ("pyrefly", "pyrefly", run_pyrefly),
    ("ty", "ty", run_ty),
    ("zuban", "zuban", run_zuban),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("bench", type=Path, help="the directory `mutate.py -o` wrote (orig/ + mut/)")
    ap.add_argument("--tools", default=None, help="comma-separated subset of the tool names")
    ap.add_argument("--out", type=Path, default=None,
                    help="write the per-mutant catch set as JSON. Without it a regression is a moved "
                         "percentage; with it, the mutants a tool stopped catching are named.")
    args = ap.parse_args()

    manifest = json.loads((args.bench / "manifest.json").read_text())
    ids = [m["id"] + ".py" for m in manifest]
    source_of = {m["id"] + ".py": m["source"] for m in manifest}
    n_sources = len(set(source_of.values()))
    wanted = set(args.tools.split(",")) if args.tools else None

    rows = []
    for name, binary, runner in TOOLS:
        if wanted and name not in wanted:
            continue
        exe = _exe(binary) if name != "pastalean" else "-"
        if exe is None:
            print(f"  (skipping {name}: not installed)", file=sys.stderr)
            continue
        t0 = time.perf_counter()
        clean = runner(exe, args.bench / "orig")
        mutant = runner(exe, args.bench / "mut")
        elapsed = time.perf_counter() - t0
        # Differential: credit only a diagnostic the seeding introduced, never pre-existing noise
        # the tool reports on the untouched original anyway.
        per_mutant = {i: bool(mutant.get(i, set()) - clean.get(i, set())) for i in ids}
        caught = sum(per_mutant.values())
        flagged = len({source_of[i] for i in ids if clean.get(i)})
        rows.append((name, caught, flagged, elapsed, per_mutant))
        print(f"  {name}: {caught}/{len(ids)} caught, {flagged}/{n_sources} originals with errors "
              f"({elapsed:.1f}s)", file=sys.stderr)

    n = len(ids)
    print(f"\n{n} seeded type errors (mutants of {len({m['source'] for m in manifest})} known-good "
          f"files); caught = the mutant has a (line, rule) diagnostic its original does not\n")
    print(f"| {'Tool':<10} | {'Caught':>13} | {'Errors on originals':>19} | {'Time':>7} |")
    print(f"|{'-' * 12}|{'-' * 15}|{'-' * 21}|{'-' * 9}|")
    for name, caught, flagged, elapsed, _per in sorted(rows, key=lambda r: -r[1]):
        print(f"| {name:<10} | {caught:>5} ({100 * caught / n:4.1f}%) | "
              f"{flagged:>3}/{n_sources} ({100 * flagged / n_sources:4.1f}%) | {elapsed:6.1f}s |")

    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(
            {"mutants": n,
             "sources": len({m["source"] for m in manifest}),
             "tools": {name: {"caught": caught, "originals_with_errors": clean,
                              "seconds": round(elapsed, 2), "per_mutant": per}
                       for name, caught, clean, elapsed, per in rows}}, indent=2), encoding="utf-8")
        print(f"\nper-mutant results -> {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
