#!/usr/bin/env python3
"""Head-to-head TYPE CHECKING: PastaLean vs the production checkers (mypy, pyright, pyrefly, ty,
zuban) on the same seeded-error corpus.

Scored differentially, which is what makes the comparison fair across tools that check wildly
different amounts of Python. `mutate.py` writes each mutant beside an untouched copy of its
original, and a tool is credited with a CATCH only when it flags the mutant and does NOT flag the
original — an error it would have reported anyway (a missing import, a rule PastaLean does not
model) cancels out on both sides and earns nothing.

Two numbers per tool:

  * **caught**       — seeded errors detected, the recall side.
  * **flagged clean** — originals the tool errors on. These are known-good programs, so for
    PastaLean every one is a false positive; for the others it is mostly extra strictness rather
    than a bug, which is exactly why recall is scored differentially and not from this column.

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
# mypy / zuban / ty: `path:line[:col]: error: …`. pyrefly's min-text: `ERROR path:line:col-col: …`.
LINE_RES = (
    re.compile(r"^([^\s:][^:]*\.py):\d+(?::\d+)?: error"),
    re.compile(r"^ERROR ([^\s:][^:]*\.py):\d+:\d+(?:-\d+)?:"),
)


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


def _from_lines(out: str, root: Path) -> set[str]:
    hits = set()
    for line in out.splitlines():
        for rx in LINE_RES:
            m = rx.match(line.strip())
            if m:
                hits.add(Path(m.group(1)).name)
                break
    return hits


def run_mypy(exe: str, d: Path) -> set[str]:
    return _from_lines(_run([exe, "--no-error-summary", "--ignore-missing-imports",
                             "--no-incremental", "--cache-dir", "/dev/null", "."], d), d)


def run_zuban(exe: str, d: Path) -> set[str]:
    return _from_lines(_run([exe, "check", "--no-error-summary", "--ignore-missing-imports", "."], d), d)


def run_ty(exe: str, d: Path) -> set[str]:
    return _from_lines(_run([exe, "check", "--output-format", "concise", "."], d), d)


def run_pyrefly(exe: str, d: Path) -> set[str]:
    # Without a config pyrefly silently checks nothing, so drop a minimal one into the corpus dir.
    (d / "pyrefly.toml").write_text('project-includes = ["**/*.py"]\n', encoding="utf-8")
    return _from_lines(_run([exe, "check", "--output-format=min-text"], d), d)


def run_pyright(exe: str, d: Path) -> set[str]:
    out = _run([exe, "--outputjson", "."], d)
    try:
        doc = json.loads(out[out.index("{"):out.rindex("}") + 1])
    except ValueError:
        return set()
    return {Path(g["file"]).name for g in doc.get("generalDiagnostics", [])
            if g.get("severity") == "error"}


def run_pastalean(_exe: str, d: Path) -> set[str]:
    from pastalean.typeinfer.check import check_dir
    return {Path(f).name for f, _diag in check_dir(d)}


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
    args = ap.parse_args()

    manifest = json.loads((args.bench / "manifest.json").read_text())
    ids = [m["id"] + ".py" for m in manifest]
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
        caught = sum(1 for i in ids if i in mutant and i not in clean)
        rows.append((name, caught, len(clean & set(ids)), elapsed))
        print(f"  {name}: {caught}/{len(ids)} caught, {len(clean & set(ids))} clean flagged "
              f"({elapsed:.1f}s)", file=sys.stderr)

    n = len(ids)
    print(f"\n{n} seeded type errors (mutants of {len({m['source'] for m in manifest})} known-good "
          f"files); caught = flagged on the mutant and NOT on its original\n")
    print(f"| {'Tool':<10} | {'Caught':>13} | {'Flagged clean':>13} | {'Time':>7} |")
    print(f"|{'-' * 12}|{'-' * 15}|{'-' * 15}|{'-' * 9}|")
    for name, caught, clean, elapsed in sorted(rows, key=lambda r: -r[1]):
        print(f"| {name:<10} | {caught:>5} ({100 * caught / n:4.1f}%) | "
              f"{clean:>5} ({100 * clean / n:4.1f}%) | {elapsed:6.1f}s |")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
