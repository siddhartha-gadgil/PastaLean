#!/usr/bin/env python3
"""Run the `checkTypes` task over a corpus and report the verdict per file.

Two modes, because a checker is only as good as BOTH its numbers:

  * `--expect clean`  — every file is known-good, so any diagnostic is a FALSE POSITIVE. Run this
    over `example_scripts/`; the rate must stay at zero.
  * `--expect error`  — every file has a seeded type error (`typecheck_bench/negative/`), so a file
    with no diagnostic is a MISS. This is the recall side.

    uv run PastaBench/typecheck_bench/check_corpus.py example_scripts --expect clean
    uv run PastaBench/typecheck_bench/check_corpus.py PastaBench/typecheck_bench/negative --expect error
"""
from __future__ import annotations
import argparse, json, subprocess, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from pastalean.transpile import driver  # noqa: E402
from pastalean import paths  # noqa: E402

EXE = str(paths.REPO_ROOT / ".lake" / "build" / "bin" / "typeinfer")


def raw_ir(py: Path):
    try:
        return json.loads(driver.translate_to_json(py.read_text(encoding="utf-8", errors="replace"),
                                                   str(py), best_effort=True, infer_only=True,
                                                   resolve_imports=False))
    except Exception:  # noqa: BLE001
        return None


def check(ast: dict) -> dict:
    proc = subprocess.run([EXE, json.dumps({"task": "checkTypes", "ast": ast})],
                          capture_output=True, text=True, timeout=180)
    try:
        return json.loads(proc.stdout.splitlines()[0])
    except Exception:  # noqa: BLE001
        return {}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus", type=Path)
    ap.add_argument("--expect", choices=("clean", "error"), default="clean")
    ap.add_argument("--show", type=int, default=20, help="how many offending files to print")
    args = ap.parse_args()

    files = sorted(args.corpus.rglob("*.py")) if args.corpus.is_dir() else [args.corpus]
    scanned = wrong = 0
    shown = []
    for py in files:
        ir = raw_ir(py)
        if ir is None:
            continue
        res = check(ir)
        if not res.get("result"):
            continue
        scanned += 1
        diags = res.get("diagnostics", [])
        bad = bool(diags) if args.expect == "clean" else not diags
        if bad:
            wrong += 1
            if len(shown) < args.show:
                msg = diags[0]["message"] if diags else "no diagnostic"
                shown.append(f"  {py.relative_to(args.corpus) if args.corpus.is_dir() else py}: {msg}")

    label = "false positives" if args.expect == "clean" else "missed seeded errors"
    for line in shown:
        print(line)
    rate = wrong / scanned if scanned else 0.0
    print(f"\n{scanned} files scanned — {wrong} {label} ({rate:.1%})")
    return 1 if wrong else 0


if __name__ == "__main__":
    sys.exit(main())
