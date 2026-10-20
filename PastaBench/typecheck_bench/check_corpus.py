#!/usr/bin/env python3
"""Run the checker over a corpus and report the verdict per file — and keep the certificates.

Two modes, because a checker is only as good as BOTH its numbers:

  * `--expect clean`  — every file is known-good, so any diagnostic is a FALSE POSITIVE. Run this
    over `example_scripts/`; the rate must stay at zero.
  * `--expect error`  — every file has a seeded type error (`typecheck_bench/negative/`), so a file
    with no diagnostic is a MISS. This is the recall side.

    uv run PastaBench/typecheck_bench/check_corpus.py example_scripts --expect clean
    uv run PastaBench/typecheck_bench/check_corpus.py PastaBench/typecheck_bench/negative --expect error

With `--certs DIR` every verdict is written out with the CERTIFICATE behind it — the slots judged,
the evidence weighed, the verdict reached (`docs/typeinfer-certificates.md`) — plus a run manifest.
`--verify` then re-checks each of those certificates against its source, which runs no inference at
all: a rejection there is a statement about the certificate, not about the Python. That pass is the
one worth having in CI, because a validator that accepted everything would pass every other check in
this file.

`--out FILE` keeps the per-file verdicts as JSON. The old version of this script computed them and
printed at most twenty, which made a regression a moved percentage rather than a named file.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from pastalean.typeinfer import check  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus", type=Path)
    ap.add_argument("--expect", choices=("clean", "error"), default="clean")
    ap.add_argument("--show", type=int, default=20, help="how many offending files to print")
    ap.add_argument("--certs", type=Path, default=None,
                    help="write one certificate per file here, plus a run manifest")
    ap.add_argument("--verify", action="store_true",
                    help="with --certs, re-check every certificate written and fail if any is rejected")
    ap.add_argument("--out", type=Path, default=None, help="write the per-file verdicts as JSON")
    ap.add_argument("-j", "--jobs", type=int, default=None)
    args = ap.parse_args()

    root = args.corpus if args.corpus.is_dir() else None
    files = [str(p) for p in sorted(args.corpus.rglob("*.py"))] if root else [str(args.corpus)]

    t0 = time.perf_counter()
    results = check.certify_paths(files, jobs=args.jobs)
    elapsed = time.perf_counter() - t0

    verdicts = []
    for src, _ir, res in results:
        diags = res.get("diagnostics", [])
        # A file is WRONG when it disagrees with what the corpus promises: a diagnostic on code
        # believed correct, or silence on code with a seeded error.
        wrong = bool(diags) if args.expect == "clean" else not diags
        verdicts.append({"file": src, "ok": res.get("ok", True), "diagnostics": len(diags),
                         "wrong": wrong,
                         "first": diags[0]["message"] if diags else None})

    scanned = len(verdicts)
    wrong = [v for v in verdicts if v["wrong"]]
    for v in wrong[: args.show]:
        rel = Path(v["file"]).relative_to(root) if root else Path(v["file"])
        print(f"  {rel}: {v['first'] or 'no diagnostic'}")

    rejected: list[tuple[str, dict]] = []
    if args.certs:
        manifest = check.write_certificates(results, args.certs, root)
        print(f"\nwrote {manifest['files']} certificates to {args.certs} "
              f"({manifest['clean']} clean, {manifest['flagged']} flagged, "
              f"{manifest['slots']} slots) — JSON and a checkable .lean for each")
        if args.verify:
            t1 = time.perf_counter()
            checked = check.verify_certificates(
                [(src, ir, res["certificate"]) for src, ir, res in results
                 if res.get("certificate") is not None], jobs=args.jobs)
            rejected = [(s, r) for s, r in checked if not r.get("valid")]
            for src, r in rejected[: args.show]:
                print(f"  certificate REJECTED {src}: {r.get('reason', 'unknown')}")
            print(f"{len(checked) - len(rejected)}/{len(checked)} certificates verified "
                  f"in {time.perf_counter() - t1:.1f}s")

    label = "false positives" if args.expect == "clean" else "missed seeded errors"
    rate = len(wrong) / scanned if scanned else 0.0
    print(f"\n{scanned} files scanned in {elapsed:.1f}s — {len(wrong)} {label} ({rate:.1%})")

    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(
            {"corpus": str(args.corpus), "expect": args.expect, "scanned": scanned,
             "wrong": len(wrong), "rate": rate, "seconds": round(elapsed, 2),
             "certificates_rejected": len(rejected), "files": verdicts}, indent=2), encoding="utf-8")
        print(f"per-file verdicts -> {args.out}")

    return 1 if (wrong or rejected) else 0


if __name__ == "__main__":
    sys.exit(main())
