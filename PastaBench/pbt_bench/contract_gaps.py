"""Refute every contracted HumanEval/LeetCode solution (`PastaBench/{humaneval,leetcode}/*/solution_contracts.py`)
through one warm backend and list the contracts it breaks, with the witness: each is a contract weaker than
the problem (a missing `Requires`, e.g. LeetCode's "elements are distinct") or a bug in the solution.

    uv run python PastaBench/pbt_bench/contract_gaps.py [--time 15] [--out gaps.json]
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from pastalean import Session  # noqa: E402
from pastalean.refute import refute_file  # noqa: E402

CORPORA = [ROOT / "PastaBench" / "humaneval", ROOT / "PastaBench" / "leetcode"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--time", type=int, default=15, help="seconds per obligation")
    ap.add_argument("--out", type=Path, default=Path("/tmp/contract_gaps.json"))
    args = ap.parse_args()
    files = sorted(p / "solution_contracts.py" for c in CORPORA for p in c.iterdir()
                   if (p / "solution_contracts.py").exists())
    gaps, untested, t0 = [], [], time.monotonic()
    with Session(target="command", mode="both") as session:
        for i, f in enumerate(files):
            try:
                report = refute_file(f, session=session, tests=10 ** 9, time_ms=args.time * 1000)
            except Exception as e:  # noqa: BLE001
                untested.append((f.parent.name, f"crash: {e}"[:120]))
                continue
            if report.error:
                untested.append((f.parent.name, report.error[:120]))
            for o in report.obligations:
                w = o.witness
                if w is not None and w.py == "violates":
                    gaps.append({"problem": f.parent.name, "function": o.name, "verdict": o.verdict,
                                 "witness": w.python, "explain": w.explain or {}})
                    print(f"GAP  {f.parent.name:45} {o.verdict:16} {gaps[-1]['witness']}", flush=True)
            if (i + 1) % 50 == 0:
                print(f"... {i + 1}/{len(files)} in {time.monotonic() - t0:.0f}s", flush=True)
    args.out.write_text(json.dumps({"gaps": gaps, "untested": untested}, indent=1))
    print(f"{len(gaps)} contract gaps in {len(files)} solutions ({len(untested)} untestable); "
          f"{time.monotonic() - t0:.0f}s; details in {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
