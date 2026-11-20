"""A held-out check for `pastalean refute`: CrossHair's own bundled examples, which refute was never
tuned on. `bugs_detected/` files hold false contracts (each refuted function counts as found);
`correct_code/` files hold true ones (any refutation there is a false alarm). With `--crosshair`, CrossHair
runs on the same files for comparison.

    uv run python PastaBench/pbt_bench/heldout.py [--timeout 30] [--crosshair]
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

import crosshair

EXAMPLES = Path(crosshair.__file__).parent / "examples"
SYNTAXES = ("PEP316", "icontract")   # deal is not a contract syntax refute reads


def refute(path: Path, timeout: int) -> tuple[set[str], str]:
    p = subprocess.run([sys.executable, "-m", "pastalean", "refute", str(path), "--json", "--tests", str(10 ** 9),
                        "--time", str(timeout * 1000)], capture_output=True, text=True, timeout=timeout * 20)
    try:
        report = json.loads(p.stdout)
    except json.JSONDecodeError:
        return set(), (p.stderr.strip().splitlines() or ["no output"])[-1][:120]
    return {o["name"] for o in report.get("obligations", []) if o.get("verdict") == "REFUTED"}, report.get("error") or ""


def crosshair_check(path: Path, timeout: int) -> set[str]:
    p = subprocess.run([sys.executable, "-m", "crosshair", "check", str(path), "--per_condition_timeout",
                        str(timeout)], capture_output=True, text=True, timeout=timeout * 40)
    # `file:line: error: false when calling f(...)` — the failing function is the one called
    found = set()
    for line in p.stdout.splitlines():
        if "when calling" in line:
            found.add(line.split("when calling ", 1)[1].split("(", 1)[0].strip())
    return found


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=int, default=30, help="seconds per obligation")
    ap.add_argument("--crosshair", action="store_true")
    args = ap.parse_args()
    totals = {"bugs": [0, 0], "false_alarms": [0, 0]}
    for syntax in SYNTAXES:
        for kind in ("bugs_detected", "correct_code"):
            for path in sorted((EXAMPLES / syntax / kind).glob("*.py")):
                if path.name == "__init__.py":
                    continue
                ours, err = refute(path, args.timeout)
                theirs = crosshair_check(path, args.timeout) if args.crosshair else set()
                slot = "bugs" if kind == "bugs_detected" else "false_alarms"
                totals[slot][0] += len(ours)
                totals[slot][1] += len(theirs)
                print(f"{syntax}/{kind}/{path.name}: refute {sorted(ours)}"
                      + (f"  crosshair {sorted(theirs)}" if args.crosshair else "") + (f"  ({err})" if err else ""))
    print(f"bugs found: refute {totals['bugs'][0]}" + (f", crosshair {totals['bugs'][1]}" if args.crosshair else ""))
    print(f"false alarms: refute {totals['false_alarms'][0]}"
          + (f", crosshair {totals['false_alarms'][1]}" if args.crosshair else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
