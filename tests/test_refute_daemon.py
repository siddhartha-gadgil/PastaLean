"""The warm refute daemon (`src/refute/daemon.py`) must be invisible: a `pastalean refute` answered by it
prints exactly what a cold local run prints, and exits with the same code.

Run with `uv run python tests/test_refute_daemon.py`.
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT / "example_scripts" / "refute" / "missing_number.py"


def run(env: dict[str, str]) -> tuple[int, str, float]:
    t0 = time.monotonic()
    p = subprocess.run([sys.executable, "-m", "pastalean", "refute", str(CASE)], capture_output=True, text=True,
                       env={**os.environ, **env}, cwd=ROOT)
    return p.returncode, p.stdout, time.monotonic() - t0


def main() -> int:
    cold = run({"PASTALEAN_NO_DAEMON": "1"})
    run({})                       # starts the daemon if none runs
    for _ in range(60):           # until it answers
        warm = run({})
        if warm[2] < cold[2] / 2:
            break
        time.sleep(2)
    ok = cold[:2] == warm[:2]
    print(f"{'ok  ' if ok else 'FAIL'} daemon output identical; cold {cold[2]:.1f}s, warm {warm[2]:.1f}s")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
