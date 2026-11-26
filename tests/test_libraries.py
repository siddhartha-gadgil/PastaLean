"""Differential checks for the Lean libraries that model Python modules (`Libraries/json`,
`Libraries/datetime`): each program in `example_scripts/libraries/` (plus `CLASS_EXAMPLES`, the class
features those libraries rely on) must print the same under CPython and as translated Lean
(`pastalean run`). Programs reading the clock print only clock-independent facts.

Run with `uv run python tests/test_libraries.py`.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIB_EXAMPLES = ROOT / "example_scripts" / "libraries"
CLASS_EXAMPLES = [ROOT / "example_scripts" / "commands" / "class_operator_effects.py"]


def main() -> int:
    failures = 0
    for prog in sorted(LIB_EXAMPLES.glob("*.py")) + CLASS_EXAMPLES:
        expected = subprocess.run([sys.executable, str(prog)], capture_output=True, text=True).stdout
        got = subprocess.run(["uv", "run", "pastalean", "run", str(prog)], capture_output=True, text=True,
                             stdin=subprocess.DEVNULL, cwd=ROOT).stdout
        if got != expected:
            failures += 1
            print(f"FAIL {prog.name}\n--- CPython\n{expected}--- Lean\n{got}")
        else:
            print(f"ok   {prog.name}")
    return failures


if __name__ == "__main__":
    raise SystemExit(main())
