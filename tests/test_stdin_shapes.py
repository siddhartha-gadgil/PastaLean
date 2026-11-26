"""Unit checks for the stdin side of `pastalean refute`: how a reading call site is classified, the format
check on replayed inputs, entry-point wrapping and shrinking. No Lean backend needed.

Run with `uv run python tests/test_stdin_shapes.py`.
"""

from __future__ import annotations

import ast
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src" / "refute"))
sys.path.insert(0, str(ROOT / "src"))

import stdin_harness as H  # noqa: E402
from pastalean.refute.stdin import shrink_candidates, with_main_entry  # noqa: E402

SHAPES = [
    ("n = int(input())", ("int",)),
    ("n = int(input().strip())", ("int",)),
    ("q = float(input())", ("float",)),
    ("a, b = map(int, input().split())", ("tokens", "int", 2)),
    ("arr = list(map(int, input().split()))", ("tokens", "int", None)),
    ("arr = [int(x) for x in input().split()]", ("tokens", "int", None)),
    ("arr = sorted(map(int, input().split()))", ("tokens", "int", None)),
    ("n, *rest = map(int, input().split())", ("tokens", "int", None)),
    ("x, y = input().split()", ("tokens", "word", 2)),
    ("xs = list(map(float, input().split()))", ("tokens", "float", None)),
    ("s = input().strip()", ("word",)),
    ("s = input()", ("word",)),
    ("import sys\nn = int(sys.stdin.readline())", ("int",)),
]


def check(cond, msg):
    if not cond:
        raise AssertionError(msg)


def test_shapes():
    for src, want in SHAPES:
        got = [s for ss in H.shapes(src).values() for s in ss]
        check(got == [want], f"{src!r}: expected {want}, got {got}")


def run_with(src, stdin):
    return H.run(compile(src, "<program>", "exec"), stdin, 1000)


PROG = '''
def main():
    t = int(input())
    for _ in range(t):
        n = int(input())
        a = list(map(int, input().split()))
        print(sum(a))
main()
'''


def test_generate_is_well_formed():
    table = H.shapes(PROG)
    for seed in range(30):
        g = H.GenStdin(table, random.Random(seed), 4, False)
        out, exc = run_with(PROG, g)
        check(exc is None, f"seed {seed}: generated input made the program raise {exc}")
        text = "".join(l + "\n" for l in g.lines)
        c = H.CheckStdin(text, table, True)
        run_with(PROG, c)
        check(c.violation is None, f"seed {seed}: generated input breaks its own format: {c.violation}")


def test_check_rejects_wrong_length():
    table = H.shapes(PROG)
    c = H.CheckStdin("1\n1\n1 0 1\n", table, True)
    run_with(PROG, c)
    check(c.violation is not None, "a list longer than its count passed the strict check")
    c = H.CheckStdin("1\n1\n1 0 1\n", table, False)
    run_with(PROG, c)
    check(c.violation is None, "the loose check should only look at token kinds")
    c = H.CheckStdin("1\nx\n1\n", table, False)
    run_with(PROG, c)
    check(c.violation is not None, "a non-integer count passed")


def test_with_main_entry():
    bare = "import math\nn = int(input())\nprint(n)\n"
    w = with_main_entry(bare)
    check(w.startswith("import math\nif __name__"), w)
    ast.parse(w)
    uncalled = "def main():\n    print(1)\n"
    check(with_main_entry(uncalled).rstrip().endswith("main()"), with_main_entry(uncalled))
    guarded = "def main():\n    pass\n\nif __name__ == '__main__':\n    main()\n"
    check(with_main_entry(guarded) == guarded, "a guarded module must be unchanged")


def test_shrink_keeps_count_in_step():
    cands = shrink_candidates("1\n2\n-1 -2\n")
    check("1\n1\n-1\n" in cands, f"no candidate drops a token together with its count: {cands}")
    check(all(c.endswith("\n") for c in cands), "candidates must end with a newline")
    # Dropping a whole test case means lowering `t` and deleting its lines in one step.
    check("1\n1\n-1\n" in shrink_candidates("2\n1\n0\n1\n-1\n"), "no candidate drops a record with its count")


def main() -> int:
    failures = 0
    for name, fn in list(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"ok   {name}")
            except AssertionError as e:
                failures += 1
                print(f"FAIL {name}: {e}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
