"""`pastalean refute` on the acceptance programs in `example_scripts/refute/`: each one's verdict is
fixed (seeded), so a regression in a search engine or in the three-world classification shows up here.

Run with `uv run python tests/test_refute.py` (it boots one Lean backend for all of them).
"""

from __future__ import annotations

import os
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from pastalean import Session  # noqa: E402
from pastalean.refute import refute_file  # noqa: E402
from pastalean.refute.stdin import refute_stdin  # noqa: E402

CASES = {
    # file: {function: (verdict, kernel-certified?)}
    "max_subarray.py": {"agree": ("REFUTED", True)},
    "missing_number.py": {"missingNumber": ("REFUTED", True)},
    "sparse_precondition.py": {"discount": ("REFUTED", True)},
    "float_roundtrip.py": {"roundtrip_identity": ("ROUNDING_SENSITIVE", False)},
    "div_by_len.py": {"mean_bound": ("PARTIALITY_GAP", False)},
    "interval_overlap.py": {"overlap_agree": ("REFUTED", True)},
    "float_midpoint.py": {"midpoint_between": ("REFUTED", True)},
    "deep_branch.py": {"classify": ("REFUTED", True)},
    # HashMap operations do not reduce in the kernel, so the refutation is evaluated, not certified.
    "dict_first_key.py": {"first_is_smallest": ("REFUTED", False)},
    "regex_near_miss.py": {"is_falsey": ("REFUTED", False)},
    "exponent_sign.py": {"is_falsey": ("REFUTED", False)},
    "str_keyed_dict.py": {"bump": ("REFUTED", False)},
    "version_compare.py": {"compare_versions": ("REFUTED", False)},
    "local_postcondition.py": {"isqrt": ("REFUTED", False)},
    "assert_precondition.py": {"headline": ("REFUTED", False)},
}

# Run with `smt=True` (an SMT model, re-checked in Lean); skipped when no z3/cvc5 is installed.
SMT_CASES = {
    "nonlinear_smt.py": {"pythag": ("REFUTED", True), "mod_square": ("REFUTED", True)},
}

# Lean tests per search where the default (1000) is too few to reach the bug.
TESTS = {"regex_near_miss.py": 20000, "version_compare.py": 200000, "exponent_sign.py": 60000}

STDIN_CASES = {
    # file: (reference or None, negative ints?, expected verdict, expected note substring)
    "stdin_word_order.py": (None, False, "FIDELITY_BUG", ""),
    "stdin_kadane_fast.py": ("stdin_kadane_brute.py", True, "PROGRAM_DIFF", "runnable and provable"),
    # Python catches ZeroDivisionError; the runnable twin's float `/` raises it as an uncatchable runtime
    # error and the provable twin's ℚ `/` returns 0.
    "../proof_mode/test_io_nested_exception.py": (None, False, "FIDELITY_BUG", "differ from each other"),
}


def main() -> int:
    failures = 0
    try:
        import crosshair  # noqa: F401
    except ImportError:
        # Only symbolic search reaches the bug behind `discount`'s narrow precondition.
        CASES.pop("sparse_precondition.py")
        print("skip sparse_precondition.py (CrossHair not installed: uv pip install -e '.[refute]')")
    with Session(target="command", mode="both") as session:
        for file, expected in CASES.items():
            report = refute_file(ROOT / "example_scripts" / "refute" / file, session=session,
                                 tests=TESTS.get(file, 1000))
            got = {o.name: (o.verdict, bool(o.kernel_proof)) for o in report.obligations}
            for fn, want in expected.items():
                ok = got.get(fn) == want
                failures += not ok
                print(f"{'ok  ' if ok else 'FAIL'} {file}:{fn} expected {want}, got {got.get(fn)}"
                      + (f" ({report.error})" if report.error else ""))
        has_solver = os.environ.get("PASTALEAN_SMT") or any(
            shutil.which(e) or (Path.home() / ".local/bin" / e).exists() for e in ("z3", "cvc5"))
        if not has_solver:
            print("skip SMT cases (no z3/cvc5: see docs/smt.md)")
        for file, expected in (SMT_CASES if has_solver else {}).items():
            report = refute_file(ROOT / "example_scripts" / "refute" / file, session=session, smt=True)
            got = {o.name: (o.verdict, bool(o.kernel_proof)) for o in report.obligations}
            for fn, want in expected.items():
                ok = got.get(fn) == want
                failures += not ok
                print(f"{'ok  ' if ok else 'FAIL'} {file}:{fn} (smt) expected {want}, got {got.get(fn)}")
        for file, (ref, negative, verdict, note) in STDIN_CASES.items():
            d = ROOT / "example_scripts" / "refute"
            report = refute_stdin((d / file).read_text(), session=session, negative=negative,
                                  against=(d / ref).read_text() if ref else None)
            got = [(f.verdict, f.note) for f in report.findings]
            ok = any(v == verdict and note in n for v, n in got)
            failures += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {file} expected {verdict}, got {got}"
                  + (f" ({report.error})" if report.error else ""))
    total = sum(map(len, CASES.values())) + len(STDIN_CASES) + (sum(map(len, SMT_CASES.values())) if has_solver else 0)
    print(f"{total - failures} passed, {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
