"""`pastalean typeinfer` command: argument wiring and dispatch.

`add_arguments` populates the subparser; `run` executes it. Everything the command does lives in this
package, so `main.py` only forwards to `run`. Modes:

  (default)          emit the source with inferred types injected (or JSON / a scope listing / a
                     `.pyi` stub via --format), optionally in place (-i).
  --coverage         print a type-coverage report.
  --check            CI mode: print a diagnostic per unresolved slot (text / GitHub / SARIF) and,
                     with --fail-under (or `[tool.typeinfer]`), exit non-zero below that coverage.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

FILE_FORMATS = ("annotated", "json", "list", "stub")
DIAG_FORMATS = ("text", "github", "sarif")


def add_arguments(p: argparse.ArgumentParser) -> None:
    p.add_argument("file", help="Python source file, or a directory (repo mode).")
    p.add_argument(
        "-o", "--output",
        help="For a file: write here instead of stdout ('-' for stdout). For a directory: the output "
             "directory for the annotated copy (default: '<dir>_typed').",
    )
    p.add_argument(
        "--format", default=None, choices=[*FILE_FORMATS, "github", "sarif"],
        help="Output format. Default 'annotated': the source with inferred type annotations added. "
             "'json': a machine-readable type map. 'list': a scope-grouped listing. 'stub': a `.pyi` "
             "stub. With --check, 'github'/'sarif' select the diagnostic format. Directory input "
             "supports only 'annotated'.",
    )
    p.add_argument(
        "-i", "--in-place", action="store_true",
        help="Write results back to disk: 'annotated' overwrites the source file; 'stub' writes "
             "'<file>.pyi' beside it.",
    )
    p.add_argument(
        "--check", action="store_true",
        help="CI mode: report a diagnostic for every parameter/return/variable/field the engine could "
             "not resolve, and exit non-zero if coverage is below --fail-under.",
    )
    p.add_argument(
        "--coverage", action="store_true",
        help="Print a type-coverage report (per dimension and overall) instead of the annotated source.",
    )
    p.add_argument(
        "--fail-under", type=float, default=None, metavar="PCT",
        help="With --check/--coverage, exit non-zero if overall coverage is below this percentage.",
    )
    p.add_argument(
        "--no-any", action="store_true",
        help="Omit bare `Any` annotations (they are added by default, with `from typing import Any`). "
             "Parametrised types like `list[Any]` are always kept.",
    )
    p.add_argument(
        "-r", "--report", action="store_true",
        help="Print a summary to stderr: annotation counts per dimension and the time taken.",
    )
    p.add_argument("--indent", action=argparse.BooleanOptionalAction, default=True,
                   help="Pretty-print --format json. Default: on.")
    p.add_argument("-j", "--jobs", type=int, default=None, metavar="N",
                   help="Repo mode: parallelism for IR generation and inference. Default: all cores.")


def _emit(code: str, output: str | None) -> None:
    if output and output != "-":
        Path(output).write_text(code + "\n", encoding="utf-8")
    else:
        print(code)


def run(args) -> int:
    from ..backend.typeinfer import TypeInferUnavailable
    from .config import load_config
    from .coverage import coverage, format_coverage_report
    from .diagnostics import diagnostics, to_github, to_sarif, to_text
    from .engine import infer_source

    cfg = load_config(Path(args.file))
    fmt = args.format or cfg.get("format") or "annotated"
    output = args.output or cfg.get("output")
    include_any = not (args.no_any or cfg.get("no_any", False))
    fail_under = args.fail_under if args.fail_under is not None else cfg.get("fail_under")

    path = Path(args.file)
    t0 = time.perf_counter()
    try:
        if path.is_dir():
            return _run_repo(args, path, fmt, output, include_any, fail_under, t0)
        source = path.read_text(encoding="utf-8")
        result = infer_source(source, args.file)
    except TypeInferUnavailable as err:
        print(f"error: {err}", file=sys.stderr)
        return 1
    elapsed = time.perf_counter() - t0

    if args.coverage:
        cov = coverage(source, result)
        print(format_coverage_report(args.file, cov))
        return _gate(cov, fail_under)

    if args.check:
        diags = diagnostics(source, result, args.file)
        dfmt = fmt if fmt in ("github", "sarif") else "text"
        if dfmt == "github":
            print(to_github(diags))
        elif dfmt == "sarif":
            print(to_sarif(diags, args.file))
        else:
            print(to_text(diags) or "no unresolved types")
        cov = coverage(source, result)
        rc = _gate(cov, fail_under)
        print(f"{cov['typed']}/{cov['total']} slots typed ({100 * cov['coverage']:.1f}%), "
              f"{len(diags)} unresolved", file=sys.stderr)
        return rc

    _emit(_format_file(fmt, source, result, args, include_any), _sink(args, path, fmt, output))

    if args.report:
        from .report import count_annotations, format_stats_report
        counts = count_annotations(result, include_any=include_any)
        print(format_stats_report(args.file, counts, elapsed), file=sys.stderr)
    return 0


def _format_file(fmt: str, source: str, result, args, include_any: bool) -> str:
    from .annotate import annotate_source
    from .report import to_json_obj, to_report
    from .stub import to_stub

    if fmt == "json":
        return json.dumps(to_json_obj(result, args.file), indent=2 if args.indent else None)
    if fmt == "list":
        return to_report(result, args.file)
    if fmt == "stub":
        return to_stub(source, result, include_any=include_any).rstrip("\n")
    return annotate_source(source, result, include_any=include_any)  # annotated (default)


def _sink(args, path: Path, fmt: str, output: str | None) -> str | None:
    """Where a file-format result goes: an explicit --output, or -i's on-disk target, or stdout."""
    if output:
        return output
    if args.in_place:
        if fmt == "stub":
            return str(path.with_suffix(".pyi"))
        if fmt == "annotated":
            return str(path)
        print("error: --in-place applies only to --format annotated or stub.", file=sys.stderr)
        raise SystemExit(2)
    return None


def _gate(cov: dict, fail_under: float | None) -> int:
    if fail_under is not None and 100.0 * cov["coverage"] < fail_under:
        print(f"coverage {100 * cov['coverage']:.1f}% is below --fail-under {fail_under:g}%",
              file=sys.stderr)
        return 1
    return 0


def _run_repo(args, repo: Path, fmt: str, output: str | None, include_any: bool,
              fail_under: float | None, t0: float) -> int:
    """Directory input: cross-file inference over the whole repo."""
    from .annotate import annotate_repo
    from .coverage import DIMENSIONS, coverage, format_coverage_report
    from .engine import infer_repo_dir

    jobs = getattr(args, "jobs", None)
    if args.coverage or args.check:
        agg = {d: {"typed": 0, "total": 0} for d in DIMENSIONS}
        for _dotted, (src, result) in infer_repo_dir(repo, jobs=jobs).items():
            c = coverage(src.read_text(encoding="utf-8"), result)
            for d in DIMENSIONS:
                agg[d]["typed"] += c["dimensions"][d]["typed"]
                agg[d]["total"] += c["dimensions"][d]["total"]
        typed = sum(d["typed"] for d in agg.values())
        total = sum(d["total"] for d in agg.values())
        cov = {"dimensions": agg, "typed": typed, "total": total,
               "coverage": (typed / total) if total else 1.0}
        print(format_coverage_report(str(repo), cov))
        return _gate(cov, fail_under)

    if fmt != "annotated":
        print("error: directory input supports only --format annotated (writes an annotated copy).",
              file=sys.stderr)
        return 1
    out_dir = Path(output) if output else repo.with_name(repo.name + "_typed")
    n_files, n_total, counts = annotate_repo(repo, out_dir, include_any=include_any, jobs=jobs)
    elapsed = time.perf_counter() - t0
    print(f"annotated {n_files}/{n_total} files -> {out_dir}", file=sys.stderr)
    if args.report:
        from .report import format_stats_report
        print(format_stats_report(str(repo), counts, elapsed, files=(n_files, n_total)),
              file=sys.stderr)
    return 0
