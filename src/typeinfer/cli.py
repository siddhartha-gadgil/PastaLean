"""`pastalean typeinfer` command: argument wiring and dispatch.

`add_arguments` populates the subparser; `run` executes it. Everything the command does lives in this
package, so `main.py` only forwards to `run`. Modes:

  (default)          emit the source with inferred types injected (or JSON / a scope listing / a
                     `.pyi` stub via --format), optionally in place (-i).
  --coverage         print a type-coverage report.
  --check            TYPE CHECK: report the Lean checker's verdicts (`checkTypes`) — an annotation
                     the body contradicts, a slot whose uses no type satisfies — and exit non-zero
                     if there is any. Errors print Lean-first, with the Python type alongside.
                     With --certificate, also write the record behind each verdict.
  --verify-cert      Re-check certificates written earlier against the sources they name. Runs no
                     inference: a rejection is a statement about the certificate, not the Python.
  --unresolved       CI mode: print a diagnostic per unresolved slot (text / GitHub / SARIF) and,
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
             "stub. With --check/--unresolved, 'github'/'sarif' select the diagnostic format "
             "('list' gives one line per error under --check). Directory input supports only "
             "'annotated'.",
    )
    p.add_argument(
        "-i", "--in-place", action="store_true",
        help="Write results back to disk: 'annotated' overwrites the source file; 'stub' writes "
             "'<file>.pyi' beside it.",
    )
    p.add_argument(
        "--check", action="store_true",
        help="Type-check: report every annotation the body contradicts and every slot whose uses no "
             "single type satisfies, and exit non-zero if there is any. Each error shows the Lean "
             "type the transpiler would emit with its Python type alongside.",
    )
    p.add_argument(
        "--certificate", metavar="DIR",
        help="With --check: write the certificate behind each verdict to DIR — for every source "
             "file a readable JSON and a .lean whose compilation is the same check done by Lean's "
             "kernel, plus a run manifest. A certificate records every slot judged, the evidence "
             "weighed and the verdict reached, and is re-checkable with --verify-cert without "
             "re-running inference.",
    )
    p.add_argument(
        "--emit-proof", metavar="FILE",
        help="Write the certificate for FILE as a Lean file whose compilation is its own check: "
             "`lake env lean <out>` proves `CertSound`. One file only. Covers the "
             "certificate-internal half; the program identity stays with --verify-cert.",
    )
    p.add_argument(
        "--verify-cert", metavar="DIR",
        help="Re-check the certificates in DIR against the file or directory given. Prints one line "
             "per rejected certificate and exits non-zero if any is rejected.",
    )
    p.add_argument(
        "--unresolved", action="store_true",
        help="CI mode: report a diagnostic for every parameter/return/variable/field the engine could "
             "not resolve, and exit non-zero if coverage is below --fail-under.",
    )
    p.add_argument(
        "--coverage", action="store_true",
        help="Print a type-coverage report (per dimension and overall) instead of the annotated source.",
    )
    p.add_argument(
        "--fail-under", type=float, default=None, metavar="PCT",
        help="With --unresolved/--coverage, exit non-zero if overall coverage is below this percentage.",
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
                   help="Repo mode: parallelism for IR generation, inference and --check. Default: all cores.")


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
        # Checking runs its own Lean pass (`checkTypes` infers twice — once as written, once with the
        # annotations stripped — so the two answers are independent), so it does not reuse `result`.
        if getattr(args, "emit_proof", None):
            return _run_emit_proof(path, Path(args.emit_proof))
        if getattr(args, "verify_cert", None):
            return _run_verify_cert(path, Path(args.verify_cert), getattr(args, "jobs", None))
        if args.check:
            return _run_check(path, fmt, getattr(args, "jobs", None),
                              getattr(args, "certificate", None))
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

    if args.unresolved:
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


def _sources(path: Path) -> list[str]:
    """The files a check covers: one, or every `.py` under a directory, in path order."""
    return [str(p) for p in sorted(path.rglob("*.py"))] if path.is_dir() else [str(path)]


def _run_check(path: Path, fmt: str, jobs: int | None = None,
               certificate: str | None = None) -> int:
    """`--check`: the Lean checker's verdicts, mypy-style — nothing printed on success, non-zero exit
    on any error. With `certificate`, the record behind every verdict is written out too."""
    from .check import (certify_paths, to_github, to_lines, to_sarif, to_text,
                        write_certificates)

    # Checking always certifies: the verdict and the certificate come out of the same pass, so there
    # is nothing to gain by computing the verdict alone. `--certificate` decides whether the record
    # behind it is kept.
    results = certify_paths(_sources(path), jobs=jobs)
    diags = [(src, d) for src, _ir, res in results for d in res["diagnostics"]]
    if certificate:
        out = Path(certificate)
        manifest = write_certificates(results, out, path if path.is_dir() else None)
        print(f"wrote {manifest['files']} certificates to {out} "
              f"({manifest['clean']} clean, {manifest['flagged']} flagged, "
              f"{manifest['slots']} slots) — JSON and a checkable .lean for each",
              file=sys.stderr)
    if fmt == "github":
        print(to_github(diags))
    elif fmt == "sarif":
        print(to_sarif(diags))
    elif diags:
        print(to_lines(diags) if fmt == "list" else to_text(diags))
    n = len(diags)
    print(f"{n} type error{'' if n == 1 else 's'}" if n else "no type errors", file=sys.stderr)
    return 1 if diags else 0


def _run_emit_proof(path: Path, out: Path) -> int:
    """`--emit-proof`: the certificate as a Lean file, checked by Lean's kernel rather than by a
    second program."""
    from .check import certify_paths
    from .proof import lean_name, write_proof

    if path.is_dir():
        print("error: --emit-proof takes a single file", file=sys.stderr)
        return 1
    results = certify_paths([str(path)])
    if not results or results[0][2].get("certificate") is None:
        print(f"error: could not certify {path}", file=sys.stderr)
        return 1
    cert = results[0][2]["certificate"]
    write_proof(cert, out, lean_name(path.stem), str(path))
    print(f"wrote {out} ({len(cert['slots'])} slots, {len(cert['diagnostics'])} diagnostics) — "
          f"check it with `lake env lean {out}`", file=sys.stderr)
    return 0


def _run_verify_cert(path: Path, out: Path, jobs: int | None = None) -> int:
    """`--verify-cert`: re-check written certificates against their sources.

    This is the half that needs no engine — `TypeInfer/Certificate/Check.lean` imports nothing from
    `Solve/` — so a rejection here says the certificate does not hold up, not that the Python is
    wrong."""
    from .check import verify_written

    srcs = _sources(path)
    results = verify_written(out, srcs, path if path.is_dir() else None, jobs=jobs)
    bad = [(src, r) for src, r in results if not r.get("valid")]
    for src, r in sorted(bad):
        print(f"{src}: certificate rejected — {r.get('reason', 'unknown')}")
    n = len(results)
    print(f"{n - len(bad)}/{n} certificates verified", file=sys.stderr)
    return 1 if bad else 0


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
    if args.coverage or args.unresolved:
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
