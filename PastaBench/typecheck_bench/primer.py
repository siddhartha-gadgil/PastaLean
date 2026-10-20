#!/usr/bin/env python3
"""The mypy_primer corpus — the ecosystem's standard "run type checkers over real code" benchmark.

[mypy_primer](https://github.com/hauntsaninja/mypy_primer) pins a list of ~160 open-source Python
projects (~37k files, ~10M lines) and runs type checkers over them; mypy, pyright, ty and pyrefly
all wire it into their own CI. Its selection rule is what makes it useful here: a project is on the
list only if it already type-checks in its own CI (a `mypy.ini`, or a `mypy` entry in `tox.ini` /
`setup.cfg`), so the code is real, large, and believed type-correct by its own maintainers.

Unlike the typing conformance suite, this is a corpus rather than a scoring rule, so it is something
PastaLean can actually be measured on. Two measurements:

  **precision** — every diagnostic on unmodified corpus code is a candidate false positive. This is
  the honest stress test of the zero-false-positive claim: `example_scripts/` is 165 files we wrote,
  this is 10M lines we didn't.

  **recall** — `mutate.py`'s seeded annotation flips, scored differentially exactly as in
  `bench_checkers.py` (credit only when the mutant is flagged and its untouched original is not), so
  a tool is never punished for the missing third-party imports that a non-installed corpus creates.

    uv run PastaBench/typecheck_bench/primer.py fetch    /tmp/primer
    uv run PastaBench/typecheck_bench/primer.py precision /tmp/primer
"""
from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from multiprocessing import get_context
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

PRIMER_PROJECTS = "https://raw.githubusercontent.com/hauntsaninja/mypy_primer/master/mypy_primer/projects.py"
#: Stop cloning if the filesystem drops below this; a wedged disk is worse than a smaller corpus.
MIN_FREE_GB = 3.0


def project_urls(projects_py: Path) -> list[str]:
    """The GitHub URLs mypy_primer pins, in its own order."""
    seen, out = set(), []
    for url in re.findall(r'"(https://github\.com/[\w.-]+/[\w.-]+)"', projects_py.read_text()):
        if url not in seen:
            seen.add(url)
            out.append(url)
    return out


def fetch(out: Path, limit: int | None, jobs: int) -> int:
    """Shallow-clone the corpus. `.git` is dropped immediately — only the source tree is measured,
    and the histories are most of the bytes."""
    out.mkdir(parents=True, exist_ok=True)
    src = out / "projects.py"
    if not src.exists():
        subprocess.run(["curl", "-sSL", "-o", str(src), PRIMER_PROJECTS], check=True)
    urls = project_urls(src)[:limit]

    def one(url: str) -> tuple[str, bool]:
        name = url.rsplit("/", 1)[-1]
        dest = out / name
        if dest.exists():
            return name, True
        if shutil.disk_usage(out).free / 1e9 < MIN_FREE_GB:
            return name, False
        ok = subprocess.run(
            ["git", "clone", "--depth", "1", "--single-branch", "--quiet", url, str(dest)],
            capture_output=True,
        ).returncode == 0
        shutil.rmtree(dest / ".git", ignore_errors=True)
        return name, ok

    with ThreadPoolExecutor(max_workers=jobs) as ex:
        done = list(ex.map(one, urls))
    have = [n for n, ok in done if ok]
    files = sum(1 for _ in out.rglob("*.py"))
    print(f"{len(have)}/{len(urls)} projects, {files} .py files in {out}")
    return 0


#: One unit of work: at most this many files, and at most this many source bytes. The corpus is
#: wildly uneven — a 4 MB generated test module sits beside thousands of 2 KB ones — so a file count
#: alone makes some chunks a thousand times the work of others. Nothing is skipped for being large:
#: a file over the budget simply gets a chunk to itself.
CHUNK = 50
CHUNK_BYTES = 600_000
#: Wall-clock ceiling for one chunk. Generous next to the ~0.1 s a 50-file chunk normally takes.
CHUNK_TIMEOUT = 90


def _run_chunk() -> int:
    """The `chunk` subcommand: check the newline-separated paths on stdin, print the diagnostics as
    JSON. Its own process so the parent can impose a hard deadline (see `_chunk_diags`)."""
    from pastalean.typeinfer.check import check_paths_report  # noqa: PLC0415

    paths = [ln for ln in sys.stdin.read().splitlines() if ln]
    sink = io.StringIO()
    with contextlib.redirect_stdout(sink), contextlib.redirect_stderr(sink):
        rep = check_paths_report(paths, jobs=1)
    # `checked`/`ir_failed` ride along so the parent's denominator is the files actually read.
    print(json.dumps({"diags": [[f, d["message"]] for f, d in rep["diagnostics"]],
                      "checked": rep["checked"], "ir_failed": rep["ir_failed"]}))
    return 0


def _run_paths(paths: list[str], timeout: float) -> tuple[str, dict]:
    """Check `paths` in a child process under a hard deadline: `("ok"|"timeout"|"error", report)`.

    The deadline has to be enforced from outside the work, not inside it. The Lean side is a blocking
    request/response over a pipe with no deadline of its own, and an in-process `SIGALRM` does not
    reliably unblock that read — a module whose fixpoint is superlinear in one giant scope would
    strand a worker for the rest of the run. Killing a child does."""
    try:
        p = subprocess.run([sys.executable, __file__, "chunk"], input="\n".join(paths),
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", {}
    try:
        return "ok", json.loads(p.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        return "error", {}


def _chunk_diags(job: tuple[str, list[str]]) -> tuple[str, int, int, list[str], list[str], int]:
    """One chunk: `(project, files checked, diagnostics, samples, timed-out files, failed files)`.

    A chunk that blows the deadline is bisected rather than written off, so only the pathological
    module is lost and the other 49 files in its chunk are still measured.

    `files checked` counts the files whose IR the front end actually built. It used to count the
    files *handed over*, which silently credited coverage for files that were dropped — one project
    (`graphql-core`) was losing 50 of 354 that way, so the corpus-wide diagnostic rate was computed
    over a denominator that included files nothing had read."""
    project, paths = job
    status, rep = _run_paths(paths, CHUNK_TIMEOUT)
    if status == "timeout" and len(paths) > 1:
        mid = len(paths) // 2
        out = [0, 0, [], [], 0]
        for half in (paths[:mid], paths[mid:]):
            _, n, d, s, t, f = _chunk_diags((project, half))
            out[0] += n; out[1] += d; out[2] += s; out[3] += t; out[4] += f
        return project, out[0], out[1], out[2], out[3], out[4]
    if status == "timeout":
        return project, len(paths), 0, [], list(paths), 0
    if status == "error":
        return project, 0, 0, [], [], len(paths)
    diags = rep["diags"]
    return (project, rep["checked"], len(diags), [f"{f}: {m}" for f, m in diags[:3]], [],
            rep["ir_failed"])


def precision(corpus: Path, jobs: int | None, out_json: Path | None) -> int:
    """PastaLean's diagnostics over the unmodified corpus. Every one is a candidate false positive:
    this code type-checks in its own CI.

    Fanned across processes at CHUNK granularity rather than per project: the corpus is wildly
    uneven (12 files to 1600), so a project-serial loop spends most of its wall clock on a handful of
    big repos while the machine idles."""
    projects = sorted(p for p in corpus.iterdir() if p.is_dir())
    jobs = jobs or (os.cpu_count() or 8)
    work: list[tuple[str, list[str]]] = []
    for proj in projects:
        cur: list[str] = []
        cur_bytes = 0
        for p in sorted(proj.rglob("*.py")):
            size = p.stat().st_size
            if cur and (len(cur) >= CHUNK or cur_bytes + size > CHUNK_BYTES):
                work.append((proj.name, cur))
                cur, cur_bytes = [], 0
            cur.append(str(p))
            cur_bytes += size
        if cur:
            work.append((proj.name, cur))

    per_project: dict[str, dict] = {}
    samples: list[str] = []
    timeouts: list[str] = []
    failed = 0
    t0 = time.time()
    with get_context("fork").Pool(jobs) as pool:
        for n, (project, nfiles, ndiags, samp, slow, nfailed) in enumerate(
                pool.imap_unordered(_chunk_diags, work), 1):
            row = per_project.setdefault(project, {"project": project, "files": 0, "diags": 0})
            row["files"] += nfiles
            row["diags"] += ndiags
            samples += samp
            timeouts += slow
            failed += nfailed
            if n % 100 == 0:
                print(f"  {n}/{len(work)} chunks, {time.time() - t0:.0f}s", flush=True)
    wall = time.time() - t0

    total_files = sum(r["files"] for r in per_project.values())
    total_diags = sum(r["diags"] for r in per_project.values())
    print(f"\nmypy_primer corpus: {len(per_project)} projects, {total_files} .py files CHECKED")
    print(f"  diagnostics       {total_diags} "
          f"({total_diags / max(total_files, 1) * 1000:.2f} per 1000 files)")
    print(f"  front-end failed  {failed} (IR could not be built; excluded from the rate above)")
    print(f"  timed out         {len(timeouts)} files (> {CHUNK_TIMEOUT}s, bisected)")
    print(f"  wall              {wall:.1f}s ({total_files / max(wall, 1e-9):.0f} files/s)")
    for row in sorted(per_project.values(), key=lambda r: -r["diags"])[:10]:
        if row["diags"]:
            print(f"    {row['diags']:>5}  {row['project']}")
    if out_json:
        out_json.write_text(json.dumps(
            {"projects": sorted(per_project.values(), key=lambda r: -r["diags"]),
             "files": total_files, "diags": total_diags,
             "wall": wall, "samples": samples, "timeouts": timeouts}, indent=2))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    f = sub.add_parser("fetch", help="shallow-clone the corpus")
    f.add_argument("out", type=Path)
    f.add_argument("--limit", type=int)
    f.add_argument("-j", "--jobs", type=int, default=16)
    p = sub.add_parser("precision", help="PastaLean's false positives on unmodified corpus code")
    p.add_argument("corpus", type=Path)
    p.add_argument("-j", "--jobs", type=int)
    p.add_argument("--json", type=Path, help="also write the per-project numbers here")
    sub.add_parser("chunk", help="internal: check the paths on stdin (one worker of a sweep)")
    args = ap.parse_args()
    if args.cmd == "fetch":
        return fetch(args.out, args.limit, args.jobs)
    if args.cmd == "chunk":
        return _run_chunk()
    return precision(args.corpus, args.jobs, args.json)


if __name__ == "__main__":
    raise SystemExit(main())
