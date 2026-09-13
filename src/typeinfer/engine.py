"""Drive the standalone `typeinfer` Lean binary over a file / directory.

Python source is parsed to JSON IR by the pure Python front-end (`driver.translate_to_json` with
`infer_only=True`, no backend boot), the compiled engine runs the fixpoint, and `collect_types`
gathers the stamped result. Repo mode ships every module's IR to the `inferRepo` task so imports
resolve in one cross-file fixpoint."""

from __future__ import annotations

import json
import math
import os
from concurrent.futures import ThreadPoolExecutor
from contextlib import nullcontext
from multiprocessing import get_context
from pathlib import Path

from ..backend.typeinfer import TypeInferServer
from ..transpile import driver
from .collect import collect_types
from .records import InferResult


def _server_ctx(server: TypeInferServer | None):
    """Reuse a caller-owned server (leaving it open) or open a one-shot server for this unit."""
    return nullcontext(server) if server is not None else TypeInferServer()


def infer_source(source: str, path: str | None = None, *,
                 server: TypeInferServer | None = None) -> InferResult:
    """Parse `source` to JSON IR (pure Python front-end, no backend boot), run the standalone
    `typeinfer` engine over it, and collect the stamped types. Pass `server` to reuse one persistent
    exe across many files in a unit; omit it and a one-shot server is opened for this file alone."""
    ir = json.loads(driver.translate_to_json(source, path, best_effort=True, infer_only=True))
    with _server_ctx(server) as srv:
        return collect_types(srv.infer_ast(ir))


def infer_file(path: str | Path, *, server: TypeInferServer | None = None) -> InferResult:
    path = Path(path)
    return infer_source(path.read_text(encoding="utf-8"), str(path), server=server)


def infer_sources(items: list[tuple[str, str | None]]) -> list[InferResult]:
    """Infer many independent files reusing ONE persistent server (the spawn is paid once for the
    whole list, not per file). `items` is a list of `(source, path)` pairs."""
    with TypeInferServer() as srv:
        return [infer_source(src, path, server=srv) for src, path in items]


def _module_name(rel: Path) -> str:
    """Dotted module name for a repo-relative path (`pkg/sub/mod.py` -> `pkg.sub.mod`,
    `pkg/__init__.py` -> `pkg`)."""
    parts = list(rel.with_suffix("").parts)
    if parts and parts[-1] == "__init__":
        parts = parts[:-1]
    return ".".join(parts)


def _raw_ir_for_file(task: tuple[str, str]) -> tuple[str, str] | None:
    """Worker: parse one file to raw JSON IR (imports unresolved). Returns `(dotted, json_text)` or
    `None` if the file will not parse. Top-level so a process pool can pickle it — IR generation is
    pure-Python CPU work, so it fans across cores here rather than in one serial loop."""
    dotted, path = task
    try:
        raw = driver.translate_to_json(Path(path).read_text(encoding="utf-8"), path,
                                       best_effort=True, infer_only=True, resolve_imports=False)
        return (dotted, raw)
    except Exception:  # noqa: BLE001  (a single unparseable file must not sink the repo)
        return None


def _collect_repo_modules(repo: Path, jobs: int = 1) -> tuple[dict[str, dict], dict[str, Path]]:
    """Raw per-file IR keyed by dotted module name (no inference here — Lean does it all). Imports are
    left unresolved (`resolve_imports=False`); `inferRepo` resolves them against this module set. With
    `jobs > 1` the per-file IR generation is fanned across a process pool."""
    tasks: list[tuple[str, str]] = []
    for py in sorted(repo.rglob("*.py")):
        dotted = _module_name(py.relative_to(repo))
        if not dotted or dotted.startswith("."):
            continue
        tasks.append((dotted, str(py)))
    if jobs > 1 and len(tasks) > 1:
        with get_context("fork").Pool(min(jobs, len(tasks))) as pool:
            results = pool.map(_raw_ir_for_file, tasks, chunksize=4)
    else:
        results = [_raw_ir_for_file(t) for t in tasks]
    paths = {dotted: Path(path) for dotted, path in tasks}
    mods: dict[str, dict] = {}
    files: dict[str, Path] = {}
    for r in results:
        if r is None:
            continue
        dotted, raw = r
        mods[dotted] = json.loads(raw)
        files[dotted] = paths[dotted]
    return mods, files


def _infer_repo_parallel(mods: dict[str, dict], jobs: int) -> dict[str, dict]:
    """Repo-level inference fanned across parallel exe processes. A single `inferRepo` call caps at
    ~7-8 cores (the Lean task scheduler contends on one shared heap); several processes over large
    module chunks scale past that. Chunks stay big (>= 180 modules) so cross-file resolution is
    preserved within each group — measured bit-identical to the single call on a 711-module repo, and
    the chunk boundaries match the benchmark harness's, so accuracy is unchanged."""
    items = list(mods.items())
    n = len(items)
    target = min(8, max(1, jobs // 8))
    if n <= 200 or target <= 1:
        with TypeInferServer() as srv:
            return srv.infer_repo(mods)
    chunk = max(180, math.ceil(n / target))
    chunks = [dict(items[i:i + chunk]) for i in range(0, n, chunk)]
    threads = max(2, jobs // len(chunks))

    def _one(sub: dict[str, dict]) -> dict[str, dict]:
        with TypeInferServer(threads=threads) as srv:
            return srv.infer_repo(sub)

    out: dict[str, dict] = {}
    with ThreadPoolExecutor(max_workers=len(chunks)) as ex:
        for r in ex.map(_one, chunks):
            out.update(r)
    return out


def infer_repo_dir(repo: Path, *, server: TypeInferServer | None = None,
                   jobs: int | None = None) -> dict[str, tuple[Path, InferResult]]:
    """Cross-file inference over every `.py` under `repo` (the `inferRepo` task). Returns each module's
    source path and collected types, keyed by dotted module name. Standalone (`server=None`) it runs
    full-throttle: IR generation fans across a process pool and inference across parallel exe processes
    (`jobs` cores, default all). Pass `server` to reuse a caller-owned unit-scoped server instead —
    that path stays single-process (the caller owns the one server)."""
    if server is not None:
        mods, files = _collect_repo_modules(repo)
        stamped = server.infer_repo(mods)
    else:
        jobs = jobs or (os.cpu_count() or 8)
        mods, files = _collect_repo_modules(repo, jobs=jobs)
        stamped = _infer_repo_parallel(mods, jobs)
    out: dict[str, tuple[Path, InferResult]] = {}
    for dotted, st in stamped.items():
        src = files.get(dotted)
        if src is not None:
            out[dotted] = (src, collect_types(st))
    return out
