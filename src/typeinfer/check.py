"""Type CHECKING: the Lean checker's verdicts on a file or a repo.

Inference answers "what is this?"; checking answers "is this consistent?". The verdicts are produced
entirely in Lean (`TypeInfer/Diagnostics/`, the `checkTypes` task) — a written annotation the body
contradicts, and a slot whose uses no single type satisfies. This module only ships the IR over and
formats what comes back; it never decides anything itself.

Each diagnostic arrives with both type worlds (`lean_expected`/`lean_actual` alongside
`expected`/`actual`) and a Lean-style multi-line `render`, so `to_text` just prefixes the file.
"""

from __future__ import annotations

import json
import math
import os
from concurrent.futures import ThreadPoolExecutor
from multiprocessing import get_context
from pathlib import Path

from ..backend.typeinfer import TypeInferServer
from ..transpile import driver

TOOL_NAME = "typeinfer"

#: Modules per exe process. One `checkBatch` call caps at ~7-8 cores (the Lean task scheduler
#: contends on a single shared heap), exactly as `inferRepo` does, so past this many modules the work
#: is split across several exe processes instead of one bigger call.
SHARD = 32


def check_source(source: str, path: str | None = None, *,
                 server: TypeInferServer | None = None) -> list[dict]:
    """Every type error in one module, as the Lean checker reports it."""
    ir = json.loads(driver.translate_to_json(source, path, best_effort=True, infer_only=True))
    if server is not None:
        return server.check_ast(ir)["diagnostics"]
    with TypeInferServer() as srv:
        return srv.check_ast(ir)["diagnostics"]


def _ir_for_file(path: str) -> tuple[str, str] | None:
    """One file's raw IR as a JSON STRING (strings pickle far cheaper than the parsed tree), or `None`
    if the front-end cannot build it — one unparseable file must not sink a whole run. Module-level so
    a process pool can pickle it."""
    try:
        src = Path(path).read_text(encoding="utf-8")
        return path, driver.translate_to_json(src, path, best_effort=True, infer_only=True)
    except Exception:  # noqa: BLE001
        return None


def _check_shards(live: list[tuple[str, dict]], jobs: int) -> list[tuple[str, dict]]:
    """Fan the checks across parallel exe processes. A single `checkBatch` saturates at ~7-8 cores
    (the Lean task scheduler contends on one shared heap), so several processes over large shards
    scale past that — the same split `_infer_repo_parallel` makes for inference."""
    shards = max(1, min(jobs // 8, math.ceil(len(live) / SHARD)))
    if shards <= 1:
        with TypeInferServer(threads=jobs) as srv:
            results = srv.check_batch([ir for _p, ir in live])
        return [(p, d) for (p, _ir), r in zip(live, results) for d in r["diagnostics"]]

    size = math.ceil(len(live) / shards)
    groups = [live[i:i + size] for i in range(0, len(live), size)]
    threads = max(2, jobs // len(groups))

    def _one(group: list[tuple[str, dict]]) -> list[tuple[str, dict]]:
        with TypeInferServer(threads=threads) as srv:
            results = srv.check_batch([ir for _p, ir in group])
        return [(p, d) for (p, _ir), r in zip(group, results) for d in r["diagnostics"]]

    out: list[tuple[str, dict]] = []
    with ThreadPoolExecutor(max_workers=len(groups)) as ex:
        for part in ex.map(_one, groups):
            out.extend(part)
    return out


def check_paths(paths: list[str], *, jobs: int | None = None) -> list[tuple[str, dict]]:
    """Check an explicit list of files. Returns `(file, diagnostic)` pairs.

    Full throttle by default, parallel on both sides exactly as inference is: the front-end builds
    every IR across a fork pool (`ast` walking is pure Python, so threads would only queue behind the
    GIL), then the checks fan across the exe's task scheduler and, past one process's ~8-core ceiling,
    across several exe processes. `jobs` defaults to every core.

    Per FILE, not per repo: `checkTypes` checks one module against its own annotations, and the
    cross-file fixpoint (`inferRepo`) has no checking counterpart yet."""
    if not paths:
        return []
    jobs = jobs or (os.cpu_count() or 8)
    if jobs > 1 and len(paths) > 1:
        with get_context("fork").Pool(min(jobs, len(paths))) as pool:
            results = pool.map(_ir_for_file, paths, chunksize=4)
    else:
        results = [_ir_for_file(p) for p in paths]
    live = [(path, json.loads(raw)) for r in results if r is not None for path, raw in [r]]
    return _check_shards(live, jobs) if live else []


def check_dir(repo: Path, *, jobs: int | None = None) -> list[tuple[str, dict]]:
    """Check every `.py` under `repo`, in path order."""
    return check_paths([str(p) for p in sorted(repo.rglob("*.py"))], jobs=jobs)


def _pos(d: dict) -> str:
    """`:line:col`, or nothing when the accused node carried no position (a node a pre-pass
    synthesised, or one inlined from another file)."""
    return f":{d['line']}:{d['col']}" if d.get("line") else ""


def to_text(diags: list[tuple[str, dict]]) -> str:
    """Lean-style, one block per error: the Lean type codegen would emit, with the Python type it
    came from as a line comment beside it."""
    return "\n\n".join(f"{file}{_pos(d)}: {d['render']}" for file, d in diags)


def to_lines(diags: list[tuple[str, dict]]) -> str:
    """One line per error, for grep-ability."""
    return "\n".join(f"{file}{_pos(d)}: error: {d['message']}" for file, d in diags)


def to_github(diags: list[tuple[str, dict]]) -> str:
    """GitHub Actions workflow commands."""
    return "\n".join(
        f"::error file={file},line={d.get('line') or 1},col={d.get('col') or 1},"
        f"title=typeinfer {d['kind']}::{d['message']}"
        for file, d in diags
    )


def to_sarif(diags: list[tuple[str, dict]]) -> str:
    """SARIF 2.1.0 JSON — the interchange format code-scanning dashboards ingest."""
    rules = {}
    for _file, d in diags:
        rules.setdefault(d["kind"], {"id": d["kind"], "shortDescription": {"text": d["kind"]}})
    results = [
        {
            "ruleId": d["kind"],
            "level": "error",
            "message": {"text": d["message"]},
            "locations": [{
                "physicalLocation": {
                    "artifactLocation": {"uri": file},
                    "region": {"startLine": d.get("line") or 1, "startColumn": d.get("col") or 1},
                }
            }],
        }
        for file, d in diags
    ]
    doc = {
        "version": "2.1.0",
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "runs": [{
            "tool": {"driver": {"name": TOOL_NAME, "rules": list(rules.values())}},
            "results": results,
        }],
    }
    return json.dumps(doc, indent=2)
