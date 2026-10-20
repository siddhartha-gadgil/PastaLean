"""Type CHECKING: the Lean checker's verdicts on a file or a repo.

Inference answers "what is this?"; checking answers "is this consistent?". The verdicts are produced
entirely in Lean (`TypeInfer/Diagnostics/`, the `checkTypes` task) — a written annotation the body
contradicts, and a slot whose uses no single type satisfies. This module only ships the IR over and
formats what comes back; it never decides anything itself.

Each diagnostic arrives with both type worlds (`lean_expected`/`lean_actual` alongside
`expected`/`actual`) and a Lean-style multi-line `render`, so `to_text` just prefixes the file.

`certify_paths` runs the same checks but keeps the CERTIFICATE behind each verdict, and
`verify_certificates` re-checks those certificates against the files they name. The second pass runs
no inference at all (`TypeInfer/Certificate/Check.lean`), so it is cheap enough to run over a whole
corpus as a self-audit.
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


def _fan(items: list, jobs: int, batch) -> list:
    """Fan a batched exe task across parallel exe processes, one result per input, in order.

    A single batch call saturates at ~7-8 cores (the Lean task scheduler contends on one shared
    heap), so several processes over large shards scale past that — the same split
    `_infer_repo_parallel` makes for inference. `batch(server, group)` runs one group."""
    shards = max(1, min(jobs // 8, math.ceil(len(items) / SHARD)))
    if shards <= 1:
        with TypeInferServer(threads=jobs) as srv:
            return batch(srv, items)

    size = math.ceil(len(items) / shards)
    groups = [items[i:i + size] for i in range(0, len(items), size)]
    threads = max(2, jobs // len(groups))

    def _one(group: list) -> list:
        with TypeInferServer(threads=threads) as srv:
            return batch(srv, group)

    out: list = []
    with ThreadPoolExecutor(max_workers=len(groups)) as ex:
        for part in ex.map(_one, groups):
            out.extend(part)
    return out


def _check_shards(live: list[tuple[str, dict]], jobs: int) -> list[tuple[str, dict]]:
    """Every `(file, diagnostic)` pair over the given IRs."""
    def batch(srv: TypeInferServer, group: list[tuple[str, dict]]) -> list[tuple[str, dict]]:
        results = srv.check_batch([ir for _p, ir in group])
        return [(p, d) for (p, _ir), r in zip(group, results) for d in r["diagnostics"]]
    return _fan(live, jobs, batch)


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
    live = _live_irs(paths, jobs)
    return _check_shards(live, jobs) if live else []


def check_paths_report(paths: list[str], *, jobs: int | None = None) -> dict:
    """`check_paths`, plus an honest account of what was actually checked.

    A file whose IR the front end cannot build is skipped — one unparseable file must not sink a run —
    but `check_paths` returns only diagnostics, so a caller counting its inputs as "files checked"
    overstates coverage by however many were dropped. This reports the split, which is what a
    precision benchmark needs: a diagnostic rate is only meaningful over the files that were read."""
    jobs = jobs or (os.cpu_count() or 8)
    if not paths:
        return {"diagnostics": [], "checked": 0, "ir_failed": 0}
    live = _live_irs(paths, jobs)
    return {"diagnostics": _check_shards(live, jobs) if live else [],
            "checked": len(live), "ir_failed": len(paths) - len(live)}


def check_dir(repo: Path, *, jobs: int | None = None) -> list[tuple[str, dict]]:
    """Check every `.py` under `repo`, in path order."""
    return check_paths([str(p) for p in sorted(repo.rglob("*.py"))], jobs=jobs)


def _live_irs(paths: list[str], jobs: int) -> list[tuple[str, dict]]:
    """Each file's raw IR, skipping the ones the front end cannot build. The `ast` walk is pure
    Python, so this forks rather than threads."""
    if jobs > 1 and len(paths) > 1:
        with get_context("fork").Pool(min(jobs, len(paths))) as pool:
            results = pool.map(_ir_for_file, paths, chunksize=4)
    else:
        results = [_ir_for_file(p) for p in paths]
    return [(path, json.loads(raw)) for r in results if r is not None for path, raw in [r]]


def certify_paths(paths: list[str], *, jobs: int | None = None) -> list[tuple[str, dict, dict]]:
    """Check an explicit list of files and keep the certificate behind each verdict.

    Returns `(file, ir, {"ok", "diagnostics", "certificate"})`. The IR comes back because a
    certificate is only meaningful against the exact program it was produced for — `verify_certificates`
    needs that same tree, and rebuilding it is the expensive half."""
    if not paths:
        return []
    jobs = jobs or (os.cpu_count() or 8)
    live = _live_irs(paths, jobs)
    if not live:
        return []

    def batch(srv: TypeInferServer, group: list[tuple[str, dict]]) -> list[tuple[str, dict, dict]]:
        results = srv.certify_batch([ir for _p, ir in group])
        return [(p, ir, r) for (p, ir), r in zip(group, results)]

    return _fan(live, jobs, batch)


def verify_certificates(items: list[tuple[str, dict, dict]], *,
                        jobs: int | None = None) -> list[tuple[str, dict]]:
    """Re-check certificates against the programs they name. `items` is
    `(file, ir, certificate)`; the result is `(file, {"valid", "reason"})` in the same order.

    This is the half that needs no engine, so a rejection here is a statement about the certificate,
    not about the Python."""
    if not items:
        return []
    jobs = jobs or (os.cpu_count() or 8)

    def batch(srv: TypeInferServer, group: list[tuple[str, dict, dict]]) -> list[tuple[str, dict]]:
        results = srv.verify_batch([{"ast": ir, "certificate": cert} for _p, ir, cert in group])
        return [(p, r) for (p, _ir, _c), r in zip(group, results)]

    return _fan(items, jobs, batch)


#: One certificate per source file, mirroring the corpus tree under the output directory. A
#: certificate names the program it is about by hash, so a stale one is refused rather than misread.
CERT_SUFFIX = ".cert.json"


def cert_path(out: Path, src: str, root: Path | None = None) -> Path:
    """Where `src`'s certificate lives under `out`. Paths mirror the corpus tree so two files with the
    same basename do not collide."""
    rel = Path(src)
    if root is not None:
        try:
            rel = rel.resolve().relative_to(root.resolve())
        except ValueError:
            rel = Path(rel.name)
    else:
        rel = Path(rel.name)
    return out / (str(rel) + CERT_SUFFIX)


#: How a verdict reads in English, for the `says` line on each slot.
def _says(slot: dict) -> str:
    """One line describing what the checker concluded about this variable."""
    v = slot["verdict"]
    kind = v["verdict"]
    declared = slot["judgment"].get("declared")
    if kind == "commits":
        return f"its uses narrow to {v['type']}"
    if kind == "unconstrained":
        return "no use constrains it"
    if kind == "conflict":
        return f"uses require both {v['expected']} and {v['actual']}, which no type satisfies"
    if kind == "agrees":
        return f"declared {declared}, and the evidence agrees"
    if kind == "rejects":
        return f"declared {v['expected']}, but the evidence says {v['actual']}"
    return kind


def readable(cert: dict, src: str | None = None) -> dict:
    """The certificate re-ordered for a human reader, with a one-line gloss per slot.

    The Lean side builds its JSON through `Json.mkObj`, which sorts keys, so `slot` and `verdict` —
    the two a reader wants first — come out buried in the middle of the alphabet. Nothing here
    changes the certificate's content: the added `file`, `summary` and `says` fields are ignored when
    it is read back (`Cert.ofCertJson?` looks up the keys it needs by name), so a re-ordered
    certificate still verifies."""
    def slot(s: dict) -> dict:
        return {"slot": s["slot"], "scope": s["scope"], "kind": s["kind"],
                "line": s["line"], "col": s["col"],
                "says": _says(s),
                "verdict": s["verdict"], "judgment": s["judgment"], "evidence": s["evidence"]}

    n_bad = len(cert["diagnostics"])
    out: dict = {}
    if src is not None:
        out["file"] = src
    out["summary"] = (f"{len(cert['slots'])} slots checked, "
                      + ("no type errors" if cert["ok"]
                         else f"{n_bad} type error{'' if n_bad == 1 else 's'}"))
    out["ok"] = cert["ok"]
    out["slots"] = [slot(s) for s in cert["slots"]]
    out["diagnostics"] = cert["diagnostics"]
    out["version"] = cert["version"]
    out["ir_hash"] = cert["ir_hash"]
    return out


def write_certificates(results: list[tuple[str, dict, dict]], out: Path,
                       root: Path | None = None, *, proofs: bool = True) -> dict:
    """Write one certificate per file and return the run manifest. The manifest is the index a later
    verify pass reads, and the per-run record a benchmark can diff.

    Each certificate is written twice: as JSON, which `--verify-cert` re-checks, and (unless
    `proofs=False`) as a `.lean` file whose compilation is the same check performed by Lean's kernel
    instead of by a second program."""
    from .proof import cert_to_lean, lean_name

    out.mkdir(parents=True, exist_ok=True)
    entries = []
    for src, _ir, res in results:
        cert = res.get("certificate")
        if cert is None:
            continue
        dest = cert_path(out, src, root)
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(json.dumps(readable(cert, src), indent=2), encoding="utf-8")
        entry = {"file": src, "certificate": str(dest.relative_to(out)),
                 "ok": res.get("ok", True), "diagnostics": len(res.get("diagnostics", [])),
                 "slots": len(cert["slots"])}
        if proofs:
            lean = dest.with_suffix(".lean")
            lean.write_text(cert_to_lean(cert, lean_name(Path(src).stem), src), encoding="utf-8")
            entry["proof"] = str(lean.relative_to(out))
        entries.append(entry)
    manifest = {
        "tool": TOOL_NAME,
        "files": len(entries),
        "clean": sum(1 for e in entries if e["ok"]),
        "flagged": sum(1 for e in entries if not e["ok"]),
        "slots": sum(e["slots"] for e in entries),
        "entries": entries,
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return manifest


def load_certificates(out: Path, paths: list[str],
                      root: Path | None = None) -> list[tuple[str, dict | None]]:
    """Read back the certificate written for each path, `None` where there is none."""
    loaded = []
    for src in paths:
        dest = cert_path(out, src, root)
        if dest.exists():
            try:
                loaded.append((src, json.loads(dest.read_text(encoding="utf-8"))))
                continue
            except json.JSONDecodeError:
                pass
        loaded.append((src, None))
    return loaded


def verify_written(out: Path, paths: list[str], root: Path | None = None, *,
                   jobs: int | None = None) -> list[tuple[str, dict]]:
    """Re-check every certificate under `out` against the sources it names. Rebuilds each IR, because
    a certificate is only meaningful against the exact program it was produced for."""
    jobs = jobs or (os.cpu_count() or 8)
    certs = dict(load_certificates(out, paths, root))
    live = _live_irs([p for p in paths if certs.get(p) is not None], jobs)
    missing = [(p, {"valid": False, "reason": "no certificate written for this file"})
               for p in paths if certs.get(p) is None]
    return verify_certificates([(p, ir, certs[p]) for p, ir in live], jobs=jobs) + missing


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
