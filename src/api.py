"""The importable PastaLean API.

Translating a file boots a Lean backend that imports Mathlib — several seconds at best. A
`Session` holds that process open so a batch of files pays the cost once:

    from pastalean import Session

    with Session(mode="run") as s:
        for path in paths:
            result = s.translate_file(path)
            if result.ok:
                print(result.lean_code)

The module-level `translate` / `translate_file` helpers are the one-shot equivalents; they share a
process-wide backend that stays warm for the life of the interpreter.

Thread-safety: translation drives module-level state in `transpile.driver`, so a `Session`
serialises its own calls with a lock. Prefer one `Session` per thread for real parallelism.
"""

from __future__ import annotations

import json
import os
import threading
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Iterator, Sequence

from .backend import LeanBackendClient
from .paths import REPO_ROOT
# The module, not its names: `driver` carries mutable state (`_LAST_UNSUPPORTED`) that we read
# after each call, and a `from ... import` would freeze the binding at import time.
from .transpile import driver

TARGETS = ("command", "term")
MODES = ("prove", "run", "both")


class TranslationError(RuntimeError):
    """Translation failed and the caller asked for an exception rather than a result object."""


@dataclass
class TranslationResult:
    """Outcome of translating one Python source to Lean."""

    ok: bool
    lean_code: str | None = None
    error: str | None = None
    target: str = "command"
    mode: str = "both"
    source_path: Path | None = None
    #: Source lines that best-effort replaced with `pyUnsupported(...)` placeholders. Non-empty
    #: means the Lean compiles but does not faithfully implement the Python.
    unsupported: list[str] = field(default_factory=list)
    #: Goals `taste?` refuted instead of proving (only with `prove_asserts`): each has the theorem
    #: (`decl`), the witness as Python (`python`) and the kernel-checked `refute_at` proof.
    counterexamples: list[dict] = field(default_factory=list)

    @property
    def degraded(self) -> bool:
        """True when the output contains `pyUnsupported` placeholders standing in for real logic."""
        return bool(self.unsupported) or (self.lean_code is not None and "pyUnsupported" in self.lean_code)

    def raise_for_status(self) -> "TranslationResult":
        if not self.ok:
            where = f" ({self.source_path})" if self.source_path else ""
            raise TranslationError(f"translation failed{where}: {self.error}")
        return self

    def __str__(self) -> str:
        return self.lean_code or ""


# ── Parallel translation (multiprocessing) ──────────────────────────────────────────────────────
# Translating one Python file to Lean is independent of every other, but a single warm backend does
# them serially (one JSON task in / out) and the driver keeps per-call module GLOBALS (`_NUMERIC_MODE`,
# `_HEAP_MODE`, …) — so speed-up comes from separate PROCESSES, each with its own backend + globals,
# NOT threads. `Session.translate_files` shards across a pool transparently, so every caller (the
# eval harnesses included) gets the win without changing. Fixed cost is the ~5s Mathlib boot each
# worker pays once, so small batches stay serial (boot-bound); warm, the convert scales ~linearly.
_PER_WORKER_GB = 1.8


def _mem_available_gb() -> float:
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) / (1024 * 1024)
    except OSError:
        pass
    return 8.0


def auto_translate_jobs(n_files: int) -> int:
    """Memory- and size-aware worker count. Translating one file is cheap (tens of µs/node warm)
    versus the fixed ~5s Mathlib boot each worker pays — and cold boots CONTEND (16 at once take far
    longer than one). So a small/medium batch stays SERIAL (parallel would lose to boot overhead);
    only a large batch, where the convert work finally dwarfs the boots, goes parallel. Measured
    break-even is ~2k files (≤1k loses, ~3k wins ~1.8×); the speed-up plateaus around 8-16 workers
    (boot-bound past that), so we cap there rather than the 16-32 a CPU-heavier stage would use.
    Pulled below by free RAM (`_PER_WORKER_GB`/backend) or core count when either is tight."""
    if n_files < 2000:
        return 1
    cores = os.cpu_count() or 4
    mem_cap = max(1, int(_mem_available_gb() / _PER_WORKER_GB))
    return max(1, min(16, cores, mem_cap, n_files // 250))


def _translate_shard(args: tuple[dict, list[str]]) -> list["TranslationResult"]:
    """One worker: boot a PRIVATE backend from `init_kwargs` and translate a slice of file paths,
    returning the results (picklable `TranslationResult`s the parent re-yields)."""
    init_kwargs, paths = args
    out: list[TranslationResult] = []
    with Session(**init_kwargs) as s:
        for p in paths:
            try:
                out.append(s.translate_file(p))
            except OSError as err:
                out.append(TranslationResult(ok=False, error=str(err), source_path=Path(p)))
    return out


class Session:
    """A warm Lean backend plus the translation options to apply to every call."""

    def __init__(
        self,
        *,
        target: str = "command",
        mode: str = "both",
        best_effort: bool = True,
        prove_asserts: bool = False,
        imports_add: bool = True,
        heap: bool = False,
        repo_root: Path = REPO_ROOT,
        client: LeanBackendClient | None = None,
    ):
        if target not in TARGETS:
            raise ValueError(f"target must be one of {TARGETS}, got {target!r}")
        if mode not in MODES:
            raise ValueError(f"mode must be one of {MODES}, got {mode!r}")
        self.target = target
        self.mode = mode
        self.best_effort = best_effort
        self.prove_asserts = prove_asserts
        self.imports_add = imports_add
        self.heap = heap
        self.client = client or LeanBackendClient(repo_root)
        self._lock = threading.Lock()

    def start(self) -> "Session":
        """Boot the backend now (imports Mathlib) rather than on the first translation."""
        self.client.start()
        # Pull library facts (e.g. which libraries are IO-effectful) from the Lean registry before
        # the first translation — the effect annotation runs before any per-statement backend call.
        driver.refresh_library_info(self.client)
        return self

    def close(self) -> None:
        self.client.close()

    def __enter__(self) -> "Session":
        return self.start()

    def __exit__(self, exc_type, exc, tb) -> None:
        self.close()

    def _opts(self, overrides: dict[str, Any]) -> dict[str, Any]:
        opts = {
            "target": self.target,
            "mode": self.mode,
            "best_effort": self.best_effort,
            "prove_asserts": self.prove_asserts,
            "imports_add": self.imports_add,
            "heap": self.heap,
        }
        unknown = set(overrides) - set(opts)
        if unknown:
            raise TypeError(f"unknown translation option(s): {sorted(unknown)}")
        opts.update(overrides)
        return opts

    def translate(self, source_code: str, *, filepath: str | Path | None = None, **overrides) -> TranslationResult:
        """Translate Python source text to Lean.

        Pass `filepath` when the source came from a file: the type-annotation pre-pass re-reads it
        by path, and without it inference is weaker.
        """
        opts = self._opts(overrides)
        path = Path(filepath) if filepath else None
        with self._lock:
            raw = driver.translate_to_lean(
                source_code,
                opts["target"],
                str(path) if path else None,
                imports_add=opts["imports_add"],
                best_effort=opts["best_effort"],
                mode=opts["mode"],
                prove_asserts=opts["prove_asserts"],
                heap=opts["heap"],
                client=self.client,
            )
            # Set by the front end during the call above; read under the same lock.
            unsupported = list(driver._LAST_UNSUPPORTED)

        if not isinstance(raw, dict) or raw.get("result") is False:
            error = raw.get("error", "translation failed") if isinstance(raw, dict) else str(raw)
            return TranslationResult(
                ok=False, error=error, target=opts["target"], mode=opts["mode"], source_path=path
            )

        code = raw.get(f"lean_{opts['target']}")
        if code is None:
            return TranslationResult(
                ok=False,
                error=f"backend returned no 'lean_{opts['target']}' field",
                target=opts["target"],
                mode=opts["mode"],
                source_path=path,
            )
        return TranslationResult(
            ok=True,
            lean_code=code,
            target=opts["target"],
            mode=opts["mode"],
            source_path=path,
            unsupported=unsupported,
            counterexamples=list(raw.get("counterexamples") or []),
        )

    def translate_file(self, path: str | Path, **overrides) -> TranslationResult:
        path = Path(path)
        return self.translate(path.read_text(encoding="utf-8"), filepath=path, **overrides)

    def translate_files(self, paths: Iterable[str | Path], *, jobs: int | str = "auto",
                        **overrides) -> Iterator[TranslationResult]:
        """Translate many files, yielding a `TranslationResult` per file.

        Parallel by default: `jobs="auto"` shards the files across a memory-aware pool of worker
        PROCESSES (each its own warm backend), transparently — every caller gets the speed-up. Pass
        `jobs=1` to force the serial path through THIS session's backend (e.g. inside a subprocess, or
        to keep original ordering). A small batch stays serial regardless (boot-bound). In parallel
        mode results are yielded shard-by-shard, so ORDER is not the input order — key by
        `result.source_path`, not position."""
        paths = [Path(p) for p in paths]
        n = len(paths)
        j = auto_translate_jobs(n) if jobs == "auto" else max(1, int(jobs))
        if j <= 1 or n <= 1:
            for path in paths:
                try:
                    yield self.translate_file(path, **overrides)
                except OSError as err:
                    yield TranslationResult(ok=False, error=str(err), source_path=path)
            return
        # Bake the per-batch options into each worker's Session (the driver applies them per process).
        init_kwargs = {"target": self.target, "mode": self.mode, "best_effort": self.best_effort,
                       "prove_asserts": self.prove_asserts, "imports_add": self.imports_add,
                       "heap": self.heap}
        init_kwargs.update({k: v for k, v in overrides.items() if k in init_kwargs})
        shards = [[str(p) for p in paths[i::j]] for i in range(j)]
        shards = [sh for sh in shards if sh]
        with ProcessPoolExecutor(max_workers=len(shards)) as ex:
            for results in ex.map(_translate_shard, [(init_kwargs, sh) for sh in shards]):
                yield from results

    def to_json_ir(self, source_code: str, *, filepath: str | Path | None = None,
                   infer_only: bool = False, **overrides) -> dict:
        """The intermediate JSON IR, before the Lean backend sees it. Does not start the backend.
        `infer_only` skips codegen-only effect passes (faster; only valid for the inferTypes task)."""
        opts = self._opts(overrides)
        with self._lock:
            raw = driver.translate_to_json(
                source_code,
                str(filepath) if filepath else None,
                best_effort=opts["best_effort"],
                infer_only=infer_only,
            )
        return json.loads(raw)

    def to_json_ir_file(self, path: str | Path, *, infer_only: bool = False, **overrides) -> dict:
        path = Path(path)
        return self.to_json_ir(path.read_text(encoding="utf-8"), filepath=path,
                               infer_only=infer_only, **overrides)


def _default_session(**kwargs) -> Session:
    """A Session bound to the process-wide backend, so one-shot helpers stay warm across calls."""
    return Session(client=driver._LEAN_BACKEND, **kwargs)


def translate(source_code: str, *, filepath: str | Path | None = None, **kwargs) -> TranslationResult:
    """One-shot translation of Python source text, reusing the process-wide warm backend."""
    session_opts = {k: kwargs.pop(k) for k in list(kwargs) if k in ("target", "mode", "best_effort", "prove_asserts", "imports_add", "heap")}
    return _default_session(**session_opts).translate(source_code, filepath=filepath, **kwargs)


def translate_file(path: str | Path, **kwargs) -> TranslationResult:
    """One-shot translation of a Python file, reusing the process-wide warm backend."""
    path = Path(path)
    return translate(path.read_text(encoding="utf-8"), filepath=path, **kwargs)


def supported_libraries() -> Sequence[str]:
    """Python libraries with a Lean shim under `Libraries/` (numpy, scipy, math, ...)."""
    return sorted(driver.SUPPORTED_LIBRARY_IMPORTS)
