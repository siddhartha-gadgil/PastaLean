"""Client for the standalone `typeinfer` Lean binary.

Type inference is a pure `Json -> Json` pipeline in Lean (`lowerGenerators -> desugarAst ->
ssaModule -> inferModule`) that touches no `Environment`, so the `typeinfer` executable runs it
without the ~4s/~1GiB Mathlib boot the full `py2lean` backend pays. This module is the thin Python
side: it hands a JSON IR module to the exe and reads back the type-stamped AST. `TypeInferServer` is
a persistent exe process scoped to one unit of work (a file or a repo) that answers many tasks over a
single ~40 ms spawn; the module-level `infer_ast`/`infer_batch`/`infer_repo` are one-shot wrappers
over it. No Mathlib to boot either way.
"""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path

from .. import paths


class TypeInferUnavailable(RuntimeError):
    """The `typeinfer` binary is missing or failed to answer."""


def typeinfer_exe() -> Path:
    exe = Path(paths.LAKE_BIN_DIR) / "typeinfer"
    if not exe.exists():
        raise TypeInferUnavailable(
            f"typeinfer binary not found at {exe} — build it with `lake build typeinfer`."
        )
    return exe


class TypeInferServer:
    """A persistent `typeinfer --server` process that answers many tasks over one spawn.

    Scope one server to a *unit of work* — a single file, or a single repo — and reuse it for every
    Lean task that unit issues, then close it (it is a context manager). Independent units get their
    OWN server: a TypyBench run over 50 repos uses 50 servers, one per repo, so there is no cross-unit
    state and separate units still parallelise. The Lean `serverLoop` streams one task per line, so
    the ~40 ms process spawn is paid once per unit instead of once per task. The line protocol also
    sidesteps argv-length limits on a large AST.

    `LEAN_NUM_THREADS` sizes the exe's task-scheduler pool so `inferBatch`/`inferRepo` fan across the
    machine's cores in-process. A dead process is respawned on the next task."""

    def __init__(self, threads: int | None = None) -> None:
        self._proc: subprocess.Popen | None = None
        # Size the exe's task-scheduler pool. Default: the whole machine (one server per unit). When
        # several servers run concurrently (parallel-chunk repo inference), pass a per-server slice so
        # the processes together stay at ~one thread per core rather than oversubscribing.
        self._threads = threads or min(os.cpu_count() or 8, 64)

    def _ensure(self) -> subprocess.Popen:
        if self._proc is not None and self._proc.poll() is None:
            return self._proc
        exe = typeinfer_exe()
        env = {**os.environ, "LEAN_NUM_THREADS": str(self._threads)}
        self._proc = subprocess.Popen(
            [str(exe), "--server"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, env=env,
        )
        return self._proc

    def run(self, task: dict) -> dict:
        """Send one task, read its single JSON response line."""
        proc = self._ensure()
        try:
            proc.stdin.write(json.dumps(task) + "\n")
            proc.stdin.flush()
            line = proc.stdout.readline()
        except (BrokenPipeError, OSError) as err:
            raise TypeInferUnavailable(f"typeinfer server died: {self._kill_and_drain() or err}")
        if not line:
            raise TypeInferUnavailable(f"typeinfer produced no output (stderr: {self._kill_and_drain()})")
        resp = json.loads(line)
        if not resp.get("result", False):
            raise TypeInferUnavailable(resp.get("error", "typeinfer task failed"))
        return resp

    def infer_ast(self, ast: dict) -> dict:
        """Whole-module inference on one JSON IR module; returns the type-stamped AST. Best-effort:
        on a pre-pass failure the exe returns the original AST unchanged, not an error."""
        return self.run({"task": "inferTypes", "ast": ast}).get("ast", ast)

    def infer_batch(self, asts: list[dict]) -> list[dict]:
        """Infer a list of independent modules in one call, fanned across cores in the exe (no
        cross-file resolution — use `infer_repo` for that)."""
        return self.run({"task": "inferBatch", "asts": asts}).get("results", [])

    def infer_repo(self, modules: dict[str, dict]) -> dict[str, dict]:
        """Repo-level inference: `modules` maps each dotted module name to its raw IR. Lean resolves
        imports, composes the repo, runs one cross-file fixpoint, returns each module's stamped IR."""
        return self.run({"task": "inferRepo", "modules": modules}).get("modules", {})

    def close(self) -> None:
        proc, self._proc = self._proc, None
        if proc is None:
            return
        try:
            if proc.stdin and not proc.stdin.closed:
                proc.stdin.close()
        except OSError:
            pass
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()

    def _kill_and_drain(self) -> str:
        """Terminate the (failed) process and return whatever it left on stderr."""
        proc = self._proc
        self.close()
        try:
            return (proc.stderr.read() or "").strip() if proc and proc.stderr else ""
        except OSError:
            return ""

    def __enter__(self) -> "TypeInferServer":
        self._ensure()
        return self

    def __exit__(self, *_exc) -> None:
        self.close()

    def __del__(self) -> None:
        try:
            self.close()
        except Exception:  # noqa: BLE001  (best-effort cleanup during interpreter shutdown)
            pass


# Module-level one-shot helpers: each opens a fresh server for one task and closes it. Use them for a
# single call; for many calls within one unit, create a `TypeInferServer` and reuse it.

def infer_ast(ast: dict) -> dict:
    with TypeInferServer() as srv:
        return srv.infer_ast(ast)


def infer_batch(asts: list[dict]) -> list[dict]:
    with TypeInferServer() as srv:
        return srv.infer_batch(asts)


def infer_repo(modules: dict[str, dict]) -> dict[str, dict]:
    with TypeInferServer() as srv:
        return srv.infer_repo(modules)
