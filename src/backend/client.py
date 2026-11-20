"""Client for the Lean `py2lean` backend executable.

The backend runs as a persistent line-oriented server: one JSON task per line in, one JSON
response per line out. Booting it imports PastaLean + Mathlib + Libraries, which is slow, so a
single client should be reused across many translations.
"""

from __future__ import annotations

import json
import logging
import os
import select
import subprocess
import threading
from collections import deque
from pathlib import Path

try:
    import fcntl  # POSIX advisory file locking; serializes the backend build across processes.
except ImportError:  # pragma: no cover - non-POSIX
    fcntl = None

from ..paths import REPO_ROOT, lake_executable
from ..refute.limits import backend_preexec, lean_env

logger = logging.getLogger(__name__)

# Booting the backend imports Mathlib; on a cold page cache that takes far longer than a normal
# request. A too-small budget here makes the first request time out, fall back to a one-shot
# `lake exe`, and (under best-effort) silently degrade real code to `pyUnsupported` placeholders.
DEFAULT_STARTUP_TIMEOUT = float(os.environ.get("PASTALEAN_STARTUP_TIMEOUT", "300"))
DEFAULT_REQUEST_TIMEOUT = float(os.environ.get("PASTALEAN_REQUEST_TIMEOUT", "60"))
DEFAULT_PROVE_TIMEOUT = float(os.environ.get("PASTALEAN_PROVE_TIMEOUT", "600"))


class BackendError(RuntimeError):
    """The Lean backend could not be built or started."""


class LeanBackendClient:
    """Persistent line-oriented client for the Lean backend server mode."""

    def __init__(
        self,
        cwd: Path = REPO_ROOT,
        *,
        startup_timeout: float = DEFAULT_STARTUP_TIMEOUT,
        request_timeout: float = DEFAULT_REQUEST_TIMEOUT,
    ):
        self.cwd = cwd
        self.proc = None
        self.startup_timeout = startup_timeout
        self.request_timeout = request_timeout
        # True once a request has come back from this process, so we know Mathlib is imported and
        # the ordinary (short) per-request budget applies from here on.
        self._warm = False
        # Cached `libraryInfo` response (library facts declared in `Libraries/Registry.lean`).
        self._library_info = None
        self._stderr_lines = deque(maxlen=200)
        self._stderr_thread = None

    @property
    def binary_path(self):
        return self.cwd / ".lake" / "build" / "bin" / "py2lean"

    def _tracked_backend_sources(self):
        """Yield Lean source files whose freshness determines whether `py2lean` must be rebuilt."""
        explicit_files = [
            self.cwd / "py2lean.lean",
            self.cwd / "lakefile.lean",
            self.cwd / "lakefile.toml",
            self.cwd / "lean-toolchain",
        ]
        for path in explicit_files:
            if path.exists():
                yield path

        pastalean_dir = self.cwd / "PastaLean"
        if pastalean_dir.exists():
            yield from pastalean_dir.rglob("*.lean")
        libraries_dir = self.cwd / "Libraries"
        if libraries_dir.exists():
            yield from libraries_dir.rglob("*.lean")

    def _binary_needs_rebuild(self):
        """Return true when the backend binary is missing or older than tracked Lean sources."""
        binary = self.binary_path
        if not binary.exists():
            logger.debug("py2lean backend binary is missing; rebuild required.")
            return True

        binary_mtime = binary.stat().st_mtime
        latest_source_mtime = max(
            (path.stat().st_mtime for path in self._tracked_backend_sources()),
            default=0.0,
        )
        if latest_source_mtime > binary_mtime:
            logger.debug(
                "A tracked Lean source is newer than the py2lean backend binary; rebuild required."
            )
            return True
        return False

    def _run_lake_build(self):
        logger.debug("Building py2lean backend binary before starting server.")
        build = subprocess.run(
            [lake_executable(), "build", "py2lean"],
            cwd=self.cwd,
            text=True,
            capture_output=True,
        )
        if build.returncode != 0:
            raise BackendError(
                build.stderr.strip() or build.stdout.strip() or "lake build py2lean failed"
            )

    def _ensure_binary(self):
        if not self._binary_needs_rebuild():
            logger.debug("Reusing existing py2lean backend binary; no rebuild needed.")
            return

        # Serialize the build across processes. Without this, N parallel workers (e.g. `regen_examples.py
        # --jobs`) each run `lake build py2lean` at once; they contend on lake's `.lake` lock, all but one
        # fail to start the backend, and best-effort then silently degrades every statement to
        # `pyUnsupported`. With an exclusive lock, the first worker builds while the rest wait, then
        # re-check and reuse the freshly-built binary.
        if fcntl is None:
            self._run_lake_build()
            return

        lock_dir = self.cwd / ".lake"
        lock_dir.mkdir(parents=True, exist_ok=True)
        lock_path = lock_dir / "py2lean-build.lock"
        with open(lock_path, "w") as lock_file:
            fcntl.flock(lock_file, fcntl.LOCK_EX)
            try:
                # Another worker may have built it while we blocked on the lock — re-check first.
                if self._binary_needs_rebuild():
                    self._run_lake_build()
            finally:
                fcntl.flock(lock_file, fcntl.LOCK_UN)

    def _command(self):
        # The binary itself, not `lake env <binary>`: a parent-death signal set before exec must land
        # on the server (lake would pass it no further), so `_lake_env` supplies lake's environment.
        return [str(self.binary_path), "--server"]

    _lake_env_cache: dict[str, str] | None = None

    def _lake_env(self) -> dict[str, str]:
        """The environment `lake env` runs a command in (LEAN_PATH, LEAN_SYSROOT, …), read once."""
        if LeanBackendClient._lake_env_cache is None:
            out = subprocess.run([lake_executable(), "env", "env", "-0"], cwd=self.cwd, capture_output=True,
                                 text=True, check=True).stdout
            LeanBackendClient._lake_env_cache = dict(kv.split("=", 1) for kv in out.split("\0") if "=" in kv)
        return LeanBackendClient._lake_env_cache

    def _drain_stderr(self):
        assert self.proc is not None and self.proc.stderr is not None
        stream = self.proc.stderr
        try:
            for line in stream:
                line = line.rstrip()
                if not line:
                    continue
                self._stderr_lines.append(line)
                logger.debug("Lean backend stderr: %s", line)
        except (ValueError, OSError):   # `close()` shut the pipe under us (a restart after a hang)
            pass

    def _recent_stderr(self):
        return "\n".join(self._stderr_lines)

    def _task_payload(self, ast_json, target, check, numeric_mode, run_suffix, user_names,
                      best_effort=False, heap=False):
        return json.dumps(
            {
                "task": "translate",
                "ast": ast_json,
                "target": target,
                "check": check,
                "numericMode": numeric_mode,
                "runSuffix": run_suffix,
                "userNames": list(user_names),
                "best_effort": best_effort,
                "heap": heap,
            },
            separators=(",", ":"),
        )

    def _one_shot_request(self, json_task, target):
        """Fallback backend path that avoids the persistent server when it misbehaves."""
        cmd = [lake_executable(), "exe", "py2lean", json_task, target]
        logger.debug("Falling back to one-shot Lean backend.")
        proc = subprocess.run(cmd, cwd=self.cwd, text=True, capture_output=True)
        if proc.returncode != 0:
            return {
                "result": False,
                "error": proc.stderr.strip() or proc.stdout.strip() or "Lean backend failed",
            }
        output = proc.stdout.strip()
        try:
            return json.loads(output)
        except json.JSONDecodeError as err:
            return {
                "result": False,
                "error": f"Invalid JSON response from one-shot Lean backend: {err}\n{output}",
            }

    def start(self):
        if self.proc is not None and self.proc.poll() is None:
            return
        self._ensure_binary()
        cmd = self._command()
        logger.debug("Starting persistent Lean backend: %s", cmd)
        self.proc = subprocess.Popen(
            cmd,
            cwd=self.cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
            preexec_fn=backend_preexec,
            env=lean_env(self._lake_env()),
        )
        self._warm = False
        self._stderr_lines.clear()
        self._stderr_thread = threading.Thread(target=self._drain_stderr, daemon=True)
        self._stderr_thread.start()

    def close(self):
        if self.proc is None:
            return
        try:
            if self.proc.stdin is not None:
                self.proc.stdin.close()
        except BrokenPipeError:
            pass
        try:
            self.proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=2)
        finally:
            if self.proc.stdout is not None:
                self.proc.stdout.close()
            if self.proc.stderr is not None:
                self.proc.stderr.close()
        self.proc = None
        self._warm = False
        self._stderr_thread = None

    def _read_response(self, timeout):
        """Wait `timeout` seconds for one response line. Returns None if the backend went away or
        did not answer in time (the caller falls back to a one-shot run)."""
        assert self.proc is not None and self.proc.stdout is not None
        ready, _, _ = select.select([self.proc.stdout], [], [], timeout)
        if not ready:
            return None
        line = self.proc.stdout.readline()
        if not line:
            return None
        return line.strip()

    def request(
        self,
        ast_json,
        target,
        check=True,
        *,
        numeric_mode="exact",
        run_suffix="",
        user_names=(),
        best_effort=False,
        heap=False,
    ):
        """Send one translation request to the persistent Lean backend."""
        self.start()
        assert self.proc is not None
        assert self.proc.stdin is not None

        json_task = self._task_payload(ast_json, target, check, numeric_mode, run_suffix, user_names,
                                       best_effort=best_effort, heap=heap)
        logger.debug("Sending request to Lean backend: target=%s check=%s", target, check)
        try:
            self.proc.stdin.write(json_task + "\n")
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.close()
            return self._one_shot_request(json_task, target)

        # The first response also covers `importModules` of Mathlib, so it gets the startup budget.
        timeout = self.request_timeout if self._warm else self.startup_timeout
        response_line = self._read_response(timeout)
        if response_line is None:
            logger.debug("Persistent Lean backend gave no response in %ss; retrying one-shot.", timeout)
            self.close()
            return self._one_shot_request(json_task, target)

        self._warm = True
        logger.debug("Lean backend response: %s", response_line)
        try:
            return json.loads(response_line)
        except json.JSONDecodeError as err:
            logger.debug("Persistent Lean backend returned invalid JSON; retrying one-shot: %s", err)
            self.close()
            return self._one_shot_request(json_task, target)

    def prove_file(self, code, timeout=DEFAULT_PROVE_TIMEOUT):
        """Elaborate an assembled generated file in the WARM backend so `taste?` searches each
        assert; return the parsed JSON carrying the ordered list of winning tactic strings
        (`winners`). Uses a long timeout because this elaborates the whole program — a
        `nlinarith`/`grind` search would blow past the ordinary per-request budget."""
        return self._long_task({"task": "proveFile", "code": code}, timeout)

    def refute(self, code, targets, witnesses=None, config=None, timeout=DEFAULT_PROVE_TIMEOUT, evals=None):
        """Search for and cross-check counterexamples in both Lean worlds (the `refute` task): `targets`
        name each obligation's theorem / checker constants, `witnesses` are inputs found elsewhere (e.g.
        by a CPython search) to evaluate in both twins, `evals` functions to evaluate at given inputs.
        See `PastaLean/PyVerify/Refute/Task.lean`."""
        payload = {"task": "refute", "code": code, "targets": targets,
                   "witnesses": witnesses or [], "config": config or {}, "evals": evals or []}
        return self._long_task(payload, timeout)

    def _long_task(self, payload, timeout):
        """One whole-file request with a long budget; `None` (and a restarted backend) on no answer."""
        self.start()
        assert self.proc is not None and self.proc.stdin is not None
        json_task = json.dumps(payload, separators=(",", ":"))
        try:
            self.proc.stdin.write(json_task + "\n")
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.close()
            return None
        # A cold backend must still import Mathlib before it can elaborate anything.
        budget = timeout if self._warm else timeout + self.startup_timeout
        line = self._read_response(budget)
        if line is None:
            logger.debug("%s got no response in %ss.", payload.get("task"), budget)
            self.close()
            return None
        self._warm = True
        try:
            return json.loads(line)
        except json.JSONDecodeError as err:
            logger.debug("%s returned invalid JSON: %s", payload.get("task"), err)
            return None

    def infer_types(self, ast_json, timeout=None):
        """Run whole-module type inference in the warm backend and return the AST stamped with
        `_ty` on its binders. Returns the original `ast_json` unchanged on any failure, so this is a
        pure best-effort enrichment — the per-statement translate still runs its intraprocedural
        fallback."""
        self.start()
        assert self.proc is not None and self.proc.stdin is not None
        json_task = json.dumps({"task": "inferTypes", "ast": ast_json}, separators=(",", ":"))
        try:
            self.proc.stdin.write(json_task + "\n")
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.close()
            return ast_json
        budget = (timeout or self.request_timeout) + (0 if self._warm else self.startup_timeout)
        line = self._read_response(budget)
        if line is None:
            self.close()
            return ast_json
        self._warm = True
        try:
            resp = json.loads(line)
        except json.JSONDecodeError:
            return ast_json
        return resp.get("ast", ast_json) if resp.get("result") else ast_json

    def library_info(self, timeout=None):
        """Library facts the driver needs, fetched from the Lean registry so they are declared in
        exactly one place (`Libraries/Registry.lean`). Cached for the process's lifetime. On any
        failure returns `{}` — callers must treat every field as optional."""
        if self._library_info is not None:
            return self._library_info
        self.start()
        assert self.proc is not None and self.proc.stdin is not None
        json_task = json.dumps({"task": "libraryInfo"}, separators=(",", ":"))
        try:
            self.proc.stdin.write(json_task + "\n")
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.close()
            return {}
        budget = (timeout or self.request_timeout) + (0 if self._warm else self.startup_timeout)
        line = self._read_response(budget)
        if line is None:
            self.close()
            return {}
        self._warm = True
        try:
            resp = json.loads(line)
        except json.JSONDecodeError:
            return {}
        if not resp.get("result"):
            return {}
        self._library_info = resp
        return resp

    def __enter__(self):
        self.start()
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()
