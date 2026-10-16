"""Run a Python program the way the Lean twin is run, so the two can be compared.

`backend.lean.run_program` executes the transpiled Lean; this executes the original Python. Both
take the same source-plus-stdin and return the same `RunResult`, which is what lets the web UI put
their outputs side by side and say whether they agree.

This executes the caller's code in a subprocess. It is not a sandbox.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence

from .backend.lean import RunResult
from .paths import REPO_ROOT


def run_python(source: str, *, stdin: str = "", timeout: float | None = 60.0,
               extra_paths: Sequence[Path] = ()) -> RunResult:
    """Execute `source` with CPython, feeding it `stdin`. `extra_paths` are prepended to
    PYTHONPATH (e.g. a directory providing the `contracts` shim)."""
    env = None
    if extra_paths:
        env = dict(os.environ)
        env["PYTHONPATH"] = os.pathsep.join([*map(str, extra_paths), env.get("PYTHONPATH", "")]).rstrip(os.pathsep)
    with tempfile.NamedTemporaryFile("w", suffix=".py", delete=False, encoding="utf-8") as handle:
        handle.write(source)
        script = Path(handle.name)
    try:
        try:
            proc = subprocess.run(
                [sys.executable, str(script)],
                cwd=REPO_ROOT,
                input=stdin,
                text=True,
                capture_output=True,
                timeout=timeout,
                env=env,
            )
        except subprocess.TimeoutExpired as err:
            return RunResult(
                ok=False,
                stdout=err.stdout or "",
                stderr=f"program timed out after {timeout}s",
                returncode=-1,
                timed_out=True,
            )
        return RunResult(
            ok=proc.returncode == 0,
            stdout=proc.stdout,
            # The temp path leaks into tracebacks and means nothing to the caller.
            stderr=proc.stderr.replace(str(script), "<program>"),
            returncode=proc.returncode,
        )
    finally:
        script.unlink(missing_ok=True)
