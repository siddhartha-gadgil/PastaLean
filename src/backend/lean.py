"""Compile and execute generated Lean.

Both commands must run with the repo as cwd so `lake` can find `lakefile.toml` and put PastaLean,
Libraries and Mathlib on `LEAN_PATH`. The generated file itself may live anywhere.
"""

from __future__ import annotations

import re
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from ..paths import REPO_ROOT, lake_executable

# `file.lean:12:4: error: unknown identifier 'foo'`, or with Lean's diagnostic code:
# `file.lean:12:4: error(lean.unknownIdentifier): Unknown identifier 'foo'`
DIAGNOSTIC_RE = re.compile(
    r"^(?P<file>[^:]+):(?P<line>\d+):(?P<col>\d+):\s*(?P<severity>error|warning)(?:\([^)]*\))?:\s*(?P<message>.*)$"
)


@dataclass
class Diagnostic:
    line: int
    column: int
    severity: str
    message: str

    def __str__(self) -> str:
        return f"{self.line}:{self.column}: {self.severity}: {self.message}"


@dataclass
class CheckResult:
    ok: bool
    stdout: str = ""
    stderr: str = ""
    diagnostics: list[Diagnostic] = field(default_factory=list)

    @property
    def errors(self) -> list[Diagnostic]:
        return [d for d in self.diagnostics if d.severity == "error"]

    def first_error(self) -> str | None:
        errs = self.errors
        return str(errs[0]) if errs else None


@dataclass
class RunResult:
    ok: bool
    stdout: str = ""
    stderr: str = ""
    returncode: int = 0
    timed_out: bool = False


def parse_diagnostics(output: str) -> list[Diagnostic]:
    """Pull `line:col: severity: message` entries out of Lean's combined output."""
    found = []
    for line in output.splitlines():
        match = DIAGNOSTIC_RE.match(line.strip())
        if match:
            found.append(
                Diagnostic(
                    line=int(match["line"]),
                    column=int(match["col"]),
                    severity=match["severity"],
                    message=match["message"],
                )
            )
    return found


def _materialise(lean_code: str | None, lean_path: str | Path | None, stack):
    """Return a path to a .lean file holding the code, creating a temp file when needed."""
    if (lean_code is None) == (lean_path is None):
        raise ValueError("pass exactly one of lean_code= or lean_path=")
    if lean_path is not None:
        return Path(lean_path)
    handle = tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8")
    stack.append(Path(handle.name))
    handle.write(lean_code)
    handle.close()
    return Path(handle.name)


def compile_check(
    lean_code: str | None = None,
    *,
    lean_path: str | Path | None = None,
    repo_root: Path = REPO_ROOT,
    timeout: float | None = 600.0,
) -> CheckResult:
    """Elaborate a Lean file with `lake env lean`, reporting any diagnostics."""
    temps: list[Path] = []
    try:
        path = _materialise(lean_code, lean_path, temps)
        try:
            proc = subprocess.run(
                [lake_executable(), "env", "lean", str(path)],
                cwd=repo_root,
                text=True,
                capture_output=True,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            return CheckResult(ok=False, stderr=f"lean timed out after {timeout}s")
        combined = proc.stdout + proc.stderr
        return CheckResult(
            ok=proc.returncode == 0,
            stdout=proc.stdout,
            stderr=proc.stderr,
            diagnostics=parse_diagnostics(combined),
        )
    finally:
        for temp in temps:
            temp.unlink(missing_ok=True)


_ROOT_MAIN_RE = re.compile(r"^def main\b", re.M)
_NAMESPACED_MAIN_RE = re.compile(r"^def (main'rn|main)\s*:\s*IO Unit", re.M)


def with_root_main(lean_code: str) -> str:
    """`lean --run` needs a root-level `main`, but generated code defines it inside
    `namespace PastaLean.User.Root`. Append a root alias to it (the runnable twin `main'rn` when
    both twins were emitted). Code that already has a root `main` is returned unchanged."""
    ns_end = lean_code.rfind("end PastaLean.User.Root")
    if ns_end < 0 or _ROOT_MAIN_RE.search(lean_code[ns_end:]):
        return lean_code
    names = set(_NAMESPACED_MAIN_RE.findall(lean_code[:ns_end]))
    entry = "main'rn" if "main'rn" in names else ("main" if "main" in names else None)
    if entry is None:
        return lean_code
    return lean_code.rstrip() + f"\n\ndef main : IO Unit := PastaLean.User.Root.{entry}\n"


def run_program(
    lean_code: str | None = None,
    *,
    lean_path: str | Path | None = None,
    stdin: str = "",
    repo_root: Path = REPO_ROOT,
    timeout: float | None = 600.0,
) -> RunResult:
    """Execute a generated program's `main` with `lake env lean --run`."""
    temps: list[Path] = []
    try:
        if lean_path is not None:
            lean_code, lean_path = Path(lean_path).read_text(encoding="utf-8"), None
        path = _materialise(with_root_main(lean_code), None, temps)
        try:
            proc = subprocess.run(
                [lake_executable(), "env", "lean", "--run", str(path)],
                cwd=repo_root,
                input=stdin,
                text=True,
                capture_output=True,
                timeout=timeout,
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
            stderr=proc.stderr,
            returncode=proc.returncode,
        )
    finally:
        for temp in temps:
            temp.unlink(missing_ok=True)
