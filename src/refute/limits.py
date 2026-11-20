"""A per-process memory cap for everything PastaLean spawns (search harnesses, the Lean backend,
benchmark tools). The cap is the address-space limit, `PASTALEAN_MEM_GB` gigabytes (default 64; `0`
disables it): a runaway process gets a `MemoryError` instead of exhausting the machine. It bounds
*virtual* memory, which Lean reserves far beyond what it touches (mmapped `.olean`s, thread stacks):
at 32 GB a Mathlib-importing `lean` fails with "failed to create thread".

Importable both as `pastalean.refute.limits` and, from the harness scripts, as a sibling `limits`.
"""

from __future__ import annotations

import os
import resource

DEFAULT_GB = 64


def cap_bytes() -> int | None:
    try:
        gb = float(os.environ.get("PASTALEAN_MEM_GB", DEFAULT_GB))
    except ValueError:
        gb = DEFAULT_GB
    return int(gb * 2 ** 30) if gb > 0 else None


def apply_memory_cap() -> None:
    """Cap this process (use directly, or as `preexec_fn` so it applies to a child)."""
    cap = cap_bytes()
    if cap is None:
        return
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    if hard != resource.RLIM_INFINITY:
        cap = min(cap, hard)
    if soft == resource.RLIM_INFINITY or soft > cap:
        resource.setrlimit(resource.RLIMIT_AS, (cap, hard))


def lean_env(base: dict[str, str] | None = None) -> dict[str, str]:
    """The environment (`base`, default ours) for a Lean process that evaluates programs: no panic
    backtraces, since every Python runtime error is a Lean panic and symbolising one costs ~70 ms."""
    return {**(os.environ if base is None else base), "LEAN_BACKTRACE": "0"}


def backend_preexec() -> None:
    """`preexec_fn` for a long-lived Lean server: the memory cap, and death with its parent (Linux), so a
    killed client does not leave the server spinning on an abandoned search."""
    apply_memory_cap()
    try:
        import ctypes
        import signal
        ctypes.CDLL("libc.so.6", use_errno=True).prctl(1, signal.SIGKILL)   # PR_SET_PDEATHSIG
    except (OSError, AttributeError):
        pass
