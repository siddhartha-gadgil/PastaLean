"""A warm `pastalean refute`: booting the Lean backend (a Mathlib import) costs ~2.4 s of a ~3.6 s cold
run, while a refutation through a warm backend takes ~0.3 s. The first `pastalean refute` starts this
daemon in the background; later ones send it their command line over a local socket and print what it
returns, so the output is exactly that of a local run.

Requests are served in parallel, each on a warm backend borrowed from a pool that grows on demand up to
the size the caller asks for (`PASTALEAN_DAEMON_POOL`, default 1; ~7 GB per backend), so parallel
benchmark jobs stay warm too. One daemon per backend binary (a rebuild starts a fresh one); it exits after
`IDLE_S` seconds without a request. `PASTALEAN_NO_DAEMON=1` disables it.
"""

from __future__ import annotations

import io
import json
import os
import queue
import socket
import subprocess
import sys
import threading
from pathlib import Path

from ..paths import BACKEND_BINARY

IDLE_S = 600
#: Environment a request carries into the daemon (engine experiments).
FORWARDED_ENV = ("PASTALEAN_REFUTE_CONFIG",)
#: `refute` arguments that name files, resolved against the caller's working directory.
PATH_ARGS = ("file", "against")


def socket_path() -> Path | None:
    try:
        stamp = int(BACKEND_BINARY.stat().st_mtime)
    except OSError:
        return None
    d = Path(os.environ.get("XDG_RUNTIME_DIR") or Path.home() / ".cache") / "pastalean"
    d.mkdir(parents=True, exist_ok=True)
    return d / f"refute-{stamp}.sock"


def pool_size() -> int:
    try:
        return max(1, int(os.environ.get("PASTALEAN_DAEMON_POOL", "1")))
    except ValueError:
        return 1


def _recv(conn: socket.socket) -> bytes:
    chunks = []
    while chunk := conn.recv(65536):
        chunks.append(chunk)
    return b"".join(chunks)


def request(argv: list[str]) -> int | None:
    """Run `pastalean refute argv` in the daemon and print its output; `None` when no daemon answers."""
    path = socket_path()
    if os.environ.get("PASTALEAN_NO_DAEMON") or path is None or not path.exists():
        return None
    try:
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as conn:
            conn.connect(str(path))
            conn.sendall(json.dumps({"argv": argv, "cwd": os.getcwd(), "pool": pool_size(),
                                     "env": {k: os.environ[k] for k in FORWARDED_ENV if k in os.environ}}).encode())
            conn.shutdown(socket.SHUT_WR)
            reply = json.loads(_recv(conn) or b"null")
    except (OSError, ValueError):
        return None
    if not isinstance(reply, dict):
        return None
    sys.stdout.write(reply.get("out", ""))
    sys.stderr.write(reply.get("err", ""))
    return int(reply.get("code", 1))


def spawn() -> None:
    """Start a daemon in the background for later calls (this call still runs locally)."""
    if os.environ.get("PASTALEAN_NO_DAEMON") or socket_path() is None:
        return
    subprocess.Popen([sys.executable, "-m", "pastalean", "refute-daemon"], stdin=subprocess.DEVNULL,
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)


class _ThreadOut(io.TextIOBase):
    """`sys.stdout` / `sys.stderr` for a threaded server: each request thread writes to its own buffer."""

    def __init__(self, real, slot: str):
        self.real, self.slot, self.local = real, slot, threading.local()

    def write(self, s: str) -> int:
        buf = getattr(self.local, self.slot, None)
        return (buf or self.real).write(s)

    def flush(self) -> None:
        if getattr(self.local, self.slot, None) is None:
            self.real.flush()


def serve() -> int:
    """The daemon: requests served in parallel by long-lived workers, each owning one warm session.

    Workers, not a thread per request: a backend dies with the *thread* that started it (its
    parent-death signal), so each backend must be started, and restarted after a hang, by a thread that
    outlives the requests it serves."""
    from .. import Session
    from .. import refute as refute_mod
    from ..main import build_parser

    path = socket_path()
    if path is None:
        return 1
    out, err = _ThreadOut(sys.stdout, "buf"), _ThreadOut(sys.stderr, "buf")
    sys.stdout, sys.stderr = out, err
    conns: queue.Queue = queue.Queue()
    sessions: list = []
    lock = threading.Lock()
    # workers started, workers waiting for a request, and the largest pool any caller asked for
    pool = {"workers": 0, "idle": 0, "cap": pool_size()}

    def handle(conn: socket.socket, session) -> None:
        with conn:
            req = json.loads(_recv(conn) or b"{}")
            with lock:
                pool["cap"] = max(pool["cap"], int(req.get("pool", 1)))
            o, e, code = io.StringIO(), io.StringIO(), 1
            out.local.buf, err.local.buf = o, e
            refute_mod.REQUEST.session, refute_mod.REQUEST.env = session, req.get("env", {})
            try:
                args = build_parser().parse_args(["refute", *req.get("argv", [])])
                for a in PATH_ARGS:
                    v = getattr(args, a, None)
                    if isinstance(v, str) and not os.path.isabs(v):
                        setattr(args, a, os.path.join(req.get("cwd", "/"), v))
                code = args.func(args)
            except SystemExit as ex:   # argparse errors
                code = int(ex.code or 0)
            except Exception as ex:  # noqa: BLE001
                e.write(f"error: {ex}\n")
            finally:
                out.local.buf = err.local.buf = None
                refute_mod.REQUEST.session = None
                refute_mod.REQUEST.env = {}
            conn.sendall(json.dumps({"out": o.getvalue(), "err": e.getvalue(), "code": code}).encode())

    def worker() -> None:
        session = Session(target="command", mode="both")
        with lock:
            sessions.append(session)
        while True:
            with lock:
                pool["idle"] += 1
            conn = conns.get()
            with lock:
                pool["idle"] -= 1
            handle(conn, session)

    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as srv:
        try:
            srv.bind(str(path))
        except OSError:
            return 0    # another daemon got there first
        srv.listen(64)
        srv.settimeout(IDLE_S)
        try:
            while True:
                try:
                    conn, _ = srv.accept()
                except TimeoutError:
                    with lock:
                        quiet = pool["idle"] == pool["workers"] and conns.empty()
                    if quiet:
                        break
                    continue
                with lock:
                    # a request no idle worker can take now gets a new worker, up to the cap
                    if pool["idle"] <= conns.qsize() and pool["workers"] < pool["cap"]:
                        pool["workers"] += 1
                        threading.Thread(target=worker, daemon=True).start()
                conns.put(conn)
        finally:
            for s in sessions:
                s.close()
            path.unlink(missing_ok=True)
    return 0
