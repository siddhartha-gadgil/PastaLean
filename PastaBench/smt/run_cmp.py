"""Elaborate every .cache/cmp/*.lean (`gen_cmp.py`) with `lake lean`, logging each `taste_cmp` goal to
.cache/cmp.jsonl; `PASTALEAN_CMP_NO_TASTE=1` runs only the SMT closers. Needs the `PastaSmt` library
(lean-smt) built: see docs/smt.md."""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
log = HERE / ".cache/cmp.jsonl"
log.unlink(missing_ok=True)
env = {**os.environ, "PASTALEAN_CMP_LOG": str(log),
       "PATH": str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.36.0/bin") + ":" + os.environ["PATH"]}
files = sorted((HERE / ".cache/cmp").glob("*.lean"))


def one(f):
    try:
        p = subprocess.run(["prlimit", f"--as={64 << 30}", "lake", "lean", str(f)], cwd=ROOT, env=env,
                           capture_output=True, text=True, timeout=900)
        f.with_suffix(".out").write_text(p.stdout + p.stderr)
        return p.returncode
    except subprocess.TimeoutExpired:
        return "timeout"


with ThreadPoolExecutor(int(sys.argv[1]) if len(sys.argv) > 1 else 8) as ex:
    codes = list(ex.map(one, files))
print({c: codes.count(c) for c in set(codes)})
