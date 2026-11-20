"""CrossHair's own benchmark: who finds the counterexample to each false contract, and how fast.

Every tool gets the same wall-clock budget per problem, as a separate process:

* `crosshair`  — `crosshair check`, exactly as crosshair-benchmark's own runner invokes it;
* `hypothesis` — plain Hypothesis (`hyp_driver.py`: `from_type` strategies, `assume(pre)`);
* `crosshair_typed` — CrossHair on a copy annotated with TypeInfer's inferred types;
* `refute`     — `pastalean refute`: the Lean search over the translated program (Python only
  executes the witnesses it finds).

    uv run python PastaBench/pbt_bench/run.py [--timeout 60] [--jobs 12] [--tools crosshair,hypothesis,pastalean]
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from fetch import fetch  # noqa: E402

sys.path.insert(0, str(HERE.parents[1] / "src"))
from pastalean.refute.limits import apply_memory_cap  # noqa: E402



def command(tool: str, path: Path, timeout: int) -> list[str]:
    py = sys.executable
    if tool == "crosshair":
        return [py, "-m", "crosshair", "check", f"--per_condition_timeout={timeout}",
                f"--per_path_timeout={timeout ** 0.5}", str(path)]
    if tool == "crosshair_typed":
        return [py, str(HERE / "crosshair_typed.py"), str(path), str(timeout)]
    if tool == "hypothesis":
        return [py, str(HERE / "hyp_driver.py"), str(path)]
    if tool == "refute":
        # Translation, then the Lean search in both twins (`--tests` past any reachable count, so it runs
        # until the deadline like the other tools), then CPython executes the witnesses found.
        return [py, "-m", "pastalean", "refute", str(path), "--json", "--tests", str(10 ** 9),
                "--time", str(int(timeout * 1000 * 0.85))]
    raise ValueError(tool)


def found(tool: str, code: int, out: str) -> str | None:
    """The counterexample a tool reported, or `None`."""
    if tool in ("crosshair", "crosshair_typed"):
        lines = [l for l in out.splitlines() if ": error: " in l]
        return lines[0].split(": error: ", 1)[1] if lines else None
    if tool == "hypothesis":
        lines = [l for l in out.splitlines() if l.startswith("FOUND")]
        return lines[0] if lines else None
    try:
        data = json.loads(out[out.index("{"):])
    except ValueError:
        return None
    # A claim is a witness CPython itself saw violate the contract (not, e.g., NONTERMINATION in a twin).
    for o in data.get("obligations", []):
        if o.get("witness") and o["witness"].get("py") == "violates":
            return json.dumps(o["witness"].get("lits", []))
    return None


def run_one(tool: str, path: Path, timeout: int) -> dict:
    t0 = time.monotonic()
    try:
        p = subprocess.run(command(tool, path, timeout), capture_output=True, text=True,
                           timeout=timeout + 15, cwd=str(path.parent), preexec_fn=apply_memory_cap)
        # JSON-reporting tools are parsed from stdout alone: translation warnings go to stderr.
        code, out = p.returncode, (p.stdout if tool == "refute" else p.stdout + p.stderr)
        err_tail = p.stderr[-400:]
    except subprocess.TimeoutExpired as e:
        code, out = -1, (e.stdout or b"").decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        err_tail = "timeout"
    dt = time.monotonic() - t0
    w = found(tool, code, out)
    check = None
    if w is not None:
        # Every claimed counterexample is re-executed against the contract, independently of the tool.
        kind = "crosshair" if tool.startswith("crosshair") else "hypothesis" if tool == "hypothesis" else "pastalean"
        v = subprocess.run([sys.executable, str(HERE / "validate.py"), str(path), kind, w], capture_output=True,
                           text=True, timeout=60, cwd=str(path.parent), preexec_fn=apply_memory_cap)
        check = (v.stdout.strip().splitlines() or ["UNPARSEABLE"])[-1]
    # Benefit of the doubt, marked `*`: a witness the validator cannot re-parse, and a CrossHair witness
    # it rejects (CrossHair prints the arguments *after* the call, so mutated inputs no longer apply).
    credited = check == "UNPARSEABLE" or (tool.startswith("crosshair") and check == "REJECTED")
    return {"tool": tool, "problem": "/".join(path.parts[-2:]), "found": check == "CONFIRMED" or credited,
            "credited": credited,
            "claimed": w is not None, "check": check, "seconds": round(dt, 2), "witness": w,
            "tail": (out[-400:] + " | " + err_tail) if w is None else ""}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("--tools", default="crosshair,crosshair_typed,hypothesis,refute")
    ap.add_argument("--only", help="Substring filter on problem paths.")
    ap.add_argument("--out", default=str(HERE / "results" / "crosshair_benchmark.json"))
    args = ap.parse_args()
    # refute runs warm: the daemon keeps one warm backend per parallel job (`refute/daemon.py`)
    os.environ["PASTALEAN_DAEMON_POOL"] = str(args.jobs)
    root = fetch()["crosshair-benchmark"] / "benchmarks"
    problems = sorted(p for p in root.rglob("crosshair_*.py") if not args.only or args.only in str(p))
    tools = args.tools.split(",")
    jobs = [(t, p) for p in problems for t in tools]
    with ThreadPoolExecutor(args.jobs) as ex:
        results = list(ex.map(lambda tp: run_one(tp[0], tp[1], args.timeout), jobs))
    Path(args.out).parent.mkdir(exist_ok=True)
    Path(args.out).write_text(json.dumps(results, indent=1))

    by = {(r["tool"], r["problem"]): r for r in results}
    names = sorted({r["problem"] for r in results})
    w = max(len(n) for n in names)
    print(f"{'problem':{w}}  " + "  ".join(f"{t[:12]:>12}" for t in tools))
    for n in names:
        cells = []
        for t in tools:
            r = by[(t, n)]
            mark = {"REJECTED": "✗", "UNPARSEABLE": "?"}.get(r.get("check"), "—")
            star = "*" if r.get("credited") else " "
            cells.append(f"{r['seconds']:>10.1f}s{star}" if r["found"] else f"{mark:>12}")
        print(f"{n:{w}}  " + "  ".join(cells))
    print(f"{'solved':{w}}  " + "  ".join(f"{sum(by[(t, n)]['found'] for n in names):>9}/{len(names)}"
                                        for t in tools))
    print(f"(timeout {args.timeout}s per problem and tool; — = no counterexample; every counterexample "
          f"re-checked against the contract: ✗ = rejected; * = credited without confirmation, see run.py)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
