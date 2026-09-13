"""Peak memory of a TypyBench single-repo scoring run, three ways, plus wall-clock.

Wraps `score.py --repo <name> --tool <tool>` (one project, whole machine) and samples the tree from
the OS every 10ms, so it captures the tool's engine processes (and, for the multi-process tools,
their forked workers) the same way for every tool:

  RSS_SUM = sum of RSS over all tree processes (over-counts pages shared between processes)
  PSS_SUM = sum of PSS (proportional set size: shared pages split across their sharers) -- the Mem
            column of Table tab:typybench, the fair single-vs-multi-process measure
  RSS_MAX = largest single-process RSS in the tree

Usage: python measure_mem.py --repo vllm --tool pastalean <dataset_dir>
"""
from __future__ import annotations

import argparse
import subprocess
import sys
import time
from pathlib import Path

import psutil

G = 1024 * 1024 * 1024


def snap(proc: psutil.Process) -> tuple[int, int, int]:
    rss_sum = pss_sum = rss_max = 0
    try:
        procs = [proc] + proc.children(recursive=True)
    except psutil.NoSuchProcess:
        return (0, 0, 0)
    for p in procs:
        try:
            r = p.memory_info().rss
            rss_sum += r
            rss_max = max(rss_max, r)
            try:
                pss_sum += p.memory_full_info().pss
            except Exception:  # noqa: BLE001  (pss needs /proc perms; fall back to rss)
                pss_sum += r
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            pass
    return (rss_sum, pss_sum, rss_max)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("dataset", type=Path)
    ap.add_argument("--repo", required=True, help="Project to score (paper uses the largest, vllm).")
    ap.add_argument("--tool", choices=("pastalean", "pyrefly", "pyre"), default="pastalean")
    args = ap.parse_args()

    cmd = [sys.executable, str(Path(__file__).with_name("score.py")), str(args.dataset),
           "--repo", args.repo, "--tool", args.tool]
    t0 = time.perf_counter()
    sp = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    pp = psutil.Process(sp.pid)
    pk = [0, 0, 0]
    while sp.poll() is None:
        pk = [max(a, b) for a, b in zip(pk, snap(pp))]
        time.sleep(0.01)
    pk = [max(a, b) for a, b in zip(pk, snap(pp))]
    wall = time.perf_counter() - t0
    print(f"{args.tool}/{args.repo}: WALL={wall:.1f}s  "
          f"RSS_SUM={pk[0]/G:.2f}G  PSS_SUM={pk[1]/G:.2f}G  RSS_MAX={pk[2]/G:.2f}G")


if __name__ == "__main__":
    main()
