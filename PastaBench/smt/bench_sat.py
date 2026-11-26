"""grind vs SMT as refute's solver step, and refute with/without --smt end to end.

    uv run python PastaBench/smt/bench_sat.py solver   # engines off: only grind / smt produce witnesses
    uv run python PastaBench/smt/bench_sat.py full     # default refute vs --smt, same budget
"""
import json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
files = sorted(p for p in (ROOT / "example_scripts/refute").glob("*.py") if not p.name.startswith("stdin_"))
files += sorted((ROOT / "PastaBench/pbt_bench/.cache/crosshair-benchmark/benchmarks").rglob("crosshair_*.py"))

OFF = {"plausible": False, "instrument": False, "enumDepth": 0, "numInst": 0, "timeMs": 200}


def run(path, cfg, extra=(), time_ms=None):
    env = {**os.environ, "PASTALEAN_REFUTE_CONFIG": json.dumps(cfg)}
    cmd = [sys.executable, "-m", "pastalean", "refute", str(path), "--json", *extra]
    if time_ms:
        cmd += ["--time", str(time_ms), "--tests", str(10 ** 9)]
    t0 = time.monotonic()
    p = subprocess.run(cmd, capture_output=True, text=True, env=env, cwd=str(path.parent), timeout=900)
    dt = time.monotonic() - t0
    try:
        return json.loads(p.stdout[p.stdout.index("{"):]), dt
    except ValueError:
        return {"error": p.stderr[-300:]}, dt


def solver_mode():
    rows = []
    def one(f):
        d, dt = run(f, {**OFF, "smt": True})
        out = []
        for o in d.get("obligations") or []:
            s = o.get("searches", {})
            ws = o.get("witnesses") or []
            ok = lambda org: any(w.get("origin") == org and w.get("verdict") == "REFUTED" for w in ws)
            out.append({"file": f.name, "ob": o["name"], "verdict": o["verdict"],
                        "grind": (s.get("solver") or {}).get("status"), "grind_ms": s.get("solverMs"),
                        "grind_refutes": ok("grind"),
                        "smt": (s.get("smt") or {}).get("status"), "smt_ms": (s.get("smt") or {}).get("ms"),
                        "smt_refutes": ok("smt")})
        if d.get("error"):
            out.append({"file": f.name, "error": str(d["error"])[:200]})
        return out
    with ThreadPoolExecutor(6) as ex:
        for out in ex.map(one, files):
            rows += out
    for r in rows:
        print(json.dumps(r))
    obs = [r for r in rows if "ob" in r]
    g = sum(r["grind_refutes"] for r in obs); s = sum(r["smt_refutes"] for r in obs)
    both = sum(r["grind_refutes"] and r["smt_refutes"] for r in obs)
    gm = sorted(r["grind_ms"] for r in obs if r["grind_ms"] is not None)
    sm = sorted(r["smt_ms"] for r in obs if r["smt_ms"] is not None)
    med = lambda xs: xs[len(xs) // 2] if xs else None
    print(f"obligations {len(obs)}: grind model refutes {g}, smt model refutes {s}, both {both}; "
          f"grind proved {sum(r['grind'] == 'proved' for r in obs)}, smt unsat(untrusted) "
          f"{sum(r['smt'] == 'unsat-untrusted' for r in obs)}; median ms grind {med(gm)} smt {med(sm)}; "
          f"total ms grind {sum(gm)} smt {sum(sm)}")


def full_mode(time_ms=8000):
    def one(f):
        res = {}
        for name, extra in (("default", ()), ("smt", ("--smt",))):
            d, dt = run(f, {}, extra, time_ms)
            obs = d.get("obligations") or []
            res[name] = {"refuted": sum(o["verdict"] == "REFUTED" for o in obs), "n": len(obs),
                         "s": round(dt, 1),
                         "origins": [((o.get("witness") or {}).get("origin")) for o in obs if o["verdict"] == "REFUTED"]}
        return f.name, res
    with ThreadPoolExecutor(4) as ex:
        tot = {"default": [0, 0, 0.0], "smt": [0, 0, 0.0]}
        for name, res in ex.map(one, files):
            print(name, json.dumps(res))
            for k in tot:
                tot[k][0] += res[k]["refuted"]; tot[k][1] += res[k]["n"]; tot[k][2] += res[k]["s"]
        print("totals (refuted, obligations, wall s):", tot)


if __name__ == "__main__":
    {"solver": solver_mode, "full": full_mode}[sys.argv[1]]()
