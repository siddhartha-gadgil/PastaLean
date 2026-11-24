"""Summarise `run_cmp.py`'s log: `taste?` vs `taste_smt` per goal."""
import json, statistics
from pathlib import Path

rows = [json.loads(l) for l in (Path(__file__).parent / ".cache/cmp.jsonl").read_text().splitlines() if l.strip()]
n = len(rows)
t = sum(r["taste"] for r in rows); s = sum(r["smt"] for r in rows); raw = sum(r["smt_raw"] for r in rows)
only_smt = [r for r in rows if r["smt"] and not r["taste"]]
only_taste = sum(r["taste"] and not r["smt"] for r in rows)
med = lambda xs: statistics.median(xs) if xs else None
both = [r for r in rows if r["smt"] and r["taste"]]
print(f"goals {n} (files {len({r['file'] for r in rows})}): taste? {t}, taste_smt {s}, smt raw {raw}, "
      f"smt-only {len(only_smt)}, taste-only {only_taste}, either {t + len(only_smt)}")
print(f"median ms when closed: taste {med([r['taste_ms'] for r in rows if r['taste']])}, "
      f"smt {med([r['smt_ms'] for r in rows if r['smt']])}; on goals both close: taste "
      f"{med([r['taste_ms'] for r in both])} vs smt {med([r['smt_ms'] for r in both])}")
print(f"median ms when failing: taste {med([r['taste_ms'] for r in rows if not r['taste']])}, "
      f"smt {med([r['smt_ms'] for r in rows if not r['smt']])}")
print(f"total ms: taste {sum(r['taste_ms'] for r in rows)}, smt {sum(r['smt_ms'] for r in rows)}")
for r in only_smt:
    print("smt-only:", Path(r["file"]).name, r["line"], r["smt_ms"], "ms vs taste", r["taste_ms"])
