"""Translate PastaBench contract solutions with every `taste?` replaced by `taste_cmp` (PastaSmt.Closer).

    uv run python PastaBench/smt/gen_cmp.py [N per suite]
"""
import random, re, sys
from pathlib import Path
from pastalean import Session

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent / ".cache/cmp"
OUT.mkdir(parents=True, exist_ok=True)
n = int(sys.argv[1]) if len(sys.argv) > 1 else 40
random.seed(7)
paths = []
for suite in ("humaneval", "leetcode"):
    ps = sorted((ROOT / "PastaBench" / suite).glob("*/solution_contracts.py"))
    paths += random.sample(ps, min(n, len(ps)))
with Session(target="command", mode="both") as s:
    for p, r in zip(paths, s.translate_files(paths)):
        if not r.ok or "taste?" not in (r.lean_code or ""):
            continue
        code = r.lean_code.replace("import PastaLean\n", "import PastaLean\nimport PastaSmt\n", 1)
        code = re.sub(r"\btaste\?", "taste_cmp", code)
        (OUT / f"{p.parent.parent.name}_{p.parent.name}.lean").write_text(code)
print(len(list(OUT.glob("*.lean"))), "files")
