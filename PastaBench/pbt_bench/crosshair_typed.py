"""CrossHair with PastaLean's types: annotate the problem, then run `crosshair check` on the copy.

Each parameter of a contracted function that is unannotated, `Any`, or a bare container (`dict`,
`list`, `set`, `tuple`) gets TypeInfer's inferred type; the user's other annotations are kept. CrossHair
then searches symbolic values of those types.

    python crosshair_typed.py PROBLEM.py TIMEOUT
"""

from __future__ import annotations

import ast
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT / "src" / "refute"))

from pastalean.refute.obligations import collect  # noqa: E402

BARE = {"dict", "list", "set", "tuple", "Dict", "List", "Set", "Tuple", "Any"}


def inferred(source: str) -> dict:
    try:
        from pastalean.typeinfer.engine import infer_source

        return {f.qualname: f.params for f in infer_source(source).functions}
    except Exception:  # noqa: BLE001
        return {}


def annotate(source: str) -> tuple[str, list[str]]:
    tree = ast.parse(source)
    obs = {o.name: o for o in collect(source)}
    ti = inferred(source)
    notes = []
    for fn in tree.body:
        if not isinstance(fn, ast.FunctionDef) or fn.name not in obs:
            continue
        ob = obs[fn.name]
        for a in fn.args.posonlyargs + fn.args.args:
            cur = ast.unparse(a.annotation) if a.annotation is not None else None
            if cur is not None and cur not in BARE:
                continue
            t = ti.get(fn.name, {}).get(a.arg)
            src = "TypeInfer"
            if t and t != cur and t != "Any":
                a.annotation = ast.parse(t, mode="eval").body
                notes.append(f"{fn.name}.{a.arg}: {cur or '-'} -> {t} ({src})")
    head = "from typing import Any\n" if "Any" in ast.unparse(tree) else ""
    return head + ast.unparse(tree) + "\n", notes


def main(path: str, timeout: int) -> int:
    source = Path(path).read_text()
    typed, notes = annotate(source)
    for n in notes:
        print("typed:", n)
    with tempfile.TemporaryDirectory() as d:
        # Same file name, so CrossHair's messages name the same function.
        target = Path(d) / Path(path).name
        target.write_text(typed)
        p = subprocess.run([sys.executable, "-m", "crosshair", "check", f"--per_condition_timeout={timeout}",
                            f"--per_path_timeout={timeout ** 0.5}", str(target)],
                           capture_output=True, text=True, cwd=str(Path(path).parent))
        print(p.stdout + p.stderr)
        return p.returncode


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1], int(sys.argv[2])))
