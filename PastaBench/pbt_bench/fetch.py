"""Fetch the benchmark suites at pinned commits into `.cache/` (they are not vendored).

* crosshair-benchmark (MIT, Phillip Schanely): false contracts CrossHair is timed on.
* etna-python-bst (Alperen Keles): Etna's BST workload for Python / Hypothesis.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
CACHE = HERE / ".cache"
SUITES = {
    "crosshair-benchmark": ("https://github.com/pschanely/crosshair-benchmark",
                            "a94f6afbec1e3cfe16b6b75fbc39eed8fe286518"),
    "etna-python-bst": ("https://github.com/alpaylan/etna-python-bst",
                        "090bd19166c75967bd0553e9cdeb00875822b3f6"),
}


def fetch() -> dict[str, Path]:
    out = {}
    for name, (url, commit) in SUITES.items():
        dest = CACHE / name
        if not dest.exists():
            CACHE.mkdir(exist_ok=True)
            subprocess.run(["git", "clone", "--quiet", url, str(dest)], check=True)
        subprocess.run(["git", "-C", str(dest), "checkout", "--quiet", commit], check=True)
        out[name] = dest
    return out


if __name__ == "__main__":
    for name, path in fetch().items():
        print(name, path)
