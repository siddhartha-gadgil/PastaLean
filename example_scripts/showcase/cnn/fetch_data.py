#!/usr/bin/env python3
"""Download a small slice of real MNIST and cache it as PNG files on disk.

We grab a handful of genuine "0" and "1" digit images from the `ylecun/mnist` dataset on
the Hugging Face Hub (streamed, so we never pull the whole 60k-image archive) and save each
one as an actual PNG under `data/`. Subsequent runs reuse the cached PNGs offline.

    source PastaLean/.venv/bin/activate
    python3 example_scripts/showcase/cnn/fetch_data.py
"""

import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA_DIR = HERE / "data"

PER_CLASS = 100
CLASSES = (0, 1)


def cached_pngs():
    """Return the cached PNGs as {label: [paths...]} if the cache is complete, else None."""
    if not DATA_DIR.is_dir():
        return None
    found = {c: sorted(DATA_DIR.glob(f"{c}_*.png")) for c in CLASSES}
    if all(len(found[c]) >= PER_CLASS for c in CLASSES):
        return {c: found[c][:PER_CLASS] for c in CLASSES}
    return None


def fetch():
    """Stream MNIST, save PER_CLASS PNGs per class, and return {label: [paths...]}."""
    from datasets import load_dataset

    DATA_DIR.mkdir(parents=True, exist_ok=True)
    ds = load_dataset("ylecun/mnist", split="train", streaming=True)

    saved = {c: [] for c in CLASSES}
    for ex in ds:
        label = ex["label"]
        if label in CLASSES and len(saved[label]) < PER_CLASS:
            path = DATA_DIR / f"{label}_{len(saved[label])}.png"
            ex["image"].save(path)          # genuine 28x28 grayscale PNG
            saved[label].append(path)
        if all(len(saved[c]) >= PER_CLASS for c in CLASSES):
            break
    return saved


def load(verbose=True):
    """Main entry: return cached PNGs, downloading them first if needed."""
    cache = cached_pngs()
    if cache is not None:
        if verbose:
            print(f"[data] using cached PNGs in {DATA_DIR}", file=sys.stderr)
        return cache
    if verbose:
        print("[data] downloading real MNIST 0/1 digits from the HF Hub ...",
              file=sys.stderr)
    return fetch()


if __name__ == "__main__":
    result = load()
    total = sum(len(v) for v in result.values())
    print(f"cached {total} PNGs under {DATA_DIR}")
    # Streaming datasets can dump a harmless core at interpreter teardown; bail cleanly.
    sys.stdout.flush()
    os._exit(0)
