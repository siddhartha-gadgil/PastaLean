#!/usr/bin/env python3
"""Pharmacokinetics showcase: a drug-dosing simulation, run in Python AND Lean 4.

`pk_model.py` is the dynamical core -- a two-compartment PK model with repeated oral dosing.
This orchestrator streams the parameters on stdin, runs the model two ways (CPython with real
SciPy, and transpiled to Lean 4 by PastaLean), checks the two trajectories agree, and animates
the drug accumulating to steady state -- with the Python and Lean curves overlaid.

    source PastaLean/.venv/bin/activate
    python3 example_scripts/showcase/scipy/run_showcase.py
"""

import subprocess
import sys
from pathlib import Path

import numpy as np
import pastalean

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[2]
MODEL_PY = HERE / "pk_model.py"
MODEL_LEAN = HERE / "pk_model.lean"
GIF = HERE / "pk_simulation.gif"
PNG = HERE / "pk_simulation.png"

# Model parameters (rate constants in 1/h, volume in L, dose in mg).
PARAMS = dict(ka=1.1, ke=0.18, k12=0.35, k21=0.25, vol=35.0, dose=100.0, dt=0.01)
DT = PARAMS["dt"]
DOSE_INTERVAL_H = 6.0
NDOSES = 8
TMAX_H = 72.0
EVERY = 12

DOSE_STEP = int(round(DOSE_INTERVAL_H / DT))
NSTEPS = int(round(TMAX_H / DT))


def build_stdin():
    floats = [PARAMS["ka"], PARAMS["ke"], PARAMS["k12"], PARAMS["k21"],
              PARAMS["vol"], PARAMS["dose"], PARAMS["dt"]]
    ints = [DOSE_STEP, NDOSES, NSTEPS, EVERY]
    return "\n".join([f"{v:.6f}" for v in floats] + [str(i) for i in ints]) + "\n"


def run_python(payload):
    proc = subprocess.run([sys.executable, str(MODEL_PY)], input=payload,
                          capture_output=True, text=True, cwd=REPO_ROOT)
    if proc.returncode != 0:
        raise RuntimeError(f"Python run failed:\n{proc.stderr}")
    return proc.stdout


def transpile_to_lean():
    result = pastalean.translate_file(MODEL_PY, target="command", mode="run")
    if not result.ok:
        raise RuntimeError(f"Transpilation failed:\n{result.error}")
    MODEL_LEAN.write_text(result.lean_code)


def run_lean(payload):
    proc = subprocess.run(["lake", "env", "lean", "--run", str(MODEL_LEAN)], input=payload,
                          capture_output=True, text=True, cwd=REPO_ROOT)
    if proc.returncode != 0:
        raise RuntimeError(f"Lean run failed:\n{proc.stderr or proc.stdout}")
    return proc.stdout


def parse(output):
    """Return arrays t, plasma, tissue, depot, load."""
    t, plasma, tissue, depot, load = [], [], [], [], []
    for line in output.splitlines():
        p = line.split()
        if len(p) == 7 and p[0] == "S":
            t.append(float(p[2])); plasma.append(float(p[3])); tissue.append(float(p[4]))
            depot.append(float(p[5])); load.append(float(p[6]))
    return tuple(np.array(a) for a in (t, plasma, tissue, depot, load))


# --------------------------------------------------------------------------------------
def animate(py, ln, err):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.animation import FuncAnimation, PillowWriter

    t, pl, ti, de, _ = py
    _, pl_l, ti_l, _, _ = ln
    dose_times = [i * DOSE_INTERVAL_H for i in range(NDOSES)]
    n = len(t)
    frames = 130
    idx = np.linspace(2, n, frames).astype(int)

    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(12, 6.6))
    fig.patch.set_facecolor("#0d1018")
    ax.set_facecolor("#0d1018")
    ax.grid(alpha=0.15)
    ax.set_xlim(0, TMAX_H)
    ax.set_ylim(0, max(pl.max(), ti.max()) * 1.18)
    ax.set_xlabel("time  (hours)", fontsize=11)
    ax.set_ylabel("concentration  (mg/L)", fontsize=11)

    # Dose markers.
    for dtm in dose_times:
        ax.axvline(dtm, color="#3a4358", lw=1, ls=":", zorder=1)
    ax.annotate("doses", (dose_times[1], ax.get_ylim()[1] * 0.96), color="#6b7693", fontsize=9)

    # Steady-state band (mean +/- amplitude over the last two dosing intervals before washout).
    ss_mask = (t >= dose_times[-1] - DOSE_INTERVAL_H) & (t <= dose_times[-1])
    if ss_mask.any():
        ax.axhspan(pl[ss_mask].min(), pl[ss_mask].max(), color="#1b6ca8", alpha=0.10, zorder=0)

    plasma_fill = ax.fill_between(t[:2], pl[:2], color="#2bb0ff", alpha=0.22, zorder=2)
    (plasma_py,) = ax.plot([], [], color="#2bb0ff", lw=2.8, zorder=4, label="plasma — Python (SciPy)")
    (tissue_py,) = ax.plot([], [], color="#ff9f43", lw=2.2, zorder=4, label="tissue — Python")
    (plasma_ln,) = ax.plot([], [], color="white", lw=1.4, ls="--", zorder=5, label="plasma — Lean 4")
    (tissue_ln,) = ax.plot([], [], color="white", lw=1.4, ls=(0, (1, 1.5)), zorder=5, label="tissue — Lean 4")
    cursor = ax.axvline(0, color="#ff5a7a", lw=1.2, alpha=0.8, zorder=6)
    readout = ax.text(0.985, 0.10, "", transform=ax.transAxes, ha="right", fontsize=10,
                      color="#9fe3a0", family="monospace",
                      bbox=dict(boxstyle="round", fc="#11151f", ec="#2b3346"))

    ax.set_title("Pharmacokinetics — drug accumulation to steady state, simulated in Lean 4",
                 fontsize=14, fontweight="bold", color="white", pad=26)
    fig.text(0.5, 0.905,
             f"two-compartment oral dosing · {NDOSES} doses q{int(DOSE_INTERVAL_H)}h · "
             f"transpiled Python → Lean 4 · max |Lean − Python| = {err:.1e} mg/L",
             ha="center", fontsize=10.5, color="#7fa9ff")
    ax.legend(loc="upper left", fontsize=9, facecolor="#11151f", edgecolor="#2b3346", framealpha=0.9)

    def update(k):
        nonlocal plasma_fill
        j = idx[k]
        plasma_py.set_data(t[:j], pl[:j])
        tissue_py.set_data(t[:j], ti[:j])
        plasma_ln.set_data(t[:j], pl_l[:j])
        tissue_ln.set_data(t[:j], ti_l[:j])
        plasma_fill.remove()
        plasma_fill = ax.fill_between(t[:j], pl[:j], color="#2bb0ff", alpha=0.22, zorder=2)
        cursor.set_xdata([t[j - 1], t[j - 1]])
        readout.set_text(f"t = {t[j-1]:5.1f} h\nCp = {pl[j-1]:5.2f} mg/L\nLean Δ = {abs(pl[j-1]-pl_l[j-1]):.1e}")
        return plasma_py, tissue_py, plasma_ln, tissue_ln, cursor, readout

    anim = FuncAnimation(fig, update, frames=frames, interval=55, blit=False)
    anim.save(GIF, writer=PillowWriter(fps=18), dpi=110)
    update(frames - 1)
    fig.savefig(PNG, dpi=130, facecolor=fig.get_facecolor())
    print(f"  saved animation -> {GIF}")
    print(f"  saved figure    -> {PNG}")


# --------------------------------------------------------------------------------------
def max_error(py, ln):
    worst = 0.0
    for a, b in zip(py[1:4], ln[1:4]):     # plasma, tissue, depot
        worst = max(worst, float(np.max(np.abs(a - b))))
    return worst
# python does the simulation. logic is lean!!

def main():
    payload = build_stdin()

    print("[1/3] running the PK model in Python (real SciPy) ...", file=sys.stderr)
    py = parse(run_python(payload))

    print("[2/3] transpiling the PK model to Lean 4 with PastaLean ...", file=sys.stderr)
    transpile_to_lean()

    print("[3/3] compiling & running the Lean PK model ...", file=sys.stderr)
    ln = parse(run_lean(payload))

    err = max_error(py, ln)
    bar = "=" * 74
    print(bar)
    print("  Pharmacokinetic simulation  —  Python (real SciPy)  vs  transpiled Lean 4")
    print(bar)
    print(f"  model     : 2-compartment, {NDOSES} oral doses q{int(DOSE_INTERVAL_H)}h over {TMAX_H:.0f} h")
    print(f"  samples   : {len(py[0])} timepoints per backend")
    print(f"  peak Cp   : python {py[1].max():.3f} mg/L   lean {ln[1].max():.3f} mg/L")
    print(f"  max |Lean − Python| : {err:.2e} mg/L")
    print(f"  verdict   : {'IDENTICAL TRAJECTORIES' if err < 1e-4 else 'DIVERGENCE'}")
    print(bar)
    animate(py, ln, err)


if __name__ == "__main__":
    main()
