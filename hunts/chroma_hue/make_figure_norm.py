"""One figure: the 224 set classes in the (|f_1|^2, |f_5|^2) plane.

|f_1|^2 = a + b sqrt3 and |f_5|^2 = a - b sqrt3 with a, b integers from the
interval vector, so every class lies on a hyperbola x y = N with N one of the
ten norms {0, 1, 4, 9, 13, 16, 25, 36, 37, 64}. Chromatic saturation times
fifths saturation is an integer, for every chord.
"""

from __future__ import annotations

import itertools
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import pc  # noqa: E402

FIG = HERE.parents[1] / "figures"
N = 12
NAMED = {(0, 3, 7): "major / minor triad", (0, 3, 6): "dim triad", (0, 2, 7): "sus",
         (0, 2, 4, 7, 9): "pentatonic / diatonic", (0, 1, 2): "cluster",
         (0, 4, 8): "grey: aug, dim7, whole tone, octatonic, tritone"}


def prime_form(S):
    best = None
    for inv in (1, -1):
        for t in range(N):
            c = tuple(sorted(((inv * x + t) % N) for x in S))
            best = c if best is None or c < best else best
    return best


def main():
    pts = {}
    for d in range(0, N + 1):
        for S in itertools.combinations(range(N), d):
            pf = prime_form(S)
            if pf in pts:
                continue
            z = pc.dft(S)
            pts[pf] = (abs(z[1]) ** 2, abs(z[5]) ** 2)
    xs = np.array([v[0] for v in pts.values()])
    ys = np.array([v[1] for v in pts.values()])
    norms = np.round(xs * ys).astype(int)
    fig, ax = plt.subplots(figsize=(7.5, 7))
    grid = np.geomspace(0.03, 60, 400)
    for n in sorted(set(norms) - {0}):
        ax.plot(grid, n / grid, color="0.8", lw=0.8, zorder=0)
        ax.text(np.sqrt(n) * 1.08, np.sqrt(n) * 1.08, f"N={n}", fontsize=7, color="0.4", ha="left", va="bottom", rotation=-45)
    grey = norms == 0
    floor = 0.03
    sc = ax.scatter(np.where(xs > 0, xs, floor), np.where(ys > 0, ys, floor), c=norms, cmap="viridis",
                    s=26, zorder=2, edgecolor="k", linewidth=0.3)
    ax.text(floor * 1.1, floor * 1.4, f"{int(grey.sum())} grey classes (N = 0)", fontsize=8)
    for pf, name in NAMED.items():
        if pf in pts:
            x, y = pts[pf]
            ax.annotate(name, (max(x, floor), max(y, floor)), textcoords="offset points", xytext=(5, 4), fontsize=8)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(0.02, 60)
    ax.set_ylim(0.02, 60)
    ax.set_aspect("equal")
    ax.set_xlabel("chromatic wheel: |f_1(S)|^2  (chroma^2 x |S|^2)")
    ax.set_ylabel("fifths wheel: |f_5(S)|^2")
    ax.set_title("The 224 set classes of Z_12 on the ten hyperbolas x y = N\n(N = |f_1|^2 |f_5|^2, the norm of sum zeta^x, always an integer)", fontsize=10)
    plt.colorbar(sc, ax=ax, label="norm N")
    fig.tight_layout()
    fig.savefig(FIG / "chroma_hue_norm.png", dpi=130)
    print("classes", len(pts), "norms", sorted(set(norms)))


if __name__ == "__main__":
    main()
