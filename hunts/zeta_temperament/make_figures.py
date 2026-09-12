"""Two figures for hunt #76, from results_landau.json."""

from __future__ import annotations

import json
from math import log
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

HERE = Path(__file__).resolve().parent
FIG = HERE.parents[1] / "figures"


def main():
    r = json.load(open(HERE / "results_landau.json"))["odlyzko"]
    L = r["mean_log"]
    # 1. the harmonic spectrum of the zeros
    fig, ax = plt.subplots(figsize=(9, 4))
    for c in r["coefficients"]:
        colour = "C3" if c["prime_power"] else "0.5"
        ax.vlines(c["log2n"], 0, c["measured_re"], color=colour, lw=2)
        ax.plot(c["log2n"], c["predicted"], "k_", ms=10, mew=1.5)
        ax.text(c["log2n"], min(c["measured_re"], 0) - 0.004, str(c["n"]), ha="center", va="top", fontsize=7)
    ax.axhline(0, color="k", lw=0.5)
    ax.set_xlabel("frequency  log2 n   (a zero mod 1 in steps-per-octave units, probed at harmonic n)")
    ax.set_ylabel("mean over zeros of n^{i gamma}")
    ax.set_title(f"The harmonic spectrum of the first {r['zeros']:,} Riemann zeros: measured bars, Landau's "
                 f"-Lambda(n)/sqrt(n)/{L:.2f} as ticks.\nRed: prime powers. Grey: composites, where the coefficient must vanish.", fontsize=9)
    ax.set_ylim(-0.105, 0.012)
    fig.tight_layout()
    fig.savefig(FIG / "zeta_temperament_landau.png", dpi=130)
    plt.close(fig)
    # 2. the density of zeros mod 1 in tuning units
    fig, ax = plt.subplots(figsize=(8, 4))
    h = np.array(r["hist20"])
    centres = (np.arange(20) + 0.5) / 20
    ax.bar(centres, h, width=1 / 20, color="0.75", edgecolor="k", lw=0.4, label="measured, 100,000 zeros")
    th = np.linspace(0, 1, 400)
    pred = 1 + 2 * sum((-log(2) / 2 ** (k / 2) / L) * np.sin(2 * np.pi * k / 40) / (2 * np.pi * k / 40) * np.cos(2 * np.pi * k * th) for k in range(1, 60))
    ax.plot(th, pred, "C3", lw=2, label="Landau's formula, octave tower 2, 4, 8, ... (bin-smoothed)")
    ax.axhline(1, color="k", lw=0.5, ls="--")
    ax.set_xlabel("fractional part of  gamma ln2 / 2pi   (0 = an integer number of steps per octave)")
    ax.set_ylabel("density (uniform = 1)")
    ax.set_title("The Riemann zeros avoid pure-octave equal temperaments", fontsize=10)
    ax.legend(fontsize=8, loc="lower center")
    fig.tight_layout()
    fig.savefig(FIG / "zeta_temperament_density.png", dpi=130)
    plt.close(fig)
    print("ok")


if __name__ == "__main__":
    main()
