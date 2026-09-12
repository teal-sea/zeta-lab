"""Landau's formula in tuning units.

Put theta = gamma ln2 / 2pi, the ordinate of a zero measured in steps per
octave. For n > 1,

    mean over zeros of exp(2 pi i theta log2 n) = mean of n^{i gamma}
        = -Lambda(n) / sqrt(n) / <log(gamma / 2pi)>  + O(log T / N(T)),

which is Landau (1912) divided by the zero count. At n = 2^k this is the k-th
Fourier coefficient of the distribution of theta mod 1: negative, so the zeros
avoid integer x, i.e. pure-octave equal temperaments. At other prime powers it
says the zeros avoid x with x log2 p near an integer, the temperaments that tune
the harmonic p. At composites Lambda = 0 and the coefficient must vanish: the
built-in control. Everything below is measured against that prediction.

Tables: Odlyzko's zeros1 (first 100,000 zeros, fetched if absent, checksum
pinned) and the laboratory's own cached 2000 zeros. Writes results_landau.json.
"""

from __future__ import annotations

import hashlib
import json
import sys
import urllib.request
from math import log, sqrt
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
from zeta.moments import ODLYZKO_TABLES, load_odlyzko_zeros  # noqa: E402

LN2 = log(2.0)
ZEROS1_SHA = "3436c916a7878261ac183fd7b9448c9a4736b8bbccf1356874a6ce1788541632"
ZEROS1_PATH = ROOT / "data" / "odlyzko" / "zeros1"
W = 0.1  # half-width of the box window, in steps per octave


def lam(n):
    """Von Mangoldt Lambda(n)."""
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return log(p) if m == 1 else 0.0
    return 0.0


def odlyzko_gammas():
    if not ZEROS1_PATH.is_file():
        ZEROS1_PATH.parent.mkdir(parents=True, exist_ok=True)
        urllib.request.urlretrieve(ODLYZKO_TABLES["zeros1"].source_url, ZEROS1_PATH)
    digest = hashlib.sha256(ZEROS1_PATH.read_bytes()).hexdigest()
    if digest != ZEROS1_SHA:
        raise RuntimeError(f"zeros1 checksum {digest} != pinned {ZEROS1_SHA}")
    table = load_odlyzko_zeros(ZEROS1_PATH, expected_sha256=ZEROS1_SHA)
    return np.array([float(table.base + o) for o in table.offsets])


def cached_gammas():
    return np.load(ROOT / "data" / "explicit_zeros.npz")["gammas"]


def box_density(frac, w=W):
    """Density (uniform = 1) of fractional parts within +-w of zero."""
    return float(np.mean(np.abs(frac) < w) / (2 * w))


def predicted_box_density(L, p, shift=0.0, w=W, kmax=60):
    """Smoothed prediction at theta = shift from the prime-power tower of p."""
    s = 0.0
    for k in range(1, kmax + 1):
        c = -log(p) / p ** (k / 2) / L
        sinc = np.sin(2 * np.pi * k * w) / (2 * np.pi * k * w)
        s += 2 * c * sinc * np.cos(2 * np.pi * k * shift)
    return float(1 + s)


def analyse(g, label):
    th = g * LN2 / (2 * np.pi)
    L = float(np.mean(np.log(g / (2 * np.pi))))
    out = {"label": label, "zeros": int(len(g)), "gamma_max": float(g[-1]), "mean_log": L,
           "random_points_se": float(1 / sqrt(2 * len(g))), "coefficients": []}
    for n in range(2, 33):
        c = complex(np.mean(np.exp(2j * np.pi * th * np.log2(n))))
        pred = -lam(n) / sqrt(n) / L
        out["coefficients"].append({"n": n, "log2n": float(np.log2(n)), "measured_re": c.real,
                                    "measured_im": c.imag, "predicted": pred,
                                    "prime_power": lam(n) > 0})
    frac = th - np.round(th)
    out["density_integer"] = box_density(frac)
    out["density_integer_predicted"] = predicted_box_density(L, 2)
    out["density_half"] = box_density(np.abs(frac) - 0.5)
    out["density_half_predicted"] = predicted_box_density(L, 2, shift=0.5)
    f3 = th * np.log2(3)
    out["density_fifth_perfect"] = box_density(f3 - np.round(f3))
    out["density_fifth_perfect_predicted"] = predicted_box_density(L, 3)
    f6 = th * np.log2(6)
    out["density_composite6_control"] = box_density(f6 - np.round(f6))
    out["fraction_within_0.05_of_integer"] = float(np.mean(np.abs(frac) < 0.05))
    bands = []
    for lo, hi in ((0, 1000), (1000, 5000), (5000, 20000), (20000, 75000)):
        sel = (g > lo) & (g <= hi)
        if sel.sum() < 100:
            continue
        Lb = float(np.mean(np.log(g[sel] / (2 * np.pi))))
        bands.append({"lo": lo, "hi": hi, "n": int(sel.sum()), "measured": box_density(frac[sel]),
                      "predicted": predicted_box_density(Lb, 2)})
    out["bands"] = bands
    hist, edges = np.histogram(th - np.floor(th), bins=20, range=(0, 1))
    out["hist20"] = (hist / len(th) * 20).tolist()
    return out


def main():
    results = {"window_halfwidth": W, "odlyzko": analyse(odlyzko_gammas(), "Odlyzko zeros1"),
               "cached": analyse(cached_gammas(), "data/explicit_zeros.npz")}
    (HERE / "results_landau.json").write_text(json.dumps(results, indent=1))
    for key in ("odlyzko", "cached"):
        r = results[key]
        print(f"\n{r['label']}: {r['zeros']} zeros, gamma <= {r['gamma_max']:.0f}, <log(gamma/2pi)> = {r['mean_log']:.3f}, random-points SE {r['random_points_se']:.4f}")
        print("  n  log2n   measured    predicted")
        for c in r["coefficients"]:
            if c["n"] in (2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 25, 27, 32):
                print(f" {c['n']:3d} {c['log2n']:6.3f}  {c['measured_re']:+.4f}    {c['predicted']:+.4f}   {'prime power' if c['prime_power'] else 'composite'}")
        print(f"  density at integers {r['density_integer']:.3f} (pred {r['density_integer_predicted']:.3f}); half-integers {r['density_half']:.3f} (pred {r['density_half_predicted']:.3f}); fifth-perfect {r['density_fifth_perfect']:.3f} (pred {r['density_fifth_perfect_predicted']:.3f}); composite-6 control {r['density_composite6_control']:.3f}")
        for b in r["bands"]:
            print(f"  band ({b['lo']},{b['hi']}] n={b['n']}: measured {b['measured']:.3f} predicted {b['predicted']:.3f}")


if __name__ == "__main__":
    main()
