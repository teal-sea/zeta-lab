"""Is the colour side a metric 12-gon at all? Three colour wheels, measured.

Wheel A (naive): HSL hues 0, 30, ..., 330 at s = 1, l = 0.5, the wheel every
colour picker draws.
Wheel B (perceptual, fixed chroma): OKLCH hues 0, 30, ..., 330 at a fixed
(L, C) inside the sRGB gamut at every hue.
Wheel C (perceptual, full chroma): OKLCH hues at the largest in-gamut chroma
for a fixed L, which is what a "vivid" perceptual wheel shows.

For each wheel: the 12 x 12 CIEDE2000 matrix, its adjacent-step spacings, how
far it is from circulant (the fraction of its energy outside the
transposition-invariant part), and for wheel A the OKLCH hue angles the HSL
angles actually land on. Writes results_perceptual.json.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import colorspace as cs  # noqa: E402

N = 12
HUES = np.arange(N) * 360.0 / N


def de_matrix(labs):
    return np.array([[cs.ciede2000(a, b) for b in labs] for a in labs])


def circulant_part(D):
    """Average D over the Z_12 translation action: C[x, y] = mean_t D[x+t, y+t]."""
    n = len(D)
    C = np.zeros_like(D)
    for t in range(n):
        C += np.roll(np.roll(D, t, axis=0), t, axis=1)
    return C / n


def non_circulant_fraction(D):
    C = circulant_part(D)
    return float(np.linalg.norm(D - C) ** 2 / np.linalg.norm(D) ** 2)


def summarise(name, rgbs, extra=None):
    labs = [cs.srgb_to_lab(c) for c in rgbs]
    oklabs = [cs.srgb_to_oklab(c) for c in rgbs]
    D = de_matrix(labs)
    adj = [D[i, (i + 1) % N] for i in range(N)]
    opp = [D[i, (i + 6) % N] for i in range(6)]
    # best-fit circle in the OKLab (a, b) plane: residual of chroma about its mean
    ab = np.array([[o[1], o[2]] for o in oklabs])
    centre = ab.mean(axis=0)
    radii = np.linalg.norm(ab - centre, axis=1)
    rec = {
        "srgb": [[round(float(v), 4) for v in c] for c in rgbs],
        "oklch": [[round(v, 4) for v in cs.oklab_to_oklch(o)] for o in oklabs],
        "de2000_adjacent": [round(float(v), 3) for v in adj],
        "de2000_adjacent_max_over_min": round(float(max(adj) / min(adj)), 3),
        "de2000_opposite": [round(float(v), 3) for v in opp],
        "non_circulant_fraction": round(non_circulant_fraction(D), 4),
        "oklab_ab_radius_spread": round(float((radii.max() - radii.min()) / radii.mean()), 4),
        "oklab_L_range": [round(float(min(o[0] for o in oklabs)), 4), round(float(max(o[0] for o in oklabs)), 4)],
    }
    if extra:
        rec.update(extra)
    return rec, D


def main():
    out = {}
    # A: HSL wheel
    rgb_A = [cs.hsl_to_srgb(h) for h in HUES]
    okh = [cs.oklab_to_oklch(cs.srgb_to_oklab(c))[2] for c in rgb_A]
    steps = [((okh[(i + 1) % N] - okh[i]) % 360) for i in range(N)]
    out["hsl_wheel"], D_A = summarise(
        "hsl",
        rgb_A,
        {"oklch_hue_of_hsl_hue": [round(v, 2) for v in okh], "oklch_hue_steps": [round(v, 2) for v in steps],
         "oklch_hue_step_max_over_min": round(max(steps) / min(steps), 3)},
    )
    # B: OKLCH fixed chroma. Pick L = 0.7 and the largest C that is in gamut at every hue.
    L = 0.7
    cmax = [cs.max_chroma_in_gamut(L, h) for h in HUES]
    C = min(cmax) * 0.98
    rgb_B = [cs.oklab_to_srgb(cs.oklch_to_oklab(L, C, h)) for h in HUES]
    assert all(cs.in_gamut(c) for c in rgb_B)
    out["oklch_fixed_chroma"], D_B = summarise("oklch_fixed", rgb_B, {"L": L, "C": round(C, 4)})
    # C: OKLCH full chroma at L = 0.7
    rgb_C = [cs.oklab_to_srgb(cs.oklch_to_oklab(L, c * 0.999, h)) for c, h in zip(cmax, HUES)]
    out["oklch_max_chroma"], D_C = summarise(
        "oklch_max", rgb_C, {"L": L, "max_chroma_by_hue": [round(c, 4) for c in cmax],
                             "max_chroma_max_over_min": round(max(cmax) / min(cmax), 3)}
    )
    # D: CIELAB fixed chroma, same protocol, to show the famous blue non-uniformity
    Lab_L, Lab_C = 65.0, 30.0
    labs_D = [np.array([Lab_L, Lab_C * np.cos(np.radians(h)), Lab_C * np.sin(np.radians(h))]) for h in HUES]
    D_D = de_matrix(labs_D)
    adjD = [D_D[i, (i + 1) % N] for i in range(N)]
    out["cielab_fixed_chroma"] = {
        "L": Lab_L, "C": Lab_C,
        "de2000_adjacent": [round(float(v), 3) for v in adjD],
        "de2000_adjacent_max_over_min": round(float(max(adjD) / min(adjD)), 3),
        "non_circulant_fraction": round(non_circulant_fraction(D_D), 4),
    }
    # sRGB primaries and secondaries in OKLCH hue: where the six "pure" colours sit
    prim = {k: cs.oklab_to_oklch(cs.srgb_to_oklab(v))[2] for k, v in
            {"R": [1, 0, 0], "Y": [1, 1, 0], "G": [0, 1, 0], "C": [0, 1, 1], "B": [0, 0, 1], "M": [1, 0, 1]}.items()}
    out["srgb_primaries_oklch_hue"] = {k: round(v, 2) for k, v in prim.items()}
    np.save(Path(__file__).with_name("de2000_hsl_wheel.npy"), D_A)
    Path(__file__).with_name("results_perceptual.json").write_text(json.dumps(out, indent=1))
    for k, v in out.items():
        print(k, json.dumps({kk: vv for kk, vv in v.items() if kk in ("de2000_adjacent_max_over_min", "non_circulant_fraction", "oklch_hue_step_max_over_min", "max_chroma_max_over_min", "oklab_ab_radius_spread", "oklch_hue_steps")} if isinstance(v, dict) else v))


if __name__ == "__main__":
    main()
