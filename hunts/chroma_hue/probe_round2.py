"""Round two: the paths the first pass stated but did not test.

1. Metamerism: how many distinguishable chord colours each wheel has.
2. Orbifold radius against chroma: is |f_1| a function of voice-leading
   distance to the nearest perfectly even chord?
3. The CRT torus: Z_12 = Z_3 x Z_4 through the two collapsed wheels k = 4, 3.
4. Perceptual distances: rerun the bijection search with the measured
   CIEDE2000 matrix of a perceptual wheel in place of the cyclic metric, with
   a hill climb and a random null.
Writes results_round2.json.
"""

from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

import numpy as np
from scipy.stats import rankdata, spearmanr

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import colorspace as cs  # noqa: E402
import pc  # noqa: E402

N = 12
SUBSETS = [S for d in range(0, N + 1) for S in itertools.combinations(range(N), d)]


def metamerism():
    out = {}
    for k in range(1, 7):
        colours = set()
        for S in SUBSETS:
            z = pc.dft(S)[k]
            colours.add((len(S), round(z.real, 6), round(z.imag, 6)))
        out[f"wheel_{k}"] = len(colours)
    both = set()
    for S in SUBSETS:
        z = pc.dft(S)
        both.add((len(S), round(z[1].real, 6), round(z[1].imag, 6), round(z[5].real, 6), round(z[5].imag, 6)))
    out["wheels_1_and_5_together"] = len(both)
    full = set()
    for S in SUBSETS:
        z = pc.dft(S)
        full.add(tuple(round(v, 6) for v in np.concatenate([z.real, z.imag])))
    out["full_dft_distinct"] = len(full)
    out["subsets"] = len(SUBSETS)
    # the worst metamer class under the fifths wheel: largest set of chords with one colour
    classes = {}
    for S in SUBSETS:
        z = pc.dft(S)[5]
        classes.setdefault((len(S), round(z.real, 6), round(z.imag, 6)), []).append(S)
    big = max(classes.values(), key=len)
    out["largest_metamer_class_wheel_5"] = {"size": len(big), "cardinality": len(big[0]), "examples": [list(s) for s in big[:4]]}
    # same-cardinality metamers that are not related by transposition or inversion
    def pf(S):
        best = None
        for inv in (1, -1):
            for t in range(N):
                c = tuple(sorted(((inv * x + t) % N) for x in S))
                best = c if best is None or c < best else best
        return best
    cross = sum(1 for v in classes.values() if len({pf(s) for s in v}) > 1)
    out["wheel_5_colour_classes_mixing_set_classes"] = cross
    out["wheel_5_colour_classes"] = len(classes)
    return out


def vl_distance_to_even(S):
    """Min over permutations and transpositions of sum |voice moves| (cyclic) from S to the perfectly even chord of its cardinality, or to the nearest 'most even' orbit for d not dividing 12."""
    d = len(S)
    if N % d:
        return None
    step = N // d
    best = 1e9
    for t in range(N):
        target = [(t + i * step) % N for i in range(d)]
        for perm in itertools.permutations(target):
            cost = sum(pc.ic(a - b) for a, b in zip(S, perm))
            best = min(best, cost)
    return best


def orbifold():
    out = {}
    for d in (3, 4, 6):
        xs, ys = [], []
        for S in itertools.combinations(range(N), d):
            r = vl_distance_to_even(S)
            xs.append(r)
            ys.append(abs(pc.dft(S)[1]))
        rho = spearmanr(xs, ys).correlation
        # is |f_1| a function of r? count distinct |f_1| per r value
        per_r = {}
        for r, y in zip(xs, ys):
            per_r.setdefault(r, set()).add(round(y, 6))
        out[f"card_{d}"] = {
            "spearman_radius_vs_f1": round(float(rho), 4),
            "distinct_f1_per_radius": {str(r): len(v) for r, v in sorted(per_r.items())},
            "function_of_radius": all(len(v) == 1 for v in per_r.values()),
        }
    return out


def crt():
    out = {}
    code = {x: (x % 3, x % 4) for x in range(N)}
    out["injective"] = len(set(code.values())) == N
    # wheel 4 colours augmented classes (x mod 3), wheel 3 colours dim-7 classes (x mod 4)
    out["wheel_4_classes"] = [[x for x in range(N) if x % 3 == r] for r in range(3)]
    out["wheel_3_classes"] = [[x for x in range(N) if x % 4 == r] for r in range(4)]
    # major triads and minor triads as (mod3, mod4) patterns; do the 24 triads get distinct colour-pair multisets?
    def pattern(S):
        return tuple(sorted(code[x] for x in S))
    majors = {t: pattern([(t + i) % N for i in (0, 4, 7)]) for t in range(N)}
    minors = {t: pattern([(t + i) % N for i in (0, 3, 7)]) for t in range(N)}
    out["distinct_triad_patterns"] = len(set(majors.values()) | set(minors.values()))
    # hexatonic and octatonic collections are unions of cosets
    out["octatonic_is_union_of_two_dim7_cosets"] = sorted(set([x for x in range(N) if x % 4 == 0] + [x for x in range(N) if x % 4 == 1])) == [0, 1, 4, 5, 8, 9]
    return out


def perceptual_search(seed=0, restarts=40, null_samples=100_000):
    """Objective: Spearman between CIEDE2000(colour f(x), colour f(y)) on a
    perceptual wheel and dissonance of ic(x - y). Two wheels: OKLCH fixed chroma
    (near circulant) and HSL (far from circulant)."""
    rng = np.random.default_rng(seed)
    pairs = pc.pair_indices(N)
    I, J = pairs[:, 0], pairs[:, 1]
    measures = pc.dissonance_measures(N)
    hues = np.arange(N) * 30.0
    L = 0.7
    cmax = [cs.max_chroma_in_gamut(L, h) for h in hues]
    C = min(cmax) * 0.98
    wheels = {
        "oklch_fixed": [cs.srgb_to_lab(cs.oklab_to_srgb(cs.oklch_to_oklab(L, C, h))) for h in hues],
        "hsl": [cs.srgb_to_lab(cs.hsl_to_srgb(h)) for h in hues],
    }
    out = {}
    for wname, labs in wheels.items():
        DE = np.array([[cs.ciede2000(a, b) for b in labs] for a in labs])
        out[wname] = {}
        for mname, m in measures.items():
            diss = np.array([m[pc.ic(j - i)] for i, j in pairs])
            rd = rankdata(diss)

            def score(f):
                f = np.asarray(f)
                x = rankdata(DE[f[I], f[J]])
                return float(np.corrcoef(x, rd)[0, 1])

            def score_batch(F):
                x = rankdata(DE[F[:, I], F[:, J]], axis=1)
                xc = x - x.mean(axis=1, keepdims=True)
                yc = rd - rd.mean()
                return (xc @ yc) / np.sqrt((xc * xc).sum(axis=1) * (yc * yc).sum())

            fifths = [(7 * x) % N for x in range(N)]
            aff = np.array(pc.affine_maps(N))
            aff_scores = score_batch(aff)
            null = score_batch(np.array([rng.permutation(N) for _ in range(null_samples)]))
            # hill climb with restarts: swap two entries while it improves
            best_overall, best_map = -2, None
            for _ in range(restarts):
                f = list(rng.permutation(N))
                s = score(f)
                improved = True
                while improved:
                    improved = False
                    for a in range(N):
                        for b in range(a + 1, N):
                            g = f.copy()
                            g[a], g[b] = g[b], g[a]
                            sg = score(g)
                            if sg > s + 1e-12:
                                f, s, improved = g, sg, True
                if s > best_overall:
                    best_overall, best_map = s, f
            out[wname][mname] = {
                "best_affine": round(float(aff_scores.max()), 4),
                "fifths_any_rotation_max": round(float(max(score([(7 * x + c) % N for x in range(N)]) for c in range(N))), 4),
                "fifths_rotation_min": round(float(min(score([(7 * x + c) % N for x in range(N)]) for c in range(N))), 4),
                "hill_climb_best": round(float(best_overall), 4),
                "hill_climb_map": [int(v) for v in best_map],
                "hill_climb_is_affine": tuple(int(v) for v in best_map) in {tuple(a) for a in aff},
                "null_mean": round(float(null.mean()), 4),
                "null_sd": round(float(null.std()), 4),
                "null_max": round(float(null.max()), 4),
                "null_frac_ge_hill": float((null >= best_overall - 1e-12).mean()),
            }
    return out


def main():
    out = {"metamerism": metamerism(), "orbifold": orbifold(), "crt": crt(), "perceptual_search": perceptual_search()}
    (HERE / "results_round2.json").write_text(json.dumps(out, indent=1))
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
