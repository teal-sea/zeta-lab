"""The Fourier formulation, checked numerically.

A wheel ``w_k : x -> k x`` (mod n) sends Z_n to the hue circle through
character k. The eye mixes lights linearly, so the "colour of a chord" S under
wheel k is the centroid ``(1/|S|) sum_{x in S} e^{2 pi i k x / n}``: its chroma
is ``|f_k(S)| / |S|`` with ``f_k`` the DFT coefficient, and its hue is the
Fourier phase. So *every* Fourier coefficient of a pitch-class set is the
colour of that set under one (possibly non-injective) wheel, and the two
injective wheels of Z_12 are k = 1 (chromatic) and k = 5 (fifths).

This probe checks, by enumeration rather than citation:

1. every affine wheel sends the tritone to the complementary hue;
2. the number of injective wheels up to hue rotation and reflection is
   phi(n)/2, and 12 is the largest n with at most two;
3. for n = 12, which set class maximises |f_k| at each cardinality (the
   Clough-Douthett / Amiot maximally-even sets), and how many sets are
   "grey" (f_k = 0) under each wheel;
4. for n-TET with n = 5..31, which Fourier mode the Sethares dissonance
   curve picks as its best circular embedding, and whether that mode is
   injective.
Writes results_fourier.json.
"""

from __future__ import annotations

import itertools
import json
import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pc  # noqa: E402

N = 12


def prime_form(S, n=N):
    """Smallest representative under transposition and inversion (lexicographic)."""
    best = None
    for inv in (1, -1):
        for t in range(n):
            cand = tuple(sorted(((inv * x + t) % n) for x in S))
            if best is None or cand < best:
                best = cand
    return best


def main():
    out = {}
    # 1. tritone -> complement under every affine wheel
    aff = pc.affine_maps(N)
    out["tritone_to_complement_all_affine"] = all(
        pc.hue_distance_matrix(f)[x, (x + 6) % N] == 6 for f in aff for x in range(N)
    )
    # 2. injective wheels up to rotation/reflection
    classes = {n: len(pc.units(n)) // 2 if n > 2 else 1 for n in range(3, 37)}
    out["injective_wheel_classes_by_n"] = classes
    out["largest_n_with_at_most_two_classes"] = max(n for n, c in classes.items() if c <= 2)
    out["n_with_at_most_two_classes"] = [n for n, c in classes.items() if c <= 2]
    # 3. maximisers of |f_k| per cardinality, n = 12
    maximisers = {}
    grey = {}
    for k in range(1, 7):
        maximisers[k] = {}
        grey[k] = 0
        for d in range(1, N):
            best_val, best_sets = -1.0, set()
            for S in itertools.combinations(range(N), d):
                v = abs(pc.dft(S)[k])
                if v > best_val + 1e-9:
                    best_val, best_sets = v, {prime_form(S)}
                elif abs(v - best_val) <= 1e-9:
                    best_sets.add(prime_form(S))
                if v < 1e-9:
                    grey[k] += 1
            maximisers[k][d] = {"max_abs_fk": round(best_val, 6), "prime_forms": sorted(best_sets)}
    out["max_abs_fk_by_mode_and_cardinality"] = {str(k): {str(d): v for d, v in m.items()} for k, m in maximisers.items()}
    out["grey_subsets_by_mode"] = {str(k): v for k, v in grey.items()}
    diatonic = prime_form((0, 2, 4, 5, 7, 9, 11))
    cluster = prime_form(tuple(range(7)))
    penta = prime_form((0, 2, 4, 7, 9))
    out["diatonic_is_unique_max_f5_among_7_sets"] = maximisers[5][7]["prime_forms"] == [diatonic]
    out["cluster_is_unique_max_f1_among_7_sets"] = maximisers[1][7]["prime_forms"] == [cluster]
    out["pentatonic_is_unique_max_f5_among_5_sets"] = maximisers[5][5]["prime_forms"] == [penta]
    # 4. dominant dissonance mode in n-TET
    dom = {}
    for n in range(5, 32):
        m = pc.dissonance_sethares(n)
        D = pc.circulant_from_ic(m, n)
        J = np.eye(n) - np.ones((n, n)) / n
        B = -0.5 * J @ (D**2) @ J
        lam = np.real(np.fft.fft(B[0]))
        order = sorted(range(1, n // 2 + 1), key=lambda k: -lam[k])
        kstar = order[0]
        fifth = round(n * math.log2(1.5))
        # the wheel through mode k places step s at angle 2 pi k s / n; the step
        # that lands next to the origin (angle 2 pi / n) is the generator
        # g with k g = 1 mod n, when k is a unit.
        gen = pow(kstar, -1, n) if math.gcd(kstar, n) == 1 else None
        dom[n] = {
            "dominant_mode": kstar,
            "second_mode": order[1] if len(order) > 1 else None,
            "eigen_top2": [round(float(lam[order[0]]), 4), round(float(lam[order[1]]), 4)] if len(order) > 1 else None,
            "injective": math.gcd(kstar, n) == 1,
            "generator_step": gen,
            "fifth_step": fifth,
            "generator_is_fifth": gen is not None and min(gen, n - gen) == min(fifth, n - fifth),
            "mode1_eigen": round(float(lam[1]), 4),
        }
    out["dominant_dissonance_mode_by_n"] = {str(n): v for n, v in dom.items()}
    Path(__file__).with_name("results_fourier.json").write_text(json.dumps(out, indent=1))
    print("tritone->complement:", out["tritone_to_complement_all_affine"])
    print("classes:", out["n_with_at_most_two_classes"], "largest", out["largest_n_with_at_most_two_classes"])
    print("diatonic max f5:", out["diatonic_is_unique_max_f5_among_7_sets"], "cluster max f1:", out["cluster_is_unique_max_f1_among_7_sets"], "penta:", out["pentatonic_is_unique_max_f5_among_5_sets"])
    print("grey:", out["grey_subsets_by_mode"])
    for k in range(1, 7):
        print(" mode", k, {d: maximisers[k][d]["prime_forms"] for d in (3, 4, 5, 6, 7)})
    for n, v in dom.items():
        print(n, v["dominant_mode"], v["second_mode"], v["injective"], "gen", v["generator_step"], "fifth", v["fifth_step"], v["generator_is_fifth"], "m1", v["mode1_eigen"])


if __name__ == "__main__":
    main()
