"""The cyclotomic ontology: a chord is the cyclotomic integer a(S) = sum_{x in S} zeta^x
in Z[zeta_12], a colour wheel is a complex place of Q(zeta_12), and the two
injective wheels are Galois conjugates (f_5 = sigma_5(f_1)).

Predictions checked here over all 4096 subsets:
1. f_5(S) equals the Galois conjugate of f_1(S) (so the fifths wheel carries no
   information beyond the chromatic one);
2. N(S) = |f_1|^2 |f_5|^2 is a non-negative integer (the field norm), and in
   interval-vector terms N = (|S| + iv2 - iv4 - 2 iv6)^2 - 3 (iv1 - iv5)^2;
3. which set classes are units (N = 1), which are grey (N = 0), and how the
   norm distributes over the 224 set classes under D_12.
Writes results_cyclotomic.json.
"""

from __future__ import annotations

import itertools
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import pc  # noqa: E402

N = 12
ZETA = np.exp(2j * np.pi / N)
NAMES = {
    (0, 4, 7): "major triad", (0, 3, 7): "minor triad", (0, 4, 8): "augmented", (0, 3, 6): "diminished",
    (0, 2, 7): "sus2/sus4", (0, 2, 4, 5, 7, 9, 11): "diatonic", (0, 2, 4, 7, 9): "pentatonic",
    (0, 3, 6, 9): "dim7", (0, 4, 7, 10): "dominant 7", (0, 3, 7, 10): "minor 7", (0, 4, 7, 11): "major 7",
    (0, 2, 4, 6, 8, 10): "whole tone", (0, 1, 2): "cluster 3", (0, 1, 3, 4, 6, 7, 9, 10): "octatonic",
    (0, 1, 4, 5, 8, 9): "hexatonic", (0, 6): "tritone", (0, 7): "fifth", (0, 4): "major third", (0, 1): "semitone",
}


def prime_form(S):
    best = None
    for inv in (1, -1):
        for t in range(N):
            c = tuple(sorted(((inv * x + t) % N) for x in S))
            best = c if best is None or c < best else best
    return best


def interval_vector(S):
    iv = [0] * 7
    for a, b in itertools.combinations(S, 2):
        iv[pc.ic(a - b)] += 1
    return iv


def main():
    out = {}
    galois_ok = True
    norm_int_ok = True
    formula_ok = True
    by_class = {}
    for d in range(0, N + 1):
        for S in itertools.combinations(range(N), d):
            z = pc.dft(S)
            f1, f5 = z[1], z[5]
            # numpy's fft uses exp(-2 pi i k x / n); sigma_5: zeta -> zeta^5 maps f_1 to f_5
            sigma5 = sum(ZETA ** (-5 * x) for x in S)
            if abs(sigma5 - f5) > 1e-9:
                galois_ok = False
            norm = abs(f1) ** 2 * abs(f5) ** 2
            if abs(norm - round(norm)) > 1e-7:
                norm_int_ok = False
            iv = interval_vector(S)
            pred = (d + iv[2] - iv[4] - 2 * iv[6]) ** 2 - 3 * (iv[1] - iv[5]) ** 2
            if abs(pred - norm) > 1e-7:
                formula_ok = False
            pf = prime_form(S) if S else ()
            by_class.setdefault(pf, (int(round(norm)), iv, round(abs(f1) ** 2, 6), round(abs(f5) ** 2, 6)))
    out["galois_conjugate_holds_all_subsets"] = galois_ok
    out["norm_is_integer_all_subsets"] = norm_int_ok
    out["interval_vector_formula_holds_all_subsets"] = formula_ok
    out["set_classes"] = len(by_class)
    norms = Counter(v[0] for v in by_class.values())
    out["norm_distribution_over_set_classes"] = {str(k): v for k, v in sorted(norms.items())}
    out["distinct_norms"] = len(norms)
    units = sorted(pf for pf, v in by_class.items() if v[0] == 1)
    grey = sorted(pf for pf, v in by_class.items() if v[0] == 0)
    out["unit_set_classes"] = [{"prime_form": list(pf), "name": NAMES.get(pf, "")} for pf in units]
    out["grey_set_classes_count"] = len(grey)
    out["named_chords"] = {
        name: {"norm": by_class[pf][0], "chroma2_chromatic": by_class[pf][2], "chroma2_fifths": by_class[pf][3], "iv": by_class[pf][1][1:]}
        for pf, name in NAMES.items() if pf in by_class
    }
    iv_classes = len({tuple(v[1]) for v in by_class.values()})
    out["distinct_interval_vectors"] = iv_classes
    by_norm = defaultdict(set)
    for pf, v in by_class.items():
        by_norm[v[0]].add(tuple(v[1]))
    out["norm_values_shared_by_different_interval_vectors"] = sum(1 for s in by_norm.values() if len(s) > 1)
    out["trichord_norms"] = {str(list(pf)): v[0] for pf, v in sorted(by_class.items()) if len(pf) == 3}
    out["max_norm"] = max(v[0] for v in by_class.values())
    out["max_norm_classes"] = [list(pf) for pf, v in by_class.items() if v[0] == out["max_norm"]]
    (HERE / "results_cyclotomic.json").write_text(json.dumps(out, indent=1))
    for k, v in out.items():
        if k != "trichord_norms":
            print(k, json.dumps(v) if not isinstance(v, (bool, int)) else v)
    print("trichords:", out["trichord_norms"])


if __name__ == "__main__":
    main()
