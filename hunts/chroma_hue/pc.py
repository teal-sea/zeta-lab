"""Pitch-class machinery on Z_n for the chroma/hue hunt.

Definitions (all of them elementary, stated so the probes are reproducible):

* ``Z_n`` pitch classes; ``ic(d)`` interval class ``min(d mod n, -d mod n)``.
* An *affine* map is ``x -> u*x + c`` with ``u`` a unit mod n. For n = 12 the
  units are {1, 5, 7, 11}: u = 1 is chromatic order, u = 7 (or 5) is the
  circle of fifths (fourths), u = 11 is inversion.
* ``dft(S)`` the discrete Fourier transform of a subset's indicator vector;
  coefficient k is ``sum_{x in S} exp(-2 pi i k x / n)``.
* Three dissonance measures on interval classes, kept apart on purpose:
  Sethares' roughness for harmonic complex tones (a computed curve),
  Tenney height of the conventional just ratio (a number-theoretic proxy), and
  a plain ordinal ranking (the textbook order). Agreement across the three is
  the robustness check; none of them is "the" consonance.
"""

from __future__ import annotations

import itertools
import math

import numpy as np


def ic(d, n=12):
    d %= n
    return min(d, n - d)


def units(n):
    return [u for u in range(1, n) if math.gcd(u, n) == 1]


def affine_maps(n=12):
    """All bijections x -> u x + c (mod n) with u a unit, as tuples."""
    return [tuple((u * x + c) % n for x in range(n)) for u in units(n) for c in range(n)]


def hue_distance_matrix(f, n=12):
    """Cyclic distance on the hue n-gon pulled back to Z_n through bijection f."""
    f = np.asarray(f)
    d = np.abs(f[:, None] - f[None, :]) % n
    return np.minimum(d, n - d)


def dft(S, n=12):
    x = np.zeros(n)
    x[list(S)] = 1.0
    return np.fft.fft(x)  # coefficient k = sum exp(-2 pi i k x / n)


# --- dissonance measures on interval classes --------------------------------


def sethares_roughness(f1, f2, partials=6, decay=0.88):
    """Sethares (1993) dissonance of two harmonic complex tones."""
    a_ = 3.5
    b_ = 5.75
    d = 0.0
    for i in range(1, partials + 1):
        for j in range(1, partials + 1):
            fi, fj = f1 * i, f2 * j
            vi, vj = decay ** (i - 1), decay ** (j - 1)
            lo, hi = min(fi, fj), max(fi, fj)
            s = 0.24 / (0.021 * lo + 19)
            d += min(vi, vj) * (math.exp(-a_ * s * (hi - lo)) - math.exp(-b_ * s * (hi - lo)))
    return d


def dissonance_sethares(n=12, base=261.63):
    """Roughness of the dyad (0, k) for k = 0..n-1, 12-TET, symmetrised to ic.

    The dyad (0, k) and (0, n-k) are different chords, so both are computed
    and the interval class gets their mean.
    """
    raw = [sethares_roughness(base, base * 2 ** (k / n)) for k in range(n)]
    return {k: 0.5 * (raw[k] + raw[(n - k) % n]) for k in range(n // 2 + 1)}


#: Conventional just ratios for the 12-TET interval classes (the 5-limit
#: assignment every textbook uses; the tritone is taken as 45/32).
JUST_RATIOS = {0: (1, 1), 1: (16, 15), 2: (9, 8), 3: (6, 5), 4: (5, 4), 5: (4, 3), 6: (45, 32)}


def dissonance_tenney():
    """Tenney height log2(p q) of the just ratio for each interval class."""
    return {k: math.log2(p * q) for k, (p, q) in JUST_RATIOS.items()}


#: Textbook ordinal ranking, most consonant first: P5/P4, M3/m6, m3/M6, M2/m7,
#: m2/M7, tritone. The tritone-vs-semitone order is contested; the Sethares and
#: Tenney measures break the tie each their own way, which is why three measures.
DISSONANCE_ORDINAL = {0: 0.0, 5: 1.0, 4: 2.0, 3: 3.0, 2: 4.0, 1: 5.0, 6: 6.0}


def dissonance_measures(n=12):
    return {
        "sethares": dissonance_sethares(n),
        "tenney": dissonance_tenney(),
        "ordinal": dict(DISSONANCE_ORDINAL),
    }


def circulant_from_ic(values, n=12):
    """The transposition-invariant dissimilarity matrix D[x, y] = values[ic(x - y)]."""
    return np.array([[values[ic(x - y, n)] for y in range(n)] for x in range(n)])


def spearman(a, b):
    from scipy.stats import spearmanr

    return float(spearmanr(a, b).correlation)


def pair_indices(n=12):
    return np.array([(i, j) for i, j in itertools.combinations(range(n), 2)])
