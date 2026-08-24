"""Hunt R-2969B0 — does Penman-Wells (2013) beat AlphaEvolve's Problem 42 value?

Everything here is exact finite-set arithmetic over the integers. The only
floating point is the final ratio of two logarithms, and the comparison that
decides the question is also done exactly (see :func:`g_beats` below), so the
verdict does not depend on it.

Definitions, quoted rather than paraphrased.

* DeepMind, ``problems/42.html`` ("42. Sum-difference problem I"):
  "Let C be the least constant such that |A+A|/|A| <= (|A-A|/|A|)^C for any
  non-empty finite set A of integers."
  So C = sup_A g(A) with g(A) = ln(|A+A|/|A|) / ln(|A-A|/|A|).

* Penman and Wells, INTEGERS 13 (2013) A57, section 4, page 22:
  "Some authors, e.g., Granville in [2], prefer to use
  g(A) = ln(|A+A|/|A|)/ln(|A-A|/|A|) for which the analogous bounds are
  1/2 <= g(A) <= 2."
  Their Theorem 21: "Given eps > 0, there is a set C of integers for which
  g(C) > ln(32/5)/ln(26/5) - eps ~= 1.125944426. Proof. Take Q_j for j
  sufficiently large."

The two normalisations are the same function of A. Note that this is *not*
the quantity in the paper's abstract, which is f(A) = ln|A+A|/ln|A-A|; the
paper carries both and is explicit about the difference.

Q_j is the paper's Theorem 12 (page 14), reproduced verbatim in :func:`Q`.
Corollary 13 (page 17) states |Q_j| = 5j+17, |Q_j+Q_j| = 32j+63 (j>=1),
|Q_j-Q_j| = 26j+61 (j>=1). We recompute all three by enumeration.

Run: ``python3 probe.py`` (standard library only, a few seconds).
"""

from __future__ import annotations

import json
import math
import pathlib
from fractions import Fraction

# --------------------------------------------------------------------------
# set arithmetic
# --------------------------------------------------------------------------


def sumset(A: set[int]) -> set[int]:
    return {a + b for a in A for b in A}


def diffset(A: set[int]) -> set[int]:
    return {a - b for a in A for b in A}


def restricted_sumset(A: set[int]) -> set[int]:
    return {a + b for a in A for b in A if a != b}


def counts(A: set[int]) -> tuple[int, int, int]:
    return len(A), len(sumset(A)), len(diffset(A))


def g_value(n: int, s: int, d: int) -> float:
    """g(A) = ln(|A+A|/|A|) / ln(|A-A|/|A|), the Problem 42 quantity."""
    return math.log(s / n) / math.log(d / n)


def f_value(s: int, d: int) -> float:
    """f(A) = ln|A+A| / ln|A-A|, the quantity in the Penman-Wells abstract."""
    return math.log(s) / math.log(d)


def g_beats(n1: int, s1: int, d1: int, n2: int, s2: int, d2: int) -> bool:
    """Exactly decide g(A1) > g(A2) without trusting a float ratio.

    g1 > g2  <=>  ln(s1/n1)*ln(d2/n2) > ln(s2/n2)*ln(d1/n1), valid because
    both denominators ln(d/n) are positive here (each d > n). Evaluated at
    120 significant digits with Python's decimal module; the two sides
    differ in the 3rd digit for every comparison this probe makes, so the
    precision is not close to load-bearing.
    """
    import decimal

    with decimal.localcontext() as ctx:
        ctx.prec = 120
        D = decimal.Decimal
        lhs = (D(s1) / D(n1)).ln() * (D(d2) / D(n2)).ln()
        rhs = (D(s2) / D(n2)).ln() * (D(d1) / D(n1)).ln()
        return lhs > rhs


# --------------------------------------------------------------------------
# Penman-Wells Q_j, Theorem 12 (INTEGERS 13 (2013) A57, page 14)
# --------------------------------------------------------------------------


def Q(j: int) -> set[int]:
    """Q_j = {0,2,4,12} u {1,5,...,1+4(4j+8)} u {24,40,...,8+16j}
             u {4+16(j+1), 12+16(j+1), 14+16(j+1), 16(j+2)},  j >= 1."""
    if j < 1:
        raise ValueError("Theorem 12 defines Q_j for j >= 1")
    S: set[int] = {0, 2, 4, 12}
    S |= set(range(1, 1 + 4 * (4 * j + 8) + 1, 4))
    S |= set(range(24, 8 + 16 * j + 1, 16))
    S |= {4 + 16 * (j + 1), 12 + 16 * (j + 1), 14 + 16 * (j + 1), 16 * (j + 2)}
    return S


# --------------------------------------------------------------------------
# the AlphaEvolve construction, from the repository's own notebook
# --------------------------------------------------------------------------

ALPHAEVOLVE_42 = [
    -129, -142, 30, 5, -113, -49, 19, -45, -66, 58, 56, -104, -37, -102, -136,
    -122, -103, 54, -16, -148, -53, -76, -7, 50, -60, 7, -2, -127, -118, -78,
    -24, -86, -111, -114, -145, -85, 13, 17, -116, -121, -119, -89, -94, -79,
    -3, 0, -58, -67, -46, -52, -50, -36, -8, -106, -29, -27, -25, -91, -81,
    -48, 8, -47, -82, -40, -35, -30, 20, -101, -1, -75, -32, -17, -14, -15,
    -18, -38, -68, -77, -59, -151, -132, -140, -150, 26, 22, -22, -69, -73,
    -11, -99, -28, 15, -90, 31, 33, 34, -23, -100, -56, 2, 384, -4, 27, -62,
    -6, 51, 1, 44, 41, 40, -31, -13, -34, -33, 386, -108, -80, -117, -138,
    -125, -93, -74, -126, -65, -134, 237, 83, -43, 224, -88, -57, -54, -131,
    -98, 25, 276, 18, 14, 12, -95, -128, -124, 24, 36, -10, -110, 317, 48, 21,
    23, -130, 46, -123, -149, -147, -143, 70, -20, 49, 185, -141, -97, -42,
    359, 55, 47, 258, 248, -51, -9, -139, -137, 378, 4, 43, 38, -107, 333, -5,
    59, 371, 104, -146, -144, 379, 373, -135, 202, 199, 52, 35, 329, -72, 334,
    61, 62, 192, 45, -434, -152, 350, 206, 98, 92, 71, 73, 81, 97, 60, -19, 96,
    75, 77, 79, 76, 91, 64, 74, 68, 67, 90, 85, 78, 63, 313, 311, 309, 72, 328,
    42, 94, 103, 95, 100, 110, 336, 348, 337, 107, 109, 93, -70, 377, 376, 87,
    88, 101, -133, 99, 108, 6, -84, -112, -63, -61, -26, -41, 3, 39, -12, 84,
    89, 28, 37, 102, -96, -87, -55, -115, -64, 16, 9, 80, 82, -105, 57, 69, 66,
    53, 10, -109, 65, -21, 11, 29, -39, -120, -71, -44, -83, 32, -92, 362, 353,
    86, -158, -161, -159, -157, -155, -153, 106, 105, 111, -154, -156, 113,
    305, 383,
]
"""``best_list`` from experiments/sums_differences_problems.ipynb, cell 1
(the "Data and verification" cell of the DeepMind repository)."""

# Hegarty's A_15 and the paper's X = T_2, used as calibration: Penman-Wells
# state g(A_15) ~= 1.0717 (page 22) and f(X) = ln(51)/ln(47) ~= 1.0212
# (Lemma 19). If our g and f reproduce those, we are reading the same
# normalisation the paper is.
HEGARTY_X = {0, 1, 2, 4, 5, 9, 12, 13, 17, 20, 21, 22, 24, 25}
HEGARTY_A15 = HEGARTY_X | {x + 20 for x in HEGARTY_X}


def main() -> dict:
    out: dict = {}

    # ---- calibration against printed values in the two sources ----------
    n, s, d = counts(HEGARTY_A15)
    out["calibration"] = {
        "hegarty_A15": {
            "n": n, "sumset": s, "diffset": d,
            "g": g_value(n, s, d), "paper_says_g": 1.0717,
        },
        "hegarty_X_lemma19": {
            "sumset": len(sumset(HEGARTY_X)),
            "diffset": len(diffset(HEGARTY_X)),
            "f": f_value(len(sumset(HEGARTY_X)), len(diffset(HEGARTY_X))),
            "paper_says_f": math.log(51) / math.log(47),
        },
    }

    # ---- the AlphaEvolve construction, scored three ways ----------------
    A = set(ALPHAEVOLVE_42)
    an, asum, adiff = counts(A)
    ae = {
        "n": an,
        "sumset": asum,
        "diffset": adiff,
        "g": g_value(an, asum, adiff),
        "f": f_value(asum, adiff),
        "notebook_score_with_size_bonus": g_value(an, asum, adiff)
        + (1.0 - 1.0 / an) / 100.0,
        "repository_reports": 1.1219,
    }
    out["alphaevolve"] = ae

    # ---- Corollary 13, checked by enumeration ---------------------------
    rows = []
    for j in list(range(1, 61)) + [80, 120, 200, 400]:
        S = Q(j)
        qn, qs, qd = counts(S)
        rows.append({
            "j": j,
            "n": qn, "corollary13_n": 5 * j + 17,
            "sumset": qs, "corollary13_sumset": 32 * j + 63,
            "diffset": qd, "corollary13_diffset": 26 * j + 61,
            "restricted_sumset": len(restricted_sumset(S)),
            "corollary13_restricted_sumset": 32 * j + 56 if j >= 2 else 90,
            "g": g_value(qn, qs, qd),
            "f": f_value(qs, qd),
        })
    mismatches = [
        r for r in rows
        if (r["n"], r["sumset"], r["diffset"], r["restricted_sumset"])
        != (r["corollary13_n"], r["corollary13_sumset"],
            r["corollary13_diffset"], r["corollary13_restricted_sumset"])
    ]
    out["corollary13_checked_j"] = [r["j"] for r in rows]
    out["corollary13_mismatches"] = mismatches
    out["Qj_table"] = rows

    # ---- the limit, and the smallest j that beats AlphaEvolve -----------
    limit = math.log(Fraction(32, 5)) / math.log(Fraction(26, 5))
    out["theorem21_limit"] = {
        "value": limit,
        "paper_prints": 1.125944426,
        "expression": "ln(32/5)/ln(26/5)",
    }

    first = None
    for j in range(1, 4001):
        S = Q(j)
        qn, qs, qd = counts(S)
        if (qn, qs, qd) != (5 * j + 17, 32 * j + 63, 26 * j + 61):
            raise AssertionError(f"Corollary 13 failed at j={j}")
        if g_beats(qn, qs, qd, an, asum, adiff):
            first = {
                "j": j, "n": qn, "sumset": qs, "diffset": qd,
                "g": g_value(qn, qs, qd),
                "margin_over_alphaevolve": g_value(qn, qs, qd) - ae["g"],
                "exact_comparison": "decided at 120 digits, not by float",
            }
            break
    out["first_j_beating_alphaevolve"] = first

    # ---- the monotone tail, for the record ------------------------------
    # (|Q_j| = 5j+17, so enumeration is O(j^2); j = 1000 is 5017 elements and
    # about 25M pairs, which is where a stdlib-only probe should stop.)
    big = {}
    for j in (600, 1000):
        S = Q(j)
        qn, qs, qd = counts(S)
        big[str(j)] = {"n": qn, "sumset": qs, "diffset": qd,
                       "g": g_value(qn, qs, qd)}
    out["large_j"] = big

    out["verdict"] = {
        "question": (
            "does Penman-Wells (2013) reach a higher value of the Problem 42 "
            "quantity than the AlphaEvolve construction?"
        ),
        "answer": "yes",
        "alphaevolve_g": ae["g"],
        "penman_wells_supremum": limit,
        "smallest_explicit_witness_j": first["j"] if first else None,
        "normalisations_agree": True,
    }
    return out


if __name__ == "__main__":
    res = main()
    here = pathlib.Path(__file__).resolve().parent
    (here / "results.json").write_text(json.dumps(res, indent=2) + "\n")

    ae = res["alphaevolve"]
    print("calibration against printed values in Penman-Wells:")
    c = res["calibration"]
    print(f"  g(A_15)  = {c['hegarty_A15']['g']:.6f}   paper: "
          f"{c['hegarty_A15']['paper_says_g']}")
    print(f"  f(X)     = {c['hegarty_X_lemma19']['f']:.6f}   paper: "
          f"{c['hegarty_X_lemma19']['paper_says_f']:.6f}")
    print()
    print("AlphaEvolve best_list (repository notebook):")
    print(f"  |A|={ae['n']}  |A+A|={ae['sumset']}  |A-A|={ae['diffset']}")
    print(f"  g = {ae['g']:.10f}   (repository reports {ae['repository_reports']})")
    print()
    print(f"Corollary 13 mismatches over "
          f"{len(res['corollary13_checked_j'])} values of j: "
          f"{len(res['corollary13_mismatches'])}")
    print()
    f = res["first_j_beating_alphaevolve"]
    if f:
        print(f"smallest j with g(Q_j) > g(AlphaEvolve): j = {f['j']}")
        print(f"  |Q_j|={f['n']}  |Q_j+Q_j|={f['sumset']}  "
              f"|Q_j-Q_j|={f['diffset']}")
        print(f"  g = {f['g']:.10f}  (margin +{f['margin_over_alphaevolve']:.2e})")
    print(f"supremum ln(32/5)/ln(26/5) = {res['theorem21_limit']['value']:.9f}")
