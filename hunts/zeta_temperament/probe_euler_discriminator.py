"""Composite lines in the zero spectrum, as a test for an Euler product.

For a Dirichlet series f = sum a(n) n^{-s} with a(1) = 1, write
-f'/f = sum c(n) n^{-s}. Weil's explicit formula makes c(n)/sqrt(n) the
weight of frequency log n in the distribution of f's zeros, so c(n) is what
`zeta.explicit.prime_spectrum` plots for zeta. The coefficients satisfy

    a(n) log n = sum_{d | n} c(d) a(n/d),

solved here by recursion from c(1) = 0. Two elementary consequences, both
re-derived below rather than assumed:

* f has an Euler product  <=>  log f is supported on prime powers  <=>  c is
  supported on prime powers. So a nonzero c at a composite is exactly a
  failure of multiplicativity, visible in the zeros.
* zeta gives c = von Mangoldt (the calibration this file runs first).

Three subjects, all with the same shape of functional equation:

1. zeta: composites vanish identically.
2. Davenport-Heilbronn (`zeta.epstein`), which violates RH: its coefficients
   are periodic mod 5 rather than multiplicative, so composites do not vanish.
3. Epstein zeta functions of binary quadratic forms, a family indexed by
   discriminant. Class number one gives zeta_Q = w * zeta * L(chi_d) and an
   Euler product; class number above one gives individual forms with no Euler
   product, whose composite lines must nevertheless cancel when summed over
   the class group, since the sum is w * zeta_K.

The recursion needs a(1) = 1, and a reduced form represents 1 exactly when it
is the principal form. So the per-form measurement runs on one form per
discriminant, `spectrum` refuses any series with a(1) != 1, and the planted
fault (2, 1, 2) of discriminant -15 shows the refusal firing. Every reduced
form still enters the class-group sum. Changed 2026-10-10 (issue #93): until
then this probe ran every form and reported the maximum, and on a form with
a(1) = 0 the recursion, which never reads a(1), returned the coefficients of
1 + Z_Q(s) rather than of Z_Q(s).

Writes results_euler.json. Nothing here is evidence about RH (`docs/08`).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from mpmath import mp
from mpmath import log as mlog

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
from zeta.epstein import dh_coefficient, epstein_reduced_forms  # noqa: E402
from zeta.epstein import epstein_representation_count as rep  # noqa: E402

NMAX = 61
DPS = 30


def spectrum(a, nmax=NMAX):
    """c(n) from a(n) log n = sum_{d|n} c(d) a(n/d), with a(1) = 1.

    The recursion isolates the d = n term as c(n) a(1), so a series with
    a(1) != 1 is refused rather than given a number that solves nothing.
    """
    if abs(a[1] - 1) > mp.mpf(10) ** -25:
        raise ValueError(
            "the recursion isolates c(n) a(1); a(1) = %s does not determine c"
            % mp.nstr(a[1], 6))
    c = [mp.mpf(0)] * nmax
    for n in range(2, nmax):
        s = a[n] * mlog(n)
        for d in range(1, n):
            if n % d == 0:
                s -= c[d] * a[n // d]
        c[n] = s
    return c


def is_prime_power(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return m == 1
    return False


COMPOSITES = [n for n in range(2, NMAX) if not is_prime_power(n)]


def defect(c):
    """L2 norm of the composite part, weighted the way the explicit formula weights it."""
    return float(mp.sqrt(sum((c[n] / mp.sqrt(n)) ** 2 for n in COMPOSITES)))


def units(d):
    return 6 if d == -3 else (4 if d == -4 else 2)


def main():
    mp.dps = DPS
    out = {"nmax": NMAX, "composites": COMPOSITES}

    # 1. calibration: zeta must return von Mangoldt
    cz = spectrum([mp.mpf(0)] + [mp.mpf(1)] * (NMAX - 1))
    out["zeta"] = {
        "c": {str(n): float(cz[n]) for n in range(2, 25)},
        "composite_defect": defect(cz),
        "matches_von_mangoldt": all(
            abs(cz[n] - (mlog(p) if any(n == p**k for k in range(1, 8)) else 0)) < mp.mpf(10) ** -25
            for n in range(2, NMAX)
            for p in [next((q for q in range(2, n + 1) if n % q == 0), n)]
        ),
    }

    # 2. Davenport-Heilbronn
    a_dh = [mp.mpf(0)] + [dh_coefficient(n, 25) for n in range(1, NMAX)]
    cd = spectrum(a_dh)
    loud = max(range(2, NMAX), key=lambda n: abs(cd[n]))
    out["davenport_heilbronn"] = {
        "c": {str(n): float(cd[n]) for n in range(2, 25)},
        "composite_defect": defect(cd),
        "loudest_line": {"n": loud, "c": float(cd[loud]), "is_composite": loud in COMPOSITES},
        "loudest_prime_line_abs": max(abs(float(cd[p])) for p in (2, 3, 5, 7, 11, 13)),
    }

    # 3. the Epstein family. The per-form loop runs over the forms that
    # represent 1, which is the principal form alone; every form enters the sum.
    fam = []
    for d in (-3, -4, -7, -8, -11, -15, -20, -23, -24, -31, -39, -47, -71, -95):
        forms = epstein_reduced_forms(d)
        w = units(d)
        total = [mp.mpf(0)] * NMAX
        per = []
        for f in forms:
            a = [mp.mpf(0)] + [mp.mpf(rep(n, f)) / w for n in range(1, NMAX)]
            for n in range(1, NMAX):
                total[n] += a[n]
            if rep(1, f) > 0:
                per.append({"form": list(f), "composite_defect": defect(spectrum(a))})
        if len(per) != 1:
            raise AssertionError(f"d = {d}: {len(per)} reduced forms represent 1, expected 1")
        summed = [mp.mpf(0)] + [total[n] / total[1] for n in range(1, NMAX)]
        fam.append({
            "discriminant": d,
            "class_number": len(forms),
            "forms": per,
            "principal_form_defect": per[0]["composite_defect"],
            "class_group_sum_defect": defect(spectrum(summed)),
        })
    out["epstein"] = fam

    # the planted fault that fires the a(1) guard: (2, 1, 2) of d = -15
    # represents 2 and 3 but not 1, so it must be refused, not measured
    planted = (2, 1, 2)
    a_bad = [mp.mpf(0)] + [mp.mpf(rep(n, planted)) / units(-15) for n in range(1, NMAX)]
    try:
        spectrum(a_bad)
    except ValueError as exc:
        out["planted_fault"] = {"discriminant": -15, "form": list(planted), "refused": str(exc)}
    else:
        raise AssertionError("the a(1) = 1 guard did not fire on (2, 1, 2) of d = -15")
    (HERE / "results_euler.json").write_text(json.dumps(out, indent=1))

    print(f"zeta: composite defect {out['zeta']['composite_defect']:.2e}, von Mangoldt {out['zeta']['matches_von_mangoldt']}")
    dh = out["davenport_heilbronn"]
    print(f"DH:   composite defect {dh['composite_defect']:.4f}; loudest line n={dh['loudest_line']['n']} "
          f"(composite={dh['loudest_line']['is_composite']}) c={dh['loudest_line']['c']:+.4f}; "
          f"loudest prime line {dh['loudest_prime_line_abs']:.4f}")
    print("\n   d     h   principal-form defect   class-group-sum defect")
    for r in fam:
        print(f"  {r['discriminant']:4d}  {r['class_number']:2d}   {r['principal_form_defect']:14.4f}   {r['class_group_sum_defect']:.2e}")
    print(f"planted fault {out['planted_fault']['form']} of d = -15 refused: {out['planted_fault']['refused']}")


if __name__ == "__main__":
    main()
