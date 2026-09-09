"""The composite-line discriminator, and the hypothesis its inputs violate.

`docs/34` section 6 (table E7) and issue #93 report a "composite defect" for
every reduced binary quadratic form of fourteen discriminants, with the
headline `36.0644` at `d = -15`, and read the family as a defect axis running
from 0 to 36 with class number as the knob.

The discriminator is defined for a Dirichlet series `f = sum a(n) n^-s` with
`a(1) = 1`.  From that normalisation, `-f'/f = sum c(n) n^-s` is fixed by

    a(n) log n = sum_{d | n} c(d) a(n/d),                                  (I)

which the probe solves by recursion, isolating the `d = n` term as
`c(n) a(1) = c(n)`.

A binary quadratic form represents 1 if and only if it is the principal form.
So for every non-principal form `a(1) = 0`, the `d = n` term of (I) vanishes,
`c(n)` is not determined by the recursion, and what the recursion returns
solves nothing.  This module measures that rather than arguing it: it
computes the residual of (I) at the returned `c`, which is zero exactly when
the recursion was entitled to run.

It then rebuilds the axis from the rows that are entitled to it, and checks
those against an independent prediction that does not use the recursion at
all: for class number one, `zeta_Q = w * zeta * L(chi_d)`, so
`c(n) = Lambda(n) (1 + chi_d(n))` exactly.

Nothing here is evidence about RH (`docs/08`).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

from mpmath import mp, log as mlog

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from zeta.epstein import epstein_reduced_forms  # noqa: E402
from zeta.epstein import epstein_representation_count as rep  # noqa: E402

ART = Path(__file__).resolve().parent / "artifacts"
NMAX = 61
DPS = 30
DISCRIMINANTS = (-3, -4, -7, -8, -11, -15, -20, -23, -24, -31, -39, -47, -71, -95)


def units(d: int) -> int:
    return 6 if d == -3 else (4 if d == -4 else 2)


def spectrum(a, nmax=NMAX):
    """The recursion as `probe_euler_discriminator.py` runs it, unchanged."""
    c = [mp.mpf(0)] * nmax
    for n in range(2, nmax):
        s = a[n] * mlog(n)
        for d in range(1, n):
            if n % d == 0:
                s -= c[d] * a[n // d]
        c[n] = s
    return c


def identity_residual(a, c, nmax=NMAX):
    """max_n |a(n) log n - sum_{d|n} c(d) a(n/d)|, the defining identity (I)."""
    worst, arg = mp.mpf(0), None
    for n in range(2, nmax):
        lhs = a[n] * mlog(n)
        rhs = sum(c[d] * a[n // d] for d in range(1, n + 1) if n % d == 0)
        e = abs(lhs - rhs)
        if e > worst:
            worst, arg = e, n
    return float(worst), arg


def is_prime_power(n: int) -> bool:
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return m == 1
    return False


COMPOSITES = [n for n in range(2, NMAX) if not is_prime_power(n)]


def defect(c) -> float:
    return float(mp.sqrt(sum((c[n] / mp.sqrt(n)) ** 2 for n in COMPOSITES)))


def kronecker(d: int, n: int) -> int:
    """chi_d(n) = (d/n), the Kronecker symbol, by its definition."""
    if n <= 0:
        raise ValueError
    if n == 1:
        return 1
    result = 1
    m = n
    # factor out 2s: (d/2) = 0 if d even, 1 if d = 1,7 mod 8, -1 if d = 3,5 mod 8
    while m % 2 == 0:
        m //= 2
        if d % 2 == 0:
            return 0
        r = d % 8
        result *= 1 if r in (1, 7) else -1
    # odd part by Jacobi symbol (d/m)
    a, b = d % m, m
    while a:
        while a % 2 == 0:
            a //= 2
            if b % 8 in (3, 5):
                result = -result
        a, b = b, a
        if a % 4 == 3 and b % 4 == 3:
            result = -result
        a %= b
    return result if b == 1 else 0


def von_mangoldt(n: int):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return mlog(p) if m == 1 else mp.mpf(0)
    return mp.mpf(0)


def represented_values(form, nmax=NMAX) -> list[int]:
    return [n for n in range(1, nmax) if rep(n, form) > 0]


def main() -> None:
    mp.dps = DPS
    rows = []
    for d in DISCRIMINANTS:
        forms = epstein_reduced_forms(d)
        w = units(d)
        h = len(forms)
        total = [mp.mpf(0)] * NMAX
        per = []
        for f in forms:
            a = [mp.mpf(0)] + [mp.mpf(rep(n, f)) / w for n in range(1, NMAX)]
            c = spectrum(a)
            res, arg = identity_residual(a, c)
            vals = represented_values(f)
            m = vals[0] if vals else None
            per.append({
                "form": list(f),
                "a1": float(a[1]),
                "recursion_entitled": bool(abs(a[1] - 1) < 1e-25),
                "identity_max_residual": res,
                "identity_argmax": arg,
                "reported_composite_defect": defect(c),
                "least_represented_value": m,
                # a rescaling n -> n/m would restore a(1) = 1 only if every
                # represented value were a multiple of m
                "all_represented_values_divisible_by_least":
                    bool(m is not None and all(v % m == 0 for v in vals)),
            })
            for n in range(1, NMAX):
                total[n] += a[n]
        summed = [mp.mpf(0)] + [total[n] / total[1] for n in range(1, NMAX)]
        c_sum = spectrum(summed)
        res_sum, _ = identity_residual(summed, c_sum)

        principal = per[0]
        row = {
            "discriminant": d, "class_number": h,
            "forms": per,
            "principal_form_defect": principal["reported_composite_defect"],
            "principal_identity_residual": principal["identity_max_residual"],
            "class_group_sum_defect": defect(c_sum),
            "class_group_sum_identity_residual": res_sum,
            "max_defect_over_entitled_forms": max(
                p["reported_composite_defect"] for p in per if p["recursion_entitled"]),
            "max_defect_as_published": max(
                p["reported_composite_defect"] for p in per),
            "n_forms_entitled": sum(1 for p in per if p["recursion_entitled"]),
        }
        if h == 1:
            # independent prediction, using no recursion: zeta_Q = w zeta L(chi_d)
            pred = [mp.mpf(0)] + [von_mangoldt(n) * (1 + kronecker(d, n))
                                  for n in range(1, NMAX)]
            a = [mp.mpf(0)] + [mp.mpf(rep(n, forms[0])) / w for n in range(1, NMAX)]
            c = spectrum(a)
            row["euler_prediction_max_defect"] = float(
                max(abs(c[n] - pred[n]) for n in range(2, NMAX)))
        rows.append(row)
        print(f"d={d:4d} h={h}  entitled forms {row['n_forms_entitled']}/{h}  "
              f"principal defect {row['principal_form_defect']:.4f}  "
              f"published max {row['max_defect_as_published']:.4f}  "
              f"entitled max {row['max_defect_over_entitled_forms']:.4f}  "
              f"class-sum {row['class_group_sum_defect']:.2e}"
              + (f"  euler-pred defect {row['euler_prediction_max_defect']:.2e}"
                 if h == 1 else ""))
    ART.mkdir(exist_ok=True)
    (ART / "axis.json").write_text(json.dumps(rows, indent=1), encoding="utf-8")
    print(f"-> {ART / 'axis.json'}")


if __name__ == "__main__":
    main()
