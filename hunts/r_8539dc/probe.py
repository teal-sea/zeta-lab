"""Exact recomputation of the two third-autocorrelation functionals.

Hunt R-8539DC. Issue teal-sea/zeta-lab#123.

Both AlphaEvolve step-function constructions for the "third autocorrelation
inequality" are evaluated under BOTH readings of the published inequality, in
exact rational arithmetic (the heights are decimals with ten places, so they
are exact rationals with denominator 10**10 and the whole computation is
integer arithmetic).

For a step function f with n equal steps of width h = 1/(2n) on [-1/4, 1/4]
and heights a_0..a_{n-1}, the autoconvolution f*f is supported on [-1/2, 1/2]
and is piecewise linear with knots at the multiples of h, taking the value
h * b_k at the k-th knot, where b = a convolved with a.  A piecewise-linear
function attains its extrema at knots, so

    max_t (f*f)(t)  =  h * max_k b_k
    max_t |f*f(t)|  =  h * max_k |b_k|
    (integral f)^2  =  (h * sum_j a_j)^2

and the two functionals are

    A(f) = max_t (f*f)(t) / (int f)^2  = 2n * max_k b_k   / (sum_j a_j)^2
    B(f) = max_t |f*f(t)| / (int f)^2  = 2n * max_k |b_k| / (sum_j a_j)^2

A is what the published verification cell computes: it writes
abs(2*n*max(conv)/sum**2), and the outer abs is a no-op because
int_{-1/2}^{1/2} f*f = (int f)^2 > 0 forces max_t f*f(t) > 0.  B is what the
inequality "max |f*f(t)| >= C (int f)^2" defines.

Usage:  python3 probe.py        (stdlib only: json, fractions, decimal)
"""

from __future__ import annotations

import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data" / "alphaevolve_sequences.json"


def exact_heights(decimal_strings: list[str]) -> list[Fraction]:
    """Decimal literals -> exact rationals.  No float ever touches these."""
    return [Fraction(Decimal(s)) for s in decimal_strings]


def autoconvolve(a: list[Fraction]) -> list[Fraction]:
    """b_k = sum_{i+j=k} a_i a_j, exactly."""
    n = len(a)
    b = [Fraction(0)] * (2 * n - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, aj in enumerate(a):
            b[i + j] += ai * aj
    return b


def functionals(a: list[Fraction]) -> dict:
    n = len(a)
    b = autoconvolve(a)
    s = sum(a)
    if s == 0:
        raise ValueError("integral of f is zero; both functionals are undefined")
    max_b = max(b)
    max_abs_b = max(abs(x) for x in b)
    min_b = min(b)
    scale = Fraction(2 * n, 1) / (s * s)
    A = scale * max_b
    B = scale * max_abs_b
    return {
        "n": n,
        "sum_a": float(s),
        "max_b_index": b.index(max_b),
        "min_b_index": b.index(min_b),
        "max_b_float": float(max_b),
        "min_b_float": float(min_b),
        # A = max f*f / (int f)^2   -- the functional the published code computes
        "A_exact_num_digits": len(str(A.numerator)),
        "A": A,
        # B = max |f*f| / (int f)^2 -- the functional "max |f*f| >= C (int f)^2" defines
        "B": B,
        "negative_side_dominates": abs(min_b) > max_b,
    }


def fmt(x: Fraction, places: int = 30) -> str:
    """Exact rational -> decimal string with `places` digits, truncated."""
    sign = "-" if x < 0 else ""
    x = abs(x)
    whole = x.numerator // x.denominator
    rem = x - whole
    digits = ""
    for _ in range(places):
        rem *= 10
        d = rem.numerator // rem.denominator
        digits += str(d)
        rem -= d
    return f"{sign}{whole}.{digits}"


def main() -> dict:
    raw = json.loads(DATA.read_text())
    report = {}
    for key, label in (
        ("height_sequence_3", "B.3 construction (n=400), published as C_3 <= 1.4557"),
        ("height_sequence_4", "B.3' construction (n=150), published as C_3' <= 1.4688"),
    ):
        a = exact_heights(raw[key])
        r = functionals(a)
        A, B = r.pop("A"), r.pop("B")
        r["label"] = label
        r["A_max_ff_over_int2"] = fmt(A)
        r["B_max_abs_ff_over_int2"] = fmt(B)
        r["A_float"] = float(A)
        r["B_float"] = float(B)
        r["B_minus_A_float"] = float(B - A)
        report[key] = r
    return report


if __name__ == "__main__":
    rep = main()
    for key, r in rep.items():
        print(f"=== {key}: {r['label']}")
        print(f"    n = {r['n']}, sum a = {r['sum_a']!r}")
        print(f"    A = max(f*f)/(int f)^2  = {r['A_max_ff_over_int2']}")
        print(f"    B = max|f*f|/(int f)^2  = {r['B_max_abs_ff_over_int2']}")
        print(f"    max b at knot {r['max_b_index']}, min b at knot {r['min_b_index']}"
              f" (min b = {r['min_b_float']:.10g})")
        print(f"    the negative side dominates: {r['negative_side_dominates']}")
    print()
    print(json.dumps(rep, indent=1))
