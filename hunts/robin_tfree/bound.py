"""Robin's inequality beyond the verified range: one Mertens-product ratio, bounded.

Robin's criterion: RH holds iff sigma(n) < e^gamma n log log n for every n > 5040.
Morrill and Platt verified it for every 5040 < n <= x0#, x0 = 29 996 208 012 611
(Integers 21 (2021) A28, Theorem 13 and Corollary 14).  Above that, every known
t-free and valuation result reduces to one quantity at the primorials N_k = p_k#,

    E(x) = log( e^{-gamma} prod_{p <= x} p/(p-1) / log theta(x) ),   x = p_k >= x0,

because N_k/phi(N_k) = prod_{p <= p_k} p/(p-1) and log log N_k = log theta(p_k).
This module bounds sup_{x >= x0} E(x) in Arb ball arithmetic (python-flint).

The identity used (RESULTS.md section 2) is exact:

    E(x) = -int_x^inf R(u) w(u) du - sum_{p > x} h(p) + g(R(x)/x),
    R = theta - id,  w(u) = (1 + log u)/(u^2 log^2 u),  h(p) = -log(1-1/p) - 1/p,
    g(d) = d/L - log(1 + log(1+d)/L),  L = log x,

so the boundary term R(x)/(x log x) of Mertens' partial summation and the
log theta(x) denominator cancel to first order, leaving |g(d)| <= d^2/L.
Earlier t-free papers bound those two terms separately; that costs about
(1.95 + 1.95)/(sqrt(x0) log x0) ~ 2.3e-8 at x0, the same size as everything else.

Inputs, each a published statement (RESULTS.md section 3 quotes them):

* Buthe, Math. Comp. 87 (2018) 1991-2009: Table 1 (upper bounds M+ for
  (t - psi(t))/sqrt(t) on dyadic blocks [x, 2x], 1e10 <= x <= 5.12e18) and
  (1.7) theta(x) < x for 1 <= x <= 1e19.
* Broadbent, Kadiri, Lumley, Ng, Wilk, Math. Comp. 90 (2021) 2281-2315:
  Table 8 (|psi(x) - x| < eps(b, b') x on [e^b, e^b'], b' the next row) and
  Table 9 (|theta(x) - x| < A_1(b) x / log x for all x >= e^b).
* Rosser and Schoenfeld, Illinois J. Math. 6 (1962), Theorem 13:
  psi(x) - theta(x) < 1.42620 sqrt(x) for x > 0 (used with 1.5).
* Morrill and Platt (above): Robin's inequality for 5040 < n <= x0#.

Run: .venv/bin/python hunts/robin_tfree/bound.py   (writes results.json)
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

PREC = 256

#: Morrill-Platt 2021, Corollary 14: Robin holds for 13# <= n <= X0#, and
#: Theorem 13 covers 5040 < n <= 10^(10^13.11485) >= X0#.
X0 = 29_996_208_012_611

#: Buthe 2018 covers x <= 1e19 ((1.5)-(1.7)); Table 1's last block ends at 1.024e19.
X_BUTHE = 10**19

#: Buthe 2018, Table 1, column M+_psi(x): (t - psi(t))/sqrt(t) <= M+ for t in [x, 2x].
#: Transcribed from the published table and checked against the rendered page.
BUTHE_TABLE1_UPPER: list[tuple[int, str]] = [
    (10**10, "0.85"), (2 * 10**10, "0.64"), (4 * 10**10, "0.80"), (8 * 10**10, "0.86"),
    (16 * 10**10, "0.68"), (32 * 10**10, "0.78"), (64 * 10**10, "0.74"),
    (10**12, "0.81"), (2 * 10**12, "0.76"), (4 * 10**12, "0.73"), (8 * 10**12, "0.76"),
    (16 * 10**12, "0.68"), (32 * 10**12, "0.93"), (64 * 10**12, "0.77"),
    (10**14, "0.72"), (2 * 10**14, "0.76"), (4 * 10**14, "0.73"), (8 * 10**14, "0.88"),
    (16 * 10**14, "0.86"), (32 * 10**14, "0.86"), (64 * 10**14, "0.66"),
    (10**16, "0.74"), (2 * 10**16, "0.70"), (4 * 10**16, "0.73"), (8 * 10**16, "0.77"),
    (16 * 10**16, "0.92"), (32 * 10**16, "0.71"), (64 * 10**16, "0.82"),
    (128 * 10**16, "0.75"), (256 * 10**16, "0.86"), (512 * 10**16, "0.94"),
]

#: Buthe 2018 (1.5): |x - psi(x)| <= 0.94 sqrt(x) for 11 < x <= 1e19. Used below 1e10.
BUTHE_GLOBAL = "0.94"

#: Buthe 2018 (1.6): x - theta(x) <= 1.95 sqrt(x) for 1423 <= x <= 1e19. Route A uses
#: only this, no table: the headline t = 25 does not depend on Table 1.
BUTHE_THETA = "1.95"

#: The table prints two decimals. If those were rounded to nearest rather than
#: outward, the true supremum could be up to half a unit higher; add it.
TABLE1_MARGIN = Fraction(5, 1000)

#: BKLNW 2021, Table 8: |psi(x) - x| < eps(b, b') x for e^b <= x <= e^b', b' = next row;
#: the last row is valid on [e^25000, e^26000]. Rows below 40 are not needed (1e19 = e^43.75).
BKLNW_TABLE8: list[tuple[int, str]] = [
    (40, "1.93378e-8"), (45, "1.09073e-8"), (50, "1.11990e-9"), (100, "2.45299e-12"),
    (200, "2.18154e-12"), (300, "2.09022e-12"), (400, "2.03981e-12"), (500, "1.99986e-12"),
    (600, "1.98894e-12"), (700, "1.97643e-12"), (800, "1.96710e-12"), (900, "1.95987e-12"),
    (1000, "1.94751e-12"), (1500, "1.93677e-12"), (2000, "1.92279e-12"), (2500, "9.06304e-13"),
    (3000, "4.59972e-14"), (3500, "2.48641e-15"), (4000, "1.42633e-16"), (4500, "8.68295e-18"),
    (5000, "5.63030e-19"), (5500, "3.91348e-20"), (6000, "2.94288e-21"), (6500, "2.38493e-22"),
    (7000, "2.07655e-23"), (7500, "1.96150e-24"), (8000, "1.97611e-25"), (8500, "2.12970e-26"),
    (9000, "2.44532e-27"), (9500, "2.97001e-28"), (10000, "3.78493e-29"),
    (10500, "5.10153e-30"), (11000, "7.14264e-31"), (11500, "1.04329e-31"),
    (12000, "1.59755e-32"), (12500, "2.53362e-33"), (13000, "4.13554e-34"),
    (13500, "7.21538e-35"), (14000, "1.22655e-35"), (15000, "4.10696e-37"),
    (16000, "1.51402e-38"), (17000, "6.20397e-40"), (18000, "2.82833e-41"),
    (19000, "1.36785e-42"), (20000, "7.16209e-44"), (21000, "4.11842e-45"),
    (22000, "2.43916e-46"), (23000, "1.56474e-47"), (24000, "1.07022e-48"),
    (25000, "7.57240e-50"),
]
BKLNW_TABLE8_END = 26000

#: The paper says printf rounding "effects only the last digit": inflate each
#: six-significant-figure entry by one unit in its last place, relative 1e-5.
BKLNW_ROUNDING = Fraction(1, 10**5)

#: BKLNW 2021, Table 9: |theta(x) - x| < A_1(25000) x / log x for all x >= e^25000.
BKLNW_A1_25000 = "7.5635e-45"

#: Rosser-Schoenfeld 1962 Theorem 13 gives 1.42620; we use a rounder, larger number.
PSI_MINUS_THETA = Fraction(3, 2)


def _arb(v) -> arb:
    if isinstance(v, Fraction):
        return arb(v.numerator) / v.denominator
    if isinstance(v, str):
        return arb(v) if "e" not in v else _arb(Fraction(v))
    return arb(v)


def _up(s: str, rel: Fraction) -> arb:
    """The decimal string s, increased by the relative amount rel, as an exact ball."""
    return _arb(Fraction(s) * (1 + rel))


def antiderivative(alpha: Fraction, y: arb) -> arb:
    """F with F'(y) = e^{(alpha-1) y} (1 + y)/y^2, so that
    int_{e^a}^{e^b} u^{alpha-2} (1 + log u)/log^2 u du = F(b) - F(a).

    beta = 1 - alpha > 0: F(y) = -e^{-beta y}/y - (1 - beta) E1(beta y), E1(z) = -Ei(-z).
    beta = 0:             F(y) = log y - 1/y.
    """
    beta = 1 - alpha
    if beta == 0:
        return y.log() - 1 / y
    b = _arb(beta)
    e1 = -((-b * y).ei())
    return -(-b * y).exp() / y - (1 - b) * e1


def power_integral(alpha: Fraction, ya: arb, yb: arb) -> arb:
    """int over u in [e^ya, e^yb] of u^alpha w(u), w(u) = (1 + log u)/(u^2 log^2 u)."""
    return antiderivative(alpha, yb) - antiderivative(alpha, ya)


def _ln(n: int) -> arb:
    return arb(n).log()


def table1_blocks(x_lo: int, x_hi: int) -> list[tuple[int, int, Fraction]]:
    """Split [x_lo, x_hi] at every Table 1 block edge; on each piece take the largest
    M+ among the blocks covering it, plus the rounding margin. Below 1e10 the global
    0.94 of (1.5) is used. Raises if any piece is uncovered."""
    edges = {x_lo, x_hi}
    for x, _ in BUTHE_TABLE1_UPPER:
        for e in (x, 2 * x):
            if x_lo < e < x_hi:
                edges.add(e)
    if x_lo < 10**10 < x_hi:
        edges.add(10**10)
    pts = sorted(edges)
    out = []
    for a, b in zip(pts[:-1], pts[1:]):
        if b <= 10**10:
            m = Fraction(BUTHE_GLOBAL)
        else:
            cover = [Fraction(v) for x, v in BUTHE_TABLE1_UPPER if x <= a and b <= 2 * x]
            if not cover:
                raise ValueError(f"no Table 1 block covers [{a}, {b}]")
            m = max(cover)
        out.append((a, b, m + TABLE1_MARGIN))
    return out


def theta_deficit_terms(u_max: int) -> list[tuple[Fraction, Fraction]]:
    """u - theta(u) - (u - psi(u)) = sum_{k>=2} theta(u^{1/k}) < u^{1/2} + u^{1/3} + u^{1/4}
    + (K - 4) u^{1/5}, K = floor(log2 u), using theta(y) < y for 1 <= y <= 1e19
    (Buthe (1.7)). Returned as (coefficient, exponent) pairs, valid for 2 <= u <= u_max."""
    k_max = u_max.bit_length() - 1  # floor(log2 u_max)
    return [(Fraction(1), Fraction(1, 2)), (Fraction(1), Fraction(1, 3)),
            (Fraction(1), Fraction(1, 4)), (Fraction(max(k_max - 4, 0)), Fraction(1, 5))]


def main_integral(x0: int, x_hi: int = X_BUTHE) -> arb:
    """Upper bound for int_{x0}^{x_hi} (u - theta(u)) w(u) du, x_hi <= 1e19."""
    assert 1427 <= x0 < x_hi <= X_BUTHE
    total = arb(0)
    extra = theta_deficit_terms(x_hi)
    for a, b, m in table1_blocks(x0, x_hi):
        ya, yb = _ln(a), _ln(b)
        piece = _arb(m) * power_integral(Fraction(1, 2), ya, yb)
        for c, al in extra:
            piece += _arb(c) * power_integral(al, ya, yb)
        total += piece
    return total


def main_integral_uniform(x0: int, x_hi: int = X_BUTHE) -> arb:
    """Route A: int_{x0}^{x_hi} 1.95 sqrt(u) w(u) du, from Buthe (1.6) alone."""
    assert 1423 <= x0 < x_hi <= X_BUTHE
    return _arb(Fraction(BUTHE_THETA)) * power_integral(Fraction(1, 2), _ln(x0), _ln(x_hi))


def tail_integral(x_from: int = X_BUTHE) -> arb:
    """Upper bound for int_{x_from}^inf |theta(u) - u| w(u) du, x_from >= 1e19 = e^43.75.

    On [e^b, e^b'] (Table 8): |theta - u| <= eps u + 1.5 sqrt(u). Past e^26000: Table 9."""
    y_from = _ln(x_from)
    assert x_from >= X_BUTHE
    total = arb(0)
    rows = BKLNW_TABLE8 + [(BKLNW_TABLE8_END, None)]
    for (b, eps), (b_next, _) in zip(rows[:-1], rows[1:]):
        lo = arb(b) if arb(b) > y_from else y_from
        hi = arb(b_next)
        if not (hi > lo):
            continue
        total += _up(eps, BKLNW_ROUNDING) * power_integral(Fraction(1), lo, hi)
        total += _arb(PSI_MINUS_THETA) * power_integral(Fraction(1, 2), lo, hi)
    # x >= e^26000: |theta(x) - x| < A_1 x / log x; int_{Y}^inf A_1/y (1+y)/y^2 dy
    y = arb(BKLNW_TABLE8_END)
    a1 = _up(BKLNW_A1_25000, BKLNW_ROUNDING)
    total += a1 * (1 / y + 1 / (2 * y * y))
    return total


def deficit_at(x: int) -> arb:
    """Upper bound for |theta(x) - x|/x at x in [x0, 1e19]: (M + 1 + small)/sqrt(x)."""
    m = max(Fraction(v) for _, v in BUTHE_TABLE1_UPPER) + TABLE1_MARGIN
    s = arb(x).sqrt()
    bound = _arb(m) * s
    for c, al in theta_deficit_terms(X_BUTHE):
        bound += _arb(c) * arb(x) ** _arb(al)
    return bound / arb(x)


def second_order(x0: int) -> arb:
    """|g(d)| <= d^2/L for |d| <= 1e-6, L >= 31 (RESULTS.md, Lemma 2), with d the
    largest |theta(x) - x|/x over x >= x0: the Buthe range at x0, or Table 8 beyond."""
    d = deficit_at(x0)
    d_far = _up(BKLNW_TABLE8[0][1], BKLNW_ROUNDING) + _arb(PSI_MINUS_THETA) / arb(X_BUTHE).sqrt()
    d = d if d > d_far else d_far
    assert d < arb("1e-6") and _ln(x0) > 31
    return d * d / _ln(x0)


def e_star(x0: int = X0, route: str = "table1") -> dict:
    """sup_{x >= x0} E(x) <= main + tail + second order (the integral bound is
    decreasing in x because its integrand bound is nonnegative).

    route "uniform" (A): Buthe (1.6) on [x0, 1e19]; route "table1" (B): Table 1 blocks."""
    ctx.prec = PREC
    main = main_integral(x0) if route == "table1" else main_integral_uniform(x0)
    tail = tail_integral()
    sec = second_order(x0)
    return {"main": main, "tail": tail, "second_order": sec, "E_star": main + tail + sec}


def slack(x0: int = X0) -> arb:
    """log of prod_{p>p_k}(1-p^{-t})^{-1} (t >= 2) and of log theta(p_{k+1})/log theta(p_k),
    each at most 4/(x0 - 1) for p_k >= x0 (RESULTS.md section 4)."""
    return arb(4) / (x0 - 1)


def max_tfree(E: arb, s: arb, t_range=range(2, 41)) -> tuple[int, dict]:
    """Largest t with log(1/zeta(t)) + s + E < 0 decided in balls (all smaller t also pass)."""
    verdicts = {}
    for t in t_range:
        lhs = (1 / arb(t).zeta()).log() + s + E
        verdicts[t] = "pass" if lhs < 0 else ("fail" if lhs > 0 else "undecided")
    passing = [t for t, v in verdicts.items() if v == "pass"]
    best = max(passing)
    assert all(verdicts[t] == "pass" for t in t_range if t <= best)
    return best, verdicts


def q_star(E: arb, s: arb) -> arb:
    """Robin holds for n > x0# whenever some prime q has q^(nu_q(n)+1) < Q*,
    Q* = 1/(1 - exp(-(E + s))). Returns a ball; use its lower endpoint."""
    return 1 / (1 - (-(E + s)).exp())


def valuation_table(qs: arb, primes: list[int]) -> dict[int, int]:
    """For each prime q, the largest nu with q^(nu+1) < Q* (decided against the lower
    endpoint of the ball, so every entry is safe)."""
    lo = qs.lower()
    out = {}
    for q in primes:
        nu = -1
        while arb(q) ** (nu + 2) < lo:
            nu += 1
        out[q] = nu
    return out


def _primes_upto(n: int) -> list[int]:
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(n + 1) if sieve[i]]


def _fmt(x: arb) -> str:
    return x.str(20, radius=True)


def _route(route: str) -> dict:
    parts = e_star(X0, route)
    E = parts["E_star"]
    s = slack(X0)
    t_best, verdicts = max_tfree(E, s)
    qs = q_star(E, s)
    vals = valuation_table(qs, _primes_upto(400))
    eps = (E + s).exp() - 1
    q_lo = int(math.floor(float(qs.lower().mid())))
    return {
        "E_star_parts": {k: _fmt(v) for k, v in parts.items()},
        "E_star_upper": float(E.upper().mid()),
        "slack": _fmt(s),
        "max_t_free": t_best,
        "t_verdicts": verdicts,
        "Q_star_lower": float(qs.lower().mid()),
        "Q_star_floor": q_lo,
        "nu_le_1_for_primes_below": math.isqrt(q_lo - 1) + 1,
        "valuation_max_nu": {str(q): v for q, v in vals.items()},
        "epsilon_upper": float(eps.upper().mid()),
    }


def run() -> dict:
    ctx.prec = PREC
    return {
        "x0": X0,
        "prec_bits": PREC,
        "route_A_uniform_1.95": _route("uniform"),
        "route_B_table1": _route("table1"),
        "compare": {
            "axler_2023_t": 21,
            "axler_2023_epsilon": 3.15367e-7,
            "axler_2023_nu2": 20,
        },
    }


if __name__ == "__main__":
    res = run()
    path = Path(__file__).with_name("results.json")
    path.write_text(json.dumps(res, indent=2) + "\n", encoding="utf-8")
    for name in ("route_A_uniform_1.95", "route_B_table1"):
        r = res[name]
        print(name, json.dumps({k: r[k] for k in ("E_star_upper", "max_t_free", "Q_star_lower",
                                                  "epsilon_upper")}))
        print("  max nu_q:", dict(list(r["valuation_max_nu"].items())[:12]))
