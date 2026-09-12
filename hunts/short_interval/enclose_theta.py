"""Enclosure-carrying lower bounds on the short-interval proportion at bandwidth theta.

Condition 5 of the gate in ``MISSION.md`` section 6.2: "bandwidth-theta decimals
must be enclosed by ball arithmetic before any number is stated". This file
does that, for both kernels, at ten bandwidths, and it does it with no
floating point on the load-bearing path at all.

The functional (``hunts/wide_search/xiprime.py``, ``landscape.py``), for an
even window ``v`` on ``I = [-1/2, 1/2]`` at bandwidth ``lambda <= 1``:

    R_lambda(v) = [ int v^2 + lambda iint F(lambda (s-s')) v(s) v(s') ds ds' ]
                  / ( lambda (int v)^2 )

with ``F(x) = |x|`` for zeta (Montgomery) and, for xi' (Farmer-Gonek-Lee),

    F_1(x) = |x| - 4x^2 + sum_{k>=1} a_k |x|^{2k+1},
    a_k    = 2^{2k+1} (k-1)! / (2k)!.

The proportion bound is ``2 - R_lambda(v)`` and it is a valid lower bound for
EVERY admissible ``v``. So the only thing that has to be enclosed is
``R_lambda(v)`` from above, for one concrete ``v``. For an even polynomial
``v`` with rational coefficients every integral is an exact rational:

    R_lambda(v) = [ c.P.c + lambda^2 c.G_1.c - 4 lambda^3 c.G_2.c
                    + sum_{k=1}^{M} a_k lambda^{2k+2} c.G_{2k+1}.c ] / (lambda (b.c)^2)
                  + (the tail k > M),

where ``G_m[i][j] = iint |s-t|^m s^{2i} t^{2j}``, ``P[i][j] = int s^{2i+2j}``,
``b[i] = int s^{2i}``, all rational. The tail is bounded above rigorously,
following ``hunts/wide_search/certify_bound.py``: for ``|x| <= lambda <= 1``,

    sum_{k>M} a_k |x|^{2k+1} <= lambda^{2M+3} sum_{k>M} a_k <= lambda^{2M+3} rho_M,

with ``rho_M`` the geometric majorant of ``certify_bound.tail_bound`` (the ratio
``a_{k+1}/a_k = 2k/((k+1)(2k+1))`` decreases in ``k``), and then, with
``|I| = 1`` and Cauchy-Schwarz ``(int |v|)^2 <= int v^2``,

    tail contribution to R  <=  lambda^{2M+3} rho_M (int v^2) / (int v)^2.

That needs no positivity of ``v``. The final bound ``2 - R - tail`` is an
exact rational, printed truncated downward. Grade: hardened (exact rationals
plus a proved tail bound). Ball arithmetic enters only the zeta CONTROL, where
Wang's closed form ``c(theta) = 2 - theta/2 - cot(theta/sqrt 2)/sqrt 2`` is
transcendental and is enclosed with Arb (``python-flint``) or ``mpmath.iv``,
with exact endpoint extraction, so the comparison "polynomial bound <= optimum"
is an exact rational comparison against the enclosure's lower end.

How each window was chosen carries no proof weight: the minimizer over even
polynomials of degree <= 6 is a 4 x 4 float linear solve, normalized to
``v(0) = 1`` and rounded to denominators <= 1000, then everything is
re-evaluated exactly. A worse window only makes the bound looser.

Controls, all mandatory and all checked exactly in ``main``:

  (i)   zeta kernel at every theta: bound <= c(theta) (it is a lower bound on
        the optimum) and within 1e-3 of it;
  (ii)  xi' at theta = 1 with the source paper's quartic
        ``1 - (7/100)(2s)^2 - (51/200)(2s)^4`` gives >= 0.86864 and the flat
        window gives >= 0.85838 (Alpoge-Furman Remark 7.1);
  (iii) the float landscape values of ``landscape.py`` at 0.55, 0.60, 0.80
        (xi') lie above the enclosed bounds.

Also checked: the exact moment matrices against sympy at several entries, the
flat-window closed form ``1/lambda + lambda/3`` for zeta, and the degree-6
bound at theta = 1 for xi' against the laboratory's ``H* = 0.8686415005``.

Run from the repo root with the repository virtualenv:

    .venv/bin/python hunts/short_interval/enclose_theta.py

Writes ``hunts/short_interval/artifacts/enclose-theta.json``.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from math import comb, factorial
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ARTIFACT = HERE / "artifacts" / "enclose-theta.json"

#: Even polynomial degree cap: v(s) = sum_{i<=3} c_i s^{2i}.
NBASIS = 4
#: Series truncation. certify_bound.py uses M = 20 at lambda = 1.
M = 20
#: Denominator cap when rounding the float-optimal window to rationals.
DENOM = 1000
#: Decimal places for the truncated display of each bound.
DIGITS = 12

THETAS = [Fraction(t, 100) for t in (100, 95, 90, 85, 80, 75, 70, 65, 60, 55)]

#: landscape.py, section 5 of its output: float optimal-window values for xi'.
LANDSCAPE_XIPRIME = {Fraction(55, 100): 0.130262, Fraction(60, 100): 0.281718,
                     Fraction(80, 100): 0.682554}
#: Alpoge-Furman Remark 7.1 (flat) and the source paper's quartic, at theta 1.
AF_FLAT = Fraction(85838, 100000)
AF_QUARTIC = Fraction(86864, 100000)
#: hunts/wide_search: the full-window xi' optimum at bandwidth 1 (float grade).
LAB_H_STAR = 0.8686415005297670641
#: The source paper's quartic in the s-monomial basis:
#: 1 - (7/100)(2s)^2 - (51/200)(2s)^4 = 1 - (7/25) s^2 - (102/25) s^4.
QUARTIC = [Fraction(1), Fraction(-7, 25), Fraction(-102, 25), Fraction(0)]
FLAT = [Fraction(1), Fraction(0), Fraction(0), Fraction(0)]

HALF = Fraction(1, 2)


# ---------------------------------------------------------------------------
# exact polynomial arithmetic, coefficients are Fractions, index = power
# ---------------------------------------------------------------------------


def _pmul(p: list[Fraction], q: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, c in enumerate(q):
            out[i + j] += a * c
    return out


def _padd(p: list[Fraction], q: list[Fraction]) -> list[Fraction]:
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def _pscale(p: list[Fraction], a: Fraction) -> list[Fraction]:
    return [a * c for c in p]


def _shift_pow(offset: Fraction, n: int) -> list[Fraction]:
    """``(s + offset)^n`` as a polynomial in ``s``."""
    return [comb(n, k) * offset ** (n - k) for k in range(n + 1)]


def _int_I(p: list[Fraction]) -> Fraction:
    """``int_{-1/2}^{1/2} p(s) ds``."""
    return sum(c * (HALF ** (k + 1) - (-HALF) ** (k + 1)) / (k + 1) for k, c in enumerate(p))


def moment_below(m: int, a: int, b: int) -> Fraction:
    """``int_I s^a int_{-1/2}^{s} (s-t)^m t^b dt ds``, exact.

    Inner: ``u = s - t``, ``t^b = (s-u)^b = sum_l C(b,l) s^{b-l} (-u)^l``, and
    ``int_0^{s+1/2} u^{m+l} du = (s+1/2)^{m+l+1}/(m+l+1)``.
    """
    inner: list[Fraction] = [Fraction(0)]
    for l in range(b + 1):
        coef = Fraction(comb(b, l) * (-1) ** l, m + l + 1)
        term = _pmul([Fraction(0)] * (b - l) + [Fraction(1)], _shift_pow(HALF, m + l + 1))
        inner = _padd(inner, _pscale(term, coef))
    return _int_I(_pmul([Fraction(0)] * a + [Fraction(1)], inner))


def moment_above(m: int, a: int, b: int) -> Fraction:
    """``int_I s^a int_{s}^{1/2} (t-s)^m t^b dt ds``, exact.

    Inner: ``u = t - s``, ``t^b = (s+u)^b``, ``int_0^{1/2-s} u^{m+l} du``.
    """
    inner: list[Fraction] = [Fraction(0)]
    for l in range(b + 1):
        coef = Fraction(comb(b, l), m + l + 1)
        # (1/2 - s)^n = (-1)^n (s - 1/2)^n
        term = _pmul([Fraction(0)] * (b - l) + [Fraction(1)],
                     _pscale(_shift_pow(-HALF, m + l + 1), Fraction((-1) ** (m + l + 1))))
        inner = _padd(inner, _pscale(term, coef))
    return _int_I(_pmul([Fraction(0)] * a + [Fraction(1)], inner))


def moment(m: int, a: int, b: int) -> Fraction:
    """``iint_{I^2} |s-t|^m s^a t^b ds dt``, exact rational."""
    return moment_below(m, a, b) + moment_above(m, a, b)


def a_coeff(k: int) -> Fraction:
    return Fraction(2 ** (2 * k + 1) * factorial(k - 1), factorial(2 * k))


def tail_bound(m: int) -> Fraction:
    """``rho_m >= sum_{k>m} a_k``, exactly as ``certify_bound.tail_bound``."""
    r = Fraction(2 * (m + 1), (m + 2) * (2 * m + 3))
    if not r < 1:
        raise ValueError("geometric ratio must be < 1")
    return a_coeff(m + 1) / (1 - r)


# ---------------------------------------------------------------------------
# the exact quadratic forms
# ---------------------------------------------------------------------------


def build_forms(nbasis: int = NBASIS, m_max: int = M):
    """``P``, ``b`` and ``G_m`` for ``m in {1, 2} + {2k+1 : 1 <= k <= M}``."""
    P = [[_int_I([Fraction(0)] * (2 * i + 2 * j) + [Fraction(1)]) for j in range(nbasis)]
         for i in range(nbasis)]
    b = [_int_I([Fraction(0)] * (2 * i) + [Fraction(1)]) for i in range(nbasis)]
    orders = [1, 2] + [2 * k + 1 for k in range(1, m_max + 1)]
    G = {}
    for m in orders:
        G[m] = [[None] * nbasis for _ in range(nbasis)]
        for i in range(nbasis):
            for j in range(i, nbasis):
                G[m][i][j] = G[m][j][i] = moment(m, 2 * i, 2 * j)
    return P, b, G


def quad(mat, c) -> Fraction:
    return sum(c[i] * mat[i][j] * c[j] for i in range(len(c)) for j in range(len(c)))


def numerator_matrix(lam: Fraction, kernel: str, P, G, m_max: int = M):
    """``N(lambda)`` with ``R = c.N.c / (lambda (b.c)^2)`` up to the tail."""
    n = len(P)
    N = [[P[i][j] + lam ** 2 * G[1][i][j] for j in range(n)] for i in range(n)]
    if kernel == "xiprime":
        for i in range(n):
            for j in range(n):
                N[i][j] -= 4 * lam ** 3 * G[2][i][j]
                for k in range(1, m_max + 1):
                    N[i][j] += a_coeff(k) * lam ** (2 * k + 2) * G[2 * k + 1][i][j]
    elif kernel != "zeta":
        raise ValueError(kernel)
    return N


def exact_R(lam: Fraction, kernel: str, c: list[Fraction], P, b, G, m_max: int = M):
    """``(R_truncated, tail_upper)``: exact rational and a proved upper bound."""
    N = numerator_matrix(lam, kernel, P, G, m_max)
    int_v = sum(bi * ci for bi, ci in zip(b, c))
    if int_v == 0:
        raise ValueError("window has zero mean")
    R = quad(N, c) / (lam * int_v ** 2)
    if kernel == "xiprime":
        tail = lam ** (2 * m_max + 3) * tail_bound(m_max) * quad(P, c) / int_v ** 2
    else:
        tail = Fraction(0)
    return R, tail


def optimal_window(lam: Fraction, kernel: str, P, b, G, denom: int = DENOM) -> list[Fraction]:
    """Float linear solve for the degree-6 minimizer, rounded to rationals.

    Carries no proof weight: any output is a valid window, a poor one only
    loosens the bound.
    """
    N = np.array([[float(x) for x in row] for row in numerator_matrix(lam, kernel, P, G)])
    bf = np.array([float(x) for x in b])
    c = np.linalg.solve(N, bf)
    c = c / c[0]
    return [Fraction(1)] + [Fraction(float(x)).limit_denominator(denom) for x in c[1:]]


# ---------------------------------------------------------------------------
# the control enclosure: Wang's closed form, ball arithmetic, exact endpoints
# ---------------------------------------------------------------------------


def _mpf_to_fraction(x) -> Fraction:
    sign, man, exp, _bc = x._mpf_
    if man == 0:
        if exp != 0:
            raise ValueError("non-finite endpoint")
        return Fraction(0)
    out = Fraction(int(man)) * Fraction(2) ** int(exp)
    return -out if sign else out


def wang_enclosure_iv(theta: Fraction, dps: int = 40) -> tuple[Fraction, Fraction]:
    """``c(theta) = 2 - theta/2 - cot(theta/sqrt 2)/sqrt 2`` via ``mpmath.iv``."""
    from mpmath import iv, mp

    old = iv.dps
    try:
        iv.dps = dps
        th = iv.mpf(theta.numerator) / iv.mpf(theta.denominator)
        s2 = iv.sqrt(iv.mpf(2))
        val = 2 - th / 2 - 1 / (s2 * iv.tan(th / s2))
        lo, hi = val._mpi_
        return _mpf_to_fraction(mp.make_mpf(lo)), _mpf_to_fraction(mp.make_mpf(hi))
    finally:
        iv.dps = old


def wang_enclosure_arb(theta: Fraction, prec: int = 160) -> tuple[Fraction, Fraction]:
    """The same quantity as an Arb ball, endpoints read out exactly."""
    import flint

    old = flint.ctx.prec
    try:
        flint.ctx.prec = prec
        th = flint.arb(flint.fmpq(theta.numerator, theta.denominator))
        s2 = flint.arb(2).sqrt()
        val = 2 - th / 2 - 1 / (s2 * (th / s2).tan())
        if not val.is_finite():
            raise ArithmeticError("Arb could not bound c(theta)")
        ends = []
        for end in (val.lower(), val.upper()):
            man, exp = end.man_exp()
            ends.append(Fraction(int(man)) * Fraction(2) ** int(exp))
        return ends[0], ends[1]
    finally:
        flint.ctx.prec = old


def wang_enclosure(theta: Fraction) -> tuple[Fraction, Fraction, str]:
    """``(lo, hi, backend)``; Arb when installed, cross-checked against iv."""
    lo_iv, hi_iv = wang_enclosure_iv(theta)
    try:
        lo_arb, hi_arb = wang_enclosure_arb(theta)
    except ImportError:
        return lo_iv, hi_iv, "mpmath.iv"
    if not (lo_arb <= hi_iv and lo_iv <= hi_arb):
        raise ArithmeticError(f"Arb and iv enclosures of c({theta}) are disjoint")
    return max(lo_arb, lo_iv), min(hi_arb, hi_iv), "python-flint (cross-checked against mpmath.iv)"


# ---------------------------------------------------------------------------
# display helpers
# ---------------------------------------------------------------------------


def trunc_down(x: Fraction, digits: int = DIGITS) -> str:
    """Decimal string of ``x`` truncated DOWNWARD (floor), never rounded."""
    scale = 10 ** digits
    n = (x.numerator * scale) // x.denominator  # floor for any sign
    q = Fraction(n, scale)
    assert q <= x
    sign = "-" if n < 0 else ""
    n = abs(n)
    return f"{sign}{n // scale}.{n % scale:0{digits}d}"


def frac_str(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def sympy_selfcheck(P, b, G) -> list[dict]:
    """A handful of exact moments recomputed by sympy. Not load-bearing."""
    import sympy as sp

    s, t = sp.symbols("s t")
    half = sp.Rational(1, 2)
    out = []
    for m, i, j in ((1, 0, 0), (2, 0, 0), (3, 1, 0), (5, 1, 2), (7, 3, 3), (11, 2, 1)):
        below = sp.integrate(sp.integrate((s - t) ** m * t ** (2 * j), (t, -half, s)) * s ** (2 * i),
                             (s, -half, half))
        above = sp.integrate(sp.integrate((t - s) ** m * t ** (2 * j), (t, s, half)) * s ** (2 * i),
                             (s, -half, half))
        ref = sp.nsimplify(below + above)
        ok = Fraction(int(ref.p), int(ref.q)) == G[m][i][j]
        out.append({"m": m, "i": i, "j": j, "value": frac_str(G[m][i][j]), "agrees_with_sympy": ok})
        if not ok:
            raise ArithmeticError(f"moment ({m},{i},{j}) disagrees with sympy: {G[m][i][j]} vs {ref}")
    assert G[1][0][0] == Fraction(1, 3) and G[2][0][0] == Fraction(1, 6)
    return out


# ---------------------------------------------------------------------------


def main() -> int:
    from zeta import rigor

    print(f"rigor backend: {rigor.BACKEND}   available: {rigor.available_backends()}")
    P, b, G = build_forms()
    checks = sympy_selfcheck(P, b, G)
    print(f"moment self-check against sympy: {len(checks)} entries agree; "
          f"G_1[0][0] = {G[1][0][0]}, G_2[0][0] = {G[2][0][0]}")

    # flat-window zeta closed form, exact
    for lam in THETAS:
        R, tail = exact_R(lam, "zeta", FLAT, P, b, G)
        assert R == 1 / lam + lam / 3 and tail == 0
    print("flat window, zeta: R = 1/lambda + lambda/3 exactly at every theta")

    rows = []
    all_pass = True
    print()
    print(f"{'theta':>6}  {'kernel':>7}  {'window c1,c2,c3 (c0 = 1)':>36}  "
          f"{'bound (trunc)':>16}  {'control':>40}")
    for theta in THETAS:
        for kernel in ("zeta", "xiprime"):
            c = optimal_window(theta, kernel, P, b, G)
            R, tail = exact_R(theta, kernel, c, P, b, G)
            R_upper = R + tail
            L = 2 - R_upper
            row = {
                "theta": frac_str(theta),
                "kernel": kernel,
                "window_coefficients_s_monomials": [frac_str(x) for x in c],
                "R_exact_truncated_series": frac_str(R),
                "series_truncation_M": M,
                "tail_upper_bound": frac_str(tail),
                "tail_upper_bound_float": float(tail),
                "lower_bound_exact": frac_str(L),
                "lower_bound_truncated_down": trunc_down(L),
                "int_v2_over_int_v_squared": frac_str(quad(P, c) / sum(bi * ci for bi, ci in zip(b, c)) ** 2),
            }
            control = ""
            if kernel == "zeta":
                lo, hi, backend = wang_enclosure(theta)
                not_above = L <= lo
                close = hi - L <= Fraction(1, 1000)
                ok = not_above and close
                row["control_wang"] = {
                    "c_theta_enclosure_lower": trunc_down(lo, 30),
                    "c_theta_enclosure_upper": trunc_down(hi + Fraction(1, 10 ** 30), 30),
                    "enclosure_backend": backend,
                    "bound_le_lower_end": not_above,
                    "gap_upper_end_minus_bound_float": float(hi - L),
                    "within_1e-3": close,
                    "pass": ok,
                }
                control = f"c(theta) in [{trunc_down(lo, 10)}, ..] gap {float(hi - L):.2e} {'PASS' if ok else 'FAIL'}"
                all_pass &= ok
            else:
                if theta in LANDSCAPE_XIPRIME:
                    land = LANDSCAPE_XIPRIME[theta]
                    ok = Fraction(land) > L
                    row["control_landscape"] = {
                        "landscape_float_value": land,
                        "landscape_minus_bound_float": float(Fraction(land) - L),
                        "landscape_above_bound": ok,
                        "pass": ok,
                    }
                    control = f"landscape {land} - bound = {float(Fraction(land) - L):+.2e} {'PASS' if ok else 'FAIL'}"
                    all_pass &= ok
                if theta == 1:
                    ok = L <= Fraction(LAB_H_STAR)
                    row["control_lab_optimum"] = {
                        "H_star_float": LAB_H_STAR,
                        "bound_le_H_star": ok,
                        "H_star_minus_bound_float": float(Fraction(LAB_H_STAR) - L),
                    }
                    control = f"H* - bound = {float(Fraction(LAB_H_STAR) - L):+.2e} {'PASS' if ok else 'FAIL'}"
                    all_pass &= ok
            rows.append(row)
            print(f"{str(theta):>6}  {kernel:>7}  {', '.join(frac_str(x) for x in c[1:]):>36}  "
                  f"{trunc_down(L):>16}  {control:>40}")

    # control (ii): the published windows at theta = 1
    print()
    published = {}
    for name, c, target in (("quartic", QUARTIC, AF_QUARTIC), ("flat", FLAT, AF_FLAT)):
        R, tail = exact_R(Fraction(1), "xiprime", c, P, b, G)
        L = 2 - R - tail
        ok = L >= target
        published[name] = {
            "window_coefficients_s_monomials": [frac_str(x) for x in c],
            "R_exact_truncated_series": frac_str(R),
            "tail_upper_bound": frac_str(tail),
            "lower_bound_truncated_down": trunc_down(L),
            "published": frac_str(target),
            "bound_ge_published": ok,
            "pass": ok,
        }
        all_pass &= ok
        print(f"control (ii) theta 1, xi', {name:>7}: bound {trunc_down(L)} >= published {float(target)}: "
              f"{'PASS' if ok else 'FAIL'}")

    out = {
        "grade": "hardened: exact rationals for every integral plus a proved upper bound on the "
                 "series tail; no floating point on the load-bearing path. Ball arithmetic is used "
                 "only to enclose Wang's transcendental c(theta) in the zeta control.",
        "functional": "R = [int v^2 + lambda iint F(lambda(s-s')) v v] / (lambda (int v)^2); bound = 2 - R",
        "tail_bound": f"lambda^(2M+3) rho_M int v^2 / (int v)^2 with M = {M}, rho_M = {frac_str(tail_bound(M))}",
        "rigor_backend": rigor.BACKEND,
        "rigor_available_backends": rigor.available_backends(),
        "moment_selfcheck_sympy": checks,
        "rows": rows,
        "published_windows_theta_1": published,
        "all_controls_pass": all_pass,
        "command": ".venv/bin/python hunts/short_interval/enclose_theta.py",
    }
    ARTIFACT.parent.mkdir(exist_ok=True)
    ARTIFACT.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print()
    print(f"wrote {ARTIFACT.relative_to(HERE.parent.parent)}")
    print("ALL CONTROLS PASS" if all_pass else "A CONTROL FAILED")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
