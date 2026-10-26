"""Li coefficients of the rival W_a = zeta(s+a) zeta(s-a), by two routes.

Hunt #150 (`rh_moonshot`), mechanism `li_arithmetic`.  Not a result about RH.

Why this rival.  W_a has a scalar Euler product, log-derivative coefficients
Lambda(m)(m^a + m^{-a}) >= 0 supported on prime powers, and its completion
F_a(s) = xi(s+a) xi(s-a) (`zeta.epstein.shifted_completed`) is entire with
F_a(1-s) = F_a(s).  Its zeros are rho +- a, off the line Re s = 1/2.  So any
step of a Li-positivity argument that uses only "Euler product, nonnegative
prime-power coefficients, functional equation" must fail for W_a, and the
index where lambda_n(W_a) first turns negative is where it fails.

Li coefficients here mean lambda_n(F_a) = n [z^n] log F_a(1/(1-z)), for which
Bombieri and Lagarias's multiset theorem applies (some lambda_n < 0, since the
zeros are off the line).

Route 1, Cauchy.  F_a is sampled on |z| = r with Arb's zeta and Gamma
(python-flint) and the coefficients come from one FFT, through
`li_arith_split.cauchy_log_coefficients`.  The radius must keep the
Apollonius disc |z| <= r free of zeros of F_a with Re s > 1/2.  Those zeros
are rho + a = 3/4 + i gamma (zeta's zeros being on the line below height
3e12, Platt-Trudgian 2021), and |1 - 1/(3/4 + i gamma)|^2 =
1 - (1/2)/(9/16 + gamma^2) > r^2 as soon as gamma^2 > (1/2)/(1 - r^2) - 9/16.
Any r < 0.99875 is admissible by that count (|gamma| > 11.2 at r = 0.998,
true for every zeta zero), but radii that close to 1 are unusable in
practice: the circle then sweeps heights up to 1/(2(1-r)) inside an angle of
order 1 - r, arg F_a turns by thousands of radians there, and the branch
cannot be tracked without millions of nodes (a first attempt at r = 0.998
with 2^17 nodes stopped on the undersampling check).  So the runs use
r = 0.95 and 0.93 and pay n log10(1/r) digits of precision instead; the
winding check re-tests admissibility on the contour.

Route 2, zeros.  Each zeta zero 1/2 + i gamma (gamma > 0) gives the quadruple
{1/2 +- a +- i gamma}, contributing q_n(gamma) = 4 - 2 (R^n + R^{-n}) cos(n psi),
with 1/R e^{i psi} = 1 - 1/(1/2 + a + i gamma).  The first ``n_zeros`` zeta zeros
are summed and the rest replaced by the smooth density theta'(t)/pi, with the
k-independent boundary term that `zeta.li._li_zeros` derives.  This route
reads zeta's zeros (computed by mpmath and cached in `data/zeros_1000.json`)
and never evaluates zeta or Gamma; it can report a negative value.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import mpmath
from mpmath import mp

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
if str(_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_ROOT))

from hunts.rh_moonshot.li_arithmetic import li_arith_split as S  # noqa: E402

A_DEFAULT = "0.25"


def wa_evaluator(a: str = A_DEFAULT):
    """F_a(s) = xi(s+a) xi(s-a) on Arb, xi(s) = s(s-1)/2 pi^{-s/2} Gamma(s/2) zeta(s)."""
    from flint import acb, arb

    def xi(s):
        return s * (s - 1) / 2 * acb(arb.pi()) ** (-s / 2) * (s / 2).gamma() * s.zeta()

    def F(s):
        sh = acb(arb(a))
        return xi(s + sh) * xi(s - sh)

    return F


def radius_admissible(radius: float, a: float = 0.25, gamma1: float = 14.134725141734694) -> bool:
    """True when no zero 1/2 + a + i gamma with gamma >= gamma1 has |w| <= radius."""
    r2 = float(radius) ** 2
    beta = 0.5 + a
    w2 = 1.0 - (2 * beta - 1) / (beta * beta + gamma1 * gamma1)
    return w2 > r2


def wa_lambda_cauchy(n_max: int, radius: str = "0.95", dps: int = 20, n_points: int | None = None) -> dict:
    """lambda_1..lambda_n_max of F_a by the Cauchy route (see module docstring)."""
    if not radius_admissible(float(radius)):
        raise ValueError("radius not admissible for W_a")
    wd = S.work_digits(n_max, dps, radius)
    N = n_points or S.node_count(n_max, wd, radius)
    res = S.cauchy_log_coefficients(wa_evaluator(), n_max, radius, wd, N)
    res.update(work_digits=wd, n_points=N, radius=radius)
    return res


def _quad_term(n: int, gamma, a):
    """q_n(gamma) = 4 - 2 (R^n + R^{-n}) cos(n psi) for the quadruple of 1/2 + i gamma."""
    s0 = mp.mpc(mp.mpf(1) / 2 + a, gamma)
    w = 1 - 1 / s0  # |w| < 1: the zero to the right of the line
    lw = mp.log(w)
    # w^n + conj(w)^{-n} summed with its conjugate pair gives the real form
    return 4 - 2 * (mp.exp(n * mp.re(lw)) + mp.exp(-n * mp.re(lw))) * mp.cos(n * mp.im(lw))


def _rs_theta(t):
    return mp.im(mp.loggamma(mp.mpc(mp.mpf(1) / 4, t / 2))) - t / 2 * mp.log(mp.pi)


def _density(t):
    return (mp.re(mp.digamma(mp.mpc(mp.mpf(1) / 4, t / 2))) / 2 - mp.log(mp.pi) / 2) / mp.pi


def wa_lambda_zeros(n_values, a: str = A_DEFAULT, n_zeros: int = 1000, dps: int = 20) -> list:
    """lambda_n(F_a) from zeta's zeros: head over n_zeros quadruples + density tail.

    Mirrors `zeta.li._li_zeros` with the pair term replaced by the quadruple
    term q_n.  The truncation error is the S(t)-weighted integral of q_n'
    above T, of size about n/T, which at n = 10^4 and T = 1420 is a few units.
    """
    from zeta.zeros import first_n_zeros

    gammas = first_n_zeros(int(n_zeros), dps=30)
    out = []
    with mp.workdps(dps + 10):
        av = mp.mpf(a)
        target = mp.pi * (mp.mpf(n_zeros) - mp.mpf(1) / 2)
        T = mp.findroot(lambda t: _rs_theta(t) - target, gammas[-1] + 1)
        S_T = mp.mpf(n_zeros) - _rs_theta(T) / mp.pi - 1
        for n in n_values:
            n = int(n)
            head = mp.fsum(_quad_term(n, g, av) for g in gammas)
            tail = mp.quad(lambda t: _quad_term(n, t, av) * _density(t), [T, 2 * T, 10 * T, 100 * T, mp.inf])
            out.append(head + tail - _quad_term(n, T, av) * S_T)
    with mp.workdps(dps):
        return [+v for v in out]


def wa_archimedean(n: int, a: str = A_DEFAULT, dps: int = 30) -> mpmath.mpf:
    """A_W(n) = A^{(a)}(n) + A^{(-a)}(n), A^{(c)}(n) = n[z^n] log((s+c) pi^{-(s+c)/2} Gamma((s+c)/2)).

    Closed form (derived like the zeta case, b = (1+c)/2):
    A^{(c)}(n) = 1 - (c/(1+c))^n - (n/2) log pi + (n/2) psi(b)
                 + sum_{m>=0} [ (1 - 1/(2(m+b)))^n - 1 + n/(2(m+b)) ],
    the sum taken directly to M = 4n + 64 and by a Hurwitz-zeta series beyond.
    The arithmetic part is then T_W(n) = lambda_n(F_a) - A_W(n), whose factor
    is (s+a-1) zeta(s+a) (s-a-1) zeta(s-a).
    """
    n = int(n)
    work = dps + 20
    total = mp.mpf(0)
    with mp.workdps(work):
        for c in (mp.mpf(a), -mp.mpf(a)):
            b = (1 + c) / 2
            M = 4 * n + 64
            head = mp.fsum(
                mp.power(1 - 1 / (2 * (m + b)), n) - 1 + n / (2 * (m + b)) for m in range(0, M + 1)
            )
            tail = mp.mpf(0)
            tol = mp.mpf(10) ** (-work)
            for j in range(2, n + 1):
                term = (-1) ** j * mp.binomial(n, j) * mp.power(2, -j) * mp.zeta(j, M + 1 + b)
                tail += term
                if j > 3 and abs(term) < tol:
                    break
            total += 1 - mp.power(c / (1 + c), n) - n * mp.log(mp.pi) / 2 + n * mp.digamma(b) / 2 + head + tail
    with mp.workdps(dps):
        return +total


def wa_arithmetic_cauchy(n_max: int, radius: str = "0.5", dps: int = 30, a: str = A_DEFAULT) -> list:
    """T_W(n) directly: Cauchy on (s+a-1) zeta(s+a) (s-a-1) zeta(s-a) (small n check)."""
    from flint import acb, arb

    def g(s):
        sh = acb(arb(a))
        return (s + sh - 1) * (s + sh).zeta() * (s - sh - 1) * (s - sh).zeta()

    wd = S.work_digits(n_max, dps, radius)
    N = S.node_count(n_max, wd, radius)
    return S.cauchy_log_coefficients(g, n_max, radius, wd, N)["coefficients"]
