"""Davenport-Heilbronn analogue of the Polymath 15 main terms, for the refusal gate.

Design and status: ``DH.md`` in this directory.  This module is the first code
for the control that gates every sweep (``EVALUATOR.md``, "Open"): before the
pipeline is trusted on zeta it must refuse the Davenport-Heilbronn function
below that function's de Bruijn-Newman constant.  Nothing here carries an
error theorem yet; every comparison with H_t is a measurement.

Conventions, all in the **wide frame** of Polymath 15 (s = (1 + iz)/2):

* f(s) = sum_n a_n n^{-s}, a_n = 1, kappa, -kappa, -1, 0 for n = 1..5 mod 5;
* F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s), and kappa is the real number for
  which F(s) = F(1 - s); it is derived here by one linear solve (``kappa``),
  never typed in;
* H_0(z) = F((1 + iz)/2), real on the real axis, and H_t(z) its backward heat
  flow, H_t(z) = int F((1 + iz)/2 + sqrt(t) v) e^{-v^2} / sqrt(pi) dv, the
  representation ``large_x_oracles.py`` uses for zeta.  A constant factor in
  H_0 changes no zero, so the normalisation of hunt #61's Phi_DH is not matched.
  Hunt #61 (``hunts/lambda_dh_bounds``) works in the narrow frame
  s = 1/2 + i z_n, where z = 2 z_n and t = 4 t_n (its ``FRAME.md``).

The main terms mirror (ft-def) of arXiv:1904.12438v2 with zeta's Gamma factor
replaced by DH's.  With s_- = (1 - y + ix)/2, s_+ = (1 + y - ix)/2 = 1 - s_-,
M(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2), alpha = M'/M,
M_t(s) = exp((t/4) alpha(s)^2) M(s) and b_n = exp((t/4) log^2 n):

    A_t + B_t = M_t(s_-) sum_{n<=N} a_n b_n n^{-(s_- + t alpha(s_-)/2)}
              + M_t(s_+) sum_{n<=N} a_n b_n n^{-(s_+ + t alpha(s_+)/2)},

the termwise Gaussian average of the approximate functional equation
F(s) ~ M(s) sum a_n n^{-s} + M(1-s) sum a_n n^{s-1}, which holds because F is
self-dual (F(s) = F(1-s) with the same real a_n).  The cutoff defaults to the
t = 0 balance point N = floor(sqrt(5x/(4 pi))); the t-shift of Polymath's
(N-def-main) is not re-derived for DH.  There is no Riemann-Siegel correction
C_t and no error bound: those are the next steps in ``DH.md``.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import acb, arb, ctx
from mpmath import mp

from effective import to_arb, workprec

# --------------------------------------------------------------------------- #
#  The function: kappa, coefficients, completed F (mpmath, the oracle side)
# --------------------------------------------------------------------------- #

_U = (0, 1, 0, 0, -1)    # a_n = U[n % 5] + kappa * W[n % 5]
_W = (0, 0, 1, -1, 0)


def _M_mp(s):
    return mp.exp(-(s + 1) / 2 * mp.log(mp.pi / 5) + mp.loggamma((s + 1) / 2))


def _F_parts_mp(s):
    """F = P + kappa Q at s: F is linear in kappa."""
    m = _M_mp(s)
    return m * mp.dirichlet(s, list(_U)), m * mp.dirichlet(s, list(_W))


def kappa(dps: int = 40, s0: tuple[str, str] = ("0.3", "7.1")):
    """The real kappa with F(s) = F(1 - s), from one linear solve at s0.

    F(s) - F(1-s) = (P(s) - P(1-s)) + kappa (Q(s) - Q(1-s)); returns the
    complex solution, whose imaginary part the tests require to vanish."""
    with mp.workdps(dps + 10):
        s = mp.mpc(mp.mpf(s0[0]), mp.mpf(s0[1]))
        p1, q1 = _F_parts_mp(s)
        p2, q2 = _F_parts_mp(1 - s)
        k = -(p1 - p2) / (q1 - q2)
    with mp.workdps(dps):
        return +k


def coefficients(dps: int = 40) -> list:
    """a_0..a_4 for n mod 5 (a_0 = 0), with kappa derived."""
    k = mp.re(kappa(dps))
    return [mp.mpf(_U[j]) + k * _W[j] for j in range(5)]


def F_mp(s, dps: int = 40):
    """The completed DH function F(s), mpmath (Hurwitz route via mp.dirichlet)."""
    with mp.workdps(dps + 10):
        a = coefficients(dps + 10)
        return _M_mp(mp.mpc(s)) * mp.dirichlet(mp.mpc(s), a)


def H_oracle(x: Any, y: Any, t: Any, n_nodes: int = 80, dps: int = 30):
    """H_t(x + iy) in the wide frame, mpmath.

    t = 0: F((1 - y + ix)/2) directly.  t > 0: Gauss-Hermite quadrature of the
    heat-kernel representation with ``n_nodes`` nodes (floating point; callers
    compare two node counts to see the quadrature error)."""
    with mp.workdps(dps + 10):
        x, y, t = mp.mpf(str(x)), mp.mpf(str(y)), mp.mpf(str(t))
        a = coefficients(dps + 10)
        s0 = mp.mpc(1 - y, x) / 2
        if t == 0:
            v = _M_mp(s0) * mp.dirichlet(s0, a)
        else:
            nodes, weights = mp.gauss_quadrature(n_nodes, "hermite")
            rt = mp.sqrt(t)
            v = mp.fsum(w * _M_mp(s0 + rt * u) * mp.dirichlet(s0 + rt * u, a) for u, w in zip(nodes, weights))
            v = v / mp.sqrt(mp.pi)
    with mp.workdps(dps):
        return +v


# --------------------------------------------------------------------------- #
#  The main terms (python-flint balls: enclosures of the formula, not of H_t)
# --------------------------------------------------------------------------- #

def N_balance(x: Any) -> int:
    """floor(sqrt(5 x / (4 pi))), the t = 0 balance point of the two sums."""
    with workprec(128):
        v = (5 * to_arb(x) / (4 * arb.pi())).sqrt()
        try:
            return int(v.floor().unique_fmpz())
        except Exception as exc:  # pragma: no cover - ball straddles an integer
            raise ValueError(f"N is not determined by the input ball: {v}") from exc


def _log_M(s: acb) -> acb:
    return -((s + 1) / 2) * (arb.pi() / 5).log() + ((s + 1) / 2).lgamma()


def _alpha(s: acb) -> acb:
    return -(arb.pi() / 5).log() / 2 + ((s + 1) / 2).digamma() / 2


def main_terms(x: Any, y: Any, t: Any, N: int | None = None, kappa_value: Any = None,
               prec: int = 192) -> dict[str, Any]:
    """A_t + B_t for DH at x + iy (wide frame), as balls of the formula.

    Returns A (the s_- term), B (the s_+ term), their sum H_main, N and the
    ratio |H_main| / |B| that sizes the value against its larger part.
    ``kappa_value`` overrides the derived kappa (used only by lesion tests)."""
    with workprec(prec):
        x, y, t = to_arb(x), to_arb(y), to_arb(t)
        if N is None:
            N = N_balance(x)
        if kappa_value is None:
            with mp.workdps(60):
                kappa_value = mp.nstr(mp.re(kappa(60)), 55)
        k = to_arb(kappa_value)
        a = [arb(_U[j]) + k * _W[j] for j in range(5)]
        out = {}
        for label, s in (("A", acb(1 - y, x) / 2), ("B", acb(1 + y, -x) / 2)):
            al = _alpha(s)
            s_star = s + (t / 2) * al
            tot = acb(0)
            for n in range(1, N + 1):
                if n % 5 == 0:
                    continue
                L = arb(n).log()
                tot += a[n % 5] * ((t / 4) * L * L - s_star * L).exp()
            out[label] = ((t / 4) * al * al + _log_M(s)).exp() * tot
        H = out["A"] + out["B"]
        return {"A": out["A"], "B": out["B"], "H_main": H, "N": N,
                "ratio_to_B": abs(H) / abs(out["B"]), "prec": ctx.prec}


# --------------------------------------------------------------------------- #
#  The smoothed split: exact A-like and B-like parts (DH.md, step 3)
# --------------------------------------------------------------------------- #
#
# With Theta(x) = sum_n n a_n exp(-pi n^2 x / 5) and Theta(1/x) = x^{3/2} Theta(x)
# (equivalent to F(s) = F(1 - s)), rotating F(s) = int_0^inf x^{(s+1)/2 - 1}
# Theta(x) dx onto the ray arg x = phi and splitting it at |x| = 1 gives, for any
# |phi| < pi/2, the exact identity
#
#     F(s) = P1(s) + P2(s),  P1 = sum_n n a_n y_n^{-w1} Gamma(w1, y_n e^{+i phi}),
#                            P2 = sum_n n a_n y_n^{-w2} Gamma(w2, y_n e^{-i phi}),
#
# y_n = pi n^2 / 5, w1 = (s+1)/2, w2 = (2-s)/2: a smoothed approximate functional
# equation in the sense of Rubinstein, with the split point moved off the real
# axis so that, for phi near pi/2, no term is much larger than F itself.  For
# n << N the n-th term of P1 is M(s) a_n n^{-s} times Gamma(w1, y_n e^{i phi}) /
# Gamma(w1), which tends to 1: P1 is the smoothed A, P2 the smoothed B, and
# A + B - (P1 + P2) is the DH correction C (no closed form; see DH.md).


def kappa_ball() -> arb:
    """kappa as a ball, from the closed form (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1).

    The closed form is checked against the linear solve ``kappa`` in the tests;
    the ball is what every enclosure below uses."""
    r5 = arb(5).sqrt()
    return ((10 - 2 * r5).sqrt() - 2) / (r5 - 1)


def _theta_coeffs(n_max: int, k: arb) -> list[arb]:
    U, W = _U, _W
    return [arb(0)] + [arb(n) * (arb(U[n % 5]) + k * W[n % 5]) for n in range(1, n_max + 1)]


def _split_tail(w: acb, phi: arb, K: int) -> arb:
    """Upper bound for sum_{n > K} n |a_n| |y_n^{-w} Gamma(w, y_n e^{+-i phi})|.

    Each term is |int over the ray| <= e^{-|Im w| phi} int_1^inf r^{Re w - 1}
    e^{-y_n r cos phi} dr, and with alpha = max(Re w - 1, 0), b = y_n cos phi:
    int_1^inf r^alpha e^{-b r} dr <= e^{-b} (1 + alpha/b)^{ceil alpha + 1} / b
    is replaced by the cruder but simpler e^{-b/2} (2/b)^{alpha + 1} Gamma(alpha + 1)
    (r^alpha e^{-b r / 2} <= (2 alpha / (e b))^alpha, then integrate e^{-b r/2}).
    |a_n| <= 1.  The n-sum is dominated geometrically from n = K + 1."""
    c = arb.pi() * phi.cos() / 5
    alpha = max(float((w.real - 1).upper()), 0.0) + 1e-9
    al = arb(alpha)
    n1 = K + 1
    b1 = c * n1 * n1
    # r^alpha e^{-b r} <= (alpha/(e b/2))^alpha e^{-b r/2} for r >= 1
    head = ((al / (arb(1).exp() * b1 / 2)) ** al if alpha > 1e-6 else arb(1))
    term = head * (-b1 / 2).exp() * 2 / b1          # int_1^inf e^{-b r/2} dr <= 2 e^{-b/2} / b
    ratio = (-c * (2 * n1 + 1) / 2).exp()           # consecutive-term ratio bound (b grows with n)
    imw = abs(w.imag).lower()
    return (n1 * term / (1 - ratio) * (-arb(imw) * phi).exp()).upper()


def F_split(s: Any, prec: int = 320, theta: Any = "0.02", K: int | None = None) -> tuple[acb, acb]:
    """(P1, P2) at s, each a ball including its n-truncation tail; P1 + P2 = F(s).

    ``theta`` is pi/2 - phi; with Im s > 0 the terms are of size
    e^{-(Im s/2) phi} against |F| ~ e^{-pi Im s / 4}, a loss of e^{Im s theta / 2},
    which ``prec`` must absorb."""
    with workprec(prec):
        s = s if isinstance(s, acb) else acb(s)
        phi = arb.pi() / 2 - to_arb(theta)
        k = kappa_ball()
        c = arb.pi() * phi.cos() / 5
        if K is None:
            K = int(math.sqrt(float(((float(abs(s.imag).upper()) * float(phi.mid()) / 2 + 60 * math.log(2) * prec / 64)) / c.mid()))) + 2
        coef = _theta_coeffs(K, k)
        w1 = (s + 1) / 2
        w2 = (2 - s) / 2
        e_plus = acb(phi.cos(), phi.sin())
        e_minus = acb(phi.cos(), -phi.sin())
        P1 = acb(0)
        P2 = acb(0)
        for n in range(1, K + 1):
            if n % 5 == 0:
                continue
            y = arb.pi() * n * n / 5
            P1 += coef[n] * acb(y).pow(-w1) * (acb(y) * e_plus).gamma_upper(w1)  # Gamma(w1, z): z is self
            P2 += coef[n] * acb(y).pow(-w2) * (acb(y) * e_minus).gamma_upper(w2)
        t1, t2 = _split_tail(w1, phi, K), _split_tail(w2, phi, K)
        return P1 + acb(arb(0, t1), arb(0, t1)), P2 + acb(arb(0, t2), arb(0, t2))



# --------------------------------------------------------------------------- #
#  H_t for t > 0, in balls: hunt #61's instrument, reused (read-only)
# --------------------------------------------------------------------------- #
#
# A Gaussian average of F_split over the real shift v, done with Arb's rigorous
# integrator, was tried on 2026-10-26 and did not finish one point in ten
# minutes (RUNS.md, E6).  Hunt #61's ``instrument.H_ball`` encloses the same
# function through H_t(z) = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du in about
# 0.07 s.  Its normalisation equals this module's exactly in the narrow frame,
# H_wide(z, t) = H_61(z/2, t/4); the tests check it against F_split at t = 0
# and against the Gauss-Hermite oracle at t > 0.

_LDB = Path(__file__).resolve().parents[2] / "lambda_dh_bounds"


def _instrument():
    if str(_LDB) not in sys.path:
        sys.path.insert(0, str(_LDB))
    import instrument  # noqa: PLC0415 - hunt #61's module, read-only

    return instrument


def H_ball(x: Any, y: Any, t: Any, prec: int = 320) -> acb:
    """An enclosure of H_t(x + iy) in the wide frame, by hunt #61's instrument.

    Inputs are read as exact rationals; the call is H_61((x + iy)/2, t/4)."""
    I = _instrument()
    x, y, t = Fraction(str(x)), Fraction(str(y)), Fraction(str(t))
    return I.H_ball((x / 2, y / 2), t / 4, prec)


def Hprime_ball(x: Any, y: Any, t: Any, prec: int = 320) -> acb:
    """An enclosure of dH_t/dz at x + iy (wide frame): (1/2) H_61'(z/2, t/4)."""
    I = _instrument()
    x, y, t = Fraction(str(x)), Fraction(str(y)), Fraction(str(t))
    with workprec(prec):
        return I.Hprime_ball((x / 2, y / 2), t / 4, prec) / 2


def split_prec(x: Any) -> int:
    """Working precision for F_split at height x: 160 bits plus pi x / (8 log 2),
    the bits lost to the cancellation between terms of size about 1 and
    |F| ~ e^{-pi x / 8} that the smoothed parts still carry at theta = 0.02
    (measured: 320 bits lost every digit at x = 1000.7, 640 sufficed)."""
    return 160 + int(math.ceil(float(Fraction(str(x))) * math.pi / (8 * math.log(2))))


def H_split_t0(x: Any, y: Any, prec: int | None = None, theta: Any = "0.02") -> dict[str, acb]:
    """F_split at s = (1 - y + ix)/2: the t = 0 smoothed A (P1), B (P2) and H."""
    if prec is None:
        prec = split_prec(x)
    with workprec(prec):
        s = acb(1 - to_arb(y), to_arb(x)) / 2
        P1, P2 = F_split(s, prec=prec, theta=theta)
        return {"P1": P1, "P2": P2, "H": P1 + P2}


def correction(x: Any, y: Any, t: Any, prec: int | None = None, theta: Any = "0.02") -> dict[str, Any]:
    """The DH correction C = A + B - H at x + iy, and how it splits.

    A, B: the sharp main terms (``main_terms``).  H: F_split at t = 0 (an exact
    identity, so C is enclosure-carrying), hunt #61's H_ball at t > 0 (also an
    enclosure).  At t = 0 the smoothed parts P1, P2 are returned too, so that
    C = (A - P1) + (B - P2) shows which side of the cutoff carries it.  Ratios
    are to |B|."""
    if prec is None:
        prec = split_prec(x)
    m = main_terms(x, y, t, prec=prec)
    with workprec(prec):
        out: dict[str, Any] = {"N": m["N"], "A": m["A"], "B": m["B"]}
        if Fraction(str(t)) == 0:
            sp = H_split_t0(x, y, prec=prec, theta=theta)
            H = sp["H"]
            out.update(P1=sp["P1"], P2=sp["P2"])
        else:
            H = H_ball(x, y, t, prec=prec)
        C = m["A"] + m["B"] - H
        aB = abs(m["B"])
        out.update(H=H, C=C, C_over_B=abs(C) / aB, ABC_over_B=abs(m["A"] + m["B"] - C) / aB,
                   AB_over_B=abs(m["A"] + m["B"]) / aB)
        return out
