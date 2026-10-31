"""Independent routes to H_t(x + iy), for checking ``effective.py``.

Two routes, neither sharing code with the evaluator:

* ``Ht_phi``: ``zeta.heatflow.H_t``, the defining integral
  H_t(z) = int_0^inf e^{t u^2} Phi(u) cos(z u) du by a composite Gauss-Legendre
  rule on Phi (or by ``mpmath.quadgl`` with ``quad="adaptive"``).  It loses
  about 0.17 digits per unit of x, so ``zeta.heatflow.recommended_dps`` sets the
  working precision.
* ``Ht_heat_kernel``: the heat-kernel representation (htz) of the paper,
  H_t(z) = int_R (1/8) xi((1 + iz)/2 + sqrt(t) v) e^{-v^2} / sqrt(pi) dv,
  integrated with ``mpmath.quad`` and mpmath's own zeta and gamma.  No
  cancellation is involved (xi carries the e^{-pi x/8} decay in its exponent), so
  modest precision suffices; the paper remarks (line 500) that it is fast and
  accurate for moderate x.

Both are floating-point routes at a requested precision: agreement between them
and with the evaluator is a measurement, not an enclosure.

A third function, ``formula_mpmath``, is not a route to H_t: it re-evaluates
the paper's formulas (f_t, C_t/B_t and the error quantities) in mpmath, written
from the TeX rather than from ``effective.py``, so that an implementation slip
too small to break any containment (C_0 conjugated, kappa dropped) still shows.
"""

from __future__ import annotations

from typing import Any

from mpmath import mp, mpc, mpf


def Ht_phi(x: Any, y: Any, t: Any, digits: int = 20, quad: str = "cached") -> Any:
    """zeta.heatflow.H_t(x + iy, t) at the precision recommended for ``digits``."""
    from zeta import heatflow as hf

    dps = hf.recommended_dps(float(x) + 1.0, digits=digits)
    with mp.workdps(dps):
        z = mp.mpc(mp.mpf(str(x)), mp.mpf(str(y)))
        return hf.H_t(z, mp.mpf(str(t)), dps=dps, quad=quad)


def _xi(s: Any) -> Any:
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Ht_heat_kernel(x: Any, y: Any, t: Any, dps: int = 30, V: float = 14.0) -> Any:
    """H_t(x + iy) from (htz) by mpmath.quad over [-V, V] (Gaussian tail beyond)."""
    with mp.workdps(dps + 10):
        x = mp.mpf(str(x))
        y = mp.mpf(str(y))
        t = mp.mpf(str(t))
        s0 = mp.mpc(1 - y, x) / 2
        if t == 0:
            return _xi(s0) / 8
        rt = mp.sqrt(t)

        def f(v: Any) -> Any:
            return _xi(s0 + rt * v) * mp.exp(-v * v)

        pts = [mp.mpf(k) for k in range(-int(V), int(V) + 1)]
        val = mp.quad(f, pts)
        return +(val / (8 * mp.sqrt(mp.pi)))


def formula_mpmath(x: Any, y: Any, t: Any, dps: int = 40) -> dict[str, Any]:
    """f_t, C_t/B_t, e_A, e_B, e_C, e_{C,0} at x + iy, from the TeX of arXiv:1904.12438v2.

    Sources (debruijn.tex): (M-def), (logM), (alpha-form), (Mt-def), lines 173-197;
    (ft-def)-(N-def-main), lines 229-234, using the printed form
    gamma sum n^y b_n n^{-(conj(s_*) + kappa)} for the second sum; Corollary 6.4,
    lines 926-947, for C_t, E_A, E_B, E_C, divided by |B_t| = |M_t(s_+)| as at
    lines 960-974; (a-def)-(U-def), lines 687-690; (C0-def), line 696;
    (eps-def), line 625, and (epsp-def), line 751, with T = x/2 for both s_+ and
    s_- (the conjugate-symmetric reading of line 924).  Floating point at
    ``dps`` digits.  Refuses within 1e-8 of the removable points p = +-1/2, which
    this direct formula does not handle.
    """
    with mp.workdps(dps):
        x, y, t = mpf(str(x)), mpf(str(y)), mpf(str(t))
        I = mpc(0, 1)
        pi = mp.pi

        def alpha(s):
            return 1 / (2 * s) + 1 / (s - 1) + mp.log(s / (2 * pi)) / 2

        def logM0(s):
            return (mp.log(s) + mp.log(s - 1) - (s / 2) * mp.log(pi) + mp.log(mp.sqrt(2 * pi) / 16)
                    + (s / 2 - mpf(1) / 2) * mp.log(s / 2) - s / 2)

        def logMt(s):
            return (t / 4) * alpha(s) ** 2 + logM0(s)

        sp = mpc(1 + y, -x) / 2
        sm = mpc(1 - y, x) / 2
        gamma = mp.exp(logMt(sm) - logMt(sp))
        s_star = sp + (t / 2) * alpha(sp)
        kappa = (t / 2) * (alpha(sm) - alpha(mpc(1 + y, x) / 2))
        N = int(mp.floor(mp.sqrt(x / (4 * pi) + t / 16)))
        T = x / 2
        sig_B = (1 + y) / 2 + (t / 2) * mp.re(alpha(sp))
        sig_A = (1 - y) / 2 + (t / 2) * mp.re(alpha(sm))
        S1 = mpc(0)
        S2 = mpc(0)
        eA = mpf(0)
        eB = mpf(0)
        for n in range(1, N + 1):
            L = mp.log(n)
            bn = mp.exp((t / 4) * L * L)
            S1 += bn * mp.exp(-s_star * L)
            S2 += mp.exp(y * L) * bn * mp.exp(-(mp.conj(s_star) + kappa) * L)
            eps_p = mp.expm1(((t * t / 8) * abs(alpha(sp) - L) ** 2 + t / 4 + mpf(1) / 6) / (T - mpf("3.33")))
            eps_m = mp.expm1(((t * t / 8) * abs(alpha(sm) - L) ** 2 + t / 4 + mpf(1) / 6) / (T - mpf("3.33")))
            eB += bn * mp.exp(-sig_B * L) * eps_p
            eA += bn * mp.exp(-sig_A * L) * eps_m
        eA *= abs(gamma)
        f = S1 + gamma * S2
        Tp = x / 2 + pi * t / 8
        a = mp.sqrt(Tp / (2 * pi))
        if int(mp.floor(a)) != N:
            raise ValueError("(N-def) and (N-def-main) disagree")
        p = 1 - 2 * (a - N)
        if min(abs(p - mpf(1) / 2), abs(p + mpf(1) / 2)) < mpf("1e-8"):
            raise ValueError("p is too close to a removable point of C_0")
        U = mp.exp(-I * (Tp / 2 * mp.log(Tp / (2 * pi)) - Tp / 2 - pi / 8))
        C0 = (mp.exp(pi * I * (p * p / 2 + mpf(3) / 8)) - I * mp.sqrt(2) * mp.cos(pi * p / 2)) / (2 * mp.cos(pi * p))
        M0iT = mp.exp(logM0(I * Tp))
        Bt = mp.exp(logMt(sp))
        C = 2 * mp.exp(-pi * I * y / 8) * (-1) ** N * mp.exp(t * pi ** 2 / 64) * mp.re(M0iT * C0 * U * mp.exp(pi * I / 8))

        def eps_tilde(sigma):
            return (mpf("0.397") * mpf(9) ** sigma / (a - mpf("0.865")) + mpf(5) / (3 * (T - 6))) * mp.exp(mpf("3.49") / (T - 4))

        ratio = mp.exp(t * pi ** 2 / 64) * abs(M0iT) / abs(Bt)
        et = eps_tilde((1 - y) / 2) + eps_tilde((1 + y) / 2)
        return {"N": N, "f": f, "CB": C / Bt, "e_A": eA, "e_B": eB, "e_C": ratio * et, "e_C0": ratio * (1 + et), "p": p}
