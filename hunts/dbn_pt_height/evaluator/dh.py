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
