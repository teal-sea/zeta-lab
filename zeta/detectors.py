"""Detector strength: how large a violation of RH would have to be to be seen.

Every RH-equivalent criterion in this laboratory consumes the *zero multiset*.
That makes a question available that the criteria themselves do not answer: if
RH were false, would this criterion notice, and at what cost?  A criterion that
cannot see a violation is not thereby wrong, it is simply blind, and knowing
where each one goes blind is a measurement, not an opinion.

The instrument is a **synthetic lesion**: a quadruple of zeros placed at

    rho = 1/2 +/- delta +/- iT,    delta > 0,

which is the shape any genuine counterexample must take, because the zeros of a
function with real coefficients satisfying ``F(s) = F(1-s)`` come in the quad
``rho, 1-rho, conj(rho), 1-conj(rho)``.  Setting ``delta = 0`` collapses the quad
onto the critical line.  Each function below returns that quad's *contribution*
to one criterion, so it can be added to the on-line background and the response
curve read off.

This is legitimate rather than a fiction: Li's criterion in the
Bombieri--Lagarias multiset form, the explicit formula and the Weil functional
are all statements quantified over a multiset of zeros, so injecting a lesion
asks exactly the question the theorems answer.  No claim is made that any
function *has* such zeros.  The real calibration point is the
Davenport--Heilbronn function, whose genuine off-line zero lives at
``delta ~ 0.3085``, ``T ~ 85.70`` (:mod:`zeta.epstein`); the tests pin these
functions against it.

The headline consequence, derived in :func:`weil_gaussian_deepest_dip`, is that
the Gaussian family's ability to see a lesion dies like ``exp(-pi*T/(2*delta))``.
A zero off the line by ``delta = 0.01`` at the height of the first zero produces
a deepest possible Weil dip near ``1e-964``.  Nothing here bears on whether RH is
true; it bounds what a computation could observe if it were not.
"""

import mpmath
from mpmath import mp

from .core import DPS_DEFAULT

__all__ = [
    "lesion_li_lambda",
    "lesion_weil_gaussian",
    "lesion_weil_fejer",
    "weil_gaussian_deepest_dip",
    "li_lesion_growth_rate",
    "li_lesion_doubling_n",
]


def _lesion_zeros(delta, T):
    """The four zeros ``1/2 +/- delta +/- iT`` of a lesion, as ``mpc``."""

    half = mp.mpf(1) / 2
    d = mp.mpf(delta)
    t = mp.mpf(T)
    return (
        mp.mpc(half + d, t),
        mp.mpc(half + d, -t),
        mp.mpc(half - d, t),
        mp.mpc(half - d, -t),
    )


def lesion_li_lambda(n: int, delta: float, T: float, dps: int = DPS_DEFAULT) -> mpmath.mpf:
    """
    Computes the contribution to Li's lambda_n from a synthetic zero quad
    at 1/2 +/- delta +/- iT.
    The quad is:
    rho1 = 1/2 + delta + iT
    rho2 = 1/2 + delta - iT
    rho3 = 1/2 - delta + iT
    rho4 = 1/2 - delta - iT

    Contribution = sum_j [1 - (1 - 1/rho_j)^n]
    """
    with mp.workdps(dps + 10):
        val = sum(1 - mp.power(1 - 1 / rho, n) for rho in _lesion_zeros(delta, T))
        return mp.re(val)


def lesion_weil_gaussian(a: float, delta: float, T: float, dps: int = DPS_DEFAULT) -> mpmath.mpf:
    """
    Computes the contribution to Weil's W(h) for the Gaussian family h(r) = exp(-a r^2)
    from a synthetic zero quad at 1/2 +/- delta +/- iT.
    gamma values: +/- T +/- i*delta
    Contribution = 4 * exp(-a(T^2 - delta^2)) * cos(2aT*delta)
    """
    with mp.workdps(dps + 10):
        a_mp = mp.mpf(a)
        d = mp.mpf(delta)
        t = mp.mpf(T)

        val = 4 * mp.exp(-a_mp * (t**2 - d**2)) * mp.cos(2 * a_mp * t * d)
        return mp.re(val)


def lesion_weil_fejer(b: float, delta: float, T: float, dps: int = DPS_DEFAULT) -> mpmath.mpf:
    """
    Computes the contribution to Weil's W(h) for the Fejer family h(r) = (sin(b r) / (b r))^2
    from a synthetic zero quad at 1/2 +/- delta +/- iT.
    gamma = T - i*delta and gamma = T + i*delta (each counted twice for +/- T)
    """
    with mp.workdps(dps + 10):
        b_mp = mp.mpf(b)
        d = mp.mpf(delta)
        t = mp.mpf(T)

        def h(r):
            if r == 0:
                return mp.mpf(1)
            return mp.power(mp.sin(b_mp * r) / (b_mp * r), 2)

        r1 = mp.mpc(t, -d)
        r2 = mp.mpc(t, d)
        val = 2 * h(r1) + 2 * h(r2)
        return mp.re(val)


def weil_gaussian_deepest_dip(delta: float, T: float, dps: int = DPS_DEFAULT):
    """The most negative Weil signal the Gaussian family can extract from a lesion.

    The lesion contributes ``4 exp(-a(T^2 - delta^2)) cos(2 a T delta)``.  The
    cosine is what allows a *negative* contribution at all, that is the whole
    falsification signal, and it first turns negative at ``2 a T delta = pi/2``
    and is deepest at ``2 a T delta = pi``.  Substituting the deepest case:

        a* = pi / (2 T delta),
        dip = -4 exp(-pi (T^2 - delta^2) / (2 T delta)).

    Returns ``(a_star, dip)``.  For ``T >> delta`` the exponent is close to
    ``-pi T / (2 delta)``, so detector power dies exponentially in ``T/delta``:
    halving ``delta`` squares the required precision.  Increasing ``a`` past
    ``a*`` does not help; the cosine has already been driven through its
    minimum, and the prefactor keeps shrinking.

    This is a statement about the Gaussian family only.  It is an upper bound on
    what *this* family can see, not a proof that no admissible test function
    does better.
    """

    with mp.workdps(dps + 10):
        d = mp.mpf(delta)
        t = mp.mpf(T)
        if d <= 0 or t <= 0:
            raise ValueError("delta and T must be positive for a lesion off the line")
        a_star = mp.pi / (2 * t * d)
        dip = -4 * mp.exp(-mp.pi * (t**2 - d**2) / (2 * t * d))
        return a_star, dip


def li_lesion_growth_rate(delta: float, T: float, dps: int = DPS_DEFAULT) -> mpmath.mpf:
    """``max_j |1 - 1/rho_j|`` over the lesion quad: Li's exponential growth rate.

    ``lambda_n`` sums ``1 - (1 - 1/rho)^n``, so a zero contributes a term growing
    like ``|1 - 1/rho|^n``.  Only quad members with ``Re(rho) < 1/2`` push that
    modulus above 1, which is why an off-line zero must eventually drive some
    ``lambda_n`` negative, and how slowly it does so is this number.
    """

    with mp.workdps(dps + 10):
        return max(abs(1 - 1 / rho) for rho in _lesion_zeros(delta, T))


def li_lesion_doubling_n(delta: float, T: float, dps: int = DPS_DEFAULT) -> mpmath.mpf:
    """The ``n`` at which the lesion's Li signal doubles: ``log 2 / log(rate)``.

    Compare this against the ``(n/2) log n`` background growth of ``lambda_n``
    for zeta to see whether the signal is visible at reachable ``n``.  For the
    Davenport--Heilbronn zero the rate is ``1.000042``, giving a doubling scale
    near ``1.65e4``, far beyond any computed range, which is precisely why
    ``lambda_n >= 0`` is observed for a function that violates RH.
    """

    with mp.workdps(dps + 10):
        rate = li_lesion_growth_rate(delta, T, dps=dps)
        if rate <= 1:
            return mp.inf
        return mp.log(2) / mp.log(rate)
