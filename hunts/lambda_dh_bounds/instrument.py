"""Ball-arithmetic instrument for the lambda_dh_bounds hunt.

Every public function returns an Arb ball (python-flint ``arb``/``acb``) that
encloses the named quantity, with every truncation accounted for by an
explicit error ball whose derivation is written in the docstring.  Vocabulary
per MISSION.md: these are enclosures used to *decide* signs and integer
counts; nothing here uses the reserved vocabulary of ``zeta/rigor.py``.

The objects, in the normalisation ``hunts/flow_repair`` measured to be exact
(constants c = a = 1):

    omega(x)  = sum_{n>=1} n a_n exp(-pi n^2 x / 5),
    Phi_DH(u) = 4 e^{3u/2} omega(e^{2u}),
    H_t(z)    = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du,      H_0 = Xi_DH,
    H_t'(z)   = -int_0^inf e^{t u^2} Phi_DH(u) u sin(zu) du,

with a_n the period-5 Davenport-Heilbronn pattern (1, kappa, -kappa, -1, 0)
and kappa the functional-equation constant, derived here by the same linear
solve as ``zeta.epstein._kappa_cached`` but carried out entirely in Arb balls
(never a remembered constant).

Input discipline (two feasibility rounds died on this): ``ctx.prec`` is set
BEFORE any ``arb``/``acb`` is constructed, and every scalar input is converted
to an exact rational (``fractions.Fraction`` -> ``fmpq``) so the input balls
are exact.  A Python float is read bit-exactly (it is a dyadic rational); a
string goes through ``Fraction(str)`` so ``"0.0575"`` means exactly 23/400.
An ``acb``/``arb`` passed in is used as-is (a ball is a valid input ball
regardless of how it was built; segment balls for contour work enter here).

Backend: python-flint (Arb) only.  The quadrature step (``acb.integral``,
Arb's rigorous adaptive integrator) has no counterpart in mpmath's ``iv``
context; the in-tree precedent is ``zeta.rigor.enclose_weil_functional``,
which is flint-only and says so.  The series arithmetic is cross-checked
against an ``mpmath.iv`` leg in ``validate.py``, pointed since 2026-08-16 at
``_truncated_integrand``, the copy of the series the decision path actually
runs (GATE.md closure item (e); before that it exercised ``phi_ball``, which
no decision path calls).
"""

from __future__ import annotations

import math
from fractions import Fraction

from flint import acb, arb, ctx, fmpq

__all__ = [
    "kappa_ball",
    "phi_ball",
    "H_ball",
    "Hprime_ball",
    "default_U",
]


class _prec_guard:
    """Set ``ctx.prec`` for a block, restoring the previous value on exit.

    Constructing this object performs no ball arithmetic; every ball inside
    the guarded block is built at the requested precision.
    """

    def __init__(self, prec: int):
        if not isinstance(prec, int) or prec < 64:
            raise ValueError(f"prec must be an int >= 64, got {prec!r}")
        self.prec = prec

    def __enter__(self):
        self.old = ctx.prec
        ctx.prec = self.prec
        return self

    def __exit__(self, *exc):
        ctx.prec = self.old
        return False


# ---------------------------------------------------------------------------
# exact input conversion
# ---------------------------------------------------------------------------


def _exact_q(value) -> Fraction:
    """The exact rational value of ``value``; refuse anything lossy.

    Same discipline as ``zeta.rigor._exact``: floats are dyadic rationals and
    convert bit-exactly; mpmath ``mpf`` values are read out of their
    ``(sign, man, exp, bc)`` tuple; strings and Fractions are taken at face
    value (``"0.0575"`` is exactly 23/400).  Anything else raises.
    """
    if isinstance(value, Fraction):
        return value
    if isinstance(value, bool):
        raise TypeError("bool is not a valid coordinate")
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError(f"non-finite coordinate {value!r}")
        return Fraction(value)
    mpf_tuple = getattr(value, "_mpf_", None)
    if mpf_tuple is not None:
        sign, man, exp, _bc = mpf_tuple
        if man == 0:
            if exp != 0:
                raise ValueError(f"non-finite coordinate {value!r}")
            return Fraction(0)
        out = Fraction(int(man)) * Fraction(2) ** int(exp)
        return -out if sign else out
    if isinstance(value, str):
        return Fraction(value)
    raise TypeError(
        f"cannot convert {type(value).__name__} to an exact rational; "
        "pass Fraction, int, float, str, or an mpmath mpf"
    )


def _q_to_arb(q: Fraction) -> arb:
    """arb ball of an exact rational at the ambient ``ctx.prec``."""
    return arb(fmpq(q.numerator, q.denominator))


def _as_acb(z) -> acb:
    """Exact conversion of ``z`` to an ``acb`` at the ambient ``ctx.prec``.

    Accepts ``acb``/``arb`` (used as-is), a ``(re, im)`` pair, a ``complex``
    (both parts bit-exact dyadics), or any scalar ``_exact_q`` accepts.
    Must be called with ``ctx.prec`` already set.
    """
    if isinstance(z, acb):
        return z
    if isinstance(z, arb):
        return acb(z)
    if isinstance(z, complex):
        return acb(_q_to_arb(_exact_q(z.real)), _q_to_arb(_exact_q(z.imag)))
    if isinstance(z, (tuple, list)) and len(z) == 2:
        return acb(_q_to_arb(_exact_q(z[0])), _q_to_arb(_exact_q(z[1])))
    mpc_val = getattr(z, "_mpc_", None)
    if mpc_val is not None:
        re, im = mpc_val
        return acb(_q_to_arb(_exact_q(re)), _q_to_arb(_exact_q(im)))
    return acb(_q_to_arb(_exact_q(z)))


def _nonfinite_acb() -> acb:
    """An indeterminate (non-finite) ball: the loud refusal value.

    Construction matters (measured, python-flint 0.9.0): ``arb(float("nan"))``
    is an EXACT NaN (midpoint nan, radius 0) and ``acb.integral`` gives up
    after a single evaluation when the integrand returns it, instead of
    subdividing.  ``arb("nan")`` is nan +/- inf, the indeterminate ball the
    integrator treats as "subdivide or fail loudly", which is the behaviour
    every refusal in this file promises.
    """
    nan = arb("nan")
    return acb(nan, nan)


# ---------------------------------------------------------------------------
# kappa as an Arb ball
# ---------------------------------------------------------------------------


def _L_chi_ball(s: acb, conjugate: bool) -> acb:
    """L(s, chi) = 5^{-s} [zeta(s,1/5) + i zeta(s,2/5) - i zeta(s,3/5) - zeta(s,4/5)],

    chi the mod-5 character with chi(2) = i; ``conjugate`` flips i -> -i.
    Same derivation as ``zeta.epstein``, in balls (acb Hurwitz zeta).
    """
    i_unit = acb(0, 1) if not conjugate else acb(0, -1)
    h = [s.zeta(acb(fmpq(a, 5))) for a in (1, 2, 3, 4)]
    total = h[0] + i_unit * h[1] - i_unit * h[2] - h[3]
    return acb(5) ** (-s) * total


def _lam_ball(s: acb, conjugate: bool) -> acb:
    """(pi/5)^{-(s+1)/2} Gamma((s+1)/2) L(s, chi), in balls."""
    return ((acb(arb.pi() / 5) ** (-(s + 1) / 2))
            * ((s + 1) / 2).gamma() * _L_chi_ball(s, conjugate))


_KAPPA_CACHE: dict[int, arb] = {}


def kappa_ball(prec: int) -> arb:
    """An Arb ball enclosing kappa, by the self-duality linear solve.

    The combination Lambda(s) + kappa * i * Mu(s) (Lambda from chi, Mu from
    the conjugate character) satisfies F(s) = F(1-s) for exactly one real
    kappa; evaluating both completed L-functions at the single point
    s0 = 3/4 + 3i/2 gives the linear equation A + i kappa B = 0 with

        A = lam(s0) + lam*(s0) - lam(1-s0) - lam*(1-s0),
        B = lam(s0) - lam*(s0) - lam(1-s0) + lam*(1-s0),

    so kappa = A / (i B).  Every step is an acb ball (Hurwitz zeta, Gamma).
    The solve is re-run per call, never a remembered constant; the imaginary
    part of the quotient must contain 0 (raises ValueError otherwise) and
    the real ball is returned.  Measured radius ~1.5e-148 at prec 500.
    """
    cached = _KAPPA_CACHE.get(prec)
    if cached is not None:
        return cached
    with _prec_guard(prec):
        s0 = acb(fmpq(3, 4), fmpq(3, 2))
        A = (_lam_ball(s0, False) + _lam_ball(s0, True)
             - _lam_ball(1 - s0, False) - _lam_ball(1 - s0, True))
        B = (_lam_ball(s0, False) - _lam_ball(s0, True)
             - _lam_ball(1 - s0, False) + _lam_ball(1 - s0, True))
        k = A / (acb(0, 1) * B)
        if not k.imag.contains(arb(0)):
            raise ValueError("kappa solve: Im of the quotient does not contain 0")
        out = k.real
        if not (arb(0) < out) or not (out < arb(1)):
            raise ValueError("kappa solve: ball does not decide 0 < kappa < 1")
    _KAPPA_CACHE[prec] = out
    return out


# ---------------------------------------------------------------------------
# Phi_DH as a ball, with a rigorous series tail
# ---------------------------------------------------------------------------


def _default_nmax(prec: int, rho_f: float) -> int:
    """Truncation order making the series tail ~2^-(prec+40).

    The tail decays like exp(-pi N^2 rho / 5); solve for N in floats (this
    choice steers cost only, the bound itself is computed in balls).
    """
    need = (prec + 40) * math.log(2.0)
    n = int(math.ceil(math.sqrt(5.0 * need / (math.pi * max(rho_f, 1e-6))))) + 4
    return min(n, 20000)


def _trunc_omega(X: acb, kap: arb, N: int) -> acb:
    """omega_N(X) = sum_{n=1}^{N} n a_n q^{n^2}, q = exp(-pi X / 5).

    Theta recurrence: q^{n^2} from q^{(n-1)^2} costs two multiplications per
    term instead of one exp.  A finite sum of entire functions of X.
    """
    q = (-arb.pi() / 5 * X).exp()
    q2 = q * q
    a_pat = {1: arb(1), 2: kap, 3: -kap, 4: arb(-1), 0: None}
    p = q            # q^{n^2} at n = 1
    w = q2 * q       # q^{2n+1} at n = 1
    s = acb(a_pat[1]) * p
    for n in range(2, N + 1):
        p = p * w
        w = w * q2
        a = a_pat[n % 5]
        if a is not None:
            s = s + (arb(n) * a) * p
    return s


def _omega_tail_upper(rho: arb, N: int) -> arb | None:
    """Upper bound for |omega(X) - omega_N(X)| when Re X >= rho > 0.

    Term bound: |n a_n exp(-pi n^2 X / 5)| = n |a_n| exp(-pi n^2 Re X / 5)
    <= n exp(-pi n^2 rho / 5) since |a_n| <= 1 (kappa is decided to lie in
    (0,1) by its ball).  For n >= N+1, n^2 >= n (N+1), so each term is
    <= n r^n with r = exp(-pi (N+1) rho / 5), and

        sum_{n>=N+1} n r^n = r^{N+1} ((N+1) - N r) / (1-r)^2
                          <= (N+1) r^{N+1} / (1-r)^2.

    Requires r < 1, i.e. rho > 0; returns None when 1 - r is not decidedly
    positive (caller refuses with a non-finite ball).
    """
    r = (-arb.pi() * (N + 1) * rho / 5).exp()
    one_minus = 1 - r
    if not (one_minus.lower() > 0):
        return None
    tail = arb(N + 1) * r ** (N + 1) / (one_minus * one_minus)
    return tail.abs_upper()


def phi_ball(u, prec: int, nmax: int | None = None, analytic: bool = False) -> acb:
    """An acb ball enclosing Phi_DH(u) = 4 e^{3u/2} omega(e^{2u}).

    ``u`` may be a complex ball (``acb``), a pair, or any exact scalar; the
    ball is evaluated over the WHOLE input ball, so this function is usable
    as an integrand for Arb's rigorous integrator.

    Series tail (rigorous, added to the radius): with X = e^{2u} evaluated
    over the ball and rho = the lower bound of Re X over the ball,

        |omega(X) - omega_N(X)| <= (N+1) r^{N+1} / (1-r)^2,
        r = exp(-pi (N+1) rho / 5),

    because |a_n| <= 1 (kappa's ball decides 0 < kappa < 1), each term obeys
    |n a_n e^{-pi n^2 X/5}| <= n e^{-pi n^2 rho/5}, and n^2 >= n(N+1) for
    n >= N+1 gives geometric domination by n r^n, summed in closed form
    (see ``_omega_tail_upper``).  The bound holds uniformly over the input
    ball, so the returned ball encloses Phi_DH at every point of the ball.
    The tail is multiplied by an upper bound of |4 e^{3u/2}| over the ball.

    Refusals: when rho <= 0 (the ball reaches Re e^{2u} <= 0, where the
    series representation diverges and its holomorphy cannot be established
    from this representation) the function returns a NON-FINITE ball, which
    Arb's integrator treats as "subdivide or fail loudly", never as a value.
    The ``analytic`` flag (the integrator's holomorphy demand) needs no
    extra branch beyond that: on rho > 0 the series converges locally
    uniformly, so Phi_DH is holomorphic there and the truncated-sum-plus-
    error ball is a valid enclosure of a holomorphic function; on rho <= 0
    this representation cannot vouch for holomorphy and the non-finite ball
    is exactly the refusal the flag demands.  (Same handling as the
    feasibility script, where the integrand is entire by truncation; here
    the tail is folded in, so the rho > 0 gate carries the holomorphy
    argument.)
    """
    with _prec_guard(prec):
        u_b = _as_acb(u)
        kap = kappa_ball(max(prec + 40, 300))
        X = (2 * u_b).exp()
        rho = X.real.lower()
        if not (rho > 0):
            return _nonfinite_acb()
        if nmax is None:
            nmax = _default_nmax(prec, float(rho))
        S = _trunc_omega(X, kap, nmax)
        pref = 4 * (3 * u_b / 2).exp()
        tail = _omega_tail_upper(rho, nmax)
        if tail is None:
            return _nonfinite_acb()
        err_mag = (pref.abs_upper() * tail).abs_upper()
        err = arb(0, err_mag)
        return pref * S + acb(err, err)


# ---------------------------------------------------------------------------
# the flow H_t and its derivative, as balls
# ---------------------------------------------------------------------------


def default_U(t, y_abs_hi: float, prec: int) -> Fraction:
    """An exact dyadic upper integration limit adaptive in t, |Im z|, prec.

    Chosen (in floats; the choice steers cost, the tails are ball-bounded
    downstream) so the integrand magnitude at U,

        8 exp(t U^2 + (3/2 + y) U - (pi/5) e^{2U}),

    is below ~2^-(prec+30), by fixed-point iteration on
    e^{2U} = (5/pi) (target + t U^2 + (3/2+y) U).  Returned as an exact
    dyadic Fraction (multiple of 1/64), at least 1 + 1/16.
    """
    t_f = float(_exact_q(t)) if not isinstance(t, (arb,)) else float(t)
    y_f = float(y_abs_hi)
    target = (prec + 30) * math.log(2.0) + math.log(8.0)
    U = 2.0
    for _ in range(60):
        A = (target + t_f * U * U + (1.5 + y_f) * U) * 5.0 / math.pi
        U_new = 0.5 * math.log(A)
        if abs(U_new - U) < 1e-9:
            U = U_new
            break
        U = U_new
    U = max(U, 1.0) + 0.0625
    return Fraction(math.ceil(U * 64), 64)


def _series_tail_finite(N: int, U: arb, t: arb, y_hi: arb,
                        deriv: bool) -> arb | None:
    """Bound for the series truncation error committed on the path [0, U].

    The exact integrand minus the truncated one is
    e^{t u^2} 4 e^{3u/2} (omega - omega_N)(e^{2u}) cos(zu)  (times -u sin(zu)
    instead of cos(zu) for the derivative).  On the real path, x = e^{2u} >= 1,
    and each tail term n e^{-pi n^2 x/5} is decreasing in x, so the omega tail
    is <= its value at x = 1: by the geometric domination of
    ``_omega_tail_upper`` with rho = 1,

        |omega - omega_N| <= (N+1) r^{N+1} / (1-r)^2,  r = e^{-pi (N+1)/5}.

    Prefactor upper bounds on [0, U] (t >= 0 enforced upstream):
    e^{t u^2} <= e^{t U^2}, e^{3u/2} <= e^{3U/2}, |cos(zu)| <= cosh(u Im z)
    <= e^{y U} with y = sup |Im z| over the input ball; path length U.  For
    the derivative an extra factor |u sin(zu)| / |cos(zu)| ... is bounded by
    replacing |cos(zu)| <= e^{yU} with |u sin(zu)| <= U e^{yU}: one extra
    factor U.
    """
    tail1 = _omega_tail_upper(arb(1), N)
    if tail1 is None:
        return None
    pref = 4 * (t * U * U + (arb(3) / 2 + y_hi) * U).exp()
    out = U * pref * tail1
    if deriv:
        out = out * U
    return out.abs_upper()


def _u_tail(U: arb, t: arb, y_hi: arb, deriv: bool) -> arb | None:
    """Bound for the discarded integral over [U, inf).

    For real u >= U >= 1, with r = e^{-pi e^{2u}/5}:
    |omega(e^{2u})| <= sum n r^{n^2} <= sum n r^n = r/(1-r)^2 <= 2r once
    r <= 0.29 (checked at u = U; r is decreasing in u).  So the integrand
    obeys |e^{t u^2} Phi_DH(u) cos(zu)| <= 8 e^{E(u)} with

        E(u) = t u^2 + (3/2 + y) u - (pi/5) e^{2u}.

    Since u e^{-2u} and u^2 e^{-2u} are decreasing for u >= 1,
    u <= U e^{-2U} e^{2u} and u^2 <= U^2 e^{-2U} e^{2u} on [U, inf), hence

        E(u) <= -c e^{2u},  c = pi/5 - (t U^2 + (3/2 + y) U) e^{-2U},

    and c > 0 is checked (else None: caller must raise U).  Substituting
    v = e^{2u} (du = dv/(2v), v >= V = e^{2U}):

        int_U^inf 8 e^{-c e^{2u}} du = int_V^inf 4 e^{-cv} dv / v
                                     <= (4/V) int_V^inf e^{-cv} dv
                                     = 4 e^{-cV} / (c V).

    For the derivative the integrand carries an extra |u| = (log v)/2 and
    (log v)/v is decreasing for v >= e, so the bound gains the factor
    (log V)/2 / (1) ... concretely int_V^inf 4 (log v / 2) e^{-cv} dv / v
    <= 2 (log V / V) int_V^inf e^{-cv} dv = 4 U e^{-cV} / (c V): one extra
    factor U.
    """
    if not (U >= 1):
        return None
    V = (2 * U).exp()
    r_at_V = (-arb.pi() * V / 5).exp()
    if not (r_at_V.abs_upper() < arb(fmpq(29, 100))):
        return None
    beta = arb(3) / 2 + y_hi
    c = arb.pi() / 5 - (t * U * U + beta * U) / V
    if not (c.lower() > 0):
        return None
    out = 4 * (-c * V).exp() / (c * V)
    if deriv:
        out = out * U
    return out.abs_upper()


def _truncated_integrand(z_b: acb, t_b: arb, N: int, kap: arb, deriv: bool):
    """The exact integrand callable that ``_H_core`` hands to ``acb.integral``.

    Hoisted out of ``_H_core`` on 2026-08-16 (GATE.md closure item (e)) and
    otherwise unchanged: same operations, same order, same ambient
    precision.  It was inline, and being inline it was unreachable, so the
    only ``mpmath.iv`` cross-leg in ``validate.py`` pointed at ``phi_ball``
    instead, which no decision path calls.  A fault in this copy of the
    theta recurrence was therefore invisible to the second backend.  With
    the callable reachable, ``validate.check_iv_cross_leg`` exercises this
    function, which is the one the count runs.

    Must be called with ``ctx.prec`` already set (``_prec_guard``): the
    constants below are built at the ambient precision, and the returned
    closure is evaluated by the integrator inside the same guarded block.

    The returned f is a FINITE sum of entire functions of u, so it is
    holomorphic on every ball and the integrator's ``analytic`` flag needs
    no branch (same handling as the feasibility script).  Its truncation
    error is not carried here; ``_H_core`` adds the two explicit tail balls
    of ``_series_tail_finite`` and ``_u_tail``.
    """
    pi5 = arb.pi() / 5
    three_half = arb(3) / 2
    a_pat = {1: arb(1), 2: kap, 3: -kap, 4: arb(-1), 0: None}
    coeffs = []
    for n in range(1, N + 1):
        a = a_pat[n % 5]
        coeffs.append(None if a is None else arb(n) * a)

    if deriv:
        def f(u, analytic):
            x = (2 * u).exp()
            q = (-pi5 * x).exp()
            q2 = q * q
            p = q
            w = q2 * q
            s = coeffs[0] * p
            for n in range(2, N + 1):
                p = p * w
                w = w * q2
                cn = coeffs[n - 1]
                if cn is not None:
                    s = s + cn * p
            return -4 * (t_b * u * u + three_half * u).exp() * s * u * (z_b * u).sin()
    else:
        def f(u, analytic):
            x = (2 * u).exp()
            q = (-pi5 * x).exp()
            q2 = q * q
            p = q
            w = q2 * q
            s = coeffs[0] * p
            for n in range(2, N + 1):
                p = p * w
                w = w * q2
                cn = coeffs[n - 1]
                if cn is not None:
                    s = s + cn * p
            return 4 * (t_b * u * u + three_half * u).exp() * s * (z_b * u).cos()

    return f


def _H_core(z, t, prec: int, U, nmax: int | None, deriv: bool,
            eval_limit: int) -> acb:
    with _prec_guard(prec):
        t_q = _exact_q(t)
        if t_q < 0:
            raise ValueError("H_ball/Hprime_ball require t >= 0 "
                             "(the tail bounds use e^{t u^2} monotonicity)")
        t_b = _q_to_arb(t_q)
        z_b = _as_acb(z)
        y_hi = arb(z_b.imag.abs_upper())
        if U is None:
            U_q = default_U(t_q, float(y_hi), prec)
        else:
            U_q = _exact_q(U)
        U_b = _q_to_arb(U_q)
        kap = kappa_ball(max(prec + 40, 300))
        N = nmax if nmax is not None else _default_nmax(prec, 1.0)

        f = _truncated_integrand(z_b, t_b, N, kap, deriv)

        I = acb.integral(f, 0, U_b, eval_limit=eval_limit)
        e1 = _series_tail_finite(N, U_b, t_b, y_hi, deriv)
        e2 = _u_tail(U_b, t_b, y_hi, deriv)
        if e1 is None or e2 is None:
            raise ValueError(
                f"tail bound not established at U={U_q} (need U >= 1, "
                "e^{-pi e^{2U}/5} <= 0.29 and c > 0); raise U"
            )
        err = arb(0, (e1 + e2).abs_upper())
        return I + acb(err, err)


def H_ball(z, t, prec: int, U=None, nmax: int | None = None,
           eval_limit: int = 10 ** 7) -> acb:
    """An acb ball enclosing H_t(z) = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du.

    Assembly: Arb's rigorous adaptive integrator (``acb.integral``, the
    ``zeta.rigor.enclose_weil_functional`` precedent, same eval_limit) over
    the truncated integrand on [0, U], plus TWO explicit error balls added to
    both components:

    1. series truncation on [0, U]: see ``_series_tail_finite`` (geometric
       domination of the omega tail at x = 1, times the path-length and
       prefactor bounds);
    2. the discarded integral over [U, inf): see ``_u_tail`` (integrand
       dominated by 8 e^{-c e^{2u}} with an explicit c > 0, integrable in
       closed form to 4 e^{-cV}/(cV), V = e^{2U}).

    ``U`` defaults to ``default_U(t, |Im z|, prec)``, adaptive in t, z and
    prec, and is always an exact rational.  ``t`` must be >= 0.  ``z`` may
    be a ball (segment input for contour work) or an exact point.
    """
    return _H_core(z, t, prec, U, nmax, deriv=False, eval_limit=eval_limit)


def Hprime_ball(z, t, prec: int, U=None, nmax: int | None = None,
                eval_limit: int = 10 ** 7) -> acb:
    """An acb ball enclosing H_t'(z) = -int_0^inf e^{t u^2} Phi_DH(u) u sin(zu) du.

    Same construction and tail treatment as ``H_ball``; both tail bounds gain
    exactly one factor of U (|u| <= U on the path; |u| <= U e^{-2U} e^{2u}
    beyond it, see the docstrings of ``_series_tail_finite`` and ``_u_tail``).
    """
    return _H_core(z, t, prec, U, nmax, deriv=True, eval_limit=eval_limit)
