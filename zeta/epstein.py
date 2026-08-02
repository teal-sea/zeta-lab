"""The counterexample battery: Davenport-Heilbronn, gate #3 made computational.

**This module is the standing reminder that the functional equation alone
CANNOT imply RH** (see ``docs/08-why-it-is-hard.md`` section 4.1 and the
counterexample gate, gate #3, of ``docs/09-new-ontologies.md``): it constructs
a function with zeta-like symmetry but *no Euler product*, and then actually
locates, verifies, and pins an off-critical-line zero of it.

The object is the **Davenport-Heilbronn function** (1936) — the classical
computable representative of the Davenport-Heilbronn / Epstein family that
gate #3 names, hence this module's filename.  Let chi be the Dirichlet
character mod 5 with chi(2) = i (an odd character; 2 generates (Z/5Z)*, so
chi(1), chi(2), chi(3), chi(4) = 1, i, -i, -1).  Each L(s, chi) is computed
through Hurwitz zeta values,

    L(s, chi) = 5^{-s} * sum_{a=1..4} chi(a) * zeta(s, a/5),

and the Davenport-Heilbronn function is the linear combination

    f(s) = ((1 - i*kappa)/2) L(s, chi) + ((1 + i*kappa)/2) L(s, chibar)

with kappa the unique real constant making the completed function

    F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s)

satisfy F(s) = F(1 - s) exactly — the odd-character completion, the same
shape of functional equation as Riemann's xi.  **kappa is derived here
numerically, not remembered**: F_kappa(s) - F_kappa(1-s) is linear in kappa,
so one linear solve at any non-symmetric point determines it
(:func:`kappa`); the derivation then *verifies* that the same constant kills
the defect at independent points to working precision, and that it is real.
Measured at dps = 50: kappa agrees across four unrelated base points to all
40 displayed digits, its imaginary residue is ~1e-50, and the defect
|F(s) - F(1-s)| at six random s in [-2,3] x [-20i,20i] is at most 1.1e-50.
(The derived value also matches the closed form
(sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1) to 1e-50 — quoted as an observation,
never used.)

What f then has, and what it lacks:

* **entire** — the Hurwitz poles at s = 1 cancel (sum of coefficients is 0;
  verified here by a mean-value/no-pole check, :func:`dh_mean_value_defect`);
* a **Riemann-type functional equation** F(s) = F(1-s), defect measured
  below 1e-30 (:func:`dh_functional_equation_defect`);
* **real Dirichlet coefficients**, periodic mod 5:
  a_n = 1, kappa, -kappa, -1, 0 for n = 1..5 mod 5 (:func:`dh_coefficient`);
* a real Hardy-style function Z_f on the critical line (:func:`Z_dh`), so
  line zeros are sign changes, exactly as for zeta;
* **no Euler product** — its coefficients are not multiplicative
  (a_6 = a_1 = 1 while a_2*a_3 = -kappa^2; :func:`claim_multiplicativity`);
* and, the payoff, **zeros off the critical line**.  The argument-principle
  count in a box (:func:`count_zeros_box`) exceeds the sign-change count on
  the line (:func:`zeros_on_line`) — the technique of
  ``scripts/02_find_zeros.py`` run in reverse — first in the window
  84 < t < 92, where the box holds 5 zeros but the line only 3.  Bisecting
  the box and polishing (:func:`find_offline_zero`) lands on

      rho = 0.80851718245663738555335196060684...
            + 85.69934848537759217192926770894...*i

  with |f(rho)| ~ 4e-71 at dps = 70 and Re(rho) - 1/2 = 0.30851..., pinned
  in ``OFFLINE_ZERO_RE`` / ``OFFLINE_ZERO_IM`` and re-verified by the test
  suite.  (This matches the literature: Spira, *Math. Comp.* 1994, lists the
  Davenport-Heilbronn zero 0.808517 + 85.699348i.)

So every ingredient the functional-equation-only proof attempts use —
symmetry s <-> 1-s, real coefficients, a real Z, completed entirety, even
"most zeros on the line" — survives in f, and RH for f is *false*.  The one
structural difference is the Euler product.  :func:`battery` packages that
observation as a falsification harness: it evaluates a claimed structural
property against both zeta and f through a common interface, and reports
whether the claim distinguishes them.  A proposed RH mechanism that f also
satisfies is dead on arrival (docs/09, gate #3).

Honest scope: nothing here proves anything about *zeta's* zeros; the module
demonstrates, to stated numerical precision, that a specific rival function
shares the symmetry and violates RH.  Conventions follow :mod:`zeta.core`:
explicit ``dps`` everywhere, guard digits internal, no global mpmath state
left modified.
"""

from __future__ import annotations

import math
from functools import lru_cache

import mpmath
from mpmath import mp

from .core import DPS_DEFAULT, Z as hardy_Z, functional_equation_defect, xi

__all__ = [
    "KAPPA_REF",
    "OFFLINE_ZERO_RE",
    "OFFLINE_ZERO_IM",
    "chi5",
    "kappa",
    "L_chi",
    "dh_f",
    "dh_coefficient",
    "completed_dh",
    "dh_functional_equation_defect",
    "dh_mean_value_defect",
    "dh_theta",
    "Z_dh",
    "zeros_on_line",
    "count_zeros_box",
    "find_offline_zero",
    "zeta_interface",
    "dh_interface",
    "battery",
    "claim_functional_equation",
    "claim_multiplicativity",
]

#: Guard digits carried internally and discarded before returning.
_GUARD: int = 10

#: kappa to 40 digits, as *derived* by :func:`kappa` (linear solve of the
#: functional-equation-defect condition at s0 = 0.75 + 1.5i, dps = 50, then
#: cross-checked at three unrelated points; imaginary residue ~1e-50).  This
#: string is a pinned reference for the tests — the running code always
#: re-derives kappa rather than trusting it.
KAPPA_REF: str = "0.2840790438404122960282918323931261690911"

#: The located off-critical-line zero rho of the Davenport-Heilbronn function,
#: to 50 digits.  Derivation (all steps reproduced by the test suite at lower
#: cost, and by ``find_offline_zero(60, 100)`` in full):
#:
#: 1. Scanning windows of height 8 over 60 < t < 100 with sigma in [-1, 2],
#:    ``count_zeros_box`` vs ``zeros_on_line`` gave 4=4, 6=6, 5=5, **5 vs 3**
#:    (t in [84, 92]), 6=6 — two zeros in the strip that are not on the line.
#: 2. Bisecting: box [84, 86] holds 2 zeros, the line 0; the right half-box
#:    sigma in [0.55, 2] holds exactly 1 (its mirror 1 - conj(rho) holds the
#:    other, as the functional equation + real coefficients force).
#: 3. A 31x41 grid minimum of |f| at 0.79 + 85.7i polished by mp.findroot at
#:    dps = 70 gives the digits below; |f(rho)| = 4.1e-71, and the winding
#:    number around a side-0.2 box centred on rho is 1.
#:
#: Independent confirmation: Spira (Math. Comp. 63 (1994), 747-748) reports the
#: Davenport-Heilbronn zero 0.808517 + 85.699348i; all published digits match.
OFFLINE_ZERO_RE: str = (
    "0.80851718245663738555335196060684412785067026830502"
)
OFFLINE_ZERO_IM: str = (
    "85.699348485377592171929267708941729037987829423408"
)


# ---------------------------------------------------------------------------
# small helpers (mirroring zeta.core conventions)
# ---------------------------------------------------------------------------

def _num(s):
    """Coerce to an mpmath number."""
    return mpmath.mpmathify(s)


def _shrink(value, dps: int):
    """Round a value computed at high precision down to ``dps`` digits."""
    with mp.workdps(dps):
        return +value


# ---------------------------------------------------------------------------
# the character, the L-functions, kappa
# ---------------------------------------------------------------------------

def chi5(n: int):
    """The Dirichlet character mod 5 with chi(2) = i.

    2 is a primitive root mod 5 (2, 4, 3, 1), so chi(2) = i forces
    chi(4) = i^2 = -1, chi(3) = i^3 = -i, chi(1) = 1, chi(0 mod 5) = 0.
    chi(-1) = chi(4) = -1: the character is **odd**, which is why the
    completing gamma factor below is Gamma((s+1)/2) and not Gamma(s/2).
    Returns an exact ``mpc`` (entries of {0, 1, i, -1, -i}).
    """
    return {
        0: mp.mpc(0),
        1: mp.mpc(1),
        2: mp.mpc(0, 1),
        3: mp.mpc(0, -1),
        4: mp.mpc(-1),
    }[int(n) % 5]


def _hurwitz_quad(s):
    """The four Hurwitz values zeta(s, a/5), a = 1..4, at ambient precision."""
    return [mp.zeta(s, mp.mpf(a) / 5) for a in range(1, 5)]


def L_chi(s, conjugate: bool = False, dps: int = DPS_DEFAULT):
    """L(s, chi) for the mod-5 character of :func:`chi5`, via Hurwitz zeta:

        L(s, chi) = 5^{-s} * [ zeta(s,1/5) + i*zeta(s,2/5)
                               - i*zeta(s,3/5) - zeta(s,4/5) ].

    ``conjugate=True`` gives L(s, chibar).  Valid on the whole plane except
    s = 1, where the individual Hurwitz terms have poles (they cancel in the
    combination — sum of chi(a) is 0 — but each summand is infinite; use
    :func:`dh_f`, which handles s = 1, if you need the combination there).
    """
    with mp.workdps(dps + _GUARD):
        s_w = _num(s)
        if s_w == 1:
            raise ValueError("the Hurwitz terms of L(s, chi) have poles at s = 1")
        h = _hurwitz_quad(s_w)
        total = mp.mpc(0)
        for a in range(4):
            c = chi5(a + 1)
            total += (mp.conj(c) if conjugate else c) * h[a]
        value = mp.power(5, -s_w) * total
    return _shrink(value, dps)


def _lambda_chi(s, conjugate: bool):
    """(pi/5)^{-(s+1)/2} Gamma((s+1)/2) L(s, chi), at ambient precision."""
    return (
        mp.power(mp.pi / 5, -(s + 1) / 2)
        * mp.gamma((s + 1) / 2)
        * L_chi(s, conjugate=conjugate, dps=mp.dps)
    )


@lru_cache(maxsize=32)
def _kappa_cached(dps: int) -> tuple:
    """(kappa, imaginary residue) derived at ``dps`` + guard digits.

    Write Lam(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) L(s, chi) and Lambar for
    the chibar version.  With c = (1 - i*kappa)/2 the completed function is
    F(s) = c*Lam(s) + conj(c)*Lambar(s), so the defect is **linear in kappa**:

        F(s) - F(1-s) = [ A(s) - i*kappa*B(s) ] / 2,
        A(s) = Lam(s) + Lambar(s) - Lam(1-s) - Lambar(1-s),
        B(s) = Lam(s) - Lambar(s) - Lam(1-s) + Lambar(1-s),

    hence kappa = A(s0)/(i*B(s0)) at any point s0 with B(s0) != 0.  That the
    quotient is (a) independent of s0 and (b) real is Gauss-sum theory — and
    is *checked*, not assumed: the residues are re-measured by the tests, and
    this function verifies the defect at an unrelated point before returning.
    """
    with mp.workdps(dps + _GUARD + 5):
        s0 = mp.mpc(mp.mpf(3) / 4, mp.mpf(3) / 2)
        A = (
            _lambda_chi(s0, False) + _lambda_chi(s0, True)
            - _lambda_chi(1 - s0, False) - _lambda_chi(1 - s0, True)
        )
        B = (
            _lambda_chi(s0, False) - _lambda_chi(s0, True)
            - _lambda_chi(1 - s0, False) + _lambda_chi(1 - s0, True)
        )
        k = A / (mp.mpc(0, 1) * B)
        k_re, k_im = mp.re(k), mp.im(k)
        # verification leg: the same constant must kill the defect elsewhere
        s1 = mp.mpc(mp.mpf(3) / 10, 2)
        c = (1 - mp.mpc(0, 1) * k_re) / 2
        defect = abs(
            c * _lambda_chi(s1, False) + mp.conj(c) * _lambda_chi(s1, True)
            - c * _lambda_chi(1 - s1, False) - mp.conj(c) * _lambda_chi(1 - s1, True)
        )
        tol = mp.mpf(10) ** (-(dps + 2))
        if not (abs(k_im) < tol and defect < tol):
            raise ArithmeticError(
                f"kappa derivation failed self-check: Im kappa = {mp.nstr(k_im, 5)}, "
                f"cross-point defect = {mp.nstr(defect, 5)} at dps={dps}"
            )
        return (k_re, k_im)


def kappa(dps: int = DPS_DEFAULT):
    """The Davenport-Heilbronn constant kappa, **derived numerically** as the
    root of the functional-equation-defect condition (see :func:`_kappa_cached`
    for the linear-solve derivation and its built-in cross-check).

    kappa = 0.2840790438404122960282918323931261690911... (:data:`KAPPA_REF`).
    Observation, not input: this equals (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1)
    to all digits computed (1e-50 at dps = 50).
    """
    k, _ = _kappa_cached(int(dps))
    return _shrink(k, dps)


# ---------------------------------------------------------------------------
# the Davenport-Heilbronn function f, its coefficients, its completion
# ---------------------------------------------------------------------------

def _dh_raw(s):
    """f(s) at ambient precision via the real-coefficient Hurwitz combination

        f(s) = 5^{-s} [ zeta(s,1/5) + kappa*zeta(s,2/5)
                        - kappa*zeta(s,3/5) - zeta(s,4/5) ],

    which is c*L(s,chi) + conj(c)*L(s,chibar) with c = (1 - i*kappa)/2
    unfolded (the imaginary parts cancel exactly; the test-suite checks the
    two forms against each other).  Assumes s != 1.
    """
    k = kappa(mp.dps)
    h = _hurwitz_quad(s)
    return mp.power(5, -s) * (h[0] + k * h[1] - k * h[2] - h[3])


def dh_f(s, dps: int = DPS_DEFAULT):
    """The Davenport-Heilbronn function f(s) — entire, functional equation
    F(s) = F(1-s) for F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s), real
    Dirichlet coefficients (period 5: 1, kappa, -kappa, -1, 0), **no Euler
    product**, and zeros off the critical line (:data:`OFFLINE_ZERO_RE`).

    Near s = 1 each Hurwitz term carries a simple pole 1/(5(s-1)); the poles
    cancel (coefficient sum 1 + kappa - kappa - 1 = 0) but the cancellation
    costs ~log10(1/|s-1|) digits, which are added to the internal guard.  At
    s = 1 exactly the removable point is evaluated as a Cauchy circle average
    of radius 1/4 (cf. ``zeta.core._removable``), which never calls f at 1.

    Returns an ``mpc`` (or the real part as ``mpf`` for real s away from 1).
    """
    with mp.workdps(dps + _GUARD):
        s_probe = _num(s)
    if s_probe == 1:
        # Cauchy mean value over a circle |z - 1| = 1/4: legitimate for a
        # removable singularity, never evaluates at the centre.
        n_points = max(48, int(math.ceil(1.5 * dps)))
        with mp.workdps(dps + _GUARD):
            total = mp.mpc(0)
            r = mp.mpf(1) / 4
            for j in range(n_points):
                total += _dh_raw(1 + r * mp.expjpi(mp.mpf(2 * j) / n_points))
            value = total / n_points
            value = mp.re(value)  # f is real on the real axis
        return _shrink(value, dps)
    # cancellation guard near the (removable) s = 1
    dist = abs(s_probe - 1)
    extra = 0
    if dist < 1:
        extra = min(int(mp.ceil(-mp.log10(dist))) + 2, 20 * dps)
    with mp.workdps(dps + _GUARD + extra):
        s_w = _num(s)
        value = _dh_raw(s_w)
        if mp.im(s_w) == 0:
            value = mp.re(value)
    return _shrink(value, dps)


def dh_coefficient(n: int, dps: int = DPS_DEFAULT):
    """The n-th Dirichlet coefficient a_n of f(s) = sum a_n n^{-s}.

    a_n = 2 Re( c * chi(n) ) with c = (1 - i*kappa)/2 — manifestly **real**,
    periodic mod 5:  a_1..a_5 = 1, kappa, -kappa, -1, 0.

    Not multiplicative: a_6 = a_1 = 1 but a_2 * a_3 = -kappa^2 = -0.0807...
    That is the precise sense in which f has no Euler product, and it is what
    :func:`claim_multiplicativity` tests.
    """
    if int(n) < 1:
        raise ValueError("Dirichlet coefficients are indexed from n = 1")
    with mp.workdps(dps + _GUARD):
        c = (1 - mp.mpc(0, 1) * kappa(dps + _GUARD)) / 2
        v = 2 * (c * chi5(int(n)))
        value = mp.re(v)  # Im is exactly 0 for c = x - iy against chi in {0,±1,±i}
    return _shrink(value, dps)


def completed_dh(s, dps: int = DPS_DEFAULT):
    """F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s): the completed function,
    entire, with F(s) = F(1-s) and F real on the critical line.

    Gamma((s+1)/2) has poles at s = -1, -3, -5, ... — exactly where f has its
    "trivial" zeros (forced by the functional equation, like zeta's at the
    even negative integers but shifted to the odd ones because chi is odd).
    F is finite there; the removable points are evaluated as Cauchy circle
    averages of radius 1/2, which stays clear of the neighbouring exceptional
    points (they are 2 apart, and s = 1 is at distance >= 2).

    The f factor is evaluated through :func:`dh_f`, so the Hurwitz-pole
    cancellation guard near the removable s = 1 applies here too (without it,
    F(1 + eps) silently lost ~log10(1/eps) digits; measured 2.3e-18 absolute
    error at eps = 1e-25, dps = 30, against 2.9e-32 with the guard).
    """
    def raw(z):
        return mp.power(mp.pi / 5, -(z + 1) / 2) * mp.gamma((z + 1) / 2) * _dh_raw(z)

    with mp.workdps(dps + _GUARD):
        s_w = _num(s)
        exceptional = (
            mp.im(s_w) == 0
            and mp.re(s_w) <= -1
            and mp.re(s_w) == mp.floor(mp.re(s_w))
            and int(mp.re(s_w)) % 2 == -1 % 2
        )
        if s_w == 1:
            value = mp.power(mp.pi / 5, -1) * mp.gamma(mp.mpf(1)) * dh_f(1, dps + _GUARD)
        elif exceptional:
            n_points = max(48, int(math.ceil(1.5 * dps)) + int(abs(float(mp.re(s_w)))))
            r = mp.mpf(1) / 2
            total = mp.mpc(0)
            for j in range(n_points):
                total += raw(s_w + r * mp.expjpi(mp.mpf(2 * j) / n_points))
            value = mp.re(total / n_points)
        else:
            # route f through dh_f, not _dh_raw: dh_f carries the cancellation
            # guard for s near the removable singularity at 1
            value = (
                mp.power(mp.pi / 5, -(s_w + 1) / 2)
                * mp.gamma((s_w + 1) / 2)
                * dh_f(s_w, dps=mp.dps)
            )
            if mp.im(s_w) == 0:
                value = mp.re(value)
    return _shrink(value, dps)


def dh_functional_equation_defect(s, dps: int = DPS_DEFAULT):
    """F(s) - F(1-s), identically zero: the Davenport-Heilbronn functional
    equation, with kappa freshly derived (never a hard-coded constant).

    Measured: |defect| < 1.1e-50 at dps = 50 over random s in
    [-2, 3] x [-20i, 20i]; the tests pin < 1e-25 at dps = 40 with margin.

    This is exactly the property that makes f a counterexample generator:
    the defect is as flat as zeta's own (``zeta.core.functional_equation_
    defect``), yet f violates RH.  Symmetry alone cannot see the difference.
    """
    with mp.workdps(dps + 2 * _GUARD):
        d = dps + 2 * _GUARD
        s_w = _num(s)
        value = completed_dh(s_w, d) - completed_dh(1 - s_w, d)
    return _shrink(value, dps)


def dh_mean_value_defect(s0, radius=0.25, dps: int = DPS_DEFAULT):
    """Numerical no-pole certificate:  (circle average of f) - f(s0).

    For f analytic on the closed disc |z - s0| <= radius the Gauss mean value
    theorem gives average = f(s0) exactly; a simple pole p inside the disc
    would instead leave a residue term res_f(p)/(p - s0).  Called with a disc
    that *contains s = 1* (e.g. s0 = 1.001, radius = 0.25) this verifies
    numerically that the four Hurwitz poles really cancel — i.e. that f is
    analytic in the strip and :func:`count_zeros_box` needs no pole-dodging,
    unlike the contour arguments for zeta itself.

    Measured: |defect| ~ 1e-50 at s0 = 1.001, radius 0.25, dps = 30 (the
    equispaced trapezoid rule on an analytic periodic integrand converges
    geometrically, cf. ``zeta.core._cauchy_mean``; the tests pin < 1e-25).
    """
    with mp.workdps(dps + 2 * _GUARD):
        d = dps + 2 * _GUARD
        s_c = _num(s0)
        r = mp.mpf(radius)
        n_points = max(64, int(math.ceil(3 * dps)))
        total = mp.mpc(0)
        for j in range(n_points):
            total += dh_f(s_c + r * mp.expjpi(mp.mpf(2 * j) / n_points), d)
        value = total / n_points - dh_f(s_c, d)
    return _shrink(value, dps)


# ---------------------------------------------------------------------------
# the Hardy-Z analogue on the critical line
# ---------------------------------------------------------------------------

def dh_theta(t, dps: int = DPS_DEFAULT):
    """The Riemann-Siegel-theta analogue for f:

        theta_f(t) = Im log Gamma(3/4 + it/2) - (t/2) log(pi/5),

    the continuous branch of the phase of the completing factor
    (pi/5)^{-(s+1)/2} Gamma((s+1)/2) at s = 1/2 + it (via ``loggamma``, so no
    wrapping at +-pi).  Grows like (t/2) log(5t/(2 pi e)): the conductor 5
    makes f's zeros on the line slightly denser than zeta's.
    """
    with mp.workdps(dps + _GUARD):
        tv = mp.mpf(mp.re(_num(t)))
        value = mp.im(mp.loggamma(mp.mpc(mp.mpf(3) / 4, tv / 2))) - tv / 2 * mp.log(
            mp.pi / 5
        )
    return _shrink(value, dps)


def Z_dh(t, dps: int = DPS_DEFAULT, tol_digits: int = 8):
    """The Hardy-Z analogue for f:  Z_f(t) = e^{i theta_f(t)} f(1/2 + it).

    Real for real t, because F(1/2 + it) is real — F(s) = F(1-s) plus the
    Schwarz reflection that f's *real* Dirichlet coefficients provide gives
    F(s) = conj(F(s)) on the line — and Z_f is F divided by the positive
    number |completing factor|.  So critical-line zeros of f are sign changes
    of Z_f, exactly as for zeta ... and yet the analogy stops there: for f the
    sign-change count genuinely undercounts the strip (:func:`find_offline_zero`).

    The numerical imaginary residue is checked to be pure round-off (below
    10^{-(dps+guard)+tol_digits} * max(|Re|, 1)) and discarded; a failure
    raises ``ValueError`` and means dps was too small, not that reality broke.
    """
    with mp.workdps(dps + _GUARD):
        tv = mp.mpf(mp.re(_num(t)))
        val = mp.expjpi(dh_theta(tv, dps + _GUARD) / mp.pi) * dh_f(
            mp.mpc(mp.mpf(1) / 2, tv), dps + _GUARD
        )
        re, im = mp.re(val), mp.im(val)
        tol = mp.mpf(10) ** (-(dps + _GUARD) + tol_digits) * max(abs(re), mp.mpf(1))
        if abs(im) >= tol:
            raise ValueError(
                f"Z_dh({t}): imaginary residue {mp.nstr(im, 8)} exceeds "
                f"{mp.nstr(tol, 8)}; increase dps"
            )
        value = re
    return _shrink(value, dps)


def _dh_mean_spacing(t):
    """Mean gap between consecutive line zeros of f near height t,
    2 pi / log(5 t / (2 pi)) (conductor-5 analogue of zeta's 2 pi/log(t/2 pi)).
    """
    t = max(mp.mpf(t), mp.mpf(10))
    return 2 * mp.pi / mp.log(5 * t / (2 * mp.pi))


def zeros_on_line(t0, t1, n_samples: int | None = None, dps: int = 15) -> int:
    """Sign-change count of Z_f on [t0, t1]: a **lower bound** for the number
    of zeros of f on the critical-line segment 1/2 + i[t0, t1].

    Grid default: 1/20 of the mean line-zero spacing 2 pi/log(5 t1/2 pi) at
    the top of the range.  A sign-change scan can miss zeros but never invent
    them, so when :func:`count_zeros_box` reports *more* zeros in the strip
    than this returns on the line — persistently, under grid refinement — the
    excess lives off the line.  For zeta that discrepancy never shows up
    (``zeta.zeros.verify_rh_up_to`` saturates the count); for f it does.
    """
    with mp.workdps(dps):
        a, b = mp.mpf(t0), mp.mpf(t1)
        if not b > a:
            raise ValueError("require t1 > t0")
        if n_samples is None:
            step = _dh_mean_spacing(b) / 20
            n_samples = int(mp.floor((b - a) / step)) + 2
        n_samples = max(int(n_samples), 2)
        count = 0
        prev = Z_dh(a, dps=dps)
        for k in range(1, n_samples):
            t = b if k == n_samples - 1 else a + (b - a) * mp.mpf(k) / (n_samples - 1)
            cur = Z_dh(t, dps=dps)
            if prev != 0 and cur != 0 and (prev > 0) != (cur > 0):
                count += 1
            prev = cur
        return count


# ---------------------------------------------------------------------------
# argument-principle zero counting in a rectangle
# ---------------------------------------------------------------------------

def _principal(d):
    """Reduce an angle difference to (-pi, pi]."""
    two_pi = 2 * mp.pi
    return d - two_pi * mp.nint(d / two_pi)


def _arg_variation(g, x0, x1, depth: int = 0, max_depth: int = 45):
    """Continuous variation of arg g along the segment x0 -> x1, by adaptive
    bisection (accepted only when the endpoint difference is < pi/3), as in
    ``zeta.zeros._arg_variation``."""
    d = _principal(mp.arg(g(x1)) - mp.arg(g(x0)))
    if abs(d) < mp.pi / 3 or depth >= max_depth:
        return d
    xm = (x0 + x1) / 2
    return _arg_variation(g, x0, xm, depth + 1, max_depth) + _arg_variation(
        g, xm, x1, depth + 1, max_depth
    )


def _edge_variation(g, x0, x1, step):
    """Arg variation along x0 -> x1 with a *forced* uniform pre-subdivision.

    The adaptive rule alone can be fooled: if the phase winds through a full
    2 pi + epsilon inside one segment, the endpoints differ by epsilon < pi/3
    and the winding is silently lost (observed: a height-8 box at t ~ 60 came
    back with winding number -1).  Along a vertical edge at sigma = -1 the
    phase of f turns at ~log(5t/2 pi) rad per unit height, so segments are
    forced shorter than ``step`` ~ 1/(2 log(5 t_max/2 pi)) — under 1/8 of a
    turn per segment — *before* the adaptive refinement runs.
    """
    n = max(1, int(mp.ceil(abs(x1 - x0) / step)))
    total = mp.mpf(0)
    prev = x0
    for k in range(1, n + 1):
        cur = x0 + (x1 - x0) * mp.mpf(k) / n
        total += _arg_variation(g, prev, cur)
        prev = cur
    return total


def count_zeros_box(s0, s1, dps: int = 20, fn=None, step=None) -> int:
    """Argument-principle count of zeros (with multiplicity) of f — or of any
    analytic ``fn`` — in the closed rectangle with opposite corners s0, s1:

        N = (1/2 pi) * (variation of arg along the boundary).

    No pole-dodging is needed for f: it is **entire** (the Hurwitz poles at
    s = 1 cancel — verified numerically by :func:`dh_mean_value_defect`, and
    guarded here by requiring every boundary sample to be finite).  Contrast
    ``zeta.zeros.N_of_T``, which must thread the pole of zeta at s = 1;
    counting with fn = ``zeta.core.xi`` (entire as well) needs no dodging and
    is how :func:`zeta_interface` reuses this routine.

    The winding is accumulated with the forced-subdivision + adaptive scheme
    of :func:`_edge_variation` and must come out an integer: a residual above
    1e-6 raises ``ArithmeticError`` (a zero sitting on the boundary, or an
    undersampled edge).  A zero *on* the contour makes the count ill-posed —
    nudge the box.

    Parameters: ``fn`` defaults to f at the working precision; ``step`` is the
    forced subdivision length (default matched to the phase-turn rate of f at
    the box height, ~1/8 turn per segment).
    """
    with mp.workdps(dps):
        z0, z1 = _num(s0), _num(s1)
        a, b = min(mp.re(z0), mp.re(z1)), max(mp.re(z0), mp.re(z1))
        c, d = min(mp.im(z0), mp.im(z1)), max(mp.im(z0), mp.im(z1))
        if a == b or c == d:
            raise ValueError("count_zeros_box needs a genuine rectangle")
        if fn is None:
            work = mp.dps

            def fn(z, _w=work):
                return dh_f(z, dps=_w)

        def g(z):
            v = fn(z)
            if not mp.isfinite(v):
                raise ArithmeticError(
                    f"count_zeros_box: fn({mp.nstr(z, 10)}) is not finite; "
                    "the contour must avoid poles"
                )
            return v

        if step is None:
            tmax = max(abs(c), abs(d), mp.mpf(10))
            step = mp.mpf(1) / (2 * mp.log(5 * tmax / (2 * mp.pi)))
        corners = [mp.mpc(a, c), mp.mpc(b, c), mp.mpc(b, d), mp.mpc(a, d), mp.mpc(a, c)]
        total = mp.mpf(0)
        for i in range(4):
            total += _edge_variation(g, corners[i], corners[i + 1], step)
        winding = total / (2 * mp.pi)
        n = int(mp.nint(winding))
        if abs(winding - n) > mp.mpf("1e-6"):
            raise ArithmeticError(
                f"count_zeros_box: winding {mp.nstr(winding, 10)} is not an "
                "integer; a zero is on (or hugging) the contour — nudge the box"
            )
        return n


# ---------------------------------------------------------------------------
# the payoff: an actual off-critical-line zero
# ---------------------------------------------------------------------------

def _stable_line_count(t0, t1, dps: int) -> int:
    """zeros_on_line with the grid doubled until the count stops changing."""
    n = None
    with mp.workdps(dps):
        step = _dh_mean_spacing(mp.mpf(t1)) / 20
        n = max(int(mp.floor((mp.mpf(t1) - mp.mpf(t0)) / step)) + 2, 8)
    prev = zeros_on_line(t0, t1, n_samples=n, dps=dps)
    for _ in range(3):
        n = 2 * (n - 1) + 1
        cur = zeros_on_line(t0, t1, n_samples=n, dps=dps)
        if cur == prev:
            return cur
        prev = cur
    return prev


def find_offline_zero(
    t_lo=60.0,
    t_hi=100.0,
    window=8.0,
    dps: int = DPS_DEFAULT,
    sigma_lo=-1.0,
    sigma_hi=2.0,
    min_offline=0.05,
    residual="1e-25",
):
    """Locate, verify, and return an off-critical-line zero of f.

    The hunt is ``scripts/02_find_zeros.py`` run in reverse.  For zeta the
    Turing-style argument is: sign changes on the line == argument-principle
    count in the strip, hence RH holds below T.  Here we *look for the
    failure* of that equality:

    1. **Smoking gun.**  Slide a height window [t0, t0 + window] up from
       ``t_lo``; in each, compare ``count_zeros_box`` over
       [sigma_lo, sigma_hi] x [t0, t1] with a grid-refined
       :func:`zeros_on_line`.  (All complex zeros of f live in that strip:
       sum_{n>=2} |a_n| n^{-2} = 0.2666... < 1 pins f away from 0 for
       Re s >= 2, and the functional equation reflects that into
       Re s <= -1 — both facts are numerically verified in the tests.)
       The first window with box > line holds off-line zeros; they arrive in
       mirror pairs rho, 1 - conj(rho), so the excess is even.
    2. **Bisect.**  Halve the window in t until it is <= 1 wide while keeping
       box - line > 0, then count the right half-box
       [1/2 + min_offline, sigma_hi]: the mirror symmetry puts half the
       excess there, isolated from the line zeros.
    3. **Polish.**  Take the minimum of |f| on a 21x21 grid over that
       half-box as the seed for ``mp.findroot`` at dps + 20.
    4. **Verify** (all enforced, ``ArithmeticError`` otherwise):
       |f(rho)| < ``residual`` (default 1e-25), |Re rho - 1/2| > min_offline,
       and the winding number around a side-0.2 box centred on rho is
       exactly 1.

    With the defaults this searches 60 < t < 100 (the literature places the
    first off-line zeros below height ~100) and finds

        rho = 0.8085171824566373855533519606... + 85.6993484853775921719292677...i
        (window [84, 92]: box = 5, line = 3; |f(rho)| ~ 1e-49 at dps = 30),

    the value pinned in :data:`OFFLINE_ZERO_RE` / :data:`OFFLINE_ZERO_IM`.
    Raises ``ArithmeticError`` if no discrepancy window is found — widen the
    range.  Returns the zero as an ``mpc`` at ``dps`` digits.
    """
    count_dps = min(max(20, dps // 2 + 10), dps + _GUARD)
    with mp.workdps(dps + _GUARD):
        t0 = mp.mpf(t_lo)
        t_top = mp.mpf(t_hi)
        w = mp.mpf(window)
        s_lo, s_hi = mp.mpf(sigma_lo), mp.mpf(sigma_hi)
        off = mp.mpf(min_offline)
        res_tol = mp.mpf(residual)

        def box_count(a, b, ta, tb):
            return count_zeros_box(
                mp.mpc(a, ta), mp.mpc(b, tb), dps=count_dps
            )

        # 1. find a discrepancy window
        found = None
        while t0 < t_top:
            t1 = min(t0 + w, t_top)
            nb = box_count(s_lo, s_hi, t0, t1)
            nl = _stable_line_count(t0, t1, dps=15)
            if nb > nl:
                found = (t0, t1)
                break
            t0 = t1
        if found is None:
            raise ArithmeticError(
                f"no box/line count discrepancy for {t_lo} < t < {t_hi}; "
                "widen the search range"
            )

        # 2. bisect the window in t, keeping a discrepancy half
        ta, tb = found
        while tb - ta > 1:
            tm = (ta + tb) / 2
            kept = None
            for (u, v) in ((ta, tm), (tm, tb)):
                if box_count(s_lo, s_hi, u, v) > _stable_line_count(u, v, dps=15):
                    kept = (u, v)
                    break
            if kept is None:
                # the pair straddles tm: widen the halves by a nudge instead
                break
            ta, tb = kept

        # right half-box, clear of the critical line
        ra, rb = mp.mpf(1) / 2 + off, s_hi
        n_right = box_count(ra, rb, ta, tb)
        if n_right < 1:
            # excess zero(s) sit left of the line: mirror the box
            ra, rb = s_lo, mp.mpf(1) / 2 - off
            n_right = box_count(ra, rb, ta, tb)
        if n_right < 1:
            raise ArithmeticError(
                "discrepancy window found but no zero clear of the line; "
                "decrease min_offline"
            )

        # 3. seed from a grid minimum of |f|, then polish
        best_v, best_s = None, None
        for i in range(21):
            for j in range(21):
                z = mp.mpc(
                    ra + (rb - ra) * mp.mpf(i) / 20, ta + (tb - ta) * mp.mpf(j) / 20
                )
                v = abs(dh_f(z, dps=count_dps))
                if best_v is None or v < best_v:
                    best_v, best_s = v, z
        polish_dps = dps + 2 * _GUARD
        with mp.workdps(polish_dps):
            root = mp.findroot(lambda z: dh_f(z, dps=polish_dps), best_s)
            fval = abs(dh_f(root, dps=polish_dps))

        # 4. verify: residual, distance from the line, and a 1-zero certificate
        if not fval < res_tol:
            raise ArithmeticError(
                f"polished root has |f| = {mp.nstr(fval, 5)} >= {residual}"
            )
        if not abs(mp.re(root) - mp.mpf(1) / 2) > off:
            raise ArithmeticError(
                f"root {mp.nstr(root, 20)} is not off the line by > {min_offline}"
            )
        h = mp.mpf(1) / 10
        if count_zeros_box(root - mp.mpc(h, h), root + mp.mpc(h, h), dps=count_dps) != 1:
            raise ArithmeticError("winding certificate around the root failed")
        value = root
    return _shrink(value, dps)


# ---------------------------------------------------------------------------
# the falsification harness
# ---------------------------------------------------------------------------

def zeta_interface(dps: int = DPS_DEFAULT) -> dict:
    """The zeta-like interface for **zeta itself** (via :mod:`zeta.core`):

    ``name``; ``coefficient(n)`` — Dirichlet coefficients (all 1 for zeta:
    the Lambda-structure of log zeta lives downstream of a_n = 1 *because*
    of the Euler product); ``completed(s)`` — the entire completion (xi);
    ``fe_defect(s)`` — completed(s) - completed(1-s); ``Z(t)`` — the real
    Hardy function; ``zeros_on_line(t0, t1)`` — sign-change count;
    ``count_zeros_box(s0, s1)`` — argument-principle count (of xi, entire, so
    the generic contour routine applies unchanged).
    """
    from .core import hardy_Z_sign_changes

    def _zeta_coefficient(n, _d=dps):
        if int(n) < 1:
            raise ValueError("Dirichlet coefficients are indexed from n = 1")
        return _shrink(mp.mpf(1), _d)

    return {
        "name": "riemann_zeta",
        "coefficient": _zeta_coefficient,
        "completed": lambda s, _d=dps: xi(s, dps=_d),
        "fe_defect": lambda s, _d=dps: functional_equation_defect(s, dps=_d),
        "Z": lambda t, _d=dps: hardy_Z(t, dps=_d),
        "zeros_on_line": lambda t0, t1, _d=dps: len(
            hardy_Z_sign_changes(t0, t1, n_samples=max(int(20 * (t1 - t0)) + 2, 8),
                                 dps=15, cache=False)
        ),
        "count_zeros_box": lambda s0, s1, _d=dps: count_zeros_box(
            s0, s1, dps=min(_d, 20), fn=lambda z: xi(z, dps=min(_d, 20))
        ),
    }


def dh_interface(dps: int = DPS_DEFAULT) -> dict:
    """The same interface for the Davenport-Heilbronn function (see
    :func:`zeta_interface` for the field contract)."""
    return {
        "name": "davenport_heilbronn",
        "coefficient": lambda n, _d=dps: dh_coefficient(n, dps=_d),
        "completed": lambda s, _d=dps: completed_dh(s, dps=_d),
        "fe_defect": lambda s, _d=dps: dh_functional_equation_defect(s, dps=_d),
        "Z": lambda t, _d=dps: Z_dh(t, dps=_d),
        "zeros_on_line": lambda t0, t1, _d=dps: zeros_on_line(t0, t1, dps=15),
        "count_zeros_box": lambda s0, s1, _d=dps: count_zeros_box(
            s0, s1, dps=min(_d, 20)
        ),
    }


def claim_functional_equation(iface: dict) -> bool:
    """Claim: "the completed function satisfies F(s) = F(1-s)" — measured as
    |fe_defect| < 1e-20 at three asymmetric sample points.

    **Passes for both** zeta and Davenport-Heilbronn: the claim does not
    distinguish them, so no argument built from it alone can prove RH.
    """
    pts = [mp.mpc(mp.mpf(3), mp.mpf(4)), mp.mpc(mp.mpf(-1) / 4, mp.mpf(21) / 2),
           mp.mpc(mp.mpf(7) / 5, mp.mpf(-3))]
    tol = mp.mpf("1e-20")
    return all(abs(iface["fe_defect"](s)) < tol for s in pts)


def claim_multiplicativity(iface: dict) -> bool:
    """Claim: "the Dirichlet coefficients are multiplicative:
    a_{mn} = a_m * a_n for coprime m, n" — the fingerprint of an Euler
    product, tested on the coprime pairs (2,3), (2,7), (3,7), (2,9), (3,4).

    **Passes for zeta** (a_n = 1 identically — and the Lambda-structure of
    the explicit formula rests on exactly this multiplicativity) and **fails
    for Davenport-Heilbronn**: a_6 = a_1 = 1 but a_2 a_3 = -kappa^2 =
    -0.0807...; a_14 = a_4 = -1 but a_2 a_7 = +kappa^2.  (Some pairs survive
    by accident of the period-5 pattern — (3,4) gives a_12 = kappa = a_3 a_4 —
    which is why the claim quantifies over several.)  This is the crisp,
    computable answer to gate #3's question "where exactly does
    Davenport-Heilbronn fail to embed?": at the Euler product.
    """
    pairs = [(2, 3), (2, 7), (3, 7), (2, 9), (3, 4)]
    tol = mp.mpf("1e-12")
    a = iface["coefficient"]
    return all(abs(a(m * n) - a(m) * a(n)) < tol for (m, n) in pairs)


def battery(claim_fn, dps: int = DPS_DEFAULT) -> dict:
    """Evaluate a claimed structural property against BOTH zeta and the
    Davenport-Heilbronn function — the falsification harness of gate #3
    (docs/09) in executable form.

    ``claim_fn`` receives a zeta-like interface dict (see
    :func:`zeta_interface`) and must return truthy/falsy.  Returns::

        {"claim": <name>, "riemann_zeta": bool, "davenport_heilbronn": bool,
         "distinguishes": bool}

    Reading the verdict: a claim that **passes for both** (e.g.
    :func:`claim_functional_equation`) cannot be the load-bearing step of an
    RH proof — Davenport-Heilbronn satisfies it and violates RH.  A claim
    that **distinguishes** them (e.g. :func:`claim_multiplicativity`) is at
    least a candidate for where a real proof must live.  This is the
    fastest known way to kill a proposed proof: find the step f satisfies
    too (docs/08 section 4.1).
    """
    results = {}
    for iface in (zeta_interface(dps), dh_interface(dps)):
        results[iface["name"]] = bool(claim_fn(iface))
    return {
        "claim": getattr(claim_fn, "__name__", repr(claim_fn)),
        "riemann_zeta": results["riemann_zeta"],
        "davenport_heilbronn": results["davenport_heilbronn"],
        "distinguishes": results["riemann_zeta"] != results["davenport_heilbronn"],
    }
