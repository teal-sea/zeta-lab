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

**The Epstein half of the family, added second.**  Gate #3 asks that a
structure be ungrantable to Davenport-Heilbronn *and to generic Epstein zeta
functions*, but for a long time only the first was computable here — the module
carried the Epstein name without an Epstein zeta in it.  It now has one:
``zeta_Q(s) = sum_{(m,k) != 0} Q(m,k)^{-s}`` for a positive-definite binary
form, continued to the whole plane by splitting the Mellin transform of the
form's theta series at ``t = 1`` (:func:`epstein_completed`).  The
transformation used for the split, ``theta_Q(1/t) = (t/sqrt(d)) theta_{Q^-1}(t)``
with ``d = |D|/4``, was *measured* before use rather than recalled, and agrees
to 12 digits at four values of ``t``.

For a discriminant of class number greater than one the individual ``zeta_Q``
reproduces the whole counterexample profile by a route sharing no code with
``f``: a functional equation, real Dirichlet coefficients (the representation
counts, :func:`epstein_representation_count`), a real Hardy-style ``Z``
(:func:`Z_epstein`), and no Euler product — for ``D = -23`` the principal form
already has ``r(2) = r(3) = 0`` while ``r(6) = 4``.  Davenport and Heilbronn
proved such ``zeta_Q`` have zeros off the critical line; that is quoted, not
recomputed here.

One caution recorded at the point of use: because the opposite form
``(c, -b, a)`` represents the same integers as ``(a, b, c)``, the
incomplete-gamma representation is *manifestly* symmetric under ``s -> 1-s``,
so :func:`epstein_functional_equation_defect` is zero by construction and
checks nothing.  The validation that can fail is
:func:`epstein_class_group_defect`, which tests
``sum_Q zeta_Q(s) = w zeta(s) L(s, chi_D)`` against mpmath's ``zeta`` and a
Hurwitz-zeta character sum — disjoint code — and comes in below 1e-18 at
``D = -4, -15, -23``.

**The third rival, added because the first two could not see an Euler
product.**  Davenport-Heilbronn and the Epstein zetas are both linear
combinations of legitimate Euler products, and what each lacks is a scalar
Euler product of its own.  That makes them silent on any claim whose content
*is* the Euler product, so such a claim passes gate #3 without having been
tested.  The symmetric shifted product ``W_a(s) = zeta(s+a) zeta(s-a)``, with
completion ``Xi_a(s) = xi(s+a) xi(s-a)``, closes that hole: it has a scalar
Euler product, non-negative multiplicative coefficients, non-negative
log-derivative coefficients, an exact ``Xi_a(1-s) = Xi_a(s)``, a real Hardy
function, and zeros on ``Re s = 1/2 +- a`` by Hardy's theorem alone.  Its
scope caveat is stated where it is built, above
:data:`SHIFTED_PRODUCT_SHIFT`, and it is not optional reading: ``W_a`` is
outside the Selberg class, so a claim it shares is not thereby irrelevant to
RH, it is shown to be blind to a shift.

Honest scope: nothing here proves anything about *zeta's* zeros; the module
demonstrates, to stated numerical precision, that specific rival functions
share the symmetry and violate RH.  Conventions follow :mod:`zeta.core`:
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
    "epstein_reduced_forms",
    "epstein_representation_count",
    "epstein_completed",
    "epstein_zeta",
    "epstein_functional_equation_defect",
    "epstein_class_group_defect",
    "Z_epstein",
    "SHIFTED_PRODUCT_SHIFT",
    "shifted_coefficient",
    "shifted_completed",
    "shifted_functional_equation_defect",
    "shifted_log_derivative_coefficient",
    "Z_shifted",
    "shifted_interface",
    "log_derivative_coefficients",
    "zeta_interface",
    "dh_interface",
    "epstein_interface",
    "battery",
    "claim_functional_equation",
    "claim_multiplicativity",
    "claim_euler_product_positivity",
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

# ---------------------------------------------------------------------------
# Epstein zeta functions of positive-definite binary quadratic forms
#
# docs/09 gate #3 asks that a proposed structure be ungrantable to the
# Davenport-Heilbronn function *and to generic Epstein zeta functions*.  Only
# the first was computable here; this section supplies the second.  For a
# discriminant with class number greater than one the individual zeta_Q has a
# functional equation, real Dirichlet coefficients, a real Hardy-style Z, and
# no Euler product -- the same counterexample profile as f, reached by a
# completely different construction.
# ---------------------------------------------------------------------------

def epstein_reduced_forms(discriminant: int) -> tuple[tuple[int, int, int], ...]:
    """Reduced positive-definite forms ``(a, b, c)`` of the given discriminant.

    Reduced means ``|b| <= a <= c`` with ``b >= 0`` whenever ``|b| == a`` or
    ``a == c``; each class of forms contains exactly one such representative,
    so the length of the result is the class number ``h(D)``.
    """

    D = int(discriminant)
    if D >= 0 or D % 4 not in (0, 1):
        raise ValueError("discriminant must be negative and congruent to 0 or 1 mod 4")
    forms = []
    limit = int(mp.floor(mp.sqrt(mp.mpf(-D) / 3))) + 1
    for b in range(-limit, limit + 1):
        if (b * b - D) % 4:
            continue
        ac4 = b * b - D
        if ac4 % 4:
            continue
        ac = ac4 // 4
        for a in range(max(1, abs(b)), int(mp.floor(mp.sqrt(mp.mpf(ac)))) + 1):
            if ac % a:
                continue
            c = ac // a
            if not (abs(b) <= a <= c):
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            forms.append((a, b, c))
    return tuple(sorted(set(forms)))


def epstein_representation_count(n: int, form: tuple[int, int, int]) -> int:
    """Dirichlet coefficient of ``zeta_Q``: the number of ``(m, k) != (0, 0)``
    with ``Q(m, k) = n``.

    These are **not** multiplicative for a form outside the principal class,
    which is exactly the Euler-product failure gate #3 turns on.  For the
    principal form of discriminant ``-23`` the failure is already visible at
    ``n = 6``: ``r(2) = r(3) = 0`` but ``r(6) = 2``.
    """

    a, b, c = (int(v) for v in form)
    n = int(n)
    if n < 1:
        raise ValueError("representation counts are indexed from n = 1")
    disc = b * b - 4 * a * c
    if disc >= 0:
        raise ValueError("form must be positive definite (negative discriminant)")
    bound = int(mp.floor(mp.sqrt(mp.mpf(4 * a * n) / (-disc)))) + 1
    total = 0
    for k in range(-bound, bound + 1):
        # a m^2 + (b k) m + (c k^2 - n) = 0
        rad = b * b * k * k - 4 * a * (c * k * k - n)
        if rad < 0:
            continue
        root = int(mp.floor(mp.sqrt(mp.mpf(rad)) + mp.mpf("0.5")))
        if root * root != rad:
            continue
        for sign in ((1,) if root == 0 else (1, -1)):
            num = -b * k + sign * root
            if num % (2 * a) == 0:
                m = num // (2 * a)
                if (m, k) != (0, 0) and a * m * m + b * m * k + c * k * k == n:
                    total += 1
    return total


def _epstein_lattice(a, b, c, dps: int):
    """Lattice radius large enough that the omitted tail is below the tolerance."""

    lam = ((a + c) - mp.sqrt((a - c) ** 2 + b ** 2)) / 2
    radius = int(mp.ceil(mp.sqrt((dps + 6) * mp.log(10) / mp.pi / lam))) + 2
    return [
        (m, k)
        for m in range(-radius, radius + 1)
        for k in range(-radius, radius + 1)
        if (m, k) != (0, 0)
    ]


def epstein_completed(s, form: tuple[int, int, int], dps: int = DPS_DEFAULT):
    """``Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s)`` with ``d = |D|/4``.

    Evaluated by splitting the Mellin transform of the form's theta series at
    ``t = 1`` and applying the measured transformation
    ``theta_Q(1/t) = (t/sqrt(d)) theta_{Q^-1}(t)``, exactly the route
    ``docs/03`` takes for ``xi``.  Each half becomes an upper incomplete gamma
    over lattice points, so no quadrature is involved and the representation is
    valid for every ``s`` apart from the poles at ``0`` and ``1``.
    """

    a, b, c = (int(v) for v in form)
    if b * b - 4 * a * c >= 0 or a <= 0:
        raise ValueError("form must be positive definite")
    with mp.workdps(dps + _GUARD):
        s = _num(s)
        af, bf, cf = mp.mpf(a), mp.mpf(b), mp.mpf(c)
        d = af * cf - bf ** 2 / 4
        ai, bi, ci = cf / d, -bf / d, af / d
        first = mp.fsum(
            mp.gammainc(s, mp.pi * (af * m * m + bf * m * k + cf * k * k))
            / (mp.pi * (af * m * m + bf * m * k + cf * k * k)) ** s
            for (m, k) in _epstein_lattice(af, bf, cf, mp.dps)
        )
        second = mp.fsum(
            mp.gammainc(1 - s, mp.pi * (ai * m * m + bi * m * k + ci * k * k))
            / (mp.pi * (ai * m * m + bi * m * k + ci * k * k)) ** (1 - s)
            for (m, k) in _epstein_lattice(ai, bi, ci, mp.dps)
        )
        mellin = first + second / mp.sqrt(d) + 1 / (mp.sqrt(d) * (s - 1)) - 1 / s
        return _shrink(d ** (s / 2) * mellin, dps)


def epstein_zeta(s, form: tuple[int, int, int], dps: int = DPS_DEFAULT):
    """``zeta_Q(s) = sum_{(m,k) != 0} Q(m,k)^{-s}``, continued to all ``s``."""

    a, b, c = (int(v) for v in form)
    with mp.workdps(dps + _GUARD):
        s = _num(s)
        d = mp.mpf(a) * c - mp.mpf(b) ** 2 / 4
        value = epstein_completed(s, form, dps=mp.dps) * mp.pi ** s
        return _shrink(value / (mp.sqrt(d) ** s * mp.gamma(s)), dps)


def epstein_functional_equation_defect(
    s, form: tuple[int, int, int], dps: int = DPS_DEFAULT
):
    """``Lambda_Q(s) - Lambda_Q(1-s)``, which is **structurally zero here**.

    The opposite form ``(c, -b, a)`` represents the same integers as
    ``(a, b, c)`` — substitute ``(m, k) -> (k, m)`` — so ``zeta_Q`` equals the
    zeta function of its own inverse class and the functional equation closes
    on ``Q`` itself.  But that same fact makes the incomplete-gamma
    representation in :func:`epstein_completed` manifestly symmetric under
    ``s -> 1-s``, so this quantity vanishes *by construction* and returns
    exactly zero rather than a round-off residue.

    It is therefore **not** an independent check of the implementation, and
    must not be read as one: unlike
    :func:`dh_functional_equation_defect`, a bug in the lattice sums would not
    show up here.  The honest validations are
    :func:`epstein_class_group_defect`, which tests the continuation against a
    completely separate computation, and agreement with the defining sum in the
    region where that sum converges.  The function exists to satisfy the
    interface contract of :func:`zeta_interface`.
    """

    with mp.workdps(dps + _GUARD):
        s = _num(s)
        left = epstein_completed(s, form, dps=mp.dps)
        right = epstein_completed(1 - s, form, dps=mp.dps)
        return _shrink(left - right, dps)


def epstein_class_group_defect(s, discriminant: int, dps: int = DPS_DEFAULT):
    """Measured defect of ``sum_Q zeta_Q(s) = w * zeta(s) * L(s, chi_D)``.

    The sum runs over the reduced forms of the discriminant and ``w`` is the
    number of units (``2`` for ``D < -4``, ``4`` at ``-4``, ``6`` at ``-3``).
    The right-hand side is built from mpmath's ``zeta`` and a Hurwitz-zeta
    evaluation of the quadratic character's L-function, so it shares no code
    with the lattice sums on the left.  This is the check that would actually
    catch an error in :func:`epstein_completed`, and unlike
    :func:`epstein_functional_equation_defect` it is not satisfied by
    construction.
    """

    from sympy import kronecker_symbol

    D = int(discriminant)
    forms = epstein_reduced_forms(D)
    units = 6 if D == -3 else 4 if D == -4 else 2
    with mp.workdps(dps + _GUARD):
        s = _num(s)
        left = mp.fsum(epstein_zeta(s, form, dps=mp.dps) for form in forms)

        modulus = abs(D)
        L = modulus ** (-s) * mp.fsum(
            int(kronecker_symbol(D, r)) * mp.zeta(s, mp.mpf(r) / modulus)
            for r in range(1, modulus + 1)
        )
        return _shrink(left - units * mp.zeta(s) * L, dps)


def Z_epstein(t, form: tuple[int, int, int], dps: int = DPS_DEFAULT):
    """The Hardy-style real function ``Lambda_Q(1/2 + it)``.

    Real for real ``t``: the coefficients are real so ``Lambda_Q(conj s)`` is
    the conjugate of ``Lambda_Q(s)``, and the functional equation identifies
    that conjugate with ``Lambda_Q(s)`` on the critical line.  The imaginary
    residue is checked to be round-off and discarded.
    """

    with mp.workdps(dps + _GUARD):
        value = epstein_completed(mp.mpc(mp.mpf(1) / 2, _num(t)), form, dps=mp.dps)
        if abs(mp.im(value)) > mp.mpf(10) ** (-(dps - 2)) * max(abs(mp.re(value)), 1):
            raise ValueError(
                f"Z_epstein: imaginary residue {mp.im(value)} exceeds round-off"
            )
        return _shrink(mp.re(value), dps)


def epstein_interface(
    form: tuple[int, int, int], dps: int = DPS_DEFAULT
) -> dict:
    """The zeta-like interface for an Epstein zeta (see :func:`zeta_interface`)."""

    a, b, c = (int(v) for v in form)

    def _line_count(t0, t1, _f=(a, b, c), _d=dps):
        samples = max(int(8 * (t1 - t0)) + 2, 8)
        grid = [t0 + (t1 - t0) * i / (samples - 1) for i in range(samples)]
        values = [Z_epstein(t, _f, dps=min(_d, 15)) for t in grid]
        return sum(
            1
            for left, right in zip(values, values[1:])
            if left != 0 and right != 0 and mp.sign(left) != mp.sign(right)
        )

    return {
        "name": f"epstein_{a}_{b}_{c}",
        "coefficient": lambda n, _f=(a, b, c): mp.mpf(
            epstein_representation_count(int(n), _f)
        ),
        "completed": lambda s, _f=(a, b, c), _d=dps: epstein_completed(s, _f, dps=_d),
        "fe_defect": lambda s, _f=(a, b, c), _d=dps: (
            epstein_functional_equation_defect(s, _f, dps=_d)
        ),
        "Z": lambda t, _f=(a, b, c), _d=dps: Z_epstein(t, _f, dps=_d),
        "zeros_on_line": _line_count,
        "count_zeros_box": lambda s0, s1, _f=(a, b, c), _d=dps: count_zeros_box(
            s0, s1, dps=min(_d, 20), fn=lambda z: epstein_completed(z, _f, dps=min(_d, 20))
        ),
    }


# ---------------------------------------------------------------------------
# the third rival: a counterexample that *does* have an Euler product
# ---------------------------------------------------------------------------
#
# Davenport-Heilbronn and the Epstein zetas are both linear combinations of
# legitimate Euler products, and what each lacks is a scalar Euler product of
# its own.  That makes them silent on any claim whose content *is* the Euler
# product: multiplicativity, or the non-negativity of the coefficients of
# ``log F``.  A claim of that shape passes gate #3 without having been tested
# at all, which is the same failure mode as a battery of rivals too weak to
# say no.
#
# The symmetric shifted product closes that hole:
#
#     W_a(s)  = zeta(s+a) zeta(s-a)          Xi_a(s) = xi(s+a) xi(s-a)
#
# for real ``a``.  It has a scalar Euler product,
# ``prod_p (1-p^{-s-a})^{-1} (1-p^{-s+a})^{-1}``; real, non-negative,
# multiplicative Dirichlet coefficients; non-negative log-derivative
# coefficients ``Lambda(n)(n^a + n^{-a})``; an exact ``Xi_a(1-s) = Xi_a(s)``;
# and a real Hardy-style function on the critical line.  Its zeros are the
# points ``rho +- a``, so **Hardy's theorem alone** puts infinitely many of
# them on ``Re s = 1/2 + a`` and ``Re s = 1/2 - a``.  Nothing about zeta's
# remaining zeros is assumed for that sentence, which is what makes it usable
# as a rival rather than as a conditional one.
#
# **Scope, stated because it is the first thing a referee should ask.**  W_a
# is not in the Selberg class: its coefficients grow like ``n^a``, so the
# Ramanujan axiom fails, its Dirichlet series converges only for
# ``Re s > 1 + a``, its gamma factor has ``Re mu_j = -a/2 < 0``, and its poles
# sit at ``1 +- a`` rather than at 1.  Those are four faces of one shift, and
# **none of them is a positivity**.  So the rival does not say that
# multiplicativity is irrelevant to RH.  It says that a mechanism resting on
# multiplicativity, or on any positivity derived from the Euler product, must
# *also* use the normalisation, and must say where.  A claim this rival shares
# has not been shown to distinguish; it has been shown to be blind to a shift.
#
# The construction is not new.  The one-sided ``zeta(s - delta)`` is already in
# this tree at ``docs/18`` section 6 and ``docs/24`` section 6, which cite
# Conrey-Ghosh (1992, remark 2) for the observation; the symmetric product is
# the standard reason the Selberg class carries a Ramanujan axiom.  What is
# new here is only that the battery now contains one.

#: Shift of the symmetric product rival.  ``1/4`` keeps its zeros inside the
#: critical strip (they sit on ``Re s = 1/4`` and ``Re s = 3/4``), keeps its
#: Dirichlet series convergent for ``Re s > 5/4``, and keeps its poles
#: (``s = 1 +- 1/4``) off the critical line.
SHIFTED_PRODUCT_SHIFT = mp.mpf(1) / 4


def _von_mangoldt(n: int):
    """``Lambda(n)``: ``log p`` on prime powers, 0 elsewhere."""
    from sympy import factorint

    factors = factorint(int(n))
    if len(factors) != 1:
        return mp.mpf(0)
    ((prime, _),) = factors.items()
    return mp.log(prime)


def shifted_coefficient(n: int, shift=SHIFTED_PRODUCT_SHIFT, dps: int = DPS_DEFAULT):
    """Dirichlet coefficient of ``W_a``: ``a_n = sum_{de=n} d^{-a} e^{a}``.

    Real, positive, and multiplicative, with ``a_1 = 1``.  They grow like
    ``n^a`` (``a_60 = 14.02`` at ``a = 1/4``, against ``d(60) = 12``), which is
    the Ramanujan violation named in the section comment above.  That growth is
    the whole of what keeps ``W_a`` outside the Selberg class, and so the whole
    of what keeps it from being a counterexample to the Grand Riemann
    Hypothesis rather than a rival for gate #3.
    """
    n = int(n)
    if n < 1:
        raise ValueError("Dirichlet coefficients are indexed from n = 1")
    with mp.workdps(dps + _GUARD):
        a = _num(shift)
        total = mp.fsum(
            mp.mpf(d) ** (-a) * mp.mpf(n // d) ** a
            for d in range(1, n + 1)
            if n % d == 0
        )
        return _shrink(total, dps)


def shifted_completed(s, shift=SHIFTED_PRODUCT_SHIFT, dps: int = DPS_DEFAULT):
    """``Xi_a(s) = xi(s+a) xi(s-a)``, entire, with ``Xi_a(1-s) = Xi_a(s)``.

    Entire because ``xi`` is: the poles of ``zeta(s+a)`` at ``s = 1-a`` and of
    ``zeta(s-a)`` at ``s = 1+a`` are removed by their own completions, and the
    trivial zeros of both factors sit outside the critical strip.  So the zeros
    of ``Xi_a`` inside the strip are exactly the points ``rho +- a``, and an
    argument-principle count of ``Xi_a`` in a box is a zero count with no pole
    correction.
    """
    with mp.workdps(dps + _GUARD):
        s = _num(s)
        a = _num(shift)
        value = xi(s + a, dps=mp.dps) * xi(s - a, dps=mp.dps)
        return _shrink(value, dps)


def shifted_functional_equation_defect(
    s, shift=SHIFTED_PRODUCT_SHIFT, dps: int = DPS_DEFAULT
):
    """Measured ``Xi_a(s) - Xi_a(1-s)``.

    Honest scope, in the same spirit as the note on
    :func:`epstein_functional_equation_defect`: this is not an independent
    check.  ``Xi_a(1-s) = xi(1-s+a) xi(1-s-a)`` becomes ``xi(s-a) xi(s+a)`` by
    applying ``xi(1-z) = xi(z)`` twice, so the defect measured here is zeta's
    own functional-equation defect (:func:`zeta.core.functional_equation_defect`)
    carried through a product.  It is reported because the interface contract
    asks for it, and because a rival whose symmetry were only asserted would
    be worth nothing.
    """
    with mp.workdps(dps + _GUARD):
        s = _num(s)
        left = shifted_completed(s, shift, dps=mp.dps)
        right = shifted_completed(1 - s, shift, dps=mp.dps)
        return _shrink(left - right, dps)


def shifted_log_derivative_coefficient(
    n: int, shift=SHIFTED_PRODUCT_SHIFT, dps: int = DPS_DEFAULT
):
    """``Lambda_{W_a}(n) = Lambda(n) (n^a + n^{-a}) >= 0``, in closed form.

    The closed form is a derivation; :func:`log_derivative_coefficients` gets
    the same numbers from the Dirichlet coefficients alone, without ever
    seeing an Euler product.  The two agree to 1.3e-15 over ``n <= 60`` at
    ``dps = 30``, which is the cross-check the house style asks for.
    """
    n = int(n)
    with mp.workdps(dps + _GUARD):
        a = _num(shift)
        lam = _von_mangoldt(n)
        if lam == 0:
            return _shrink(mp.mpf(0), dps)
        return _shrink(lam * (mp.mpf(n) ** a + mp.mpf(n) ** (-a)), dps)


def Z_shifted(t, shift=SHIFTED_PRODUCT_SHIFT, dps: int = DPS_DEFAULT):
    """The Hardy-style real function ``Xi_a(1/2 + it)``.

    Real for real ``t`` by the same argument as :func:`Z_epstein`: the
    coefficients are real, so conjugation reflects ``s`` across the real axis,
    and the functional equation identifies the reflection with the original on
    the critical line.  The imaginary residue is checked and discarded.

    Note what this function does *not* have: zeros.  Under RH for zeta,
    ``Xi_a`` has none on its own critical line at all, because its zeros are at
    ``Re s = 1/2 +- a``.  A sign-change count of ``Z_shifted`` against an
    argument-principle count of :func:`shifted_completed` in the same window is
    therefore the starkest form of the gate-#3 measurement in this module: at
    ``a = 1/4`` the box ``[0.1, 0.9] x [10, 25]`` holds four zeros and the line
    holds none.
    """
    with mp.workdps(dps + _GUARD):
        value = shifted_completed(
            mp.mpc(mp.mpf(1) / 2, _num(t)), shift, dps=mp.dps
        )
        if abs(mp.im(value)) > mp.mpf(10) ** (-(dps - 2)) * max(abs(mp.re(value)), 1):
            raise ValueError(
                f"Z_shifted: imaginary residue {mp.im(value)} exceeds round-off"
            )
        return _shrink(mp.re(value), dps)


def shifted_interface(
    shift=SHIFTED_PRODUCT_SHIFT, dps: int = DPS_DEFAULT
) -> dict:
    """The zeta-like interface for ``W_a`` (see :func:`zeta_interface`).

    The name is ``shifted_product`` and does not carry the shift, so that
    verdict dictionaries and the tests that read them stay stable when the
    default shift is changed.
    """

    def _line_count(t0, t1, _a=shift, _d=dps):
        samples = max(int(8 * (t1 - t0)) + 2, 8)
        grid = [t0 + (t1 - t0) * i / (samples - 1) for i in range(samples)]
        values = [Z_shifted(t, _a, dps=min(_d, 15)) for t in grid]
        return sum(
            1
            for left, right in zip(values, values[1:])
            if left != 0 and right != 0 and mp.sign(left) != mp.sign(right)
        )

    return {
        "name": "shifted_product",
        "coefficient": lambda n, _a=shift, _d=dps: shifted_coefficient(
            int(n), _a, dps=_d
        ),
        "completed": lambda s, _a=shift, _d=dps: shifted_completed(s, _a, dps=_d),
        "fe_defect": lambda s, _a=shift, _d=dps: (
            shifted_functional_equation_defect(s, _a, dps=_d)
        ),
        "Z": lambda t, _a=shift, _d=dps: Z_shifted(t, _a, dps=_d),
        "zeros_on_line": _line_count,
        "count_zeros_box": lambda s0, s1, _a=shift, _d=dps: count_zeros_box(
            s0, s1, dps=min(_d, 20),
            fn=lambda z: shifted_completed(z, _a, dps=min(_d, 20)),
        ),
    }


def log_derivative_coefficients(coefficient, n_max: int, dps: int = DPS_DEFAULT):
    """``Lambda_F(n)`` for ``n <= n_max``, from the Dirichlet coefficients alone.

    Solves ``b_n log n = sum_{d | n} Lambda_F(d) b_{n/d}`` with
    ``b_n = a_n / a_1``, which is ``-F'/F`` read off ``F = sum a_n n^{-s}``.
    The route never sees an Euler product, so it is the one a rival can be put
    through: it turns "does this function have the positivity the Euler product
    gives zeta?" into a finite computation on coefficients.

    Returns a list indexed by ``n``, with entry 0 unused and
    ``Lambda_F(1) = 0``.

    Raises ``ValueError`` when ``a_1 = 0``.  That is not a corner case: the
    non-principal Epstein form ``(2,1,3)`` does not represent 1, so it has no
    log-derivative Dirichlet series in this normalisation at all.  A claim that
    reads these coefficients must decide what to do about that rather than
    have it decided by a silent coercion, which is why this raises instead of
    returning something.
    """
    n_max = int(n_max)
    with mp.workdps(dps + _GUARD + 5):
        a1 = _num(coefficient(1))
        if a1 == 0:
            raise ValueError(
                "a_1 = 0: this function has no log-derivative Dirichlet series "
                "in the normalisation a_1 = 1"
            )
        b = [mp.mpf(0)] * (n_max + 1)
        for n in range(1, n_max + 1):
            b[n] = _num(coefficient(n)) / a1
        lam = [mp.mpf(0)] * (n_max + 1)
        for n in range(2, n_max + 1):
            acc = b[n] * mp.log(n)
            for d in range(2, n):
                if n % d == 0:
                    acc -= lam[d] * b[n // d]
            lam[n] = acc
        return [_shrink(x, dps) for x in lam]


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


def claim_euler_product_positivity(
    iface: dict, n_max: int = 200, dps: int = 25
) -> bool:
    """Claim: "the coefficients of ``log F`` are non-negative", i.e.
    ``Lambda_F(n) >= 0`` for ``n <= n_max``, read from the Dirichlet
    coefficients through :func:`log_derivative_coefficients`.

    For zeta this is exactly the Euler product: ``log zeta(s) =
    sum_n (Lambda(n)/log n) n^{-s}`` with every coefficient non-negative, which
    is the input to the classical zero-free region.  It is strictly weaker than
    multiplicativity, and the difference is the point: it asks for a positivity
    rather than a factorisation, so it is the shape a positivity-based
    mechanism actually uses.

    **Measured verdicts at** ``n_max = 200``: holds for zeta (most negative
    coefficient -9.2e-41, i.e. round-off); fails for Davenport-Heilbronn
    immediately at ``n = 3`` (``Lambda_F = -6.78``); fails for the principal
    Epstein form ``(1,1,6)`` at ``n = 48`` (``-19.88``); **undefined** for the
    non-principal form ``(2,1,3)``, which does not represent 1, so ``a_1 = 0``
    and there is no such series.  The claim **raises** there rather than
    returning a verdict it has not earned, and :func:`battery` records that as
    ``undefined_for`` instead of scoring it as a rival the claim survived;
    and **holds exactly** for
    the shifted product, whose coefficients are
    ``Lambda(n)(n^a + n^{-a}) >= 0``.  So EPP does not distinguish, and the
    rival it is shared with is the one that has an Euler product.

    **The truncation is part of the claim, and it is not academic.**  At
    ``n_max = 40`` this same claim *holds* for the principal Epstein form and
    the verdict reads as shared with it rather than with the shifted product.
    That form's log-derivative coefficients are 0 at ``n = 24, 32, 36`` and
    ``40`` before going negative at 48: they sit on the boundary of the claim
    for a stretch, so a short scan reads as a pass.  Unique factorisation in
    the principal-class ideal monoid of discriminant -23 first fails at
    ``n = 36``, where ``(2)(3) = (p2 p3bar)(p2bar p3)``.
    ``tests/test_epstein.py`` pins both readings.
    """
    lam = log_derivative_coefficients(iface["coefficient"], n_max, dps=dps)
    tol = mp.mpf(10) ** (-dps + 8)
    return all(x > -tol for x in lam[2:])


def _claim_name(claim_fn) -> str:
    """A stable, printable name for a claim.

    ``functools.partial`` has no ``__name__``, and ``repr`` of one carries a
    memory address, which would put a different string in every run of
    ``scripts/23_gate_3_battery.py``.  A claim whose truncation is bound by
    ``partial`` is the normal case here, so the wrapped name and the bound
    keywords are reported instead.
    """
    name = getattr(claim_fn, "__name__", None)
    if name is not None:
        return name
    inner = getattr(claim_fn, "func", None)
    inner_name = getattr(inner, "__name__", None)
    if inner_name is None:
        return repr(claim_fn)
    keywords = getattr(claim_fn, "keywords", None) or {}
    if not keywords:
        return inner_name
    bound = ", ".join(f"{k}={v}" for k, v in sorted(keywords.items()))
    return f"{inner_name}({bound})"


def battery(
    claim_fn,
    dps: int = DPS_DEFAULT,
    forms: tuple[tuple[int, int, int], ...] = ((2, 1, 3), (1, 1, 6)),
    shift=SHIFTED_PRODUCT_SHIFT,
) -> dict:
    """Evaluate a claimed structural property against zeta and every rival:
    the Davenport-Heilbronn function, the Epstein zeta functions of
    discriminant -23 (class number 3, the non-principal form ``(2,1,3)`` and
    the principal form ``(1,1,6)``), and the symmetric shifted product
    ``W_a(s) = zeta(s+a) zeta(s-a)``.  This is the falsification harness of
    gate #3 (docs/09) in executable form.

    The rivals come in two kinds, and the distinction is the whole reason the
    second kind was added.

    **Linear combinations of Euler products.**  Davenport-Heilbronn is a
    self-dual combination of the two Dirichlet L-functions of the quartic
    characters mod 5; each discriminant -23 Epstein function is a combination
    of the three Hecke L-functions of the class group.  Every one is assembled
    from legitimate Euler products, and what each lacks is a *scalar* Euler
    product of its own, because linear combination destroys primitive
    multiplicative structure while preserving the functional equation.  A
    claim that survives on any of them is prime-blind in exactly the way the
    gate exists to detect.

    **A counterexample that has an Euler product.**  Those rivals are, by
    construction, silent on any claim whose content *is* the Euler product,
    and such a claim passes the gate without having been tested.  ``W_a`` has
    a scalar Euler product, non-negative multiplicative coefficients and
    non-negative log-derivative coefficients, and its zeros lie on
    ``Re s = 1/2 +- a`` by Hardy's theorem alone.  Its scope caveat is stated
    where it is constructed, above :data:`SHIFTED_PRODUCT_SHIFT`, and it
    matters: ``W_a`` is outside the Selberg class, so a claim it shares is not
    thereby irrelevant to RH.  It is shown to be blind to a shift, and a
    mechanism resting on it must say which normalisation it uses and where.
    Pass ``shift=None`` to run the two-rival set that predates it.

    ``claim_fn`` receives a zeta-like interface dict (see
    :func:`zeta_interface`) and must return truthy/falsy.  Returns::

        {"claim": <name>, "riemann_zeta": bool, "davenport_heilbronn": bool,
         "epstein_2_1_3": bool, "epstein_1_1_6": bool, "shifted_product": bool,
         "distinguishes": bool, "shared_with": (...), "undefined_for": (...),
         "undefined_reasons": {...}}

    **A claim that raises on a rival is recorded, not swallowed.**  Its entry
    is ``False``, its name goes in ``undefined_for`` with the exception text in
    ``undefined_reasons``, and ``distinguishes`` is then never ``True``: a
    rival the claim could not be evaluated on is a rival the claim was not
    tested against, and reporting that as a pass is the flattering collapse
    this harness exists to prevent.  The live instance is
    :func:`log_derivative_coefficients` on the non-principal Epstein form,
    whose ``a_1`` is 0.

    Reading the verdict: a claim that **passes for all** cannot be the
    load-bearing step of an RH proof.  A claim that **distinguishes** zeta from
    every rival is at least a candidate for where a real proof must live, and
    is still only a candidate.
    """
    results = {}
    undefined: dict[str, str] = {}
    interfaces = [zeta_interface(dps), dh_interface(dps)]
    interfaces.extend(epstein_interface(form, dps) for form in forms)
    if shift is not None:
        interfaces.append(shifted_interface(shift, dps))
    for iface in interfaces:
        try:
            results[iface["name"]] = bool(claim_fn(iface))
        except Exception as exc:  # noqa: BLE001 - the point is to name it
            results[iface["name"]] = False
            undefined[iface["name"]] = f"{type(exc).__name__}: {exc}"

    # Gate #3 asks that the structure be ungrantable to *every* counterexample,
    # not merely to one of them: a claim zeta shares with any rival cannot be
    # the load-bearing step, however many other rivals it excludes.
    counterexamples = [name for name in results if name != "riemann_zeta"]
    verdict = {
        "claim": _claim_name(claim_fn),
        "riemann_zeta": results["riemann_zeta"],
        "davenport_heilbronn": results["davenport_heilbronn"],
        "distinguishes": bool(results["riemann_zeta"])
        and not any(results[name] for name in counterexamples)
        and not undefined,
        "shared_with": tuple(sorted(name for name in counterexamples if results[name])),
        "undefined_for": tuple(sorted(undefined)),
        "undefined_reasons": dict(undefined),
    }
    for name, value in results.items():
        verdict.setdefault(name, value)
    return verdict
