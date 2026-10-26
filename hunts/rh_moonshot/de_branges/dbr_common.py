"""de_branges: the Lagarias structure functions E_h and their Hermite-Biehler defect.

Hunt #150 (``rh_moonshot``), mechanism 2.  Nothing here is a result about RH;
see NOTES.md for what each number is and how it is graded.

The object.  For a completed function Lambda with Lambda(1 - s) = Lambda(s)
and Lambda(conj s) = conj Lambda(s), put

    E_h(z) = Lambda(1/2 + h - i z),   z = x + i y,

so E_h(z) = Lambda(1/2 + h + y - i x) and E_h(conj z) = Lambda(1/2 + h - y - i x).
E_h is Hermite-Biehler (de Branges structure function) when

    D_h(z) := log|E_h(conj z)| - log|E_h(z)| < 0   for every y > 0,

and then A_h = (E_h + E_h^#)/2, which on the line is Re Lambda(1/2 + h + i t),
has only real zeros (Lagarias, Acta Arith. 120 (2005), Lemma 2.1 and section 6).
For zeta, h = 1/2 is de Branges's E(z) = xi(1 - iz) (Bull. AMS 15 (1986)),
the space Conrey and Li tested (IMRN 2000, no. 18).

The completed functions, two routes each (``mp_*``: mpmath and the lab's
``zeta`` package; ``arb_*``: python-flint balls, sharing no evaluator with the
mp route except where named):

* zeta: xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s);
* dh: F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s) (``zeta.epstein.completed_dh``;
  the Arb route rebuilds f from Arb's Hurwitz zeta and shares only kappa);
* epstein: s (s-1) (sqrt(d)/pi)^s Gamma(s) zeta_Q(s), Q = (1, 1, 6), d = 23/4
  (mp: the lab's lattice route; Arb: hunt #120's Fourier-Bessel ball route,
  ``hunts/qrh_rival_step/probe.route_b_ball``, read-only);
* wa: xi(s + 1/4) xi(s - 1/4);
* zshift: xi(s - delta), delta = 1/5, which has no s -> 1 - s symmetry (its
  completion is symmetric about 1/2 + delta), kept as the rival that lacks the
  functional-equation hypothesis.

Nothing is written into the tree by import.
"""

from __future__ import annotations

import math
import os
import sys
from fractions import Fraction

from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
for _p in (ROOT, os.path.join(ROOT, "hunts", "qrh_rival_step")):
    if _p not in sys.path:
        sys.path.insert(0, _p)

KINDS = ("zeta", "dh", "epstein", "wa", "zshift")
EPSTEIN_FORM = (1, 1, 6)
EPSTEIN_D = Fraction(23, 4)
WA_SHIFT = Fraction(1, 4)
ZSHIFT_DELTA = Fraction(1, 5)

#: Off-line zeros (real part, ordinate) each rival is known to carry, and the
#: offset delta = |beta - 1/2| that sets where its E_h must fail.
OFFLINE = {
    "dh": ("0.80851718245663738", "85.69934848537759"),  # zeta.epstein pins 50 digits
    "epstein": ("0.953260474794661", "16.2902157203904"),  # weil_propagation, measured
    "wa": ("0.75", "14.134725141734694"),  # rho + 1/4 for zeta's first zero
    "zshift": ("0.7", "14.134725141734694"),  # rho + 1/5
}


# ---------------------------------------------------------------------------
# mpmath routes
# ---------------------------------------------------------------------------


def mp_completed(kind: str, s, dps: int = 25):
    """Lambda_kind(s) by the mpmath route, at ``dps`` digits relative."""
    from zeta import epstein as EP
    from zeta.core import xi

    s = mp.mpc(s)
    if kind == "zeta":
        return xi(s, dps=dps)
    if kind == "dh":
        return EP.completed_dh(s, dps=dps)
    if kind == "wa":
        return EP.shifted_completed(s, shift=mp.mpf(1) / 4, dps=dps)
    if kind == "zshift":
        with mp.workdps(dps + 10):
            return xi(s - mp.mpf(1) / 5, dps=dps + 10)
    if kind == "epstein":
        # s (s-1) Lambda_Q is entire, but the lattice route divides by s and s - 1:
        # at those two points take the mean over a circle of radius 1e-4 (mean
        # value property; 8 nodes leave an error of order r^8)
        if s == 1 or s == 0:
            r = mp.mpf("1e-4")
            pts = [s + r * mp.expjpi(mp.mpf(k) / 4) for k in range(8)]
            return mp.fsum(mp_completed(kind, p, dps) for p in pts) / 8
        lift = math.ceil(EP.EPSTEIN_DIGITS_PER_UNIT_HEIGHT * abs(float(mp.im(s))))
        with mp.workdps(dps + 20 + lift):
            return s * (s - 1) * EP.epstein_completed(s, EPSTEIN_FORM, dps=mp.dps)
    raise ValueError(kind)


# ---------------------------------------------------------------------------
# Arb routes
# ---------------------------------------------------------------------------


def _arb_xi(s):
    from flint import acb, arb

    return s * (s - 1) / 2 * acb(arb.pi()) ** (-s / 2) * (s / 2).gamma() * s.zeta()


_DH_F = {}


def _arb_dh(s, prec):
    from flint import acb, arb

    from hunts.rh_moonshot.li_arithmetic import li_arith_split as S

    if prec not in _DH_F:
        _DH_F[prec] = S.dh_f_evaluator(int(prec / 3.32) + 20)
    f = _DH_F[prec](s)
    q = acb(arb.pi() / 5)
    return q ** (-(s + 1) / 2) * ((s + 1) / 2).gamma() * f


def _arb_epstein(s, prec):
    from flint import acb, arb

    import probe as QP  # hunts/qrh_rival_step, read-only

    re_s = s.real.mid().str(int(prec / 3.32) + 5, radius=False)
    im_s = s.imag.mid().str(int(prec / 3.32) + 5, radius=False)
    zq = QP.route_b_ball(EPSTEIN_FORM, re_s, im_s, prec)
    d = arb(EPSTEIN_D.numerator) / EPSTEIN_D.denominator
    return s * (s - 1) * acb(d.sqrt() / arb.pi()) ** s * s.gamma() * zq


def arb_completed(kind: str, s, prec: int = 160):
    """Lambda_kind(s) as an Arb ball (``s`` an acb or a complex/mpc)."""
    from flint import acb, arb, ctx

    old = ctx.prec
    ctx.prec = prec
    try:
        if not isinstance(s, acb):
            s = acb(arb(mp.nstr(mp.re(s), 40)), arb(mp.nstr(mp.im(s), 40)))
        if kind == "zeta":
            return _arb_xi(s)
        if kind == "dh":
            return _arb_dh(s, prec)
        if kind == "wa":
            a = acb(arb(1) / 4)
            return _arb_xi(s + a) * _arb_xi(s - a)
        if kind == "zshift":
            return _arb_xi(s - acb(arb(1) / 5))
        if kind == "epstein":
            return _arb_epstein(s, prec)
        raise ValueError(kind)
    finally:
        ctx.prec = old


# ---------------------------------------------------------------------------
# the Hermite-Biehler defect
# ---------------------------------------------------------------------------


def s_pair(h, x, y):
    """(s for E_h(z), s for E_h(conj z)) as mpc, z = x + i y."""
    h, x, y = mp.mpf(h), mp.mpf(x), mp.mpf(y)
    half = mp.mpf(1) / 2
    return mp.mpc(half + h + y, -x), mp.mpc(half + h - y, -x)


def defect_mp(kind, h, x, y, dps=25):
    """D_h(x + i y) = log|E_h(conj z)| - log|E_h(z)| by the mp route (mpf)."""
    with mp.workdps(dps + 10):
        sp, sm = s_pair(h, x, y)
        a = abs(mp_completed(kind, sm, dps))
        b = abs(mp_completed(kind, sp, dps))
        return mp.log(a) - mp.log(b)


def defect_arb(kind, h, x, y, prec=160):
    """The same defect as an Arb ball (arb); its sign is decided when the ball
    excludes 0."""
    from flint import acb, arb, ctx

    with mp.workdps(40):
        sp, sm = s_pair(h, x, y)
    a = arb_completed(kind, sm, prec)
    b = arb_completed(kind, sp, prec)
    old = ctx.prec
    ctx.prec = prec
    try:
        return abs(a).log() - abs(b).log()
    finally:
        ctx.prec = old


def offset(kind):
    """delta = |beta - 1/2| of the rival's pinned off-line zero (float)."""
    return abs(float(OFFLINE[kind][0]) - 0.5)


# ---------------------------------------------------------------------------
# the local Euler factor is not Hermite-Biehler (derived, see NOTES.md s3)
# ---------------------------------------------------------------------------


def local_factor_ratio(p: int, h, x, y):
    """|E_p(conj z)| / |E_p(z)| for the local factor E_p(z) = (1 - p^{-(1/2+h-iz)})^{-1}.

    Equals sqrt(f(r+)/f(r-)) with f(r) = 1 - 2 r cos(x log p) + r^2 and
    r+- = p^{-(1/2+h+-y)}; it exceeds 1 exactly when
    cos(x log p) > (r+ + r-)/2.
    """
    with mp.workdps(30):
        sp, sm = s_pair(h, x, y)
        ez = 1 / (1 - mp.power(p, -sp))
        ezb = 1 / (1 - mp.power(p, -sm))
        return abs(ezb) / abs(ez)


# ---------------------------------------------------------------------------
# Conrey and Li's two printed numbers, reproduced
# ---------------------------------------------------------------------------


def conrey_li_numbers(dps=30):
    """CL use xi_CL(s) = s (s-1) pi^{-s/2} Gamma(s/2) zeta(s) (twice the lab's xi).

    Returns (-Re xi_CL'(rho_34) xi_CL(1 + rho_34), Re xi(1 + 282i)/xi(2 + 282i)),
    printed in CL section 3.1 as -5.389100507182945e-69 and -0.000131957.
    At a zero, xi_CL'(rho) = rho (rho - 1) pi^{-rho/2} Gamma(rho/2) zeta'(rho).
    """
    with mp.workdps(dps + 20):
        rho = mp.zetazero(34)

        def xcl(s):
            return s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

        dxi = rho * (rho - 1) * mp.pi ** (-rho / 2) * mp.gamma(rho / 2) * mp.zeta(rho, derivative=1)
        first = -mp.re(dxi * xcl(1 + rho))
        second = mp.re(xcl(mp.mpc(1, 282)) / xcl(mp.mpc(2, 282)))
        return first, second


def conrey_li_numbers_arb(prec=200):
    """The same two numbers on Arb, with zeta'(rho) from an acb series and rho
    from Arb's own zeta_zero (no mpmath)."""
    from flint import acb, acb_series, arb, ctx

    old = ctx.prec
    ctx.prec = prec
    try:
        rho = acb.zeta_zero(34)

        def xcl(s):
            return s * (s - 1) * acb(arb.pi()) ** (-s / 2) * (s / 2).gamma() * s.zeta()

        zser = acb_series([rho, 1], prec=2).zeta()
        dz = zser[1]
        dxi = rho * (rho - 1) * acb(arb.pi()) ** (-rho / 2) * (rho / 2).gamma() * dz
        first = -(dxi * xcl(1 + rho)).real
        second = (xcl(acb(1, 282)) / xcl(acb(2, 282))).real
        return first, second
    finally:
        ctx.prec = old
