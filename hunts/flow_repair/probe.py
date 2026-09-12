"""Repairing the counterexample: the de Bruijn-Newman flow on Davenport-Heilbronn.

Run from the repo root:

    .venv/bin/python hunts/flow_repair/probe.py validate
    .venv/bin/python hunts/flow_repair/probe.py pair1
    .venv/bin/python hunts/flow_repair/probe.py survey --pairs 2,3,4,5
    .venv/bin/python hunts/flow_repair/probe.py ode --pairs 1,2,3,4,5
    .venv/bin/python hunts/flow_repair/probe.py lesions
    .venv/bin/python hunts/flow_repair/probe.py precision
    .venv/bin/python hunts/flow_repair/probe.py figure
    .venv/bin/python hunts/flow_repair/probe.py merge   # fold results_*.json partials in

Writes ``results.json`` (and stage partials via ``--out``) plus
``flow_repair.png`` next to this file.  See ``MISSION.md`` for the
pre-registered predictions.

Vocabulary note (the probe discipline, ``tests/test_hunt_probe_discipline.py``):
everything in this hunt is the accurate regime, mpmath floats with measured
cross-route defects.  The strongest words used are *measured* and *observed*;
the reserved enclosure word belongs to ``zeta/rigor.py`` and appears nowhere
in this directory.  No enclosure claims are made.

The construction (derived, then measured, never trusted):

    F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s)   is entire, F(s) = F(1-s),
    Xi_DH(z) := F(1/2 + iz) = int_0^inf Phi_DH(u) cos(zu) du,
    Phi_DH(u) = 4 e^{3u/2} omega(e^{2u}),  omega(x) = sum_n n a_n e^{-pi n^2 x/5},

with a_n the (real, period-5) Dirichlet coefficients of f.  Unlike zeta there
are **no pole terms**: f is entire, so the Mellin split at x = 1 leaves no
1/s or 1/(s-1) residue pieces behind.  The flow is then

    H_t(z) = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du,     H_0 = Xi_DH,

the same backward-heat deformation as ``zeta.heatflow.H_t`` (dH/dt = -d2H/dz2:
increasing t repels real zeros and pulls conjugate pairs onto the axis).  An
off-line zero rho = beta + i*gamma of f sits at z = gamma - i(beta - 1/2):
a conjugate pair at distance y0 = beta - 1/2 from the real axis, which the
flow lands at some t* > 0, the pair's repair time, a lower bound for
Lambda_DH := inf{t : H_t has only real zeros}.

Pair tracking is done on quantities that are analytic through the collision:
contour moments q_k = (1/2 pi i) contour-int (z-c)^k H'/H dz give the count
N = q0 (must be an integer, must be 2), the centroid x = c + q1/2, and the
discriminant Delta = 2 q2 - q1^2 = (z1 - z2)^2, which runs from -4 y0^2 < 0
through 0 (the landing, t = t*) to +gap^2 > 0, no root-chasing near a
double zero, ever.  The ODE null control integrates the same pair in the
collision-safe variable Q = Delta/4, using the identity (any external zero a,
real or a member of a conjugate pair):

    dQ/dt = 2 - 4Q sum_a 1/((x - a)^2 - Q),
    dx/dt = sum_a 2(x - a)/((x - a)^2 - Q),

exact for the N-body dynamics dz_k/dt = 2 sum_{j != k} 1/(z_k - z_j) and
manifestly analytic through Q = 0.
"""

from __future__ import annotations

import argparse
import glob
import json
import math
import os
import time
from functools import lru_cache

from mpmath import mp

from zeta.epstein import (
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    Z_dh,
    completed_dh,
    count_zeros_box,
    dh_f,
    kappa,
)
from zeta.heatflow import H_t as H_t_zeta
from zeta.heatflow import Phi as Phi_zeta
from zeta.heatflow import _gauss_legendre  # cross-validated in zeta/heatflow.py

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "results.json")

#: Digits of |Xi_DH(z)| lost per unit of z: |Gamma(3/4 + iz/2)| ~ e^{-pi z/4}.
#: (Twice zeta.heatflow's 0.1706 because this normalisation has no z/2.)
DIGITS_LOST_PER_Z = math.pi / 4 / math.log(10)  # ~0.34109

#: The off-line quadruples surveyed: (beta, gamma) seeds.  Pair 1 is the
#: repo's own 50-digit pinned zero (zeta/epstein.py, re-verified by its test
#: suite and matching Spira 1994).  Pairs 2-4 are Spira's (Math. Comp. 63,
#: 1994); pairs 5-9 are Balanzario & Sanchez-Ortiz (Math. Comp. 76, 2007).
#: Every seed is re-polished by mp.findroot on dh_f, with a winding check,
#: before anything downstream uses it (see polish_pair), the literature
#: supplies starting guesses, never data.
LIT_PAIRS: dict[int, tuple[str, str]] = {
    1: (OFFLINE_ZERO_RE, OFFLINE_ZERO_IM),
    2: ("0.650830", "114.163343"),
    3: ("0.574356", "166.479306"),
    4: ("0.724258", "176.702461"),
    5: ("0.86953", "240.4046"),
    6: ("0.81955", "320.8764"),
    7: ("0.76822", "331.0502"),
    8: ("0.62850", "366.6409"),
    9: ("0.81587", "411.7967"),
}


def site_dps(gamma: float, extra: int = 24) -> int:
    """Working precision for flow work at height gamma: |H| ~ 10^{-0.341 gamma},
    so absolute accuracy must undercut that by a healthy relative margin."""
    return int(math.ceil(DIGITS_LOST_PER_Z * float(gamma))) + extra


def mean_gap(gamma: float) -> float:
    """Mean spacing of the real zeros of Xi_DH near height gamma:
    2 pi / log(5 gamma / 2 pi) (conductor-5; cf. zeta.epstein._dh_mean_spacing)."""
    return float(2 * math.pi / math.log(5 * float(gamma) / (2 * math.pi)))


# ---------------------------------------------------------------------------
# the weight Phi_DH and the flow evaluator
# ---------------------------------------------------------------------------


def omega_dh(x, kap):
    """omega(x) = sum_{n>=1} n a_n exp(-pi n^2 x / 5) at ambient precision.

    a_n has period 5: (1, kappa, -kappa, -1, 0).  The tail bound is the term
    itself: n * exp(-pi n^2 x/5) below the ambient floor for three consecutive
    n ends the sum.
    """
    a_pat = (mp.mpf(1), kap, -kap, mp.mpf(-1), mp.mpf(0))
    total = mp.mpf(0)
    floor = mp.mpf(10) ** (-(mp.dps + 8))
    n, small = 1, 0
    while small < 3:
        e = mp.exp(-mp.pi * n * n * x / 5)
        if n * e < floor:
            small += 1
        else:
            small = 0
            a = a_pat[(n - 1) % 5]
            if a != 0:
                total += n * a * e
        n += 1
    return total


def phi_dh_raw(u, kap):
    """The **unfolded** Phi_DH(u) = 4 e^{3u/2} omega(e^{2u}), trustworthy for
    Re u >= 0 only (for u < 0 the sum is a catastrophic cancellation, exactly
    as documented for zeta's Phi in zeta/heatflow.py)."""
    u = mp.mpmathify(u)
    return 4 * mp.exp(mp.mpf(3) / 2 * u) * omega_dh(mp.exp(2 * u), kap)


def phi_dh(u, kap):
    """Phi_DH with the evenness fold applied first (the identity is measured
    separately by stage ``validate``; the fold keeps the hot path out of the
    cancellation regime)."""
    u = mp.mpmathify(u)
    if mp.re(u) < 0:
        u = -u
    return phi_dh_raw(u, kap)


class DHFlow:
    """H_t for the Davenport-Heilbronn Xi, one instance per (dps, z-height).

    Composite Gauss-Legendre on [0, U] with Phi_DH memoised at the nodes
    (Phi depends on neither z nor t, so the rule is paid for once), the same
    architecture as zeta.heatflow._quad_rule, rebuilt here for the DH weight
    and exponents.  ``n_gauss`` grows with dps so the panel count stays sane
    at the precisions the high survey pairs need.
    """

    def __init__(self, dps: int, z_scale: float, t_max: float = 0.12,
                 imz_max: float = 1.6):
        self.dps = int(dps)
        self.z_scale = float(z_scale)
        self.t_max = float(t_max)
        self.imz_max = float(imz_max)
        with mp.workdps(self.dps + 10):
            self.kap = kappa(self.dps + 10)
            self.U = self._integration_limit()
            self.n_gauss = max(20, min(64, 8 + self.dps // 3))
            self.n_panels = self._panels()
            xs, ws = _gauss_legendre(self.n_gauss, self.dps)
            h = self.U / self.n_panels
            nodes, weights = [], []
            for p in range(self.n_panels):
                a = p * h
                for x, w in zip(xs, ws):
                    nodes.append(a + h * (x + 1) / 2)
                    weights.append(w * h / 2)
            self.nodes = nodes
            self.phis = [phi_dh_raw(u, self.kap) for u in nodes]
            self.weights = weights
        self.n_nodes = len(nodes)

    def _integration_limit(self):
        """Smallest U with e^{tU^2 + imz*U} * Phi_DH(U) below the rounding
        floor 10^{-(dps+12)}; the DH integrand dies like exp(-pi e^{2U}/5)."""
        tgt = -(self.dps + 12) * mp.log(10)
        t, im = mp.mpf(self.t_max), mp.mpf(self.imz_max)

        def f(U):
            return (t * U ** 2 + (mp.mpf(3) / 2 + im) * U + mp.log(4)
                    - mp.pi * mp.exp(2 * U) / 5 - tgt)

        return +mp.findroot(f, mp.mpf(2.5))

    def _panels(self) -> int:
        """Oscillation-resolving panel count: a k-point Gauss rule on a panel
        carrying omega_p radians of cos(z u) errs like (e*omega_p/(8k))^{2k};
        demand 10^{-(dps+6)}, then add the dps-driven floor zeta.heatflow uses
        for Phi's own super-exponential variation."""
        k = self.n_gauss
        omega_p = (8.0 * k / math.e) * 10.0 ** (-(self.dps + 6) / (2.0 * k))
        need_osc = int(math.ceil(self.z_scale * float(self.U) / omega_p)) + 4
        floor = 24 * 2 ** max(0, math.ceil((self.dps - 45) / 45))
        return max(need_osc, floor, 16)

    def H_and_dH(self, z, t):
        """(H_t(z), H_t'(z)) in one pass: one expj per node serves both the
        cosine (for H) and the sine (for H')."""
        with mp.workdps(self.dps):
            z = mp.mpc(z)
            t = mp.mpf(t)
            tot_h = mp.mpc(0)
            tot_dh = mp.mpc(0)
            if t == 0:
                for u, w, ph in zip(self.nodes, self.weights, self.phis):
                    e = mp.expj(z * u)
                    ei = 1 / e
                    wph = w * ph
                    tot_h += wph * (e + ei)
                    tot_dh += wph * u * (e - ei)
            else:
                for u, w, ph in zip(self.nodes, self.weights, self.phis):
                    e = mp.expj(z * u)
                    ei = 1 / e
                    wph = w * ph * mp.exp(t * u * u)
                    tot_h += wph * (e + ei)
                    tot_dh += wph * u * (e - ei)
            # cos = (e + 1/e)/2 ; d/dz cos(zu) = -u sin(zu) = -u (e - 1/e)/(2i)
            return +(tot_h / 2), +(tot_dh * mp.mpc(0, 1) / 2)

    def H(self, z, t):
        return self.H_and_dH(z, t)[0]


# ---------------------------------------------------------------------------
# contour moments: N, centroid, discriminant, analytic through the collision
# ---------------------------------------------------------------------------


class WindingError(ArithmeticError):
    """The contour count refused: non-integer winding or unexpected N."""


def contour_moments(flow: DHFlow, center, radius, t, M: int = 96,
                    expect_n: int | None = 2) -> dict:
    """q_k = (1/2 pi i) oint (z - center)^k H'/H dz for k = 0, 1, 2 by the
    trapezoid rule (spectrally accurate on a periodic analytic integrand).

    Returns N (checked integer), x (centroid of the two zeros), Delta
    (= 2 q2 - q1^2, the squared zero separation, negative for a conjugate
    pair, positive after landing), the imaginary residuals of q1, q2 (pure
    round-off when the configuration is conjugate-symmetric: an accuracy
    meter), and min |H| on the contour (a conditioning meter).

    Raises WindingError when q0 is not within 1e-6 of an integer (a zero on
    or hugging the contour) or when the integer disagrees with ``expect_n``,
    the same refusal contract as zeta.epstein.count_zeros_box, and the
    lesion stage measures that it actually fires.
    """
    with mp.workdps(flow.dps):
        c = mp.mpc(center)
        r = mp.mpf(radius)
        q0 = mp.mpc(0)
        q1 = mp.mpc(0)
        q2 = mp.mpc(0)
        min_abs_h = None
        for j in range(M):
            w = r * mp.expjpi(mp.mpf(2 * j) / M)  # r e^{i theta_j}
            zj = c + w
            h, dh = flow.H_and_dH(zj, t)
            ah = abs(h)
            if min_abs_h is None or ah < min_abs_h:
                min_abs_h = ah
            g = (dh / h) * w  # (H'/H)(z_j) * (z_j - c), trapezoid factor 1/M
            q0 += g
            q1 += g * w
            q2 += g * w * w
        q0 /= M
        q1 /= M
        q2 /= M
        n_int = int(mp.nint(mp.re(q0)))
        defect = abs(q0 - n_int)
        if defect > mp.mpf("1e-6"):
            raise WindingError(
                f"winding {mp.nstr(q0, 10)} at t={mp.nstr(mp.mpf(t), 8)} is not "
                "an integer; a zero is on (or hugging) the contour"
            )
        if expect_n is not None and n_int != expect_n:
            raise WindingError(
                f"contour holds N={n_int} zeros, expected {expect_n} "
                f"(center={mp.nstr(c, 12)}, radius={mp.nstr(r, 6)}, "
                f"t={mp.nstr(mp.mpf(t), 8)})"
            )
        delta = 2 * q2 - q1 ** 2
        return {
            "N": n_int,
            "winding_defect": defect,
            "x": mp.re(c) + mp.re(q1) / 2,
            "Delta": mp.re(delta),
            "im_q1": abs(mp.im(q1)),  # pure round-off for a conjugate-symmetric pair
            "im_Delta": abs(mp.im(delta)),
            "min_abs_H": min_abs_h,
        }


# ---------------------------------------------------------------------------
# polishing the literature zeros in-tree
# ---------------------------------------------------------------------------


def polish_pair(k: int, dps: int) -> dict:
    """Re-derive quadruple k's zero from its literature seed: mp.findroot on
    dh_f at ``dps`` digits, then a unit winding check on a small box.  The
    literature supplies a starting guess; the polished value is the datum."""
    beta_s, gamma_s = LIT_PAIRS[k]
    with mp.workdps(dps + 10):
        seed = mp.mpc(mp.mpf(beta_s), mp.mpf(gamma_s))
        root = mp.findroot(lambda s: dh_f(s, dps=mp.dps), seed)
        resid = abs(dh_f(root, dps=mp.dps))
        h = mp.mpf(1) / 10
        n_box = count_zeros_box(root - mp.mpc(h, h), root + mp.mpc(h, h), dps=20)
        if n_box != 1:
            raise WindingError(f"polish_pair({k}): winding check got {n_box} != 1")
        beta, gamma = mp.re(root), mp.im(root)
        moved = abs(root - seed)
        return {
            "pair": k,
            "beta": mp.nstr(beta, min(dps, 40)),
            "gamma": mp.nstr(gamma, min(dps, 40)),
            "y0": mp.nstr(beta - mp.mpf(1) / 2, min(dps, 40)),
            "residual": mp.nstr(resid, 3),
            "moved_from_seed": mp.nstr(moved, 3),
            "tstar_naive": float((beta - mp.mpf(1) / 2) ** 2 / 2),
        }


# ---------------------------------------------------------------------------
# the repair time t*: Illinois root find on Delta(t)
# ---------------------------------------------------------------------------


def make_site(k: int, polished: dict, extra_dps: int = 24,
              radius: float | None = None) -> dict:
    """Assemble the working context for quadruple k from its polished zero."""
    gamma = float(mp.mpf(polished["gamma"]))
    y0 = float(mp.mpf(polished["y0"]))
    dps = site_dps(gamma, extra_dps)
    if radius is None:
        radius = min(0.9, max(0.35, 2.6 * y0))
    flow = DHFlow(dps, z_scale=gamma + 2.0)
    return {
        "k": k,
        "gamma": gamma,
        "y0": y0,
        "dps": dps,
        "radius": float(radius),
        "flow": flow,
        "center0": mp.mpc(gamma, 0),
    }


def delta_at(site: dict, t, center=None, M: int = 96) -> dict:
    """Delta(t) for the site's pair, recentering on the measured centroid."""
    c = site["center0"] if center is None else center
    out = contour_moments(site["flow"], c, site["radius"], t, M=M)
    out["t"] = float(t)
    return out


def find_tstar(site: dict, tol: float = 1e-8, M: int = 96,
               trace: list | None = None) -> dict:
    """The landing time: the root of Delta(t), by bracketed Illinois iteration.

    Delta is analytic and (measured) nearly linear in t, so this converges in
    a handful of contour evaluations.  Every evaluation re-asserts N = 2 and
    recenters the contour on the measured centroid.
    """
    y0 = site["y0"]
    m0 = delta_at(site, 0.0, M=M)
    if trace is not None:
        trace.append(m0)
    center = mp.mpc(m0["x"], 0)
    d0 = float(m0["Delta"])
    t_lo, f_lo = 0.0, d0
    t_hi = 0.55 * y0 * y0
    m_hi = delta_at(site, t_hi, center=center, M=M)
    if trace is not None:
        trace.append(m_hi)
    center = mp.mpc(m_hi["x"], 0)
    f_hi = float(m_hi["Delta"])
    grew = 0
    while f_hi < 0:
        grew += 1
        if grew > 4:
            raise ArithmeticError(
                f"Delta still negative at t={t_hi}: the pair has not landed "
                "inside the bracket, prediction P1 would be dead; investigate"
            )
        t_hi *= 1.3
        m_hi = delta_at(site, t_hi, center=center, M=M)
        if trace is not None:
            trace.append(m_hi)
        center = mp.mpc(m_hi["x"], 0)
        f_hi = float(m_hi["Delta"])
    # Illinois (bracket-preserving secant)
    n_eval = 0
    side = 0
    while (t_hi - t_lo) > tol * max(t_hi, 1e-3):
        t_mid = t_lo + f_lo * (t_lo - t_hi) / (f_hi - f_lo)
        # keep strictly inside the bracket
        lo_g, hi_g = t_lo + 0.01 * (t_hi - t_lo), t_hi - 0.01 * (t_hi - t_lo)
        t_mid = min(max(t_mid, lo_g), hi_g)
        m = delta_at(site, t_mid, center=center, M=M)
        if trace is not None:
            trace.append(m)
        center = mp.mpc(m["x"], 0)
        f_mid = float(m["Delta"])
        n_eval += 1
        if n_eval > 60:
            break
        if f_mid < 0:
            t_lo, f_lo = t_mid, f_mid
            if side == -1:
                f_hi *= 0.5
            side = -1
        else:
            t_hi, f_hi = t_mid, f_mid
            if side == +1:
                f_lo *= 0.5
            side = +1
    tstar = 0.5 * (t_lo + t_hi)
    return {
        "pair": site["k"],
        "tstar": tstar,
        "bracket": [t_lo, t_hi],
        "tstar_naive": 0.5 * y0 * y0,
        "shave_percent": 100.0 * (1.0 - tstar / (0.5 * y0 * y0)),
        "Delta_at_0": d0,
        "n_contour_evals": n_eval + 2 + grew,
        "dps": site["dps"],
        "radius": site["radius"],
        "M": M,
    }


# ---------------------------------------------------------------------------
# the zero census around a site (for the ODE null control)
# ---------------------------------------------------------------------------


def line_zeros_near(gamma: float, half_width: float, step_frac: float = 8.0,
                    dps: int = 15) -> list[float]:
    """Real zeros of Xi_DH in [gamma - w, gamma + w]: sign changes of Z_dh
    refined by bisection.  Grid = mean_gap/step_frac."""
    lo, hi = max(1.0, gamma - half_width), gamma + half_width
    step = mean_gap(gamma) / step_frac
    n = int(math.ceil((hi - lo) / step)) + 1
    with mp.workdps(dps):
        grid = [lo + (hi - lo) * i / n for i in range(n + 1)]
        vals = [Z_dh(t, dps=dps) for t in grid]
        out = []
        for i in range(n):
            a, b = grid[i], grid[i + 1]
            fa, fb = vals[i], vals[i + 1]
            if fa == 0:
                out.append(float(a))
                continue
            if mp.sign(fa) != mp.sign(fb):
                for _ in range(60):
                    m = (a + b) / 2
                    fm = Z_dh(m, dps=dps)
                    if fm == 0:
                        break
                    if mp.sign(fm) == mp.sign(fa):
                        a, fa = m, fm
                    else:
                        b, fb = m, fm
                out.append(float((a + b) / 2))
        return out


def strip_count_window(gamma: float, half_width: float, dps: int = 20) -> int:
    """Argument-principle count of ALL zeros of f in the window strip
    [-1.05, 2.05] x [gamma - w, gamma + w], the accounting that says whether
    the line scan plus the known quadruples explain everything.  Edges are
    nudged off likely zeros; retried on the refusal the counter raises."""
    for nudge in (0.0, 0.0371, -0.0619, 0.1093):
        try:
            return count_zeros_box(
                mp.mpc(mp.mpf("-1.05"), gamma - half_width + nudge),
                mp.mpc(mp.mpf("2.05"), gamma + half_width + nudge),
                dps=dps,
            )
        except ArithmeticError:
            continue
    raise ArithmeticError("strip_count_window: every nudge hit a zero")


def ode_null_control(site: dict, reals: list[float], other_pairs: list[dict],
                     t_end: float, n_steps: int = 800,
                     rho_tail: float | None = None,
                     window: float | None = None) -> dict:
    """Integrate the N-body zero dynamics in collision-safe coordinates.

    State: the target pair and every other quadruple in the window as
    (x_p, Q_p); each real zero as w_i.  Mirrors (the -z copies) enter the
    force assembly analytically.  Tail beyond the window enters dQ/dt as
    -4 Q * (2 rho / W) with rho the local mean density, a correction the
    result records rather than hides.

    No arithmetic enters: the input is the measured t = 0 configuration and
    the universal dynamics.  If this lands within ~1% of the PDE's t*, the
    repair clock reads zero geometry (prediction P3).
    """
    x0 = site["gamma"]
    y0 = site["y0"]
    W = window if window is not None else 40.0
    rho = rho_tail if rho_tail is not None else 1.0 / mean_gap(x0)

    # state vectors (floats: the null control is a 1%-scale model, and the
    # collision-safe coordinates keep it well conditioned)
    pairs = [{"x": x0, "Q": -y0 * y0}]
    for p in other_pairs:
        pairs.append({"x": p["x"], "Q": -p["y"] * p["y"]})
    reals = [float(w) for w in reals]

    def rhs(state):
        px, pq, rw = state
        n_p, n_r = len(px), len(rw)
        dpx = [0.0] * n_p
        dpq = [0.0] * n_p
        drw = [0.0] * n_r

        def pair_terms(x, Q, exclude_pair=None, exclude_real=None):
            """sum over all other zeros a of 1/((x-a)^2 - Q) and of
            2(x-a)/((x-a)^2 - Q); a runs over reals (+mirrors) and pair
            members (+mirror pairs), using the universal identity that only
            needs (x_a, Q_a) for a pair: its two members contribute
            1/((x-xa)^2 - ...) summed exactly via complex arithmetic."""
            s_q = 0.0
            s_x = 0.0
            for i, w in enumerate(rw):
                for a in ((w, False), (-w, True)):
                    if exclude_real == i and not a[1]:
                        continue
                    d = x - a[0]
                    den = d * d - Q
                    s_q += 1.0 / den
                    s_x += 2.0 * d / den
            for jp in range(n_p):
                for mirror in (False, True):
                    if exclude_pair == jp and not mirror:
                        continue
                    xa = -px[jp] if mirror else px[jp]
                    Qa = pq[jp]
                    # two members xa +- sqrt(Qa): sum_{m} 1/((x - m)^2 - Q)
                    # = analytic in Qa; evaluate via the two roots of
                    # (x - xa \mp s)^2 with s^2 = Qa, using complex sqrt.
                    s = complex(Qa, 0.0) ** 0.5
                    for sgn in (1.0, -1.0):
                        d = complex(x, 0.0) - (complex(xa, 0.0) + sgn * s)
                        den = d * d - Q
                        s_q += (1.0 / den).real
                        s_x += (2.0 * d / den).real
            # tail beyond the window (integral of rho/(u^2) past both edges)
            # plus the far mirror cluster around -x, treated as a density
            s_q += 2.0 * rho / W + rho / (2.0 * abs(x) - W)
            return s_q, s_x

        for jp in range(n_p):
            s_q, s_x = pair_terms(px[jp], pq[jp], exclude_pair=jp)
            dpq[jp] = 2.0 - 4.0 * pq[jp] * s_q
            dpx[jp] = s_x
        for i, w in enumerate(rw):
            s_q, s_x = pair_terms(w, 0.0, exclude_real=i)
            drw[i] = s_x
        return dpx, dpq, drw

    def add(state, deriv, h):
        px, pq, rw = state
        dpx, dpq, drw = deriv
        return ([x + h * d for x, d in zip(px, dpx)],
                [q + h * d for q, d in zip(pq, dpq)],
                [w + h * d for w, d in zip(rw, drw)])

    state = ([p["x"] for p in pairs], [p["Q"] for p in pairs], reals)
    h = t_end / n_steps
    t = 0.0
    tstar_ode = None
    q_prev, t_prev = state[1][0], 0.0
    slope0 = None
    trajectory = [(0.0, state[1][0])]
    for _ in range(n_steps):
        k1 = rhs(state)
        if slope0 is None:
            slope0 = 4.0 * k1[1][0]  # dDelta/dt at t=0 (Delta = 4Q)
        k2 = rhs(add(state, k1, h / 2))
        k3 = rhs(add(state, k2, h / 2))
        k4 = rhs(add(state, k3, h))
        state = (
            [x + h / 6 * (a + 2 * b + 2 * c + d) for x, a, b, c, d in
             zip(state[0], k1[0], k2[0], k3[0], k4[0])],
            [q + h / 6 * (a + 2 * b + 2 * c + d) for q, a, b, c, d in
             zip(state[1], k1[1], k2[1], k3[1], k4[1])],
            [w + h / 6 * (a + 2 * b + 2 * c + d) for w, a, b, c, d in
             zip(state[2], k1[2], k2[2], k3[2], k4[2])],
        )
        t += h
        q_now = state[1][0]
        trajectory.append((t, q_now))
        if tstar_ode is None and q_prev < 0 <= q_now:
            tstar_ode = t_prev + (0.0 - q_prev) * (t - t_prev) / (q_now - q_prev)
        q_prev, t_prev = q_now, t
    tail_fraction = (2.0 * rho / W) / (1.0 / (y0 * y0))  # vs the mirror term
    return {
        "tstar_ode": tstar_ode,
        "slope0_ode": slope0,
        "n_reals": len(reals),
        "n_pairs": len(pairs),
        "window": W,
        "rho": rho,
        "tail_term_vs_mirror": tail_fraction,
        "trajectory_Q": [(float(a), float(b)) for a, b in trajectory[:: max(1, n_steps // 200)]],
    }


# ---------------------------------------------------------------------------
# results plumbing
# ---------------------------------------------------------------------------


def load_results(path: str = RESULTS) -> dict:
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


def save_results(update: dict, path: str = RESULTS) -> None:
    data = load_results(path)
    data.update(update)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")


def _n(x, d=17):
    """Compact float for JSON."""
    return float(mp.nstr(mp.mpf(x), d)) if not isinstance(x, float) else x


# ---------------------------------------------------------------------------
# stages
# ---------------------------------------------------------------------------


def stage_validate(out: str) -> None:
    """Route agreement, constant fit, evenness defect, sibling cross-check."""
    t0 = time.time()
    dps = 40
    res: dict = {}
    with mp.workdps(dps + 10):
        kap = kappa(mp.dps)
        flow = DHFlow(dps, z_scale=30.0)
        res["rule"] = {"dps": dps, "U": float(flow.U), "n_gauss": flow.n_gauss,
                       "n_panels": flow.n_panels, "n_nodes": flow.n_nodes}
        # 1) route agreement at t=0 against completed_dh (Hurwitz route)
        rows = []
        worst = mp.mpf(0)
        for zv in [mp.mpf(0), mp.mpf(2), mp.mpf(10), mp.mpf("14.5"),
                   mp.mpf(25), mp.mpc(3, "0.2"), mp.mpc(20, "-0.9")]:
            h = flow.H(zv, 0)
            x = completed_dh(mp.mpf(1) / 2 + mp.mpc(0, 1) * zv, dps=mp.dps)
            d = abs(h - x)
            worst = max(worst, d)
            rows.append({"z": mp.nstr(zv, 8), "abs_defect": mp.nstr(d, 3),
                         "abs_Xi": mp.nstr(abs(x), 3)})
        res["route_agreement_t0"] = {"rows": rows, "worst": mp.nstr(worst, 3)}

        # 2) constants (c, a) in H0(z) = c * Xi_DH(a z), fitted from the data
        h0 = flow.H(0, 0)
        xi0 = completed_dh(mp.mpf(1) / 2, dps=mp.dps)
        c_meas = h0 / xi0
        # curvature route for a: H0''(0) = -int u^2 Phi du
        h0pp = -mp.fsum(w * ph * u * u for u, w, ph in
                        zip(flow.nodes, flow.weights, flow.phis))
        step = mp.mpf(10) ** (-8)
        xipp = (completed_dh(mp.mpf(1) / 2 + mp.mpc(0, 1) * step, dps=mp.dps)
                - 2 * xi0
                + completed_dh(mp.mpf(1) / 2 - mp.mpc(0, 1) * step, dps=mp.dps)) / step ** 2
        a_meas = mp.sqrt((h0pp / h0) / (xipp / xi0))
        res["constants"] = {
            "c_measured": mp.nstr(mp.re(c_meas), 20),
            "a_measured": mp.nstr(mp.re(a_meas), 12),
            "c_minus_1": mp.nstr(abs(c_meas - 1), 3),
            "a_minus_1": mp.nstr(abs(a_meas - 1), 3),
            "note": "curvature route differences completed_dh at h=1e-8, so "
                    "a_measured carries ~h^2 stencil error; c is exact-route",
        }

        # 3) evenness of the raw series (the functional equation in disguise)
        rows = []
        for uv in ("0.1", "0.2", "0.35", "0.5"):
            u = mp.mpf(uv)
            lhs = phi_dh_raw(u, kap)
            rhs = phi_dh_raw(-u, kap)
            rows.append({"u": uv, "abs": mp.nstr(abs(lhs - rhs), 3),
                         "rel": mp.nstr(abs(lhs - rhs) / abs(lhs), 3)})
        res["phi_evenness_defect"] = rows
        res["phi_at_0"] = mp.nstr(phi_dh_raw(0, kap), 25)

        # 4) the same evaluator architecture pointed at zeta's Phi must
        #    reproduce zeta.heatflow.H_t (independent rule construction)
        zflow = _ZetaFlowForValidation(dps)
        rows = []
        worstz = mp.mpf(0)
        for (zv, tv) in [(mp.mpf("28.269"), 0), (mp.mpf(30), mp.mpf("0.3")),
                         (mp.mpf(60), mp.mpf("-0.2")), (mp.mpc(14, "0.5"), mp.mpf("0.1"))]:
            mine = zflow.H(zv, tv)
            theirs = H_t_zeta(zv, tv, dps=dps)
            d = abs(mine - theirs)
            worstz = max(worstz, d)
            rows.append({"z": mp.nstr(zv, 8), "t": mp.nstr(mp.mpf(tv), 4),
                         "abs_diff": mp.nstr(d, 3)})
        res["zeta_sibling_check"] = {"rows": rows, "worst": mp.nstr(worstz, 3)}

    res["seconds"] = round(time.time() - t0, 2)
    save_results({"validate": res}, out)
    print(json.dumps(res, indent=2)[:2400])


class _ZetaFlowForValidation:
    """The DHFlow architecture instantiated for zeta's Phi: same panel logic,
    own integration limit (zeta's integrand dies like exp(-pi e^{4u})), used
    only to show the generic evaluator reproduces zeta.heatflow.H_t."""

    def __init__(self, dps: int, z_scale: float = 70.0):
        self.dps = dps
        with mp.workdps(dps + 10):
            tgt = -(dps + 12) * mp.log(10)
            self.U = +mp.findroot(
                lambda U: mp.mpf("0.12") * U ** 2 + 9 * U + mp.log(2 * mp.pi ** 2)
                - mp.pi * mp.exp(4 * U) - tgt, mp.mpf(1.0))
            self.n_gauss = max(20, min(64, 8 + dps // 3))
            k = self.n_gauss
            omega_p = (8.0 * k / math.e) * 10.0 ** (-(dps + 6) / (2.0 * k))
            self.n_panels = max(int(math.ceil(z_scale * float(self.U) / omega_p)) + 4,
                                24 * 2 ** max(0, math.ceil((dps - 45) / 45)), 16)
            xs, ws = _gauss_legendre(self.n_gauss, dps)
            h = self.U / self.n_panels
            self.nodes, self.weights = [], []
            for p in range(self.n_panels):
                a = p * h
                for x, w in zip(xs, ws):
                    self.nodes.append(a + h * (x + 1) / 2)
                    self.weights.append(w * h / 2)
            self.phis = [Phi_zeta(u, dps=dps) for u in self.nodes]

    H_and_dH = DHFlow.H_and_dH
    H = DHFlow.H


def stage_pair1(out: str) -> None:
    """The famous quadruple, in full: polish, t=0 checks, dense Delta(t)
    sweep for the figure, t*, slope."""
    t0 = time.time()
    res: dict = {}
    pol = polish_pair(1, dps=60)
    res["polished"] = pol
    site = make_site(1, pol)
    res["site"] = {"dps": site["dps"], "radius": site["radius"],
                   "n_nodes": site["flow"].n_nodes, "U": float(site["flow"].U),
                   "n_gauss": site["flow"].n_gauss}

    with mp.workdps(site["dps"]):
        y0 = mp.mpf(pol["y0"])
        gam = mp.mpf(pol["gamma"])
        m0 = contour_moments(site["flow"], mp.mpc(gam, 0), site["radius"], 0.0)
        res["t0_checks"] = {
            "N": m0["N"],
            "winding_defect": mp.nstr(m0["winding_defect"], 3),
            "x_vs_gamma": mp.nstr(abs(m0["x"] - gam), 3),
            "Delta0_vs_minus4y0sq": mp.nstr(abs(m0["Delta"] + 4 * y0 * y0), 3),
            "y0_from_moments": mp.nstr(mp.sqrt(-m0["Delta"]) / 2, 25),
            "y0_from_zero": mp.nstr(y0, 25),
            "im_Delta": mp.nstr(m0["im_Delta"], 3),
            "min_abs_H_on_contour": mp.nstr(m0["min_abs_H"], 3),
        }

    trace: list = []
    tst = find_tstar(site, trace=trace)
    res["tstar"] = tst

    # dense sweep for the figure + measured slope at 0
    y0f = float(mp.mpf(pol["y0"]))
    sweep_ts = [i * 1.15 * tst["tstar"] / 22 for i in range(23)]
    sweep = []
    center = None
    for tv in sweep_ts:
        m = delta_at(site, tv, center=center)
        center = mp.mpc(m["x"], 0)
        sweep.append({"t": tv, "Delta": _n(m["Delta"]), "x": _n(m["x"], 20)})
    res["sweep"] = sweep
    d_first = (sweep[1]["Delta"] - sweep[0]["Delta"]) / (sweep_ts[1] - sweep_ts[0])
    res["slope0_measured"] = d_first
    res["slope_isolated_pair"] = 8.0
    res["seconds"] = round(time.time() - t0, 2)
    save_results({"pair1": res}, out)
    print(json.dumps({k: v for k, v in res.items() if k != "sweep"}, indent=2))


def stage_survey(pairs: list[int], out: str) -> None:
    """t* for the requested quadruples (sparse contour evaluations)."""
    t0 = time.time()
    res: dict = {}
    for k in pairs:
        tk = time.time()
        gamma_seed = float(mp.mpf(LIT_PAIRS[k][1]))
        pol = polish_pair(k, dps=site_dps(gamma_seed, 20))
        site = make_site(k, pol)
        tst = find_tstar(site)
        tst["polished"] = pol
        tst["seconds"] = round(time.time() - tk, 2)
        res[f"pair{k}"] = tst
        print(f"pair {k} (gamma~{gamma_seed:.2f}): t* = {tst['tstar']:.8f} "
              f"(naive {tst['tstar_naive']:.8f}, shave {tst['shave_percent']:.2f}%) "
              f"[{tst['seconds']}s, dps={tst['dps']}]", flush=True)
    res["seconds_total"] = round(time.time() - t0, 2)
    save_results({f"survey_{'_'.join(map(str, pairs))}": res}, out)


def stage_ode(pairs: list[int], out: str) -> None:
    """Null control per pair: census the window, check the accounting,
    integrate the arithmetic-free dynamics, compare t*."""
    t0 = time.time()
    data = load_results()
    res: dict = {}
    # pull every measured pair's polished zero for cross-pair force terms
    polished_all = {}
    for key, blob in data.items():
        if key == "pair1" and "polished" in blob:
            polished_all[1] = blob["polished"]
        if key.startswith("survey"):
            for pk, tst in blob.items():
                if pk.startswith("pair") and isinstance(tst, dict) and "polished" in tst:
                    polished_all[int(pk[4:])] = tst["polished"]

    for k in pairs:
        tk = time.time()
        if k not in polished_all:
            print(f"pair {k}: no polished zero on record yet, run pair1/survey first")
            continue
        pol = polished_all[k]
        gam = float(mp.mpf(pol["gamma"]))
        y0 = float(mp.mpf(pol["y0"]))
        half = 40.0
        reals = line_zeros_near(gam, half)
        n_strip = strip_count_window(gam, half)
        # other known quadruples inside the window
        others = []
        for j, pj in polished_all.items():
            gj = float(mp.mpf(pj["gamma"]))
            if j != k and abs(gj - gam) < half:
                others.append({"x": gj, "y": float(mp.mpf(pj["y0"]))})
        accounted = len(reals) + 2 * (1 + len(others))
        entry: dict = {
            "n_line_zeros": len(reals),
            "n_strip_zeros": n_strip,
            "n_other_pairs_in_window": len(others),
            "accounting_ok": bool(accounted == n_strip),
        }
        if accounted != n_strip:
            # refine the scan once before declaring a discrepancy
            reals = line_zeros_near(gam, half, step_frac=16.0)
            accounted = len(reals) + 2 * (1 + len(others))
            entry["n_line_zeros_refined"] = len(reals)
            entry["accounting_ok"] = bool(accounted == n_strip)
        # measured PDE t* for comparison
        tst_pde = None
        if k == 1 and "pair1" in data:
            tst_pde = data["pair1"]["tstar"]["tstar"]
        else:
            for key, blob in data.items():
                if key.startswith("survey") and f"pair{k}" in blob:
                    tst_pde = blob[f"pair{k}"]["tstar"]
        t_end = 1.25 * (tst_pde if tst_pde else 0.5 * y0 * y0)
        ode = ode_null_control(
            {"gamma": gam, "y0": y0}, reals, others, t_end)
        entry["ode"] = {kk: vv for kk, vv in ode.items() if kk != "trajectory_Q"}
        entry["trajectory_Q"] = ode["trajectory_Q"]
        if tst_pde and ode["tstar_ode"]:
            entry["tstar_pde"] = tst_pde
            entry["tstar_ode"] = ode["tstar_ode"]
            entry["ode_vs_pde_percent"] = 100.0 * (ode["tstar_ode"] / tst_pde - 1.0)
        entry["seconds"] = round(time.time() - tk, 2)
        res[f"pair{k}"] = entry
        print(f"pair {k}: line={len(reals)} strip={n_strip} pairs={1+len(others)} "
              f"ode_t*={ode['tstar_ode']} pde_t*={tst_pde} "
              f"[{entry['seconds']}s]", flush=True)
    res["seconds_total"] = round(time.time() - t0, 2)
    save_results({"ode_null": res}, out)


def stage_lesions(out: str) -> None:
    """(a) clipped contour must refuse; (b) the newborn real pair is invisible
    to a default-step sign scan for a measured while."""
    t0 = time.time()
    data = load_results()
    if "pair1" not in data:
        raise SystemExit("run pair1 first")
    pol = data["pair1"]["polished"]
    tstar = data["pair1"]["tstar"]["tstar"]
    site = make_site(1, pol)
    gam = float(mp.mpf(pol["gamma"]))
    y0 = float(mp.mpf(pol["y0"]))
    res: dict = {}

    # (a) a contour holding exactly one member: N=1 must be refused loudly
    refusal = None
    try:
        contour_moments(site["flow"], mp.mpc(gam, y0), y0, 0.0, expect_n=2)
    except WindingError as e:
        refusal = str(e)
    res["clipped_contour_refused"] = bool(refusal is not None)
    res["refusal_message"] = refusal

    # (a') and a contour *through* the zero neighbourhood: non-integer winding
    grazing = None
    try:
        contour_moments(site["flow"], mp.mpc(gam, 0), y0, 0.0, expect_n=None)
    except WindingError as e:
        grazing = str(e)
    res["grazing_contour"] = grazing if grazing else "integer winding (not on zero)"

    # (b) post-landing blindness of the default grid
    step_default = mean_gap(gam) / 20.0
    slope = data["pair1"]["slope0_measured"]
    res["default_scan_step"] = step_default
    res["blind_until_t_model"] = tstar + step_default ** 2 / slope
    rows = []
    for frac in (0.02, 0.3, 1.0, 3.0):
        tv = tstar * (1.0 + frac * 0.1)
        m = delta_at(site, tv)
        gap = math.sqrt(max(float(m["Delta"]), 0.0)) if m["Delta"] > 0 else 0.0
        # default-step sign scan across the landing site, swept through five
        # grid phases (hunt #3's lesson: a single phase can be lucky, the
        # newborn pair is visible exactly when it straddles a grid point)
        n_pts = int(4.0 / step_default) + 2
        per_phase = []
        with mp.workdps(20):
            for ph in range(5):
                lo = m["x"] - 2.0 + step_default * ph / 5.0
                vals = []
                for i in range(n_pts):
                    zv = lo + i * step_default
                    vals.append(mp.sign(mp.re(site["flow"].H(zv, tv))))
                changes = sum(1 for a, b in zip(vals, vals[1:])
                              if a != 0 and b != 0 and a != b)
                per_phase.append(changes)
        # 3 changes = newborn pair resolved (plus the fixed zero at 87.65);
        # 1 change = the pair is invisible at this phase
        rows.append({"t": tv, "gap": gap, "gap_over_step": gap / step_default,
                     "sign_changes_by_phase": per_phase,
                     "phases_seeing_pair": sum(1 for c in per_phase if c >= 3),
                     "N_contour": 2})
    res["post_landing_scan"] = rows
    res["seconds"] = round(time.time() - t0, 2)
    save_results({"lesions": res}, out)
    print(json.dumps(res, indent=2))


def stage_precision(out: str) -> None:
    """t* for pair 1 at three precisions and two contour node counts."""
    t0 = time.time()
    data = load_results()
    if "pair1" not in data:
        raise SystemExit("run pair1 first")
    pol = data["pair1"]["polished"]
    res: dict = {"runs": []}
    base = None
    for extra, M in ((14, 96), (24, 96), (40, 96), (24, 192)):
        site = make_site(1, pol, extra_dps=extra)
        tst = find_tstar(site, M=M, tol=1e-10)
        row = {"dps": site["dps"], "M": M, "tstar": tst["tstar"],
               "n_contour_evals": tst["n_contour_evals"]}
        if base is None:
            base = tst["tstar"]
        row["diff_vs_first"] = tst["tstar"] - base
        res["runs"].append(row)
        print(row, flush=True)
    spread = max(r["tstar"] for r in res["runs"]) - min(r["tstar"] for r in res["runs"])
    res["spread"] = spread
    res["seconds"] = round(time.time() - t0, 2)
    save_results({"precision": res}, out)
    print(json.dumps(res, indent=2))


def stage_figure(out: str) -> None:
    """Two panels: pair 1's landing (Delta(t) PDE vs ODE null), and the
    survey t* vs the naive y0^2/2 across quadruples."""
    import matplotlib

    matplotlib.use("Agg")  # before pyplot, per repo rule
    import matplotlib.pyplot as plt

    data = load_results()
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12.5, 4.6))

    p1 = data["pair1"]
    ts = [row["t"] for row in p1["sweep"]]
    ds = [row["Delta"] for row in p1["sweep"]]
    ax1.axhline(0.0, color="0.6", lw=0.8)
    ax1.plot(ts, ds, "o-", ms=3.5, lw=1.2, color="#1f77b4",
             label=r"measured $\Delta(t)=2q_2-q_1^2$ (contour moments)")
    if "ode_null" in data and "pair1" in data["ode_null"]:
        traj = data["ode_null"]["pair1"]["trajectory_Q"]
        ax1.plot([a for a, _ in traj], [4 * b for _, b in traj], "--",
                 lw=1.2, color="#d62728",
                 label=r"$N$-body null control $4Q(t)$ (no arithmetic)")
    tstar = p1["tstar"]["tstar"]
    ax1.axvline(tstar, color="#1f77b4", lw=0.8, ls=":")
    ax1.annotate(rf"$t^\ast = {tstar:.5f}$", (tstar, 0),
                 xytext=(tstar * 0.62, -0.16), fontsize=10,
                 arrowprops=dict(arrowstyle="->", lw=0.8))
    ax1.set_xlabel("flow time $t$")
    ax1.set_ylabel(r"pair discriminant $\Delta(t)$")
    ax1.set_title("Pair 1 (height 85.70): the landing, analytic through the collision")
    ax1.legend(fontsize=8, loc="upper left")

    ks, naive, meas = [], [], []
    for k in range(1, 10):
        tst = None
        if k == 1:
            tst = p1["tstar"]
        else:
            for key, blob in data.items():
                if key.startswith("survey") and f"pair{k}" in blob:
                    tst = blob[f"pair{k}"]
        if tst:
            ks.append(k)
            naive.append(tst["tstar_naive"])
            meas.append(tst["tstar"])
    width = 0.38
    ax2.bar([k - width / 2 for k in ks], naive, width, color="0.75",
            label=r"isolated-pair model $y_0^2/2$")
    ax2.bar([k + width / 2 for k in ks], meas, width, color="#1f77b4",
            label=r"measured $t^\ast$")
    if meas:
        imax = max(range(len(meas)), key=lambda i: meas[i])
        ax2.annotate(rf"$\max$: pair {ks[imax]}"
                     f"\n$t^*={meas[imax]:.4f}$",
                     (ks[imax] + width / 2, meas[imax]), xytext=(ks[imax] - 2.2,
                     meas[imax] * 1.04), fontsize=9,
                     arrowprops=dict(arrowstyle="->", lw=0.8))
        ax2.axhline(meas[imax], color="#1f77b4", lw=0.7, ls=":", alpha=0.6)
    ax2.set_xticks(ks)
    ax2.set_xticklabels([f"{k}\n{LIT_PAIRS[k][1][:5]}" for k in ks], fontsize=8)
    ax2.set_xlabel("quadruple (height)")
    ax2.set_ylabel(r"repair time")
    ax2.set_title(r"The survey: every measured $t^\ast$ is a lower bound for $\Lambda_{DH}$")
    ax2.legend(fontsize=8)
    fig.suptitle("The heat-flow clock on the Davenport–Heilbronn counterexample "
                 "(hunt #4, a probe, not a result)", fontsize=11)
    fig.tight_layout(rect=[0, 0, 1, 0.94])
    png = os.path.join(HERE, "flow_repair.png")
    fig.savefig(png, dpi=160)
    print("wrote", png)


def stage_merge() -> None:
    """Fold results_*.json partials into results.json and remove them."""
    for path in sorted(glob.glob(os.path.join(HERE, "results_*.json"))):
        with open(path, "r", encoding="utf-8") as f:
            save_results(json.load(f))
        os.remove(path)
        print("merged", os.path.basename(path))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("stage", choices=["validate", "pair1", "survey", "ode",
                                      "lesions", "precision", "figure", "merge"])
    ap.add_argument("--pairs", default="2,3,4,5",
                    help="comma-separated quadruple indices for survey/ode")
    ap.add_argument("--out", default=RESULTS,
                    help="write results here (use a partial file for "
                         "concurrent stages, then run merge)")
    args = ap.parse_args()
    pairs = [int(s) for s in args.pairs.split(",") if s.strip()]
    if args.stage == "validate":
        stage_validate(args.out)
    elif args.stage == "pair1":
        stage_pair1(args.out)
    elif args.stage == "survey":
        stage_survey(pairs, args.out)
    elif args.stage == "ode":
        stage_ode(pairs, args.out)
    elif args.stage == "lesions":
        stage_lesions(args.out)
    elif args.stage == "precision":
        stage_precision(args.out)
    elif args.stage == "figure":
        stage_figure(args.out)
    elif args.stage == "merge":
        stage_merge()


if __name__ == "__main__":
    main()
