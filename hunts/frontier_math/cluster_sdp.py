"""The R-vs-D trade, supplied as constraints, and the SDP re-run with them.

WHY THIS MODULE EXISTS.  ``sos_certificate.py`` put the whole multi-pair
obligation into one matrix inequality

    Xi(Q) = sum_{a,b} c(a,b) Q(a,b)^2 - 4k  >=  0,
    Q(a,b) = Psi(zeta_a + conj zeta_b)/A,

over the atom set ``zeta = i x_j`` (on-line) and ``zeta = +/- y_i + i t_i``
(pairs), and then closed that route: :func:`sos_certificate.cone_violator`
is an exactly rational family satisfying positive semidefiniteness, the
involution relations, ``diag >= 1`` and Cauchy-Schwarz while driving
``Xi -> -infinity``.  Its witness is not realizable (relative fit residual
0.135) and the diagnosis recorded there is precise:

    *a pointwise entry bound cannot close a joint obligation; what is
    missing is the R-vs-D trade -- the on-line atoms cannot all sit at the
    damage minimum at once.*

This module supplies that trade.  Every constraint below is DERIVED from
one structural fact the earlier attempt never used, and each is measured
on genuine configurations before it is imposed.

THE ONE FACT.  ``g(u) = cos(sqrt2 u) 1_{|u| <= 1/2} >= 0``, so
``dmu = g du / A`` is a PROBABILITY measure on ``[-1/2, 1/2]`` and
``Q(a,b) = int e^{zeta_a u} conj(e^{zeta_b u}) dmu(u)``.  Consequently the
SQUARES that the objective actually sums are moments of the self-
convolution ``nu = mu * mu``, a probability measure on ``[-1, 1]`` with
density ``c2/A^2``:

    Q(a,b)^2 = T(zeta_a + conj zeta_b),   T(z) = int_{-1}^{1} e^{zw} dnu(w).

So the whole objective is a 2-body energy in ONE positive measure, and the
on-line block, the cross block and the pair block are values of the SAME
function at arguments built from the SAME real numbers.  That is the
coupling the earlier lift could not see, because it treated the entries of
``Q`` as free reals.

WHAT IS DERIVED (section 2), with the constant each one costs:

  (T1) SHADOW ATOMS.  For each pair ``p`` adjoin the on-line-type atom
       ``zeta = i t_p`` -- the pair's own centre, put on the line.  It is
       a legitimate extra atom of the same Gram matrix, it carries weight
       0 in the objective, and it makes three families of entries members
       of one matrix: ``Q(a, w_p) = G(x_a - t_p)`` (a LINE entry),
       ``Q(a, P+) = psi(y_p + i(x_a - t_p))`` (a CROSS entry) and
       ``Q(w_p, P+) = psi(y_p)`` (a CONSTANT of the depth).  The cross
       block and the on-line block stop being independent.

  (T2) THE DEPTH CURVE.  ``Q(w_p, P+) = psi(y_p) =: r_p`` and
       ``Q(P+,P+) = psi(2 y_p) =: d_p`` are two values of one parameter, so
       ``(r_p, d_p)`` lies on the curve ``{(psi(y), psi(2y)) : y in
       [0,1/2]}``.  ``d`` is a convex function of ``r`` along it, so its
       convex hull is cut by tangents from below and one chord from above.
       The earlier lift had no relation between a pair's diagonal and
       anything else.

  (T3) DAMAGE AGAINST BUDGET (joint, not pointwise).  For a cross entry
       ``C = psi(y + is)`` and the same pair's diagonal ``d = psi(2y)``,

           Re(C^2)  >=  -C_DAMAGE * (d^2 - 1),     C_DAMAGE = 0.0651241,

       measured over ``s`` in [0,300] and ``y`` in (0,1/2].  ``d^2 - 1`` is
       exactly the pair's own budget over ``4k`` (``2(d^2-1)`` for one
       pair), so this ties the damage an on-line atom can do to the budget
       the pair carrying it must pay.  It is what makes the k = 1 relaxation
       positive up to ``n = 1/(2 C_DAMAGE) = 7.68``.

  (T4) THE TRADE CUT.  ``Re(C^2) >= Q(a,w_p)^2 - C_TRADE (d^2-1)`` with
       ``C_TRADE = 0.147218``: an on-line atom close to the pair centre
       (line entry near 1) cannot damage at all.  This is the joint
       constraint in its most direct form -- a cross entry bounded by a
       LINE entry -- and it is the one the earlier attempt asked for.

  (T5) BAND LIMITATION (the localizing matrix).  ``supp mu`` is contained
       in ``[-1/2,1/2]``, so with ``Q_r(a,b) = int u^r e^{...} dmu`` the
       moment matrix ``[[Q, Q_1],[Q_1^H, Q_2]]`` is positive semidefinite
       (Gram of ``{f_a} u {u f_a}``) and the localizing matrix
       ``Q/4 - Q_2`` is too.  This is the candidate the earlier module
       named and did not build.

  (T6) THE TWO BOUNDS ALREADY PROVED.  ``sum over the pair block of
       Q^2 >= 4k`` (``PairEnergy.lean``, zero sorry) and the generalised
       inertia bound ``sum_{a,b} Q^2 >= (n+2k)^2/(n+k)``
       (``sos_certificate.inertia_bound``).  The degree-2 lift cannot see
       either -- both are inertia facts -- so they are supplied rather
       than rediscovered.

WHAT COMES OUT.

  (F1) The entry-level SDP with (T1)-(T6) returns ``0`` at every size with
       ``k = 1`` and ``n <= 7``, against ``(1-theta) n(n-1) - n^2 - 4k``
       for the earlier lift (``-19.94`` at (4,1), ``-67.72`` at (8,1)).
       For ``n >= 8`` it returns ``(psi(1)^2-1)(2 - 4 n C_DAMAGE)``
       (``-0.00672`` at (8,1)), a deficit LINEAR in n instead of
       quadratic; for ``k >= 2`` it returns ``-0.0533`` at (2,2) and
       ``-0.6667`` at (8,4), reaching ``-4 n k C_DAMAGE (psi(1)^2-1)``
       exactly at ``k = 4``.  It also returns 0 at every ``(0,k)``, which
       the earlier lift could not (its finding F4).  Values in
       :data:`TRADE_RECORD`.

  (F2) ``cone_violator`` is excluded, and the screen names which constraint
       does it: the depth cap ``d <= psi(1) = 1.0392`` kills the exact
       rational family outright (it has ``d = 1 + 2t^2 >= 1.5``), and with
       ``t`` rescaled so that ``d`` is admissible, (T3) kills what is left
       -- its cross entries are purely imaginary of modulus ``t``, so
       ``Re(C^2) = -t^2`` while (T3) allows only ``-0.0651 (d^2-1) =
       -0.0052``.  Reported entry by entry in :func:`violator_screen`.

  (F3) THE REMAINING DEFICIT IS A COUNTING FACT, and the entry level cannot
       see it.  What the SDP still cannot exclude is n atoms all attaining
       the worst cross entry at once.  In truth the damage of an on-line
       atom at offset ``s`` from a pair is ``D(s,y) = -4 Re psi(y+is)^2``,
       which is POSITIVE only inside narrow windows near ``s = 2 pi j``
       (measured: 47 windows in ``[0,300]`` at ``y = 1/2``, widths 0.96,
       peaks 0.02083, 0.00462, 0.00201, ... falling like ``1/j^2``), and two
       atoms in the same window are nearly coincident, which charges
       ``(1-theta)`` per pair of them.  That is a statement about how many
       atoms fit in a window -- degree 3 and higher in the entries -- so no
       degree-2 cut on pairs of entries can carry it.

  (F4) SO THE TRADE IS SUPPLIED AT THE CONFIGURATION LEVEL INSTEAD, and
       there it CLOSES the single-pair case for every n at once.
       :func:`window_occupancy_bound` charges each damage window
       separately,

           Xi  >=  budget(y) - 2 sum_j max_{N in Z>=0}
                        [ N D_j - (1-theta) gamma_j N (N-1) ],

       every term of which is one-sided (window peak up, repulsion down,
       cross-window and out-of-window repulsion dropped).  Measured at
       ``y = 1/2``: ``0.15996 - 2(0.045991 + 0.000391) = +0.06720``, and
       the margin is positive at every depth -- 42% of the budget survives
       at ``y = 1/2`` and 60% at small depth.  The bound
       contains no ``n`` at all -- the occupancy N is optimised away -- so
       it is size-independent by construction.  The cluster SDP
       (:func:`cluster_relaxation`) is the same statement solved as a
       moment program and agrees (+0.0690 at grid 0.5, +0.0551 at grid
       1.0, both after the tail).  Like everything else here it is a
       MEASURED one-sided accounting on a grid and not an enclosure:
       gaps G1 and G2 of :data:`NAMED_GAPS` say exactly what would have
       to be tightened before it could be called more than that.

  (F5) AND IT DOES NOT REACH ``k >= 2``, for one measured reason.  The same
       accounting needs ``budget(P) >= 0.5799 sum_p slack(y_p)`` while
       ``joint_universal``'s measured budget floor is
       ``0.2918 sum_p slack``, a factor 1.99 short.  The k >= 2 gap is
       therefore located on the BUDGET side (non-additivity of the pair
       block), not on the damage side.

  (F6) SIZE INDEPENDENCE, both halves.  The entry-level program's tight
       sizes are carried by a multiplier with no size in it at all --
       weight 1 on the pair block's identity and weight 2 on every
       cross-entry (T3) cut (:func:`entry_dual_certificate`) -- and that
       multiplier is nonnegative exactly while ``n <= 7.68``.  So a
       size-independent dual exists and is insufficient, the same shape of
       finding as ``sos_certificate.inertia_multiplier``.  The window
       bound's certificate is also size-free but is NOT a per-entry
       constant: it is the occupancy schedule ``N_j = 3, 1, 1, 1, ...``
       against a peak law ``D_j (2 pi j)^2 -> 8 c^2 (cosh y - 1)``,
       ``c = cos(sqrt2/2)/A``, which :func:`window_peak_fit` measures at
       0.6991956 against the predicted 0.6991402 (relative error 3.0e-4
       over the far half of the windows).  That closed form is what makes
       the schedule summable, and it is why the second certificate reaches
       every ``n`` while the first stops at 7.

Nothing here computes a proportion and nothing here is evidence about RH.
No claim in this file is a proof of the universally quantified statement:
the window bound is a measured one-sided accounting on a grid, its named
gaps are listed in :data:`NAMED_GAPS`, and every relaxation value is
labelled as a relaxation value.

Run ``.venv/bin/python hunts/frontier_math/cluster_sdp.py`` (~40 s).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import A, MEAN_GAP, phipap  # noqa: E402
from sos_certificate import (  # noqa: E402
    PHI_MIN,
    PSI_HALF,
    PSI_ONE,
    THETA_FULL,
    Psi,
    atoms,
    cone_violator,
    qmat,
    target_from_config,
)

__all__ = [
    "psi", "line_kernel", "cross_entry", "damage", "budget", "slack",
    "window_peak_fit", "entry_dual_certificate", "multi_pair_requirement",
    "nu_moment_defect", "C_DAMAGE", "C_TRADE", "depth_curve_cuts",
    "constraint_defects", "relax_trade", "trade_scan", "violator_screen",
    "damage_windows", "window_occupancy_bound", "window_scan",
    "cluster_relaxation", "TRADE_RECORD", "WINDOW_RECORD", "NAMED_GAPS",
    "CONSTANT_LADDER", "constant_ladder",
]


# ---------------------------------------------------------------------------
# 1. the kernel layer: one positive measure, and everything else its moments
# ---------------------------------------------------------------------------


def psi(z):
    """``psi(z) = Psi(z)/A = int e^{zu} dmu(u)``, ``dmu = g du / A``.

    ``g >= 0`` on its support (``cos(sqrt2 u) >= cos(sqrt2/2) > 0`` for
    ``|u| <= 1/2``), so ``mu`` is a probability measure on ``[-1/2, 1/2]``
    and ``psi`` is its two-sided Laplace transform.  ``psi(0) = 1``,
    ``psi`` is even, and ``psi(x) >= 1`` for real ``x`` by ``cosh >= 1``.
    """
    return Psi(z) / A


def line_kernel(v):
    """``G(v) = psi(i v) = phipap(v)/A``: the on-line entry at separation
    ``v``.  Real and even because ``mu`` is; ``G(0) = 1``; ``|G| <= 1``
    since ``mu`` is a probability measure; and ``G`` is a positive-definite
    function of ``v`` (Bochner, ``mu >= 0``), which is why the on-line
    block is positive semidefinite as a function on the reals."""
    return np.real(phipap(np.asarray(v, float))) / A


def cross_entry(s, y):
    """``C(s,y) = psi(y + i s)``: the entry between an on-line atom at
    offset ``s`` from a pair's centre and that pair's ``+y`` atom.  Note
    ``C(s,y)`` and ``G(s)`` are values of ONE analytic function at
    arguments differing by the real shift ``y``."""
    return psi(np.asarray(y, float) + 1j * np.asarray(s, float))


def damage(s, y):
    """``D(s,y) = -4 Re psi(y+is)^2``: what one on-line atom at offset ``s``
    subtracts from the obligation, for one pair of depth ``y``.

    DERIVATION.  The cross block of the matrix form is ``2 Re sum_{a in On,
    b in Pr} Q(a,b)^2``.  The two atoms of a pair contribute
    ``Q(a,P-) = conj Q(a,P+)`` (from (Q3)), so their squares have equal
    real parts and the pair contributes ``4 Re Q(a,P+)^2 = -D``.
    """
    return -4.0 * np.real(cross_entry(s, y) ** 2)


def slack(y):
    """``psi(2y)^2 - 1``: the pair diagonal's excess over the on-line one,
    squared.  Zero exactly at ``y = 0``."""
    return float(np.real(psi(2.0 * float(y)))) ** 2 - 1.0


def budget(y):
    """``2(psi(2y)^2 - 1)``: one pair's block minus its share of ``4k``.

    The pair block of a single pair is ``Q(P+,P+)^2 + Q(P-,P-)^2 +
    2 Q(P+,P-)^2 = 2 d^2 + 2`` with ``d = psi(2y)`` (by (Q2),
    ``Q(P+,P-) = 1``), so ``pair block - 4 = 2(d^2 - 1)``.  Exact, no
    quadrature.
    """
    return 2.0 * slack(y)


def nu_moment_defect(zs=(0.3, 1.0j, 0.2 + 3.0j, -0.4 + 1.7j),
                     n: int = 400001) -> float:
    """Control on the one structural fact: ``psi(z)^2 = int e^{zw} dnu(w)``
    with ``dnu = c2 dw / A^2`` the self-convolution of ``mu``.

    DERIVATION.  ``psi(z)^2 = int int e^{z(u+u')} dmu(u) dmu(u')`` is the
    transform of the push-forward of ``mu x mu`` under addition, i.e. of
    ``mu * mu``; and ``mu * mu`` has density ``c2/A^2`` because ``c2`` is
    the autocorrelation of ``g`` and ``g`` is even.  Measured against
    ``joint_universal.autocorr``'s closed form by quadrature; the residual
    is the grid's error, and it falls as the grid is refined.
    """
    from joint_universal import autocorr  # local: heavy import
    w = np.linspace(-1.0, 1.0, n)
    c2 = autocorr(w)
    worst = 0.0
    for z in zs:
        integ = np.trapezoid(c2 * np.exp(np.real(z) * w) *
                             np.cos(np.imag(z) * w), w) / A ** 2
        worst = max(worst, abs(integ - float(np.real(psi(z) ** 2))))
    return float(worst)


# ---------------------------------------------------------------------------
# 2. the derived constants of the trade
# ---------------------------------------------------------------------------


def _measure_damage_constant(s_max: float = 300.0, n_s: int = 600001,
                             n_y: int = 401) -> dict:
    """``C_DAMAGE = max_{y in (0,1/2], s} [-Re psi(y+is)^2] / (psi(2y)^2-1)``.

    Both sides vanish at ``y = 0`` like ``y^2``, so the ratio has a finite
    limit; the maximum is attained at the boundary ``y = 1/2``.  This is a
    MEASURED constant on a grid, re-run up a ladder by
    :func:`constant_ladder`.
    """
    ss = np.linspace(0.0, s_max, n_s)
    best, arg = -np.inf, None
    for y in np.linspace(1e-3, 0.5, n_y):
        v = np.real(cross_entry(ss, y) ** 2)
        sl = slack(y)
        i = int(np.argmin(v))
        r = -v[i] / sl
        if r > best:
            best, arg = r, (float(y), float(ss[i]))
    return {"constant": float(best), "argmax": arg,
            "s_max": s_max, "n_s": n_s, "n_y": n_y}


def _measure_trade_constant(s_max: float = 300.0, n_s: int = 600001,
                            n_y: int = 201) -> dict:
    """``C_TRADE = max_{y,s} [G(s)^2 - Re psi(y+is)^2] / (psi(2y)^2-1)``.

    The constant of (T4).  At ``y -> 0`` the numerator is
    ``G(s)^2 - G(s)^2 = 0`` to first order and the denominator vanishes
    quadratically, so the ratio is again finite; the measured argmax sits
    at small ``y``.
    """
    ss = np.linspace(0.0, s_max, n_s)
    g2 = line_kernel(ss) ** 2
    best, arg = -np.inf, None
    for y in np.linspace(1e-3, 0.5, n_y):
        v = np.real(cross_entry(ss, y) ** 2)
        sl = slack(y)
        r = (g2 - v) / sl
        i = int(np.argmax(r))
        if r[i] > best:
            best, arg = float(r[i]), (float(y), float(ss[i]))
    return {"constant": float(best), "argmax": arg,
            "s_max": s_max, "n_s": n_s, "n_y": n_y}


#: (T3)'s constant.  ``Re psi(y+is)^2 >= -C_DAMAGE (psi(2y)^2 - 1)``.
C_DAMAGE = 0.06512409723687337

#: (T4)'s constant.  ``Re psi(y+is)^2 >= G(s)^2 - C_TRADE (psi(2y)^2 - 1)``.
C_TRADE = 0.1472177115605612

#: ``1/(2 C_DAMAGE)``: the number of on-line atoms one pair's budget pays
#: for at the worst cross entry.  Derived in one line from (T3):
#: ``Xi >= 2(d^2-1) - 4 n C_DAMAGE (d^2-1)``.
N_PAID_FOR = 1.0 / (2.0 * C_DAMAGE)


def constant_ladder(kind: str = "damage",
                    ladder=((100.0, 200001, 101), (200.0, 400001, 201),
                            (300.0, 600001, 401))) -> list:
    """The precision-response control the hunt's checklist asks for: each
    measured constant re-run up a discretisation ladder."""
    f = (_measure_damage_constant if kind == "damage"
         else _measure_trade_constant)
    return [f(s_max=s, n_s=ns, n_y=ny) for s, ns, ny in ladder]


def depth_curve_cuts(n_tangent: int = 12) -> dict:
    """(T2) as linear inequalities in ``(r, d) = (psi(y), psi(2y))``.

    DERIVATION.  Along the curve, ``dd/dr = 2 psi'(2y)/psi'(y)``, and
    ``psi'`` is positive and increasing on ``[0, 1]`` (``psi'(x) =
    int u sinh(xu) dmu >= 0`` with an increasing integrand), so ``dd/dr``
    increases with ``y``: ``d`` is a CONVEX function of ``r``.  Hence
      * from below, every tangent is a valid cut
        ``d >= d_0 + m_0 (r - r_0)``;
      * from above, the chord through the endpoints
        ``(1,1)`` and ``(psi(1/2), psi(1))`` is a valid cut
        ``d <= 1 + M (r - 1)``, ``M = (psi(1)-1)/(psi(1/2)-1)``.
    Returns ``{"tangents": [(r0, d0, m0)], "chord": M, "r_max": psi(1/2),
    "d_max": psi(1)}``; convexity itself is measured by
    :func:`depth_curve_convexity_defect`.
    """
    from paper_chain import phipap_d1
    ys = np.linspace(1e-6, 0.5, n_tangent)
    tang = []
    for y in ys:
        r0 = float(np.real(psi(y)))
        d0 = float(np.real(psi(2 * y)))
        # psi(z) = phipap(-i z), so psi'(x) = -i phipap'(-i x)/A on the reals
        dr = float(np.real(-1j * phipap_d1(-1j * y))) / A
        dd = 2.0 * float(np.real(-1j * phipap_d1(-2j * y))) / A
        m0 = dd / dr if abs(dr) > 1e-12 else 0.0
        tang.append((r0, d0, m0))
    chord = (PSI_ONE - 1.0) / (PSI_HALF - 1.0)
    return {"tangents": tang, "chord": chord, "r_max": PSI_HALF,
            "d_max": PSI_ONE}


def depth_curve_convexity_defect(n: int = 400) -> float:
    """Measured convexity of ``d`` as a function of ``r`` along the depth
    curve: the worst violation of the secant test.  Nonpositive means the
    tangent cuts of :func:`depth_curve_cuts` are valid."""
    ys = np.linspace(1e-6, 0.5, n)
    r = np.array([float(np.real(psi(y))) for y in ys])
    d = np.array([float(np.real(psi(2 * y))) for y in ys])
    worst = -np.inf
    for i in range(1, n - 1):
        lam = (r[i] - r[i - 1]) / (r[i + 1] - r[i - 1])
        secant = (1 - lam) * d[i - 1] + lam * d[i + 1]
        worst = max(worst, d[i] - secant)
    return float(worst)


# ---------------------------------------------------------------------------
# 3. the constraints, measured on genuine configurations
# ---------------------------------------------------------------------------


def augmented_atoms(online, pairs):
    """The atom set of (T1): on-line atoms, then one SHADOW atom ``i t_p``
    per pair, then the pair atoms.

    Returns ``(zeta, sigma, kinds)`` with ``kinds`` 0 = on-line (carries
    objective weight), 2 = shadow (weight 0), 1 = pair.  ``sigma`` fixes
    every on-line and shadow atom and swaps the two atoms of each pair.
    """
    xs = [float(x) for x in online]
    ps = [(float(t), float(y)) for t, y in pairs]
    zeta = [1j * x for x in xs]
    kinds = [0] * len(xs)
    for t, _y in ps:
        zeta.append(1j * t)
        kinds.append(2)
    sigma = list(range(len(zeta)))
    for t, y in ps:
        a = len(zeta)
        zeta += [y + 1j * t, -y + 1j * t]
        kinds += [1, 1]
        sigma += [a + 1, a]
    return (np.array(zeta, complex), np.array(sigma, int),
            np.array(kinds, int))


def constraint_defects(online, pairs) -> dict:
    """Every derived constraint, measured on ONE genuine configuration.

    Each entry is a SIGNED SLACK: nonnegative means the configuration
    satisfies the constraint.  A negative number is a bug in the
    derivation, not a tightening -- which is what
    ``test_cluster_sdp.py``'s
    ``test_every_derived_constraint_holds_on_genuine_configurations``
    checks over a sample.
    """
    z, sig, kinds = augmented_atoms(online, pairs)
    Q = qmat(z)
    N = len(z)
    ps = [(float(t), float(y)) for t, y in pairs]
    line = np.flatnonzero(kinds != 1)
    on = np.flatnonzero(kinds == 0)
    out = {}

    ev = np.linalg.eigvalsh((Q + Q.conj().T) / 2) if N else np.zeros(1)
    out["T1_psd"] = float(ev.min()) if N else 0.0
    out["T1_hermitian"] = -float(np.abs(Q - Q.conj().T).max()) if N else 0.0
    # (T1) the shadow rows are genuine entries of the same Gram matrix:
    # Q(a, w_p) must equal G(x_a - t_p) and Q(w_p, P+_p) must equal psi(y_p)
    d1 = d2 = 0.0
    for i, (t, y) in enumerate(ps):
        w = len(on) + i
        pplus = len(on) + len(ps) + 2 * i
        for a in on:
            d1 = max(d1, abs(Q[a, w] - line_kernel(float(np.imag(z[a])) - t)))
        d2 = max(d2, abs(Q[w, pplus] - float(np.real(psi(y)))))
        d2 = max(d2, abs(Q[w, pplus + 1] - float(np.real(psi(y)))))
    out["T1_shadow_is_line_entry"] = -d1
    out["T1_shadow_pair_entry_is_psi_y"] = -d2

    # (T2) the depth curve, as the cuts impose it
    cuts = depth_curve_cuts()
    worst_t, worst_c = math.inf, math.inf
    for i, (_t, y) in enumerate(ps):
        r = float(np.real(psi(y)))
        d = float(np.real(psi(2 * y)))
        for (r0, d0, m0) in cuts["tangents"]:
            worst_t = min(worst_t, d - (d0 + m0 * (r - r0)))
        worst_c = min(worst_c, 1.0 + cuts["chord"] * (r - 1.0) - d)
    out["T2_tangent_cuts"] = float(worst_t) if ps else 0.0
    out["T2_chord_cut"] = float(worst_c) if ps else 0.0

    # (T3) and (T4) on every (line atom, pair atom) entry
    w3, w4 = math.inf, math.inf
    for i, (_t, y) in enumerate(ps):
        d = float(np.real(psi(2 * y)))
        wsh = len(on) + i
        for b in (len(on) + len(ps) + 2 * i, len(on) + len(ps) + 2 * i + 1):
            for a in line:
                re2 = float(np.real(Q[a, b] ** 2))
                w3 = min(w3, re2 + C_DAMAGE * (d * d - 1.0))
                g2 = float(np.real(Q[a, wsh])) ** 2
                w4 = min(w4, re2 - g2 + C_TRADE * (d * d - 1.0))
    out["T3_damage_vs_budget"] = float(w3) if ps else 0.0
    out["T4_trade_cut"] = float(w4) if ps else 0.0

    # (T5) the localizing matrices
    loc = localizing_defect(z)
    out["T5_moment_matrix"] = loc["moment_min_eig"]
    out["T5_localizing"] = loc["localizing_min_eig"]

    # (T6) the two bounds already proved
    pr = np.flatnonzero(kinds == 1)
    k = len(ps)
    n = len(on)
    pair_block = float(np.real((Q[np.ix_(pr, pr)] ** 2).sum()))
    out["T6_pair_block_ge_4k"] = pair_block - 4 * k
    orig = np.concatenate([on, pr]).astype(int)
    tot = float(np.real((Q[np.ix_(orig, orig)] ** 2).sum()))
    out["T6_inertia"] = tot - ((n + 2 * k) ** 2 / (n + k) if n + k else 0.0)

    # ranges used as first-moment constraints
    lb = np.real(Q[np.ix_(line, line)])
    out["range_line_lower"] = float(lb.min()) - PHI_MIN if len(line) else 0.0
    out["range_line_upper"] = 1.0 - float(lb.max()) if len(line) else 0.0
    if len(pr):
        out["range_pair_diag"] = PSI_ONE - float(np.real(np.diag(Q)[pr]).max())
        cr = np.abs(Q[np.ix_(line, pr)])
        out["range_cross_modulus"] = (PSI_HALF - float(cr.max())
                                      if cr.size else 0.0)
    return out


def localizing_defect(zeta) -> dict:
    """(T5) measured: the moment matrix and the localizing matrix of the
    multiplication operator by ``u``.

    DERIVATION.  With ``f_a(u) = e^{zeta_a u}`` in ``L^2(mu)`` and
    ``Q_r(a,b) = int u^r f_a conj(f_b) dmu = psi^{(r)}(zeta_a + conj
    zeta_b)``, the Gram matrix of ``{f_a} u {u f_a}`` is
    ``[[Q_0, Q_1],[Q_1^H, Q_2]]``, positive semidefinite by construction;
    and ``u^2 <= 1/4`` on ``supp mu`` makes ``(1/4) Q_0 - Q_2`` the Gram
    matrix against the nonnegative measure ``(1/4 - u^2) dmu``, so it is
    positive semidefinite too.  Derivatives of ``psi`` are taken by the
    ``phipap`` derivatives ``paper_chain`` pins.
    """
    from paper_chain import phipap_d1, phipap_d2
    z = np.asarray(zeta, complex)
    S = z[:, None] + np.conj(z)[None, :]
    Q0 = Psi(S) / A
    # psi(z) = phipap(-i z)  =>  d/dz psi = -i phipap'(-i z), and
    # d^2/dz^2 psi = - phipap''(-i z).
    Q1 = (-1j) * phipap_d1(-1j * S) / A
    Q2 = (-1.0) * phipap_d2(-1j * S) / A
    n = len(z)
    if n == 0:
        return {"moment_min_eig": 0.0, "localizing_min_eig": 0.0}
    M = np.block([[Q0, Q1], [Q1.conj().T, Q2]])
    L = 0.25 * Q0 - Q2
    return {"moment_min_eig": float(np.linalg.eigvalsh(
                (M + M.conj().T) / 2).min()),
            "localizing_min_eig": float(np.linalg.eigvalsh(
                (L + L.conj().T) / 2).min())}


#: Genuine configurations the constraint validators run against.  Mixed
#: sizes, depths and spacings, including the two degenerate ends.
SAMPLE_CONFIGS = [
    ("n=1 k=1 deep", [0.7], [(0.0, 0.49)]),
    ("n=3 k=1 lattice", [0.0, MEAN_GAP, 2 * MEAN_GAP], [(3.1, 0.30)]),
    ("n=2 k=2 mixed", [-1.4, 2.6], [(0.0, 0.10), (5.5, 0.45)]),
    ("n=4 k=3 tight", [0.0, 0.3, 0.9, 1.7],
     [(0.05, 0.49), (0.21, 0.49), (0.44, 0.02)]),
    ("n=5 k=2 sparse", [-12.0, -4.0, 0.0, 6.5, 15.2],
     [(-8.0, 0.25), (11.0, 0.40)]),
    ("n=0 k=2 pairs only", [], [(0.0, 0.49), (2.05 * MEAN_GAP, 0.49)]),
    ("n=3 k=0 on-line only", [0.0, 1.1, 7.9], []),
    ("n=6 k=4 dense", [0.0, 1.0, 2.0, 3.0, 4.0, 5.0],
     [(0.5, 0.49), (1.5, 0.31), (2.5, 0.17), (3.5, 0.05)]),
    ("n=2 k=1 at the damage peak", [6.517, -6.517], [(0.0, 0.5)]),
    ("n=4 k=1 stacked at the peak", [6.517, 6.517, 6.517, 6.517],
     [(0.0, 0.5)]),
]


def random_configs(count: int = 24, seed: int = 11, n_max: int = 6,
                   k_max: int = 3, spread: float = 30.0):
    """Random genuine configurations for the constraint controls."""
    rng = np.random.default_rng(seed)
    out = []
    for i in range(count):
        n = int(rng.integers(0, n_max + 1))
        k = int(rng.integers(1, k_max + 1))
        xs = np.sort(rng.uniform(-spread, spread, n)).tolist()
        pr = [(float(rng.uniform(-spread, spread)),
               float(rng.uniform(0.0, 0.5))) for _ in range(k)]
        out.append((f"random {i}", xs, pr))
    return out


# ---------------------------------------------------------------------------
# 4. the entry-level relaxation, with the trade constraints in it
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TradeIndex:
    """Real coordinates of the augmented Hermitian matrix, plus the atom
    combinatorics.  ``X = Re Q`` symmetric, ``Y = Im Q`` antisymmetric;
    ``ix``/``iy`` map an index pair to its coordinate and ``sy`` carries
    antisymmetry's sign.  ``kinds`` is 0 on-line, 2 shadow, 1 pair; the
    shadow atoms exist only to couple blocks and carry objective weight 0.
    """

    n: int
    k: int
    N: int
    d: int
    sigma: np.ndarray
    kinds: np.ndarray
    pair_of: np.ndarray
    ix: np.ndarray
    iy: np.ndarray
    sy: np.ndarray


def trade_index(n: int, k: int) -> TradeIndex:
    N = n + 3 * k
    sigma = np.arange(N)
    kinds = np.zeros(N, int)
    pair_of = -np.ones(N, int)
    for i in range(k):
        kinds[n + i] = 2                       # shadow atom of pair i
        pair_of[n + i] = i
        a = n + k + 2 * i
        kinds[a] = kinds[a + 1] = 1
        pair_of[a] = pair_of[a + 1] = i
        sigma[a], sigma[a + 1] = a + 1, a
    ix = np.zeros((N, N), int)
    iy = np.zeros((N, N), int)
    sy = np.zeros((N, N))
    c = 0
    for a in range(N):
        for b in range(a, N):
            ix[a, b] = ix[b, a] = c
            c += 1
    for a in range(N):
        for b in range(a + 1, N):
            iy[a, b] = iy[b, a] = c
            sy[a, b], sy[b, a] = 1.0, -1.0
            c += 1
    return TradeIndex(n=n, k=k, N=N, d=c, sigma=sigma, kinds=kinds,
                      pair_of=pair_of, ix=ix, iy=iy, sy=sy)


def trade_weight_matrix(kinds, theta: float) -> np.ndarray:
    """``c(a,b)``: the objective weights on the AUGMENTED atom set.

    Identical to ``sos_certificate.weight_matrix`` on the original atoms
    (1 on the pair block and both cross blocks, ``1-theta`` on the on-line
    off-diagonal, 0 on the on-line diagonal) and ZERO on every entry
    touching a shadow atom -- shadows are not part of the obligation, they
    are extra columns of the same Gram matrix.
    """
    kk = np.asarray(kinds, int)
    N = len(kk)
    on = (kk == 0).astype(float)
    c = np.ones((N, N))
    c = c - theta * (on[:, None] * on[None, :])
    np.fill_diagonal(c, np.where(kk == 0, 0.0, 1.0))
    live = (kk != 2).astype(float)
    c = c * live[:, None] * live[None, :]
    return c


def relax_trade(n: int, k: int, theta: float = THETA_FULL, constant=None,
                shadows: bool = True, depth_curve: bool = True,
                damage_cut: bool = True, trade_cut: bool = True,
                ranges: bool = True, proved_bounds: bool = True,
                schur: bool = True, cauchy_schwarz: bool = True,
                pin=None, solver: str = "CLARABEL", verbose: bool = False,
                **solver_opts) -> dict:
    """Minimise ``Xi`` over the per-entry moment lift of the trade cone.

    THE LIFT.  ``p`` carries the first moments (``X``, ``Y``); for each
    index pair ``(a,b)`` three second moments ``S = X^2``, ``T = Y^2``,
    ``U = XY`` are carried with their own ``3 x 3`` moment block
    ``[[1,X,Y],[X,S,U],[Y,U,T]] >= 0``, and the diagonal coordinates carry
    one shared block so that Cauchy-Schwarz can be written at the moment
    level.  The objective ``sum c(a,b)(S-T) - 4k`` is linear in the second
    moments, so the minimum is a valid LOWER BOUND for ``min Xi`` over
    real configurations: every configuration supplies a feasible point.

    Compared with ``sos_certificate.relax`` this lift drops the moments
    that couple DIFFERENT entries (which bought nothing there -- see its
    finding F4) and adds the trade constraints (T1)-(T6), each switchable
    so the before/after table is produced by one function.

    ``constant`` replaces the ``4k`` (the planted-infeasibility control
    raises it above the true optimum and checks the value goes negative).
    ``pin = (ReQ, ImQ, idx)`` fixes the first AND second moments on the
    sub-block ``idx`` to a given matrix, turning the program into a
    feasibility test for that matrix -- how :func:`violator_in_sdp` asks
    the constraint set whether it still admits the cone violator.
    """
    import cvxpy as cp

    L = trade_index(n, k if shadows else k)
    N, kk = L.N, L.kinds
    if not shadows:                     # drop the shadow rows and columns
        keep = np.flatnonzero(kk != 2)
    else:
        keep = np.arange(N)
    const = 4 * k if constant is None else float(constant)
    c = trade_weight_matrix(kk, theta)

    p = cp.Variable(L.d, name="p")
    S = cp.Variable((N, N), symmetric=True, name="S")   # X^2
    T = cp.Variable((N, N), symmetric=True, name="T")   # Y^2
    U = cp.Variable((N, N), name="U")                   # X Y
    cons = []

    X = cp.reshape(p[L.ix.reshape(-1)], (N, N), order="C")
    Y = cp.multiply(L.sy, cp.reshape(p[L.iy.reshape(-1)], (N, N), order="C"))

    drop = [a for a in range(N) if a not in set(keep.tolist())]
    for a in drop:                      # neutralise dropped atoms
        cons += [X[a, a] == 1.0]
        for b in range(N):
            if b != a:
                cons += [X[a, b] == 0.0, Y[a, b] == 0.0,
                         S[a, b] == 0.0, T[a, b] == 0.0, U[a, b] == 0.0]

    # (Q1) Q >= 0 as the real 2N x 2N embedding of a Hermitian matrix
    cons.append(cp.bmat([[X, -Y], [Y, X]]) >> 0)
    # (Q2) involution, (Q3) sigma-symmetry -- unchanged from the earlier lift
    for a in range(N):
        s = int(L.sigma[a])
        cons.append(X[a, s] == 1.0)
        if s != a:
            cons.append(Y[a, s] == 0.0)
    for a in range(N):
        for b in range(N):
            sa, sb = int(L.sigma[a]), int(L.sigma[b])
            if (sa, sb) != (a, b):
                cons.append(X[sa, sb] == X[a, b])
                cons.append(Y[sa, sb] == -Y[a, b])
            elif a != b and sa == a and sb == b:
                cons.append(Y[a, b] == 0.0)     # the line block is real
    # (Q4) diagonal
    cons.append(cp.diag(X) >= 1.0)
    cons.append(U == -U.T)
    cons.append(cp.diag(T) == 0.0)
    cons.append(cp.diag(U) == 0.0)

    # LOCALISATION.  A coordinate pinned to a constant by an equality has
    # zero variance, so its second moments are the products of the
    # constants; without this the lift keeps the equalities in the first
    # moment and forgets them in the second (the defect `sos_certificate`
    # repairs with `L Z = c p'`).
    for a in range(N):
        s = int(L.sigma[a])
        cons.append(S[a, s] == 1.0)
        if s != a:
            cons += [T[a, s] == 0.0, U[a, s] == 0.0]
    for a in range(N):
        for b in range(N):
            sa, sb = int(L.sigma[a]), int(L.sigma[b])
            if (sa, sb) != (a, b):
                cons += [S[sa, sb] == S[a, b], T[sa, sb] == T[a, b],
                         U[sa, sb] == -U[a, b]]
            elif a != b and sa == a and sb == b:
                cons += [T[a, b] == 0.0, U[a, b] == 0.0]

    # per-entry moment blocks
    for a in range(N):
        cons.append(cp.bmat([[np.ones((1, 1)),
                              cp.reshape(X[a, a], (1, 1), order="C")],
                             [cp.reshape(X[a, a], (1, 1), order="C"),
                              cp.reshape(S[a, a], (1, 1), order="C")]]) >> 0)
        for b in range(a + 1, N):
            cons.append(cp.bmat(
                [[np.ones((1, 1)), cp.reshape(X[a, b], (1, 1), order="C"),
                  cp.reshape(Y[a, b], (1, 1), order="C")],
                 [cp.reshape(X[a, b], (1, 1), order="C"),
                  cp.reshape(S[a, b], (1, 1), order="C"),
                  cp.reshape(U[a, b], (1, 1), order="C")],
                 [cp.reshape(Y[a, b], (1, 1), order="C"),
                  cp.reshape(U[a, b], (1, 1), order="C"),
                  cp.reshape(T[a, b], (1, 1), order="C")]]) >> 0)

    if cauchy_schwarz:
        # (Q5) at the moment level: |Q(a,b)|^2 <= Q(a,a) Q(b,b); the product
        # of two diagonal first moments is carried by one shared block.
        Zd = cp.Variable((N, N), symmetric=True, name="Zd")
        dcoord = cp.hstack([cp.reshape(X[a, a], (1,), order="C")
                            for a in range(N)])
        cons.append(cp.bmat([[np.ones((1, 1)),
                              cp.reshape(dcoord, (1, N), order="C")],
                             [cp.reshape(dcoord, (N, 1), order="C"),
                              Zd]]) >> 0)
        for a in range(N):
            cons.append(Zd[a, a] == S[a, a])
            for b in range(a + 1, N):
                cons.append(S[a, b] + T[a, b] <= Zd[a, b])

    if schur:
        # Schur product theorem: Q >= 0 implies M = Q o Q >= 0, and M is
        # linear in the per-entry moments (Re M = S - T, Im M = 2 X Y).
        ReM = S - (T - cp.diag(cp.diag(T)))
        ImM = cp.multiply(2.0 * L.sy, U)
        cons.append(cp.bmat([[ReM, -ImM], [ImM, ReM]]) >> 0)

    line = [a for a in keep if kk[a] != 1]
    pr = [a for a in keep if kk[a] == 1]
    if ranges:
        # DERIVED WINDOWS, at the first AND second moment level.  For a
        # coordinate confined to ``[l, u]`` the box cut ``(X-l)(u-X) >= 0``
        # reads ``S <= (l+u) X - l u`` and is a valid moment inequality; it
        # is what makes the lift bounded at all, since the objective's
        # ``-T`` terms are otherwise free to run away.
        #   line entries:  G(v) in [PHI_MIN, 1]   (Bochner: |G| <= G(0) = 1)
        #   pair diagonal: psi(2y) in [1, psi(1)] (depth y in [0,1/2])
        #   cross entries: |psi(y+is)| <= psi(y) <= psi(1/2)
        #   pair-pair:     |psi(y+y'+i dt)| <= psi(1)
        for i, a in enumerate(line):
            for b in line[i + 1:]:
                cons += [X[a, b] <= 1.0, X[a, b] >= PHI_MIN,
                         S[a, b] <= (PHI_MIN + 1.0) * X[a, b] - PHI_MIN]
        for a in line:
            cons.append(S[a, a] == 1.0)
        for a in pr:
            cons += [X[a, a] <= PSI_ONE,
                     S[a, a] <= (1.0 + PSI_ONE) * X[a, a] - PSI_ONE]
        for a in line:
            for b in pr:
                cons.append(S[a, b] + T[a, b] <= PSI_HALF ** 2)
        for i, a in enumerate(pr):
            for b in pr[i + 1:]:
                if int(L.sigma[a]) != b:
                    cons.append(S[a, b] + T[a, b] <= PSI_ONE ** 2)

    if shadows and depth_curve:
        cuts = depth_curve_cuts()
        for i in range(k):
            w = n + i
            pp = n + k + 2 * i
            # (T1): the shadow's entries against its own pair are psi(y),
            # real and equal for both atoms of the pair.
            cons += [Y[w, pp] == 0.0, Y[w, pp + 1] == 0.0,
                     X[w, pp] == X[w, pp + 1]]
            r, d = X[w, pp], X[pp, pp]
            cons += [r >= 1.0, r <= PSI_HALF]
            for (r0, d0, m0) in cuts["tangents"]:
                cons.append(d >= d0 + m0 * (r - r0))
            cons.append(d <= 1.0 + cuts["chord"] * (r - 1.0))

    if damage_cut or trade_cut:
        for i in range(k):
            pp = n + k + 2 * i
            dd = S[pp, pp]                     # d^2 = psi(2y)^2
            for a in line:
                for b in (pp, pp + 1):
                    if damage_cut:
                        cons.append(S[a, b] - T[a, b]
                                    >= -C_DAMAGE * (dd - 1.0))
                    if trade_cut and shadows:
                        cons.append(S[a, b] - T[a, b]
                                    >= S[a, n + i] - C_TRADE * (dd - 1.0))

    if proved_bounds:
        # (T6a) PairEnergy.lean, zero sorry: the pair block is at least 4k.
        if pr:
            cons.append(sum(S[a, b] - (T[a, b] if a != b else 0.0)
                            for a in pr for b in pr) >= 4.0 * k)
        # (T6b) the generalised inertia bound on the ORIGINAL atom set.
        orig = [a for a in keep if kk[a] != 2]
        if orig and n + k > 0:
            cons.append(sum(S[a, b] - (T[a, b] if a != b else 0.0)
                            for a in orig for b in orig)
                        >= (n + 2 * k) ** 2 / (n + k))

    if pin is not None:
        re_, im_, idx = pin
        for a, ia in enumerate(idx):
            for b, ib in enumerate(idx):
                xv, yv = float(re_[a][b]), float(im_[a][b])
                cons += [X[ia, ib] == xv, Y[ia, ib] == yv,
                         S[ia, ib] == xv * xv, T[ia, ib] == yv * yv,
                         U[ia, ib] == xv * yv]

    obj = sum(c[a, b] * (S[a, b] - (T[a, b] if a != b else 0.0))
              for a in range(N) for b in range(N)) - const
    prob = cp.Problem(cp.Minimize(obj), cons)
    prob.solve(solver=solver, verbose=verbose, **solver_opts)
    rec = {"n": n, "k": k, "N": N, "d": L.d, "theta": theta,
           "constant": const, "status": prob.status,
           "value": float(prob.value) if prob.value is not None else None,
           "solver": solver, "index": L, "problem": prob}
    if p.value is not None:
        pv = np.asarray(p.value, float)
        rec["Q"] = pv[L.ix] + 1j * (L.sy * pv[L.iy])
    return rec


def trade_scan(sizes, theta: float = THETA_FULL, solver: str = "CLARABEL",
               **opts) -> list:
    """:func:`relax_trade` over sizes, with the earlier lift's recorded
    value alongside so the before/after is one table."""
    from sos_certificate import SDP_RECORD
    out = []
    for n, k in sizes:
        rec = relax_trade(n, k, theta, solver=solver, **opts)
        base = SDP_RECORD["values"].get((n, k))
        if base is None:
            base = (1 - theta) * n * (n - 1) - n ** 2 - 4 * k
        out.append({"n": n, "k": k, "N": rec["N"], "status": rec["status"],
                    "trade": rec["value"], "baseline": base,
                    "predicted": trade_prediction(n, k, theta)})
    return out


def trade_prediction(n: int, k: int, theta: float = THETA_FULL) -> float:
    """The closed form the trade constraints imply, before any solver runs.

    DERIVATION, for ``k = 1``.  The pair block of one pair is exactly
    ``2 d^2 + 2`` with ``d = Q(P+,P+)``, so ``budget = 2(d^2-1)``; (T3)
    bounds each of the ``2n`` cross entries by ``-C_DAMAGE (d^2-1)`` and
    the cross block counts each twice, giving ``cross >= -4 n C_DAMAGE
    (d^2-1)``; the on-line block is nonnegative.  Hence

        Xi >= (d^2-1)(2 - 4 n C_DAMAGE),

    minimised over the admissible range ``1 <= d <= psi(1)``: zero when
    ``n <= 1/(2 C_DAMAGE) = 7.68`` and ``(psi(1)^2-1)(2 - 4 n C_DAMAGE)``
    beyond.

    For ``k >= 2`` the pair block is only known to be ``>= 4k`` (T6a) --
    the cross-pair entries can pay for the diagonal slack -- so every pair
    may sit at the depth cap and cost nothing extra, and the accounting
    gives ``-4 n k C_DAMAGE (psi(1)^2 - 1)``.  The scan meets that value
    exactly at ``k = 4`` and stays above it at ``k = 2, 3``, where the
    pair block's own positive semidefiniteness still bites: read the
    prediction as a floor for the relaxation, not as its value.
    """
    sl = PSI_ONE ** 2 - 1.0
    if k == 0:
        return 0.0
    if k == 1:
        return min(0.0, sl * (2.0 - 4.0 * n * C_DAMAGE))
    return min(0.0, -4.0 * n * k * C_DAMAGE * sl)


# ---------------------------------------------------------------------------
# 5. the cone violator, screened against the new constraints
# ---------------------------------------------------------------------------


def violator_screen(n: int = 3, t: Fraction = Fraction(1, 2),
                    theta: float = THETA_FULL) -> dict:
    """Which of (T1)-(T6) excludes ``sos_certificate.cone_violator``.

    The witness is the exactly rational matrix with on-line block all
    ones, cross entries ``+/- i t`` and pair diagonal ``d = 1 + 2t^2``.
    Each new constraint is evaluated on it in closed form:

      * DEPTH CAP.  ``d = 1 + 2t^2`` must be ``psi(2y)`` for some
        ``y in [0,1/2]``, so ``d <= psi(1) = 1.03922``.  At ``t = 1/2``
        the witness has ``d = 3/2``: excluded outright.
      * (T3).  Its cross entries are purely imaginary, so
        ``Re(C^2) = -t^2``, while (T3) allows only
        ``-C_DAMAGE (d^2 - 1)``.  This is the constraint that survives
        rescaling: even at the largest depth-admissible ``t``
        (``t^2 = (psi(1)-1)/2 = 0.0196``) the witness needs 3.76x more
        damage than (T3) permits.
      * (T4).  Vacuous here on its own -- the witness has no shadow entry,
        and the screen reports the value the shadow entry would have to
        take.
      * (T2).  The witness's pair diagonal and its (absent) shadow entry
        cannot both sit on the depth curve; reported as the ``r`` the
        curve would require.

    Returns the closed-form slacks (negative = the witness is excluded by
    that constraint) plus the value of ``Xi`` on the witness, so the
    screen also says that exclusion was necessary.
    """
    t = Fraction(t)
    d = 1 + 2 * t * t
    df = float(d)
    xi = ((1 - theta) * n * (n - 1) + 2 * df ** 2 - 2 - 4 * n * float(t) ** 2)
    # the largest t the depth cap admits, and Xi there
    t_adm = math.sqrt((PSI_ONE - 1.0) / 2.0)
    d_adm = 1.0 + 2 * t_adm ** 2
    xi_adm = ((1 - theta) * n * (n - 1) + 2 * d_adm ** 2 - 2
              - 4 * n * t_adm ** 2)
    return {
        "n": n, "t": float(t), "d": df, "Xi": xi, "violates": xi < 0,
        "depth_cap_slack": PSI_ONE - df,
        "depth_cap_excludes": df > PSI_ONE,
        "T3_slack": -float(t) ** 2 + C_DAMAGE * (df ** 2 - 1),
        "T3_excludes": (-float(t) ** 2) < -C_DAMAGE * (df ** 2 - 1),
        "t_admissible": t_adm,
        "d_admissible": d_adm,
        "Xi_at_admissible_t": xi_adm,
        "violates_at_admissible_t": xi_adm < 0,
        "T3_slack_at_admissible_t": (-t_adm ** 2
                                     + C_DAMAGE * (d_adm ** 2 - 1)),
        "T3_ratio_at_admissible_t": t_adm ** 2 / (C_DAMAGE
                                                  * (d_adm ** 2 - 1)),
        "T4_shadow_entry_required": math.sqrt(max(
            0.0, -t_adm ** 2 + C_TRADE * (d_adm ** 2 - 1))),
    }


def violator_in_sdp(n: int = 3, t: Fraction = Fraction(1, 2),
                    theta: float = THETA_FULL, solver: str = "CLARABEL",
                    **opts) -> dict:
    """The same question asked of the solver: pin the relaxation's moments
    to the witness and report that the program is infeasible.

    :func:`violator_screen` says WHICH inequality the witness breaks; this
    says the constraint set as actually built rejects it.  The witness
    occupies the ``n`` on-line atoms and the two pair atoms; the shadow
    atom is left free, so the test also asks whether ANY shadow row could
    have rescued it.
    """
    re, im = cone_violator(n, t)
    idx = list(range(n)) + [n + 1, n + 2]   # on-line, then the pair atoms
    rec = relax_trade(n, 1, theta, pin=(re, im, idx), solver=solver, **opts)
    st = str(rec["status"])
    return {"n": n, "t": float(t), "status": st,
            "infeasible": st.startswith("infeasible"),
            "value": rec["value"]}


def violator_family_in_sdp(n: int = 3, theta: float = THETA_FULL,
                           solver: str = "CLARABEL", **opts) -> list:
    """:func:`violator_in_sdp` along the witness family, including the
    largest ``t`` the depth cap admits -- the case where the exclusion has
    to come from (T3) rather than from the range alone."""
    t_adm = math.sqrt((PSI_ONE - 1.0) / 2.0)
    out = []
    for t in (Fraction(1, 2), Fraction(1, 4),
              Fraction(round(t_adm * 1000), 1000)):
        rec = violator_in_sdp(n, t, theta, solver=solver, **opts)
        scr = violator_screen(n, t, theta)
        out.append({**rec, "Xi": scr["Xi"], "d": scr["d"],
                    "depth_cap_excludes": scr["depth_cap_excludes"],
                    "T3_excludes": scr["T3_excludes"]})
    return out


# ---------------------------------------------------------------------------
# 6. the cluster program: the trade at the CONFIGURATION level
# ---------------------------------------------------------------------------


def damage_windows(y: float, s_max: float = 300.0,
                   n_s: int = 600001) -> list:
    """The connected components of ``{s > 0 : D(s,y) > 0}``.

    WHY THIS IS THE RIGHT OBJECT.  One integration by parts on
    ``psi(y+is) = int g(u) e^{yu} e^{isu} du / A`` leaves the boundary term
    ``(1/is)(G_y(1/2) e^{is/2} - G_y(-1/2) e^{-is/2})``, so
    ``Re psi(y+is)^2 = (2 c^2/s^2)(1 - cosh(y) cos s) + O(s^{-3})`` with
    ``c = cos(sqrt2/2)/A``: the damage ``D = -4 Re psi^2`` is positive only
    where ``cos s > sech(y)``, i.e. in narrow windows around ``s = 2 pi j``,
    with peak height falling like ``1/j^2``.  Measured, at ``y = 1/2``:
    windows at 6.517, 12.699, 18.939, ... of width 0.96 and peaks 0.02083,
    0.00462, 0.00201, ...

    Returns one record per window with its bracket, width and peak.
    """
    ss = np.linspace(0.0, s_max, n_s)
    D = damage(ss, y)
    pos = D > 0.0
    idx = np.flatnonzero(pos)
    if not len(idx):
        return []
    brk = np.flatnonzero(np.diff(idx) > 1)
    out = []
    for grp in np.split(idx, brk + 1):
        if not len(grp):
            continue
        lo, hi = float(ss[grp[0]]), float(ss[grp[-1]])
        j = int(np.argmax(D[grp]))
        out.append({"lo": lo, "hi": hi, "width": hi - lo,
                    "peak": float(D[grp][j]), "peak_at": float(ss[grp][j])})
    return out


def window_repulsion(width: float, n: int = 4001) -> float:
    """``gamma(w) = min_{|v| <= w} G(v)^2``: the least repulsion two atoms
    inside one window of width ``w`` can charge each other.  One-sided
    downward, so using it in place of the true ``G(x_a-x_b)^2`` can only
    lower the bound."""
    v = np.linspace(0.0, float(width), n)
    return float((line_kernel(v) ** 2).min())


def occupancy_max(D_j: float, gamma: float, theta: float = THETA_FULL,
                  n_cap: int = 400) -> dict:
    """``M(D, gamma) = max_{N in Z>=0} [ N D - (1-theta) gamma N(N-1) ]``.

    THE TRADE, in one line.  ``N`` atoms inside one damage window take at
    most ``N D_j``; being inside one window they are within ``width`` of
    each other, so they charge the on-line block at least ``(1-theta)
    gamma N (N-1)``.  The maximum over ``N`` is what one window can cost,
    whatever ``n`` is -- which is why the resulting bound carries no
    ``n``.  The parabola's vertex sits at ``N* = 1/2 + D/(2(1-theta)
    gamma)``, so the maximiser is one of the two neighbouring integers.
    """
    c = (1.0 - theta) * gamma
    if c <= 0:
        return {"N": None, "value": math.inf}
    star = 0.5 + D_j / (2 * c)
    best, arg = -math.inf, 0
    for N in {0, 1, max(0, int(math.floor(star))), int(math.ceil(star)),
              min(n_cap, int(math.ceil(star)) + 1)}:
        v = N * D_j - c * N * (N - 1)
        if v > best:
            best, arg = v, N
    return {"N": arg, "value": float(best), "vertex": star}


def far_field_envelope(y: float, s0: float = 20.0, s_max: float = 300.0,
                       n_s: int = 600001) -> float:
    """``E(y) = max_{s >= s0} s^2 D(s,y)``: the measured far-field envelope
    behind the tail estimate.  The integration-by-parts asymptotics say the
    limit is ``8 c^2 (cosh y - 1)``; this measures it rather than assuming
    it."""
    ss = np.linspace(s0, s_max, n_s)
    return float((ss ** 2 * damage(ss, y)).max())


def window_occupancy_bound(y: float, s_max: float = 300.0, n_s: int = 600001,
                           theta: float = THETA_FULL) -> dict:
    """The single-pair obligation, bounded below with NO reference to n.

    THE ACCOUNTING, every step one-sided:

        Xi  =  budget(y) - sum_a D(s_a, y) + (1-theta) sum_{a != b} G_ab^2
            >=  budget(y) - sum_j [ sum_{a in window j} D(s_a)
                                    - (1-theta) sum_{a != b in window j}
                                      G_ab^2 ]
            >=  budget(y) - 2 sum_{j >= 1} M(D_j, gamma_j)   -   tail,

    because (i) atoms outside every window have ``D <= 0`` and contribute
    only nonnegative repulsion, (ii) repulsion between different windows
    is dropped (a sum of squares), (iii) inside window ``j`` the damage of
    each atom is at most the window's peak and the repulsion of each pair
    of them at least ``gamma_j``, and (iv) the windows come in mirror
    pairs ``+/- s``, hence the factor 2.

    The tail beyond the scanned range uses the measured envelope
    ``D(s) <= E/s^2`` and the measured minimum window spacing ``P``:
    ``sum_{s_j > s_max} D_j <= E (1/s_max^2 + 1/(P s_max))``, valid because
    at those heights the occupancy maximiser is ``N = 1`` (checked and
    reported as ``tail_single_occupancy``).

    Returns the bound, its parts, and the margin ratio to the budget.
    """
    wins = damage_windows(y, s_max=s_max, n_s=n_s)
    terms = []
    for w in wins:
        gam = window_repulsion(w["width"])
        occ = occupancy_max(w["peak"], gam, theta)
        terms.append({**w, "gamma": gam, "N": occ["N"], "M": occ["value"]})
    body = sum(t["M"] for t in terms)
    if len(wins) >= 2:
        spacing = min(wins[i + 1]["peak_at"] - wins[i]["peak_at"]
                      for i in range(len(wins) - 1))
    else:
        spacing = float(MEAN_GAP)
    env = far_field_envelope(y, s_max=s_max, n_s=n_s)
    tail = env * (1.0 / s_max ** 2 + 1.0 / (spacing * s_max))
    last = terms[-1] if terms else None
    bud = budget(y)
    val = bud - 2.0 * (body + tail)
    return {"y": y, "budget": bud, "windows": len(wins), "terms": terms,
            "body": body, "tail": tail, "envelope": env, "spacing": spacing,
            "bound": val, "ratio": val / bud if bud > 0 else float("nan"),
            "first_window_N": terms[0]["N"] if terms else None,
            "tail_single_occupancy": (last is None or last["N"] <= 1),
            "s_max": s_max}


def window_scan(ys=(0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.49, 0.5),
                s_max: float = 300.0, n_s: int = 200001) -> list:
    """:func:`window_occupancy_bound` across the depth range."""
    return [window_occupancy_bound(y, s_max=s_max, n_s=n_s) for y in ys]


def cluster_relaxation(y: float, s_max: float = 40.0, h: float = 1.0,
                       theta: float = THETA_FULL, lift: bool = True,
                       solver: str = "CLARABEL", **opts) -> dict:
    """The same single-pair statement as a moment program over occupancies.

    Grid the offsets ``s`` into cells; let ``c_i`` be the number of on-line
    atoms in cell ``i`` and ``Gam = c c'``.  Then, exactly,

        Xi  =  budget(y) - d' c + (1-theta) [ <W, Gam> - 1' c ],
        d_i = max_{cell i} D(s, y),   W_ij = min_{cells i,j} G(s-s')^2,

    with both cell quantities taken one-sided, so a genuine configuration
    supplies a feasible point whose objective is at most its ``Xi``.
    Relaxing ``Gam = c c'`` to the Shor lift ``[[1, c'],[c, Gam]] >= 0``
    plus the integrality cuts ``Gam >= 0`` entrywise and
    ``Gam_ii >= c_i`` (true of ``c_i^2`` for every nonnegative integer)
    gives a semidefinite program whose value is a lower bound for every
    ``n`` at once -- the mass ``1' c`` is free.

    Without the ``Gam_ii >= c_i`` cut the program is unbounded below: a
    diffuse ``c`` has no self-energy and the ``-(1-theta) 1'c`` term runs
    away.  That is worth stating because it is exactly the place where the
    integrality of the atom count is load-bearing.
    """
    import cvxpy as cp
    s = np.arange(-s_max, s_max + 1e-9, h)
    m = len(s)
    fine = max(3, int(round(h / 0.02)) + 1)
    d = np.array([damage(np.linspace(si - h / 2, si + h / 2, fine), y).max()
                  for si in s])
    diff = s[:, None] - s[None, :]
    W = np.empty((m, m))
    for i in range(m):
        for j in range(m):
            v = np.linspace(abs(diff[i, j]) - h, abs(diff[i, j]) + h, fine)
            W[i, j] = float((line_kernel(np.abs(v)) ** 2).min())
    wins = [w for w in damage_windows(y) if w["peak_at"] > s_max]
    tail = 2.0 * sum(occupancy_max(w["peak"], window_repulsion(w["width"]),
                                   theta)["value"] for w in wins)
    c = cp.Variable(m, nonneg=True)
    cons = []
    if lift:
        Gam = cp.Variable((m, m), symmetric=True)
        cons += [cp.bmat([[np.ones((1, 1)), cp.reshape(c, (1, m), order="C")],
                          [cp.reshape(c, (m, 1), order="C"), Gam]]) >> 0,
                 Gam >= 0, cp.diag(Gam) >= c]
        R = cp.sum(cp.multiply(W, Gam)) - cp.sum(c)
    else:
        R = cp.quad_form(c, cp.psd_wrap(W)) - cp.sum(c)
    prob = cp.Problem(cp.Minimize(budget(y) - d @ c + (1 - theta) * R), cons)
    prob.solve(solver=solver, **opts)
    val = float(prob.value) if prob.value is not None else None
    kkt = None
    if c.value is not None:
        # The QP-form KKT residual: for the plain quadratic
        # (1-theta)(c'Wc - 1'c) - d'c, optimality would read
        # F_i = d_i - (1-theta)(2 (W c)_i - 1) <= 0 for every cell, with
        # equality on the support.  The program actually solved carries the
        # lifted Gam, so F is a DIAGNOSTIC rather than an identity: a small
        # F_max says Gam came out essentially c c', i.e. the moment
        # relaxation is not buying anything the configuration could not.
        # F is a function of the offset alone and carries no atom count,
        # which is what size independence means for a free-mass program.
        kkt = d - (1 - theta) * (2.0 * (W @ np.asarray(c.value, float)) - 1.0)
    return {"y": y, "s_max": s_max, "h": h, "m": m, "status": prob.status,
            "kkt": (None if kkt is None else kkt),
            "kkt_max": (None if kkt is None else float(kkt.max())),
            "value": val, "tail": tail,
            "bound": None if val is None else val - tail,
            "mass": (float(np.sum(c.value)) if c.value is not None else None),
            "occupancy": (None if c.value is None else
                          [(float(s[i]), float(c.value[i]))
                           for i in np.argsort(-c.value)[:8]
                           if c.value[i] > 1e-6])}


def configuration_minimum(y: float, n: int, restarts: int = 30,
                          seed: int = 0, spread: float = 40.0,
                          theta: float = THETA_FULL) -> dict:
    """The single-pair objective minimised over genuine configurations of
    ``n`` on-line atoms -- the number the bounds have to sit below."""
    from scipy.optimize import minimize as _min
    rng = np.random.default_rng(seed)

    def obj(v):
        return target_from_config(np.asarray(v, float), [(0.0, y)], theta)

    best, bx = math.inf, None
    for _ in range(restarts):
        v0 = rng.uniform(-spread, spread, n)
        r = _min(obj, v0, method="Nelder-Mead",
                 options=dict(maxiter=8000, maxfev=8000, fatol=1e-13,
                              xatol=1e-9))
        if r.fun < best:
            best, bx = float(r.fun), np.sort(r.x)
    return {"y": y, "n": n, "min": best, "argmin": bx}


def window_peak_fit(y: float = 0.5, s_max: float = 300.0,
                    n_s: int = 200001) -> dict:
    """The closed-form law behind the window schedule, fitted and checked.

    The integration-by-parts asymptotics give
    ``D(s,y) ~ (8 c^2/s^2)(cosh(y) cos s - 1)`` with
    ``c = cos(sqrt2/2)/A``, so the ``j``-th window's peak should be
    ``D_j ~ 8 c^2 (cosh y - 1)/(2 pi j)^2``.  This measures
    ``D_j (2 pi j)^2`` against that constant and reports the relative
    error, which is what makes the window schedule summable and the tail
    estimate legitimate: the certificate is a list of numbers falling like
    ``1/j^2`` with a predicted constant, not an unexplained table.
    """
    c = math.cos(math.sqrt(2.0) / 2.0) / A
    pred = 8.0 * c * c * (math.cosh(y) - 1.0)
    wins = damage_windows(y, s_max=s_max, n_s=n_s)
    rows = []
    for j, w in enumerate(wins, start=1):
        scaled = w["peak"] * (2 * math.pi * j) ** 2
        rows.append({"j": j, "peak": w["peak"], "scaled": scaled,
                     "rel_error": scaled / pred - 1.0})
    tail_rows = rows[len(rows) // 2:]
    return {"y": y, "predicted": pred, "rows": rows,
            "worst_rel_error_tail": (max(abs(r["rel_error"])
                                         for r in tail_rows)
                                     if tail_rows else float("nan")),
            "asymptote": (rows[-1]["scaled"] if rows else float("nan"))}


def entry_dual_certificate(n: int, k: int = 1,
                           theta: float = THETA_FULL) -> dict:
    """The size-independent dual of the entry-level program, in closed form.

    The tight sizes are carried by ONE multiplier vector with no
    dependence on ``n``, ``k`` or on where the atoms sit:

        multiplier 1 on the pair block's own identity
                     (``pair block = 2 d^2 + 2`` at ``k = 1``),
        multiplier 2 on EVERY cross-entry (T3) cut,
        multiplier 0 on everything else,

    which adds up to ``Xi >= (d^2-1)(2 - 4 n C_DAMAGE)``.  It is exactly
    the shape a size-independent certificate has to take -- a fixed
    constant per entry TYPE -- and it is exactly as far as such a
    certificate can go: it is nonnegative only while
    ``n <= 1/(2 C_DAMAGE) = 7.68``.  That the multiplier exists and is
    insufficient is the same shape of finding as
    ``sos_certificate.inertia_multiplier``: the counting the general case
    needs is not a per-entry constant.
    """
    sl = PSI_ONE ** 2 - 1.0
    return {"n": n, "k": k, "pair_block_multiplier": 1.0,
            "cross_cut_multiplier": 2.0, "cuts_used": 2 * n * k,
            "coefficient_of_slack": (2.0 - 4.0 * n * C_DAMAGE if k == 1
                                     else -4.0 * n * k * C_DAMAGE),
            "value": trade_prediction(n, k, theta),
            "max_slack": sl,
            "nonnegative_while": N_PAID_FOR,
            "size_independent": True,
            "sufficient": n <= N_PAID_FOR}


def multi_pair_requirement(ys=(0.05, 0.1, 0.2, 0.3, 0.4, 0.49, 0.5),
                           s_max: float = 300.0, n_s: int = 200001,
                           floor: float = 0.2918) -> dict:
    """Where the same accounting stops for ``k >= 2``, as a ratio.

    For one pair the window accounting spends ``2 sum_j M_j`` of that
    pair's own budget ``slack(y)``.  With ``k`` pairs the damage side is
    still at most ``sum_p 2 sum_j M_j(y_p)`` -- an on-line atom can be in
    one damage window of each pair at once -- so the same argument closes
    iff

        budget(P)  >=  ratio * sum_p slack(y_p),
        ratio = max_y [ 2 sum_j M_j(y) / slack(y) ].

    ``joint_universal`` measures the budget floor at
    ``0.2918 sum_p slack(y_p)`` (500 restarts, the binding shape a lattice
    at 1.005 mean gaps).  Returns the required ratio, the measured floor
    and the factor between them: the k >= 2 gap is on the BUDGET side.
    """
    rows = [window_occupancy_bound(y, s_max=s_max, n_s=n_s) for y in ys]
    req = max(2.0 * (r["body"] + r["tail"]) / r["budget"] for r in rows)
    at = max(rows, key=lambda r: 2.0 * (r["body"] + r["tail"]) / r["budget"])
    return {"required_ratio": req, "at_y": at["y"], "measured_floor": floor,
            "short_by_factor": req / floor, "closes_for_k_ge_2": req <= floor,
            "per_depth": [(r["y"], 2.0 * (r["body"] + r["tail"]) / r["budget"])
                          for r in rows]}


# ---------------------------------------------------------------------------
# 7. the recorded campaign
# ---------------------------------------------------------------------------

#: The entry-level relaxation by size, at theta = 995/1000, CLARABEL.
#: ``baseline`` is ``sos_certificate.SDP_RECORD`` (the earlier lift, whose
#: observed fit was ``(1-theta) n(n-1) - n^2 - 4k``); ``ranges`` is THIS
#: lift with the trade constraints switched off, i.e. derived entry windows
#: only; ``trade`` is the same lift with (T1)-(T6) on.  The true minimum
#: over real configurations is 0 at every size
#: (:func:`configuration_minimum` and ``sos_certificate``).  Reproduce with
#: ``trade_scan(TRADE_RECORD["sizes"])``.
TRADE_RECORD = {
    "theta": THETA_FULL,
    "solver": "CLARABEL",
    "sizes": [(0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (2, 1), (3, 1), (4, 1),
              (5, 1), (6, 1), (7, 1), (8, 1), (2, 2), (4, 2), (6, 2), (2, 3),
              (4, 3), (2, 4), (4, 4), (8, 4)],
    "trade": {(0, 1): 0.0, (0, 2): 0.0, (0, 3): 0.0, (0, 4): 0.0,
              (1, 1): 0.0, (2, 1): 0.0, (3, 1): 0.0, (4, 1): 0.0,
              (5, 1): 0.0, (6, 1): 0.0, (7, 1): 0.0, (8, 1): -0.00672,
              (2, 2): -0.05330, (4, 2): -0.10648, (6, 2): -0.15954,
              (2, 3): -0.11025, (4, 3): -0.21980, (2, 4): -0.16668,
              (4, 4): -0.33336, (8, 4): -0.66671},
    "ranges": {(0, 1): 0.0, (0, 2): -8.0, (0, 3): -12.0, (0, 4): -16.0,
               (1, 1): -4.0, (2, 1): -7.99, (3, 1): -12.04659,
               (4, 1): -16.09470, (5, 1): -20.13281, (6, 1): -24.16092,
               (7, 1): -28.17903, (8, 1): -32.18714, (2, 2): -11.99,
               (4, 2): -23.94, (6, 2): -40.15635, (2, 3): -15.99,
               (4, 3): -27.94, (2, 4): -19.99, (4, 4): -31.94,
               (8, 4): -79.72},
    "observed": "0 for k = 1, n <= 7; (psi(1)^2-1)(2 - 4 n C_DAMAGE) at "
                "n >= 8; about -4 n k C_DAMAGE (psi(1)^2-1) for k >= 4",
    "n_paid_for": N_PAID_FOR,
}

#: The precision-response control the hunt's checklist requires: each
#: measured constant re-run up a discretisation ladder
#: ((100, 100001, 51), (200, 200001, 101), (300, 300001, 201)).  Both are
#: stable to ten digits, and both argmaxes are unmoved -- C_DAMAGE at
#: (y, s) = (1/2, 6.517), C_TRADE at (0.001, 4.768).
CONSTANT_LADDER = {
    "damage": [0.0651240972, 0.0651240972, 0.0651240972],
    "trade": [0.1472177105, 0.1472177105, 0.1472177105],
    "damage_argmax": (0.5, 6.517),
    "trade_argmax": (0.001, 4.768),
}

#: The configuration-level window bound, by depth (s_max = 300, 200001
#: grid points).  ``bound`` is a lower bound for the single-pair
#: obligation at EVERY n; ``ratio`` is ``bound / budget``.
WINDOW_RECORD = {
    "theta": THETA_FULL,
    "by_depth": {0.05: 0.000932, 0.1: 0.003730, 0.3: 0.033759,
                 0.49: 0.067034, 0.5: 0.067197},
    "ratio_by_depth": {0.05: 0.6012, 0.1: 0.6009, 0.3: 0.5982,
                       0.49: 0.4369, 0.5: 0.4201},
    "windows_scanned": 47,
    "first_window_occupancy": {0.05: 1, 0.1: 1, 0.3: 1, 0.49: 3, 0.5: 3},
    "cluster_sdp": {"s_max": 20.0, "h": 1.0, "value": 0.064447,
                    "tail": 0.009353, "bound": 0.055094, "mass": 10.33,
                    "h_half": {"value": 0.078322, "bound": 0.068969,
                               "mass": 9.27}},
    "configuration_minimum_y_half": {1: 0.139127, 2: 0.118296, 3: 0.107464,
                                     5: 0.092112, 8: 0.084549, 14: 0.079641},
}

#: What the window bound does NOT establish, stated where it can be read.
NAMED_GAPS = [
    "G1 the window bound is a MEASURED one-sided accounting on a grid: the "
    "window brackets, their peaks and gamma_j come from a 600001-point scan "
    "of [0, 300], not from a closed-form enclosure of D and G.",
    "G2 the tail beyond s_max uses a MEASURED far-field envelope "
    "max_{s>=20} s^2 D(s,y) and the measured minimum window spacing; the "
    "integration-by-parts asymptotics predict the envelope but nothing here "
    "derives the constant with an enclosure.",
    "G3 the argument is single-pair. For k >= 2 the same accounting needs a "
    "budget floor of about 0.58 sum_p slack(y_p) against the 0.2918 "
    "joint_universal measures -- see multi_pair_requirement.",
    "G4 the entry-level relaxation's residual deficit at n >= 8 (k = 1) and "
    "at every n (k >= 2) is real: the lift has no constraint that counts "
    "how many atoms fit in a damage window, and no degree-2 cut on pairs "
    "of entries can supply one.",
    "G5 nothing here is a proof of the universally quantified statement, "
    "and no proportion is claimed to have moved.",
]


def audit():
    import time
    print("= 1. the structural fact: squares are moments of nu = mu*mu =")
    print(f"  psi(z)^2 vs int e^{{zw}} dnu(w): worst defect "
          f"{nu_moment_defect():.2e} (quadrature-limited)")
    print(f"  C_DAMAGE = {C_DAMAGE:.8f}   C_TRADE = {C_TRADE:.8f}   "
          f"1/(2 C_DAMAGE) = {N_PAID_FOR:.4f} atoms per pair's budget")
    print(f"  depth curve convex in (psi(y), psi(2y)): worst secant defect "
          f"{depth_curve_convexity_defect(200):+.2e} (<= 0 wanted)")

    print("= 2. every derived constraint, on genuine configurations =")
    for name, on, pr in SAMPLE_CONFIGS:
        d = constraint_defects(on, pr)
        worst = min(d.items(), key=lambda kv: kv[1])
        print(f"  {name:30s} worst slack {worst[1]:+.2e}  ({worst[0]})")

    print("= 3. THE ENTRY-LEVEL SDP, BEFORE AND AFTER =")
    print("  size   earlier lift   ranges only     + trade      predicted")
    for nk in TRADE_RECORD["sizes"]:
        n, k = nk
        from sos_certificate import SDP_RECORD
        base = SDP_RECORD["values"].get(nk)
        b = f"{base:+10.4f}" if base is not None else "     --   "
        print(f"  ({n},{k}) {b}  {TRADE_RECORD['ranges'][nk]:+11.5f}  "
              f"{TRADE_RECORD['trade'][nk]:+11.5f}  "
              f"{trade_prediction(n, k):+11.5f}")
    print("  live re-run of four of them:")
    for nk in ((4, 1), (8, 1), (0, 2), (2, 2)):
        t0 = time.time()
        r = relax_trade(*nk)
        print(f"    n={nk[0]} k={nk[1]}: {r['value']:+.6f}  [{r['status']}] "
              f"{time.time()-t0:.1f}s")

    print("= 4. THE CONE VIOLATOR IS EXCLUDED, and by which constraint =")
    for n in (3, 4, 6):
        for row in violator_family_in_sdp(n):
            who = ("depth cap" if row["depth_cap_excludes"]
                   else ("(T3)" if row["T3_excludes"] else "NOTHING"))
            print(f"  n={n} t={row['t']:.3f}: d={row['d']:.4f} "
                  f"Xi={row['Xi']:+.5f}  pinned into the program: "
                  f"{row['status']:12s} first constraint that excludes it: "
                  f"{who}")
    scr = violator_screen(3)
    print(f"  at the largest depth-admissible t = {scr['t_admissible']:.4f} "
          f"the family still has Xi = {scr['Xi_at_admissible_t']:+.5f} < 0, "
          f"and (T3) rejects it by a factor "
          f"{scr['T3_ratio_at_admissible_t']:.2f}")

    print("= 5. THE TRADE AT THE CONFIGURATION LEVEL: the damage windows =")
    wins = damage_windows(0.5, n_s=200001)
    print(f"  y = 1/2: {len(wins)} windows in [0,300]; the first five:")
    for w in wins[:5]:
        gam = window_repulsion(w["width"])
        occ = occupancy_max(w["peak"], gam)
        print(f"    s in [{w['lo']:7.3f},{w['hi']:7.3f}] "
              f"width {w['width']:.3f}"
              f" peak {w['peak']:.6f} gamma {gam:.4f} -> N* = {occ['N']}, "
              f"cost {occ['value']:.6f}")
    print("= 6. the window occupancy bound: size-free, and positive =")
    for y in (0.05, 0.1, 0.3, 0.49, 0.5):
        r = window_occupancy_bound(y, n_s=200001)
        print(f"  y={y:.2f}: budget {r['budget']:.6f} - 2({r['body']:.6f} + "
              f"tail {r['tail']:.2e}) = {r['bound']:+.6f}  "
              f"({100*r['ratio']:.1f}% of the budget survives, "
              f"first-window occupancy N* = {r['first_window_N']})")
    print("  the same statement as a moment program over occupancies:")
    t0 = time.time()
    cl = cluster_relaxation(0.5, s_max=20.0, h=1.0)
    print(f"    cluster SDP (m={cl['m']}, mass free): value {cl['value']:+.6f}"
          f" - tail {cl['tail']:.6f} = {cl['bound']:+.6f}, mass "
          f"{cl['mass']:.2f}  [{cl['status']}] {time.time()-t0:.0f}s")
    occ = [(round(s_, 1), round(v_, 2)) for s_, v_ in cl['occupancy']]
    print(f"    its occupancy: {occ}")
    print("  against the true minimum over configurations at y = 1/2:")
    for n, v in sorted(WINDOW_RECORD["configuration_minimum_y_half"].items()):
        print(f"    n={n:2d}: {v:+.6f}")

    print("= 7. and where it stops: k >= 2 =")
    req = multi_pair_requirement()
    print(f"  the accounting needs budget(P) >= {req['required_ratio']:.4f} "
          f"sum_p slack(y_p) (worst at y={req['at_y']}), while the measured "
          f"floor is {req['measured_floor']}: short by a factor "
          f"{req['short_by_factor']:.2f}")
    print("  so the k >= 2 gap is on the BUDGET side, not the damage side.")

    print("= 8. size independence, both halves =")
    for n in (4, 7, 8, 10):
        c_ = entry_dual_certificate(n)
        print(f"  entry-level dual at n={n:2d}, k=1: pair-block multiplier "
              f"{c_['pair_block_multiplier']:.0f}, cross-cut multiplier "
              f"{c_['cross_cut_multiplier']:.0f} on {c_['cuts_used']} cuts "
              f"-> Xi >= {c_['coefficient_of_slack']:+.5f} (d^2-1), value "
              f"{c_['value']:+.6f}, sufficient {c_['sufficient']}")
    fit = window_peak_fit(0.5, n_s=200001)
    print(f"  window peak law: D_j (2 pi j)^2 -> {fit['asymptote']:.7f} "
          f"against the predicted 8 c^2 (cosh y - 1) = {fit['predicted']:.7f}"
          f"  (worst relative error over the far half "
          f"{fit['worst_rel_error_tail']:.2e})")
    print("  the occupancy schedule, which is the whole size-free "
          "certificate:")
    r5 = window_occupancy_bound(0.5, n_s=200001)
    print("    N_j = " + ", ".join(str(t_["N"]) for t_ in r5["terms"][:10])
          + ", ...")
    print(f"  QP-form KKT residual of the cluster program: "
          f"{cl['kkt_max']:.2e} (small = the lift's Gam is essentially c c')")

    print("= controls =")
    print("  CLARABEL vs SCS on the entry-level program:")
    for nk in ((0, 1), (2, 1), (8, 1), (2, 2)):
        a_ = relax_trade(*nk, solver="CLARABEL")["value"]
        b_ = relax_trade(*nk, solver="SCS", eps=1e-9)["value"]
        print(f"    n={nk[0]} k={nk[1]}: {a_:+.6f} vs {b_:+.6f}  |diff| "
              f"{abs(a_-b_):.2e}")
    print("  planted infeasibility (the constant raised above the optimum):")
    for c_ in (4.0, 4.25, 5.0):
        v = relax_trade(2, 1, constant=c_)["value"]
        print(f"    constant {c_}: {v:+.6f} "
              f"{'(rejected)' if v < -1e-6 else '(accepted)'}")
    print("  named gaps:")
    for g in NAMED_GAPS:
        print(f"    {g}")


if __name__ == "__main__":
    audit()
