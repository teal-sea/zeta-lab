"""Is the joint verdict a statement about ALL configurations, or only the sweep?

`paper_joint.py` reports theta_full = 0.995 at the paper's field by
running a *sweep of configuration families* — isolated pair, far pair,
worst dipole, sparse/soft/dense lattices, alternating/sandwich/staggered.
A real configuration is an arbitrary finite set of off-line pairs at
arbitrary ordinates and depths, so a family sweep leaves the quantifier
open.  The composition corollary consumes a hypothesis quantified over
*all* configurations, so the open quantifier is a mathematical gap, not a
formalisation one.  This module attacks that gap and reports how far it
gets, which is **not all the way**.

WHAT THE MODULE ESTABLISHES, in the order the work was done.

**1. The budget side, exactly (and it is NOT additive).**  For pairs
``P = {(t_i, y_i)}`` the chain's budget is, by LAW K + LAW L,

    budget(P) = sum_i slack(y_i) + sum_{i != j} T(t_i - t_j, y_i, y_j),

each unordered pair contributing ``2 T``.  The cross term is signed, so
"k pairs give k * slack" is false in both directions.  Writing
``phi^2 * phi^2 =: c2`` (the paper window's autocorrelation, supported in
[-1, 1], and *positive* on (-1, 1) in closed form because
``phi^2 = cos(sqrt2 u) >= cos(sqrt2/2) > 0``), LAW L collapses by the
addition formula ``cosh(a-b) + cosh(a+b) = 2 cosh a cosh b`` into

    T(dt, y1, y2) = (4/A^2) int_{-1}^{1} c2(w) cosh(y1 w) cosh(y2 w)
                                          cos(dt w) dw,

so with ``S_P(w) := sum_i cosh(y_i w) e^{i t_i w}`` and ``int c2 = A^2``,

    **budget(P) = (4/A^2) int_{-1}^{1} c2(w) [ |S_P(w)|^2 - k ] dw**,

exact for every finite configuration (:func:`budget_via_autocorr`,
measured defect ~1e-11, quadrature-limited).  This is the pair-only
shadow of the T1 window's Fourier bridge (`fourier_bridge.py`),
transplanted to the paper field and reduced to the pair block alone; the
diagonal ``T(0, y, y) = 4 + slack(y)`` is what produces the ``- 4k``.
Two immediate consequences: the pair term is a nonnegative-kernel
quadratic form (``sum_{i,j} T_ij >= 0`` for *every* configuration), and
the budget's floor is a positive multiple of the summed slack — measured
minimum ``0.2918 * sum_i slack(y_i)`` at y = 0.49 (500 restarts x 200
local steps; the binding shape is a lattice at 1.005 mean gaps), 0.4818
at y = 0.30, 0.4034 with depths free in [0.05, 0.4999], and negative in
no run (:func:`budget_floor_search`).  That is a measured floor, not a
theorem, and the distinction is load-bearing: a negative budget with a
nonnegative cap would refute the hypothesis outright.

**1b. And the whole verdict restates in the same variable.**  With
``F_on(w) = sum_x e^{i x w}``, ``F_p(w) = sum_i 2 cosh(y_i w) e^{i t_i
w}`` and ``E[G] = (1/A^2) int c2 |G|^2``, the chain's inequality is
*identically*

    budget(P) - [ D(X) - (1-theta) R(X) ]
        = E[F_on + F_p] - theta E[F_on] - (1-theta) n - 4k

(:func:`verdict_fourier_gap`, defect ~1e-11 on mixed configurations), so
the universally-quantified hypothesis is exactly

    **E[F_on + F_p] >= theta E[F_on] + (1-theta) n + 4k**

for every finite on-line multiset (size n) and pair set (size k).  That
does not close the quantifier, but it changes what is left: one
nonnegative bandlimited kernel and two exponential sums, instead of a
family of configuration sweeps.

**2. RUNG 1 — cap subadditivity: it FAILS, and the mechanism is exact.**
The damage field is additive across pairs *before* clipping, and the
chain clips the joint field, so per-pair clipping is one-sided upward at
the level of the FIELD.  It is not one-sided at the level of the CAP.
The per-cell square completion, relaxed,

    Bq(F, K) = (F + cK)^2 / (4 c K),      c = 1 - theta,

satisfies the exact identity

    Bq(sum_p F_p, K) - sum_p Bq(F_p, K)
        = [ 2 sum_{i<j} F_i F_j - (k-1) (cK)^2 ] / (4 c K),

which is *positive* as soon as the pairwise products beat the per-cell
credit — the adversary collects k times the damage from one stack of
zeros but pays the internal charge once.  Measured at theta = 0.995,
y = 0.49, k coincident pairs: joint cap / sum of single-pair caps =
1.4475 (k=2), 1.9318 (k=3), 2.4100 (k=4), 3.3796 (k=6).  The failure is
*entirely* the square completion and not the band structure: the same
ratios are **exactly 1.0000** at every k once theta drops below the
k-fold single-occupancy threshold ``1 - k F_max / (2 K)`` (1.0914 /
1.2268 / 1.3734 at theta = 0.98, and 1.0000 flat at theta <= 0.95).
The two halves separate cleanly under measurement
(:func:`band_structure_comparison`, :func:`occupancy_profile`): the
joint band SET only ever shrinks — for a coincident stack it is
identical to one pair's, and the pointwise positive-part inequality
``max(0, sum f_p) <= sum max(0, f_p)`` never fails — while the
occupancy grows, ``m* = 7`` on the joint cells of a coincident triple
against ``m* = 3`` on each pair's own.

**3. And the per-pair route could not have worked anyway.**  Even where
subadditivity holds, the conclusion does not: at the nu = 1 lattice
(spacing = one mean gap) at y = 0.49, theta = 0.995,

    k = 3:  budget 0.27827  <  sum_i cap_single(y_i) 0.28422,

while the JOINT cap is 0.16684 and the verdict closes with +0.11144.
So there is an explicit three-pair witness at which the per-pair route
``sum_i cap_single <= budget`` is false while the joint statement is
true.  The joint field's shielding is load-bearing, not decorative:
**no argument that bounds the joint cap by a sum of single-pair caps can
establish universality at theta* = 0.995**, whatever the direction of
the subadditivity inequality.  (:func:`per_pair_route_witness`.)

**4. RUNG 2 — the repairs, and why they do not close it either.**

- *Even split* (proven, per cell): ``B(sum_p F_p, K) <= sum_p B(F_p,
  K/k)`` because the charge can be shared before the maximisation.  It
  converts the joint cap into k single-pair caps at the DEGRADED charge
  ``(1-theta)/k``, i.e. at ``theta_k = 1 - (1-theta)/k``.  At
  theta = 0.995 and k = 2 that is theta = 0.9975, and the single-pair
  dual at this field already fails at 0.999 — so the bound is valid and
  useless.  Measured in :func:`even_split_bound`.
- *Union refinement* (the suggested repair): band maxima do **not**
  increase under refinement (a max over a subinterval is a max over a
  subset), but the cap does, because every sub-cell inherits the parent
  band's maximum while the cell count grows.  Measured on the delta
  ladder: 0.08745 (delta >= 1) -> 0.17050 (delta = 0.5) -> 0.33890
  (delta = 0.25) for one pair at y = 0.49.  Refinement is one-sided in
  the direction that inflates the cap, so a common-refinement comparison
  cannot repair a domination failure.  (:func:`refinement_ladder`.)

**5. RUNG 3 — randomised adversarial search.**  320 configurations (260
random + 60 descent steps; k in 2..12; jittered lattices, near-coincident
clusters, uniform windows, tight windows; equal and mixed depths) at
theta = 0.995 against a conservative instance of the cap.  Results, all
in :data:`WORST_RANDOM_RECORD`:

- **0 configurations opened the verdict**;
- worst relative margin **+0.2423** on the search instance, **+0.2749**
  re-checked at the module's resolution — a two-pair configuration at
  2.05 mean gaps, i.e. the sparse-lattice family that already binds
  paper_joint.py's sweep, rediscovered without being told;
- **37 of 320 configurations broke rung-1 domination**, worst ratio
  1.4128 (1.3460 re-checked) at nine pairs inside 0.55 grid units.  So
  the subadditivity failure is not an artifact of hand-built stacks; a
  blind search finds it in about one configuration in nine.

This is evidence, **not** a proof, and it is labelled so everywhere it is
used: a search bounds the adversary from below and the quantifier not at
all.

WHAT REMAINS OPEN, stated plainly: the multi-pair verdict is still a
statement about a (much larger) tested set, not about all configurations.
What this module changes is the shape of the remaining obligation — it is
now a statement about one nonnegative kernel ``c2`` and two exponential
sums, with the per-pair reduction ruled out by an explicit witness rather
than left untried.

**THE BOTTOM LINE.**  Multi-pair universality does **not** follow from
the single-pair bound.  Two independent blockers, both quantified above:
the cap is superadditive in the coincidence regime (rung 1), and even
where it is not, the sum of single-pair caps exceeds the budget from
three pairs on (section 3).  What the module leaves behind instead of a
proof: the exact budget identity, the exact excess identity, the
theta-threshold that separates the two branches, the one-variable
restatement of the whole verdict, and a 320-configuration search that
found no violation.  The multi-pair verdict remains a statement about a
tested set.

Nothing here computes a proportion and nothing here is evidence about RH.
Run ``.venv/bin/python hunts/frontier_math/joint_universal.py`` (~8 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import (  # noqa: E402
    A, MEAN_GAP, PaperChain, phipap, phipap_d1, phipap_d2,
)
from paper_joint import PaperJoint  # noqa: E402

S2 = math.sqrt(2.0)

#: the retention grid point paper_joint.py reports for the swept families
THETA_FULL = 0.995


# ---------------------------------------------------------------------------
# 1. the window autocorrelation c2 = phi^2 * phi^2, in closed form
# ---------------------------------------------------------------------------


def autocorr(w):
    """``c2(w) = (phi^2 * phi^2)(w)`` for ``phi^2(u) = cos(sqrt2 u)`` on
    ``[-1/2, 1/2]``, in closed form.

    For ``0 <= w <= 1`` the overlap integral is
    ``int_{w-1/2}^{1/2} cos(sqrt2 u) cos(sqrt2 (w-u)) du``; the
    product-to-sum identity gives

        c2(w) = sin(sqrt2 (1-w)) / (2 sqrt2) + (1-w) cos(sqrt2 w) / 2,

    even in ``w`` and supported in ``[-1, 1]``.

    **Positivity is closed-form, not measured**: on ``[0, 1]`` the first
    term has argument in ``[0, sqrt2] subset [0, pi]`` and the second has
    ``sqrt2 w <= sqrt2 < pi/2``, so both terms are nonnegative and c2 is
    strictly positive on ``(-1, 1)``.  That is the whole reason the pair
    energy of section 2 is a nonnegative-kernel quadratic form.
    """
    a = np.minimum(np.abs(np.asarray(w, float)), 1.0)
    val = np.sin(S2 * (1 - a)) / (2 * S2) + (1 - a) * np.cos(S2 * a) / 2
    return np.where(np.abs(np.asarray(w, float)) < 1.0, val, 0.0)


def autocorr_mass(n: int = 2_000_001) -> float:
    """``int_{-1}^{1} c2 = (int phi^2)^2 = A^2`` — the normalisation that
    turns the ``k`` in the budget identity into ``4k``."""
    ws = np.linspace(-1.0, 1.0, n)
    return float(np.trapezoid(autocorr(ws), ws))


def autocorr_defect(n_quad: int = 200001, probes=(0.0, 0.17, 0.5, 0.83, 0.99)):
    """Closed form against a direct numerical convolution of ``phi^2``.

    The overlap interval is integrated exactly (``u`` from ``w - 1/2`` to
    ``1/2``) rather than masked on a fixed grid: a mask puts the window's
    jump inside the quadrature and measures the differencer, not the
    closed form.
    """
    worst = 0.0
    for w in probes:
        lo, hi = abs(w) - 0.5, 0.5
        if hi <= lo:
            continue
        us = np.linspace(lo, hi, n_quad)
        num = float(np.trapezoid(np.cos(S2 * us) * np.cos(S2 * (abs(w) - us)),
                                 us))
        cls = float(autocorr(np.array([w]))[0])
        worst = max(worst, abs(num - cls) / max(abs(cls), 1e-30))
    return worst


# ---------------------------------------------------------------------------
# 2. the pair energy as a nonnegative-kernel quadratic form
# ---------------------------------------------------------------------------


def W_via_autocorr(g: float, y: float, n: int = 400001) -> float:
    """``W(g, y) = (2/A^2) int c2(w) cosh(y w) cos(g w) dw``.

    From ``Phi2(z)^2 = int c2(w) e^{i z w} dw`` and the evenness of c2:
    ``Re Phi2(g+iy)^2 = int c2(w) cosh(y w) cos(g w) dw``.  Quadrature
    grade; the control is :func:`W_autocorr_defect`.
    """
    ws = np.linspace(-1.0, 1.0, n)
    return 2 * float(np.trapezoid(autocorr(ws) * np.cosh(y * ws)
                                  * np.cos(g * ws), ws)) / A**2


def W_autocorr_defect(probes=((0.0, 0.0), (1.3, 0.49), (5.0, 0.3),
                              (20.0, 0.1), (0.0, 0.49))) -> float:
    """Worst absolute defect of the representation against ``PaperChain.W``."""
    pc = PaperChain()
    worst = 0.0
    for g, y in probes:
        direct = float(pc.W(np.array([g]), y)[0])
        worst = max(worst, abs(direct - W_via_autocorr(g, y)))
    return worst


def pair_energy_matrix(pairs) -> np.ndarray:
    """``T_ij = T(t_i - t_j, y_i, y_j)`` including the diagonal
    ``T_ii = W(0,0) + W(0,2y_i) = 4 + slack(y_i)``.

    Vectorised over the whole configuration: this is the object the
    budget is a shadow of, and it is cheap enough to search over.
    """
    ts = np.array([t for t, _ in pairs], float)
    ys = np.array([y for _, y in pairs], float)
    dt = ts[:, None] - ts[None, :]
    yd = np.abs(ys[:, None] - ys[None, :])
    ysum = ys[:, None] + ys[None, :]
    v1 = phipap(dt + 1j * yd)
    v2 = phipap(dt + 1j * ysum)
    return 2 * ((v1.real**2 - v1.imag**2)
                + (v2.real**2 - v2.imag**2)) / A**2


def budget_terms(pairs) -> dict:
    """The budget's exact decomposition — **the slack-additivity relation**.

    Returns ``sum_slack`` (the additive part), ``pair_term``
    (``sum_{i != j} T_ij``, the signed non-additive part), ``budget``
    (their sum, identical to ``PaperJoint.budget``), ``pair_energy``
    (``sum_{i,j} T_ij >= 0``), and ``per_pair`` (the exact per-pair
    split ``b_i = slack_i + sum_{j != i} T_ij``, which sums to the
    budget but may individually be negative).
    """
    pc = PaperChain()
    T = pair_energy_matrix(pairs)
    k = len(pairs)
    slacks = np.array([pc.slack(y) for _, y in pairs])
    off = T - np.diag(np.diag(T))
    return {
        "k": k,
        "sum_slack": float(slacks.sum()),
        "pair_term": float(off.sum()),
        "budget": float(slacks.sum() + off.sum()),
        "pair_energy": float(T.sum()),
        "per_pair": (slacks + off.sum(axis=1)).tolist(),
        "worst_per_pair": float((slacks + off.sum(axis=1)).min()),
    }


def budget_via_autocorr(pairs, n: int = 600001) -> float:
    """``budget(P) = (4/A^2) int_{-1}^{1} c2(w) [ |S_P(w)|^2 - k ] dw``.

    ``S_P(w) = sum_i cosh(y_i w) e^{i t_i w}``.  Exact identity, checked
    against :func:`budget_terms` to quadrature accuracy; it is the form
    in which "the budget can never be driven below zero" would have to be
    shown, since c2 >= 0 and the only negative contribution is the ``-k``.
    """
    ws = np.linspace(-1.0, 1.0, n)
    S = np.zeros_like(ws, dtype=complex)
    for t, y in pairs:
        S += np.cosh(y * ws) * np.exp(1j * t * ws)
    return 4 * float(np.trapezoid(autocorr(ws) * (np.abs(S) ** 2 - len(pairs)),
                                  ws)) / A**2


def damage_and_charge(online, pairs) -> dict:
    """``D(X) = sum_x f_P(x)`` and ``R(X) = sum_{x != x'} omega^2(x-x')``.

    The two primal quantities the cap bounds: ``D`` is the joint damage
    the on-line multiset collects, ``R`` the internal charge it pays.
    ``online`` is a multiset (repeat an ordinate to stack zeros there).
    """
    pc = PaperChain()
    xs = np.array(list(online), float)
    D = 0.0
    for t, y in pairs:
        D += float((-2 * pc.W(xs - t, y)).sum())
    dx = xs[:, None] - xs[None, :]
    om = pc.omega2(dx.astype(complex)).real
    R = float(om.sum() - np.trace(om))
    return {"D": D, "R": R, "n": len(xs)}


def energy(fun, n: int = 400001) -> float:
    """``E[G] = (1/A^2) int_{-1}^{1} c2(w) |G(w)|^2 dw`` — the one
    nonnegative-kernel form every object of the chain is a shadow of."""
    ws = np.linspace(-1.0, 1.0, n)
    return float(np.trapezoid(autocorr(ws) * np.abs(fun(ws)) ** 2, ws)) / A**2


def verdict_fourier_gap(online, pairs, theta: float,
                        n: int = 400001) -> dict:
    """**The whole joint verdict, restated in one variable.**

    With ``F_on(w) = sum_x e^{i x w}``, ``F_p(w) = sum_i 2 cosh(y_i w)
    e^{i t_i w}``, ``E[G] = (1/A^2) int c2 |G|^2``, ``n = |X|`` and
    ``k = |P|``, the chain's inequality is *exactly*

        budget(P) - [ D(X) - (1-theta) R(X) ]
              =  E[F_on + F_p] - theta E[F_on] - (1-theta) n - 4k,

    so the joint verdict holds for every configuration if and only if

        **E[F_on + F_p]  >=  theta E[F_on] + (1-theta) n + 4k**

    for every finite on-line multiset and every finite pair set.  The
    bookkeeping: ``E[F_on] = n + R``, ``E[F_p] = sum_{i,j} T_ij =
    budget + 4k``, and the cross term is ``-D``.

    This is the paper field's instance of the T1 window's Fourier bridge
    (`fourier_bridge.py`), carried through the pair diagonal so that the
    subtraction is the pair of explicit constants ``(1-theta) n + 4k``.
    It does not close the quantifier; it changes what the remaining
    obligation is *about* — one nonnegative bandlimited kernel and two
    exponential sums, rather than a family of configuration sweeps.
    """
    xs = np.array(list(online), float)
    ts = np.array([t for t, _ in pairs], float)
    ys = np.array([y for _, y in pairs], float)

    def F_on(w):
        return np.exp(1j * xs[:, None] * w[None, :]).sum(axis=0) \
            if len(xs) else np.zeros_like(w, dtype=complex)

    def F_p(w):
        if not len(ts):
            return np.zeros_like(w, dtype=complex)
        return (2 * np.cosh(ys[:, None] * w[None, :])
                * np.exp(1j * ts[:, None] * w[None, :])).sum(axis=0)

    e_on = energy(F_on, n)
    e_tot = energy(lambda w: F_on(w) + F_p(w), n)
    dr = damage_and_charge(online, pairs)
    pj = PaperJoint()
    b = pj.budget(pairs)
    direct = b - (dr["D"] - (1 - theta) * dr["R"])
    fourier = e_tot - theta * e_on - (1 - theta) * dr["n"] - 4 * len(pairs)
    return {"direct": direct, "fourier": fourier,
            "defect": abs(direct - fourier), "budget": b,
            "D": dr["D"], "R": dr["R"], "E_on": e_on, "E_total": e_tot}


def budget_fast(ts, ys) -> float:
    """``budget`` from arrays, for search loops (no Python-level pair loop)."""
    ts = np.asarray(ts, float)
    ys = np.asarray(ys, float)
    dt = ts[:, None] - ts[None, :]
    v1 = phipap(dt + 1j * np.abs(ys[:, None] - ys[None, :]))
    v2 = phipap(dt + 1j * (ys[:, None] + ys[None, :]))
    T = 2 * ((v1.real**2 - v1.imag**2) + (v2.real**2 - v2.imag**2)) / A**2
    return float(T.sum()) - 4 * len(ts)


# ---------------------------------------------------------------------------
# 3. the square completion, and the exact excess that breaks subadditivity
# ---------------------------------------------------------------------------


def completion(F: float, K: float, c: float) -> float:
    """The chain's per-cell cap: ``F`` on the single-occupancy branch,
    the relaxed completion above it.  Mirrors ``PaperJoint.cap``'s inline
    expression; :func:`completion_matches_module` pins the two together."""
    if c <= 0 or K <= 0:
        return math.inf
    return F if F <= 2 * c * K else (F + c * K) ** 2 / (4 * c * K)


def completion_relaxed(F: float, K: float, c: float) -> float:
    """``Bq(F,K) = (F + cK)^2 / (4cK)``, the continuous relaxation of
    ``max_m [m F - c m(m-1) K]``.  Always ``>= F`` (the difference is
    ``(F - cK)^2 / (4cK) >= 0``), so it majorises :func:`completion`."""
    if c <= 0 or K <= 0:
        return math.inf
    return (F + c * K) ** 2 / (4 * c * K)


def completion_excess(Fs, K: float, c: float) -> dict:
    """The **exact** superadditivity of the relaxed completion:

        Bq(sum F_p) - sum_p Bq(F_p)
            = [ 2 sum_{i<j} F_i F_j - (k-1) (cK)^2 ] / (4 c K).

    Returns the two sides and their defect.  This closed form is the
    whole mechanism of the rung-1 failure: the damage adds over pairs but
    the internal charge is paid once, so the pairwise products
    ``F_i F_j`` are pure profit to the adversary.
    """
    Fs = list(map(float, Fs))
    k = len(Fs)
    lhs = (completion_relaxed(sum(Fs), K, c)
           - sum(completion_relaxed(F, K, c) for F in Fs))
    cross = sum(Fs[i] * Fs[j] for i in range(k) for j in range(i + 1, k))
    rhs = (2 * cross - (k - 1) * (c * K) ** 2) / (4 * c * K)
    return {"lhs": lhs, "rhs": rhs, "defect": abs(lhs - rhs),
            "positive": lhs > 0}


def even_split_theta(theta: float, k: int) -> float:
    """``theta_k = 1 - (1-theta)/k`` — the charge each pair keeps when the
    per-cell charge is split evenly before the maximisation.

    **The even-split lemma** (exact, per cell): since
    ``m sum_p F_p - c m(m-1) K = sum_p [ m F_p - (c/k) m(m-1) K ]`` and a
    sup of a sum is at most the sum of sups,

        max_m [ m sum_p F_p - c m(m-1) K ]
            <= sum_p max_m [ m F_p - (c/k) m(m-1) K ].

    So the joint per-cell cap at charge ``c`` is dominated by ``k``
    single-pair per-cell caps at charge ``c/k``.
    """
    return 1.0 - (1.0 - theta) / k


def even_split_defect(F1: float, F2: float, K: float, c: float) -> float:
    """Slack in the even-split lemma at one cell (must be ``>= 0``)."""
    return (completion_relaxed(F1, K, c / 2) + completion_relaxed(F2, K, c / 2)
            - completion_relaxed(F1 + F2, K, c))


# ---------------------------------------------------------------------------
# 4. the domination instrument
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class JointUniversal:
    """Rung-1/2 instrumentation around an unmodified ``PaperJoint``.

    ``pj`` is the joint cap exactly as ``paper_joint.py`` builds it — this
    module never re-implements the cap, it only compares it against
    per-pair objects computed with the same instrument (so any difference
    is structural and not a resolution artifact).
    """

    pj: PaperJoint = PaperJoint()

    # -- per-pair reference objects -----------------------------------------

    @lru_cache(maxsize=512)
    def cap_single(self, y: float, theta: float) -> float:
        """The joint cap on the one-pair configuration — the per-pair
        object a subadditive argument would sum."""
        return self.pj.cap([(0.0, float(y))], float(theta))["cap"]

    def cap_single_sum(self, pairs, theta: float) -> float:
        return sum(self.cap_single(y, theta) for _, y in pairs)

    # -- rung 1 --------------------------------------------------------------

    def domination(self, pairs, theta: float) -> dict:
        """``cap_joint`` against ``sum_p cap_single``.

        ``ratio <= 1`` is the rung-1 inequality (joint dominated by the
        per-pair sum).  ``ratio > 1`` is a subadditivity failure.
        """
        cj = self.pj.cap(pairs, theta)["cap"]
        cs = self.cap_single_sum(pairs, theta)
        return {"cap_joint": cj, "cap_single_sum": cs,
                "ratio": cj / cs if cs > 0 else math.inf,
                "subadditive": cj <= cs + 1e-12}

    def per_pair_route(self, pairs, theta: float) -> dict:
        """The route rung 1 was supposed to open: does the *sum of
        single-pair caps* sit inside the budget?

        This is the statement a subadditive argument would have to end
        at.  Where ``closes`` is False the per-pair route is refuted for
        that configuration, whatever the domination ratio does.
        """
        b = self.pj.budget(pairs)
        cs = self.cap_single_sum(pairs, theta)
        cj = self.pj.cap(pairs, theta)["cap"]
        return {"budget": b, "cap_single_sum": cs, "cap_joint": cj,
                "per_pair_margin": b - cs, "joint_margin": b - cj,
                "closes": b - cs >= 0, "joint_closes": b - cj >= 0}

    # -- rung 2 --------------------------------------------------------------

    def even_split_bound(self, pairs, theta: float) -> dict:
        """``sum_p cap_single(y_p; theta_k)`` with ``theta_k`` from
        :func:`even_split_theta` — the universal-but-lossy bound.

        The per-cell lemma is exact; the module-level comparison below
        additionally assumes the cells can be taken common to the joint
        and the single-pair partitions, which is *not* established here
        and is named as the residual step.
        """
        k = len(pairs)
        th_k = even_split_theta(theta, k)
        bound = sum(self.cap_single(y, th_k) for _, y in pairs)
        cj = self.pj.cap(pairs, theta)["cap"]
        b = self.pj.budget(pairs)
        return {"theta_k": th_k, "bound": bound, "cap_joint": cj,
                "budget": b, "dominates": cj <= bound + 1e-12,
                "funds_universality": bound <= b}

    def refinement_ladder(self, pairs, theta: float,
                          deltas=(0.25, 0.5, 1.0, 2.0, 3.0, 5.0)) -> list:
        """The per-cell sum along the delta ladder (no tail, no allowance).

        Answers the rung-2 sub-question directly: band maxima do not grow
        under refinement, but each sub-cell inherits the parent band's
        maximum, so the *cap* grows.  Refinement is one-sided upward.
        """
        c = 1 - theta
        out = []
        for d in deltas:
            cells = self.pj.band_cells(pairs, d)
            total, ok = 0.0, True
            for F, w in cells:
                K = self.pj.K_of(w)
                if K <= 0:
                    ok = False
                    break
                total += completion(F, K, c)
            out.append({"delta": d, "cells": len(cells),
                        "sum": total if ok else math.inf})
        return out

    def multiplicity_threshold_k(self, y: float, k: int,
                                 delta: float = 1.0) -> float:
        """``1 - k F_max(y) / (2 K(delta))``: the theta below which a
        k-fold coincident stack keeps every cell on the single-occupancy
        branch, where the completion is additive in F and the rung-1
        inequality holds with ratio exactly 1."""
        bs = self.pj.bands([(0.0, float(y))])
        F_max = max(F for _, _, F in bs)
        return 1.0 - k * F_max / (2 * self.pj.K_of(delta))

    # -- rung 2: which half of the cap moves? --------------------------------

    def band_structure_comparison(self, pairs) -> dict:
        """Joint bands against the per-pair band systems.

        ``{f_P > 0}`` sits inside the union of ``{f_p > 0}`` because
        ``max(0, sum) <= sum max(0, .)`` pointwise, so the joint band set
        can only be *smaller* than that union — the shielding.  Two
        different reductions are reported separately, because conflating
        them is easy: ``overlap_fraction`` is how much the per-pair band
        systems share ground (it is 1 - 1/k for coincident pairs and has
        nothing to do with the field), and ``shielded_fraction`` compares
        the joint bands against the UNION, which is the real shielding.

        ``outside_fraction`` is the joint band measure falling outside
        every listed per-pair band.  It is not exactly 0: ``PaperJoint``
        drops one-grid-point groups from a band list, so a per-pair band
        thinner than two steps is absent from the per-pair list while its
        contribution still shows up jointly.  That is a listing
        artifact of the discretisation, not a failure of the pointwise
        inequality, which :func:`positive_part_domination` checks
        directly.
        """
        joint = self.pj.bands(pairs)
        j_meas = sum(hi - lo for lo, hi, _ in joint)
        p_meas = 0.0
        singles = []
        for t, y in pairs:
            bs = self.pj.bands([(t, y)])
            p_meas += sum(hi - lo for lo, hi, _ in bs)
            singles.append(bs)
        ivs = sorted((a, b) for bs in singles for a, b, _ in bs)
        u_meas, cur_lo, cur_hi = 0.0, None, None
        for a, b in ivs:
            if cur_hi is None or a > cur_hi:
                if cur_hi is not None:
                    u_meas += cur_hi - cur_lo
                cur_lo, cur_hi = a, b
            else:
                cur_hi = max(cur_hi, b)
        if cur_hi is not None:
            u_meas += cur_hi - cur_lo
        outside = 0
        total = 0
        for lo, hi, _ in joint:
            gs = np.arange(lo, hi, self.pj.step * 5)
            total += len(gs)
            covered = np.zeros(len(gs), bool)
            for bs in singles:
                for a, b, _ in bs:
                    covered |= (gs >= a - self.pj.step) & (gs <= b + self.pj.step)
            outside += int((~covered).sum())
        return {"joint_measure": j_meas, "per_pair_measure": p_meas,
                "union_measure": u_meas,
                "overlap_fraction": 1 - u_meas / p_meas if p_meas else 0.0,
                "shielded_fraction": 1 - j_meas / u_meas if u_meas else 0.0,
                "outside_fraction": outside / total if total else 0.0}

    def positive_part_domination(self, pairs, halo: float = 40.0) -> dict:
        """``max(0, sum_p f_p) <= sum_p max(0, f_p)`` pointwise, measured.

        The inequality is elementary; what is worth measuring is how far
        from an equality it is, because that gap *is* the shielding the
        chain buys by clipping the joint field rather than each pair's.
        Returns the worst pointwise violation (must be ``<= 0``) and the
        ratio of the two integrated positive parts.
        """
        lo = min(t for t, _ in pairs) - halo
        hi = max(t for t, _ in pairs) + halo
        gs = np.arange(lo, hi, self.pj.step)
        joint = np.zeros_like(gs)
        per_pair = np.zeros_like(gs)
        for t, y in pairs:
            w = -2 * self.pj.pc.W(gs - t, y)
            joint += w
            per_pair += np.maximum(0.0, w)
        jp = np.maximum(0.0, joint)
        return {"worst_violation": float((jp - per_pair).max()),
                "joint_positive_mass": float(jp.sum()) * self.pj.step,
                "per_pair_positive_mass": float(per_pair.sum()) * self.pj.step,
                "ratio": float(jp.sum() / max(per_pair.sum(), 1e-30))}

    def occupancy_profile(self, pairs, theta: float,
                          delta: float = 1.0) -> dict:
        """The optimal per-cell multiplicity ``m*`` on the joint cells and
        on the per-pair cells — the other half of the rung-2 question.

        ``m* = 1`` everywhere is the single-occupancy branch, where the
        completion is additive in ``F``; ``m* > 1`` on the joint cells
        while ``m* = 1`` on the per-pair cells is exactly the shape of the
        subadditivity failure.
        """
        c = 1 - theta

        def profile(ps):
            ms = []
            for F, w in self.pj.band_cells(ps, delta):
                K = self.pj.K_of(w)
                if K <= 0:
                    ms.append(math.inf)
                elif F <= 2 * c * K:
                    ms.append(1)
                else:
                    ms.append(int(round((F + c * K) / (2 * c * K))))
            return ms

        joint = profile(pairs)
        singles = [m for t, y in pairs for m in profile([(t, y)])]
        return {"joint_max_m": max(joint) if joint else 0,
                "single_max_m": max(singles) if singles else 0,
                "joint_cells_above_1": sum(1 for m in joint if m > 1),
                "single_cells_above_1": sum(1 for m in singles if m > 1)}

    # -- the verdict ---------------------------------------------------------

    def verdict(self, pairs, theta: float) -> dict:
        rec = self.pj.verdict(pairs, theta)
        rec["rel_margin"] = rec["margin"] / max(rec["budget"], 1e-12)
        return rec


# ---------------------------------------------------------------------------
# 5. the lesion: a planted inflation of one pair's damage
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InflatedJoint(PaperJoint):
    """``PaperJoint`` with one pair's damage contribution scaled by
    ``inflate`` — a planted fault, for detector power.

    The budget is untouched (it is built from ``slack`` and ``T``), so a
    configuration that closes honestly must be pushed OPEN by a large
    enough inflation.  A verdict that stays closed under an arbitrary
    inflation of the damage would be measuring nothing.
    """

    inflate: float = 1.0
    inflate_index: int = 0

    def field(self, pairs, lo: float, hi: float):
        gs = np.arange(lo, hi, self.step)
        f = np.zeros_like(gs)
        Q = np.zeros_like(gs)
        qpp = np.zeros_like(gs)
        slope = np.zeros_like(gs)
        for idx, (t, y) in enumerate(pairs):
            scale = self.inflate if idx == self.inflate_index else 1.0
            z = (gs - t) + 1j * y
            v = phipap(z)
            v1 = phipap_d1(z)
            v2 = phipap_d2(z)
            re2 = v.real**2 - v.imag**2
            Q += scale * re2
            f += scale * (-4 * re2 / A**2)
            av, a1, a2 = np.abs(v), np.abs(v1), np.abs(v2)
            slope += scale * 8 * av * a1 / A**2
            qpp += scale * 2 * (a1**2 + av * a2)
        return gs, f, Q, qpp, slope


def planted_violation(pairs=None, theta: float = THETA_FULL,
                      inflations=(1.0, 2.0, 4.0, 8.0)) -> list:
    """Run the lesion ladder: the honest verdict must close and a large
    enough planted inflation must open it."""
    if pairs is None:
        pairs = [(0.0, 0.49), (MEAN_GAP, 0.49), (2 * MEAN_GAP, 0.49)]
    out = []
    for s in inflations:
        pj = InflatedJoint(inflate=s)
        rec = pj.verdict(pairs, theta)
        out.append({"inflate": s, "cap": rec["cap"], "budget": rec["budget"],
                    "margin": rec["margin"], "closes": rec["closes"]})
    return out


# ---------------------------------------------------------------------------
# 6. rung 3: randomised adversarial search
# ---------------------------------------------------------------------------

#: the search instance.  A coarser step at the SAME resolved half-range is
#: conservative — wider band edges and larger local slope margins push the
#: cap up (measured 0.5-5% above the step = 0.001 cap across the probe
#: configurations), so a configuration that closes here closes at the
#: module default.  Completeness still clears the >100 gate.
SEARCH_STEP = 0.005

#: Depths are drawn from a ladder rather than the continuum.  The reason
#: is mechanical, not statistical: ``PaperJoint.tail`` needs a band period
#: per depth, which costs a 800k-point field pass and is memoised with
#: ``maxsize=16``, so a continuum of depths spends the entire search
#: recomputing single-pair band systems.  Twelve rungs keep that cache
#: warm; the geometry (positions, spacings, clustering, k) stays
#: continuous, and that is where the adversary lives.
DEPTH_LADDER = (0.02, 0.063, 0.106, 0.148, 0.191, 0.234,
                0.277, 0.319, 0.362, 0.405, 0.448, 0.49)


def random_config(rng, kmax: int = 12, kmin: int = 1):
    """One random configuration: shape, positions, depths.

    Five shapes, chosen so that the two regimes the sweep misses are both
    reachable — near-coincident clusters (where the cap is superadditive)
    and near-mean-gap lattices at the deep end (where the pair term eats
    the most budget, measured floor ~0.29 of the summed slack).  Depths
    are drawn deep half the time on purpose: a uniform draw over
    (0, 1/2) puts most configurations where the field is nearly flat and
    the search learns nothing.
    """
    k = int(rng.integers(kmin, kmax + 1))
    shape = int(rng.integers(0, 5))
    if shape == 0:                                  # jittered lattice
        s = float(rng.uniform(4.0, 20.0))
        ts = np.arange(k) * s + rng.normal(0.0, 0.35, k)
    elif shape == 1:                                # uniform window
        span = float(rng.uniform(2.0, 30.0)) * MEAN_GAP
        ts = np.sort(rng.uniform(0.0, span, k))
    elif shape == 2:                                # clusters (coincidence)
        n_c = max(1, int(rng.integers(1, max(2, k // 2 + 1))))
        centres = rng.uniform(0.0, 12.0 * MEAN_GAP, n_c)
        ts = np.sort(rng.choice(centres, k)
                     + rng.normal(0.0, float(rng.uniform(0.001, 1.0)), k))
    elif shape == 3:                                # near the mean gap
        s = float(rng.uniform(5.6, 7.2))
        ts = np.arange(k) * s + rng.normal(0.0, 0.15, k)
    else:                                           # tight window
        ts = np.sort(rng.uniform(0.0, 3.0 * MEAN_GAP, k))
    ladder = np.array(DEPTH_LADDER)
    if rng.random() < 0.5:                          # deep half of the ladder
        ladder = ladder[len(ladder) // 2:]
    if rng.random() < 0.5:                          # one common depth
        ys = np.full(k, float(rng.choice(ladder)))
    else:
        ys = rng.choice(ladder, k)
    return [(float(t), float(y)) for t, y in zip(ts, ys)]


def random_search(n: int = 300, theta: float = THETA_FULL, seed: int = 2026,
                  kmax: int = 12, kmin: int = 2, step: float = SEARCH_STEP,
                  descend: int = 0, report_every: int = 0) -> dict:
    """Rung 3.  **Evidence, not a proof, and it is labelled so.**

    Draws ``n`` random configurations, takes the joint verdict at
    ``theta`` on the conservative search instance, then (optionally) runs
    ``descend`` steps of local perturbation from the worst draw to push
    the relative margin down further.  Returns the worst relative margin,
    the configuration attaining it, and the worst rung-1 domination ratio
    seen along the way.
    """
    ju = JointUniversal(PaperJoint(step=step))
    rng = np.random.default_rng(seed)
    worst = {"rel_margin": math.inf, "pairs": None}
    worst_ratio = {"ratio": 0.0, "pairs": None}
    n_open = 0
    n_nonsub = 0

    def score(pairs):
        """One field pass: the cap is computed once and reused for both
        the verdict and the rung-1 ratio."""
        cap = ju.pj.cap(pairs, theta)["cap"]
        b = ju.pj.budget(pairs)
        cs = ju.cap_single_sum(pairs, theta)
        return {"cap": cap, "budget": b, "margin": b - cap,
                "rel_margin": (b - cap) / max(b, 1e-12),
                "cap_single_sum": cs,
                "ratio": cap / cs if cs > 0 else math.inf}

    def absorb(pairs, rec):
        nonlocal n_open, n_nonsub, worst, worst_ratio
        if rec["margin"] < 0:
            n_open += 1
        if rec["rel_margin"] < worst["rel_margin"]:
            worst = {"rel_margin": rec["rel_margin"], "pairs": pairs,
                     "budget": rec["budget"], "cap": rec["cap"],
                     "margin": rec["margin"]}
        if rec["cap"] > rec["cap_single_sum"] + 1e-12:
            n_nonsub += 1
        if rec["ratio"] > worst_ratio["ratio"]:
            worst_ratio = {"ratio": rec["ratio"], "pairs": pairs}

    for i in range(n):
        pairs = random_config(rng, kmax, kmin)
        absorb(pairs, score(pairs))
        if report_every and (i + 1) % report_every == 0:
            print(f"    [{i+1}/{n}] worst rel margin so far "
                  f"{worst['rel_margin']:+.5f}, worst ratio "
                  f"{worst_ratio['ratio']:.4f}, opens {n_open}, "
                  f"non-subadditive {n_nonsub}", flush=True)

    for it in range(descend):
        base = worst["pairs"]
        amp = 0.6 * math.exp(-it / max(1, descend / 3))
        # positions move continuously; depths hop on the ladder, for the
        # cache reason recorded at DEPTH_LADDER
        cand = [(t + float(rng.normal(0.0, amp)),
                 (y if rng.random() > 0.15
                  else float(rng.choice(np.array(DEPTH_LADDER)))))
                for t, y in base]
        absorb(cand, score(cand))
        if report_every and (it + 1) % report_every == 0:
            print(f"    [descent {it+1}/{descend}] worst rel margin "
                  f"{worst['rel_margin']:+.5f}", flush=True)

    return {"n": n, "descend": descend, "theta": theta, "seed": seed,
            "step": step, "worst": worst, "worst_ratio": worst_ratio,
            "n_open": n_open, "n_non_subadditive": n_nonsub}


def budget_floor_search(n_restart: int = 200, kmax: int = 26, seed: int = 11,
                        y_lo: float = 0.05, y_hi: float = 0.4999,
                        iters: int = 200) -> dict:
    """Can the budget be driven below zero?  Local descent on
    ``budget / sum_slack`` from random starts.

    The Fourier form makes the question sharp: ``budget = (4/A^2) int c2
    (|S|^2 - k)``, and only the ``-k`` is negative.  No run here has
    reached a negative budget; the measured floor is reported.
    """
    pc = PaperChain()
    rng = np.random.default_rng(seed)
    best = {"ratio": math.inf, "k": None, "ts": None, "ys": None}
    for trial in range(n_restart):
        k = int(rng.integers(2, kmax))
        mode = trial % 3
        if mode == 0:
            ts = np.arange(k) * float(rng.uniform(4.0, 30.0))
        elif mode == 1:
            ts = np.sort(rng.uniform(0.0, k * float(rng.uniform(3.0, 25.0)), k))
        else:
            ts = np.arange(k) * float(rng.uniform(5.5, 8.0)) \
                + rng.normal(0.0, 0.4, k)
        ys = (np.full(k, y_lo) if y_lo == y_hi
              else rng.uniform(y_lo, y_hi, k))
        obj = budget_fast(ts, ys) / sum(pc.slack(float(v)) for v in ys)
        for it in range(iters):
            st = 0.4 * math.exp(-it / 55)
            tn = ts + rng.normal(0.0, st, k)
            yn = (ys if y_lo == y_hi
                  else np.clip(ys + rng.normal(0.0, st * 0.05, k), y_lo, y_hi))
            o = budget_fast(tn, yn) / sum(pc.slack(float(v)) for v in yn)
            if o < obj:
                ts, ys, obj = tn, yn, o
        if obj < best["ratio"]:
            best = {"ratio": obj, "k": k, "ts": ts.copy(), "ys": ys.copy()}
    return best


# ---------------------------------------------------------------------------
# 7. the named witnesses
# ---------------------------------------------------------------------------

#: The worst configuration the rung-3 campaign reached, as data.  Recorded
#: so a reader can re-check the reported number without rerunning the
#: search, and so that the number cannot drift silently.  Produced by
#: ``random_search(n=260, seed=2026, kmax=12, kmin=2, descend=60)`` on the
#: conservative instance (320 configurations in all), then re-checked at
#: the module's own resolution.  **This is a search result: it bounds the
#: adversary from below and the quantifier not at all.**
#:
#: It is a two-pair configuration at 12.896 grid units = 2.05 mean gaps —
#: the sparse-lattice family that binds paper_joint.py's own sweep, found
#: independently by a search that was not told about it.
WORST_RANDOM = [(-0.391266, 0.49), (12.504789, 0.49)]

#: The configuration with the worst rung-1 domination ratio the campaign
#: found: nine pairs inside 0.554 grid units at mixed depths — a
#: near-coincident cluster, i.e. exactly the shape the family sweep has
#: no member of.
WORST_RANDOM_RATIO_PAIRS = [
    (61.291029, 0.448), (61.340090, 0.405), (61.345794, 0.063),
    (61.386117, 0.063), (61.529631, 0.319), (61.548584, 0.106),
    (61.600596, 0.362), (61.635442, 0.405), (61.844517, 0.277),
]

WORST_RANDOM_RECORD = {
    "n_random": 260,
    "n_descent": 60,
    "seed": 2026,
    "kmax": 12,
    "theta": THETA_FULL,
    "search_step": SEARCH_STEP,
    "n_open": 0,                       # no configuration violated the verdict
    "n_non_subadditive": 37,           # rung-1 domination failures found
    # the worst margin, on the conservative search instance
    "rel_margin_search": 0.2422938,
    "budget": 0.2907173,
    "cap_search": 0.2202783,
    # and re-checked at step = 0.001
    "cap_full": 0.2108030,
    "margin_full": 0.0799142,
    "rel_margin_full": 0.2748864,
    # the worst rung-1 ratio, both resolutions
    "worst_ratio_search": 1.4128081,
    "worst_ratio_full": 1.3459918,
}


def per_pair_route_witness(theta: float = THETA_FULL, y: float = 0.49,
                           kmax: int = 8) -> dict:
    """The nu = 1 lattice: the smallest k at which
    ``sum_i cap_single > budget`` while the joint verdict closes.

    This is what rules the per-pair route out: it is not that the
    subadditivity inequality is hard to prove, it is that its conclusion
    is false at theta* = 0.995.
    """
    ju = JointUniversal()
    rows = []
    first = None
    for k in range(2, kmax + 1):
        pairs = [(i * MEAN_GAP, y) for i in range(k)]
        rec = ju.per_pair_route(pairs, theta)
        rec["k"] = k
        rows.append(rec)
        if first is None and not rec["closes"]:
            first = k
    return {"rows": rows, "first_failing_k": first, "y": y, "theta": theta}


def coincident_ratios(theta: float = THETA_FULL, y: float = 0.49,
                      ks=(2, 3, 4, 6)) -> dict:
    """Rung 1 against coincident stacks — the family the sweep omits."""
    ju = JointUniversal()
    return {k: ju.domination([(0.0, y)] * k, theta)["ratio"] for k in ks}


# ---------------------------------------------------------------------------
# 8. cross-checks against the module under test
# ---------------------------------------------------------------------------


def completion_matches_module(theta: float = THETA_FULL,
                              pairs=((0.0, 0.49),)) -> float:
    """:func:`completion` reproduces ``PaperJoint.cap``'s per-cell sum."""
    pj = PaperJoint()
    pairs = [tuple(p) for p in pairs]
    c = 1 - theta
    best = math.inf
    for delta in pj.delta_choices:
        cells = pj.band_cells(pairs, delta)
        if not cells:
            return 0.0
        total, ok = 0.0, True
        for F, w in cells:
            K = pj.K_of(w)
            if K <= 0:
                ok = False
                break
            total += completion(F, K, c)
        if ok:
            best = min(best, total)
    got = pj.cap(pairs, theta)["cap"]
    want = best + pj.tail(pairs) + pj.off_band_allowance(pairs)
    return abs(got - want)


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------


NU1_3 = [(i * MEAN_GAP, 0.49) for i in range(3)]


def audit():
    ju = JointUniversal()
    pc = PaperChain()
    print("= the window autocorrelation c2 = phi^2 * phi^2 (closed form) =")
    print(f"  int c2 = {autocorr_mass():.12f}  vs A^2 = {A*A:.12f}  "
          f"defect {abs(autocorr_mass() - A*A):.2e}")
    print(f"  closed form vs numerical convolution: worst rel defect "
          f"{autocorr_defect():.2e}")
    ws = np.linspace(-0.999, 0.999, 20001)
    print(f"  min c2 on (-1, 1): {float(autocorr(ws).min()):.6f}  "
          "(positive in closed form, see the docstring)")

    print("= LAW L collapses onto one nonnegative kernel =")
    print(f"  W(g,y) = (2/A^2) int c2 cosh(yw) cos(gw) dw: worst defect "
          f"{W_autocorr_defect():.2e}")
    print("= THE SLACK-ADDITIVITY RELATION (budget is NOT additive) =")
    named = [
        ("isolated pair y=0.49", [(0.0, 0.49)]),
        ("two coincident y=0.49", [(0.0, 0.49)] * 2),
        ("worst dipole y=0.49", [(0.0, 0.49), (6.406, 0.49)]),
        ("nu=1 lattice k=8 y=0.49", [(i * MEAN_GAP, 0.49) for i in range(8)]),
        ("mixed depths k=3", [(0.0, 0.3), (2.1, 0.1), (9.9, 0.45)]),
    ]
    for name, pairs in named:
        bt = budget_terms(pairs)
        four = budget_via_autocorr(pairs)
        print(f"  {name:26s} sum_slack {bt['sum_slack']:9.5f} + pair_term "
              f"{bt['pair_term']:+10.5f} = budget {bt['budget']:10.5f}   "
              f"(autocorr form defect {abs(four - bt['budget']):.1e}; "
              f"pair energy {bt['pair_energy']:.4f} >= 0)")
    print("  => budget = sum_i slack(y_i) + sum_{i != j} T_ij, and the pair "
          "term is signed:")
    print("     coincidence pays (+8.31 for two pairs at y=0.49), separation "
          "costs (-0.08 at the worst dipole).")

    print("= RUNG 1: cap subadditivity against coincident stacks =")
    for th in (THETA_FULL, 0.99, 0.98, 0.95, 0.9):
        rs = coincident_ratios(th)
        thr = {k: ju.multiplicity_threshold_k(0.49, k) for k in rs}
        print(f"  theta={th:6.3f}  " + "  ".join(
            f"k={k}: ratio {v:6.4f} (single-occupancy below "
            f"{thr[k]:.4f})" for k, v in rs.items()))
    print("  => the failure is the square completion alone: ratio is exactly "
          "1.0000 wherever theta sits below the k-fold threshold.")

    print("= the exact excess identity (relaxed completion) =")
    K = ju.pj.K_of(1.0)
    for c, Fs in ((0.005, (0.02, 0.02)), (0.005, (0.02, 0.02, 0.02)),
                  (0.05, (0.02, 0.02))):
        rec = completion_excess(Fs, K, c)
        print(f"  c={c}, F={Fs}: excess {rec['lhs']:+.8f} vs closed form "
              f"{rec['rhs']:+.8f}  defect {rec['defect']:.2e}  "
              f"{'superadditive' if rec['positive'] else 'subadditive'}")

    print("= THE PER-PAIR ROUTE IS REFUTED BY A WITNESS (nu = 1, y = 0.49) =")
    w = per_pair_route_witness()
    for r in w["rows"]:
        print(f"  k={r['k']}: budget {r['budget']:8.5f}  sum cap_single "
              f"{r['cap_single_sum']:8.5f} (margin {r['per_pair_margin']:+8.5f}"
              f" {'OPEN' if not r['closes'] else 'closes'})   cap_joint "
              f"{r['cap_joint']:8.5f} (margin {r['joint_margin']:+8.5f} "
              f"{'closes' if r['joint_closes'] else 'OPEN'})")
    print(f"  first k at which the per-pair route fails: {w['first_failing_k']}")

    print("= RUNG 2 characterisation: which half of the cap moves? =")
    for name, pairs in (("coincident k=3 y=0.49", [(0.0, 0.49)] * 3),
                        ("nu=1 lattice k=3", NU1_3),
                        ("worst dipole y=0.49", [(0.0, 0.49), (6.406, 0.49)])):
        bsc = ju.band_structure_comparison(pairs)
        occ = ju.occupancy_profile(pairs, THETA_FULL)
        ppd = ju.positive_part_domination(pairs)
        print(f"  {name:22s} bands: joint {bsc['joint_measure']:7.3f}, union "
              f"{bsc['union_measure']:7.3f}, per-pair sum "
              f"{bsc['per_pair_measure']:7.3f} (overlap "
              f"{bsc['overlap_fraction']:.3f}, shielded "
              f"{bsc['shielded_fraction']:.3f}, outside "
              f"{bsc['outside_fraction']:.4f})")
        print(f"  {'':22s} m*: joint {occ['joint_max_m']} "
              f"({occ['joint_cells_above_1']} cells > 1) vs per-pair "
              f"{occ['single_max_m']} ({occ['single_cells_above_1']} cells "
              f"> 1);  positive part: joint/per-pair mass "
              f"{ppd['ratio']:.4f}, worst violation "
              f"{ppd['worst_violation']:+.2e}")
    print("  => the band set only shrinks; what grows is the occupancy m*.")

    print("= RUNG 2 repair A: the even-split bound (valid, not enough) =")
    for name, pairs in (("two coincident y=0.49", [(0.0, 0.49)] * 2),
                        ("nu=1 lattice k=3", [(i * MEAN_GAP, 0.49)
                                              for i in range(3)])):
        rec = ju.even_split_bound(pairs, THETA_FULL)
        print(f"  {name:24s} theta_k {rec['theta_k']:.5f}  bound "
              f"{rec['bound']:9.5f}  cap_joint {rec['cap_joint']:9.5f}  "
              f"budget {rec['budget']:9.5f}  dominates "
              f"{rec['dominates']}  funds universality "
              f"{rec['funds_universality']}")
    print(f"  per-cell lemma slack at (F1,F2)=(0.02,0.02), K={K:.4f}, "
          f"c=0.005: {even_split_defect(0.02, 0.02, K, 0.005):+.6f} (>= 0)")

    print("= RUNG 2 repair B: refinement is one-sided the WRONG way =")
    for name, pairs in (("single y=0.49", [(0.0, 0.49)]),
                        ("nu=1 lattice k=4", [(i * MEAN_GAP, 0.49)
                                              for i in range(4)])):
        rows = ju.refinement_ladder(pairs, THETA_FULL)
        print(f"  {name:20s} " + "  ".join(
            f"d={r['delta']}: {r['cells']} cells, {r['sum']:.5f}"
            for r in rows))
    print("  => band maxima do not grow under refinement, but the cap does; "
          "a common refinement cannot repair a domination failure.")

    print("= the budget floor (can the budget go negative?) =")
    for lab, lo, hi in (("y = 0.49", 0.49, 0.49), ("y = 0.30", 0.30, 0.30),
                        ("y free", 0.05, 0.4999)):
        best = budget_floor_search(n_restart=60, y_lo=lo, y_hi=hi, iters=120)
        gaps = np.diff(np.sort(best["ts"]))
        print(f"  {lab}: min budget / sum_slack = {best['ratio']:+.6f} at "
              f"k={best['k']}, mean gap {float(gaps.mean()):.3f} "
              f"({float(gaps.mean())/MEAN_GAP:.3f} mean gaps)")
    print("  (measured floor only; the closed form makes the question sharp "
          "but does not settle it)")

    print("= control: theta = 1 must diverge =")
    for pairs in ([(0.0, 0.49)], [(0.0, 0.49)] * 3):
        print(f"  k={len(pairs)}: cap(theta=1) = "
              f"{ju.pj.cap(pairs, 1.0)['cap']}")

    print("= control: the planted inflation must open a closing verdict =")
    for r in planted_violation():
        print(f"  inflate x{r['inflate']:<4}: cap {r['cap']:9.5f}  budget "
              f"{r['budget']:9.5f}  margin {r['margin']:+9.5f}  "
              f"{'closes' if r['closes'] else 'OPEN (flagged)'}")

    print("= control: this module's completion reproduces PaperJoint.cap =")
    print(f"  defect {completion_matches_module():.2e}")

    print("= RUNG 3: randomised adversarial search (EVIDENCE, not a proof) =")
    print("  (a short re-run; the recorded campaign is WORST_RANDOM_RECORD)")
    for key, val in WORST_RANDOM_RECORD.items():
        if key != "pairs":
            print(f"    {key}: {val}")
    res = random_search(n=40, descend=10, report_every=20)
    w = res["worst"]
    print(f"  {res['n']} configurations at theta={res['theta']} "
          f"(step={res['step']}, conservative): {res['n_open']} open, "
          f"{res['n_non_subadditive']} non-subadditive")
    print(f"  worst relative margin {w['rel_margin']:+.5f} at k="
          f"{len(w['pairs'])} (budget {w['budget']:.5f}, cap {w['cap']:.5f})")
    print(f"  worst rung-1 domination ratio {res['worst_ratio']['ratio']:.4f}")
    print("  A search is a lower bound on the adversary and no bound at all "
          "on the quantifier.")


if __name__ == "__main__":
    audit()
