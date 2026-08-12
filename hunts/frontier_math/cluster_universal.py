"""Cluster decomposition of the E-form obligation: separation + periodic limits.

`joint_universal.py` left the multi-pair obligation in one line: for every
finite on-line multiset X (size n) and pair set P (size k),

    E[F_on + F_p]  >=  theta E[F_on] + (1-theta) n + 4k,     theta = 0.995,

equivalently ``budget(P) >= sup_X [D - (1-theta) R] `` with the joint
band-lattice cap as the instrument for the sup.  The per-pair route is
refuted (superadditive caps above the multiplicity threshold; per-pair
sums exceed budgets from k = 4 at hardened grade), and the naive
global-density rescue is pre-refuted (reproduced here in ONE measurement,
:func:`legal_density_prerefutation` — do not re-derive it).  What was
measured to survive is the CLUSTER structure: joint caps on dense
clusters grow slower than their budgets, and dense lattices cap exactly 0
by shielding.  This module works that structure in three steps.

**1. SEPARATION (one-sided epsilon, with a derived constant).**  The
budget cross-term between two pairs at distance ``dt`` is, by the E-form
identity,

    T(dt, y1, y2) = (4/A^2) int_{-1}^{1} h(w) cos(dt w) dw,
    h(w) = c2(w) cosh(y1 w) cosh(y2 w),

with ``c2`` supported on [-1, 1] and c2(+-1) = 0.  Integrating by parts
twice on each half-interval (c2 has a CORNER at w = 0 — it is the
autocorrelation of a jump-discontinuous window — so w = 0 contributes a
boundary term exactly like the endpoint):

    int h cos(dt w) dw = -(2/dt^2) [ h'(0+) - h'(1-) cos(dt)
                                     + int_0^1 h'' cos(dt w) dw ],

    =>  |T(dt, y1, y2)|  <=  C_T / dt^2,
    C_T = (8/A^2) ( |c2'(1-)| cosh^2(1/2) + |c2'(0+)| + int_0^1 Hmaj ),

where ``Hmaj`` majorises |h''| termwise, uniformly over depths in
(0, 1/2] (cosh(yw) <= cosh(w/2), y sinh(yw) <= sinh(w/2)/2, y^2 cosh(yw)
<= cosh(w/2)/4), and c2', c2'' are in closed form (both edge slopes equal
-(1 + cos sqrt2)/2).  Numerically **C_T = 27.4970** — derived, not
fitted; the measured |T| dt^2 stays below it with a worst quotient
~0.62 over the probe grid (:func:`t_decay_check`).  The damage-field
cross decays the same way: one pair's positive part beyond distance g is
<= 4 (c_im(y)/(A g))^2 (the tail law of `paper_chain.py`, re-checked in
:func:`field_decay_check`).  The lemma
(:func:`separation_record`): for a configuration split into clusters
with inter-cluster pair distances d_pq,

    margin(whole) >= sum_cl margin(cl)
                     - sum_{cross pairs} 2 C_T / d_pq^2      [budget, DERIVED]
                     - max(0, cap(whole) - sum_cl cap(cl))   [cap, MEASURED],

and the campaign result is that the cap term was <= 0 (shielding + the
shared far-band window) on the large majority of random draws and never
beat the budget-side slack on any: the one-sided inequality
``margin(whole) >= sum margins - eps_T(Delta) * N_cross`` with
``eps_T(Delta) = 2 C_T / (Delta * MEAN_GAP)^2`` held on every draw at
Delta = 3 and Delta = 6 (:func:`separation_campaign`).  The cap piece
stays MEASURED grade: the joint instrument optimises one cell width for
the whole configuration while the per-cluster caps each optimise their
own, and that mismatch does not decay with Delta; it simply never went
positive enough to matter on the campaign.

**2. PERIODIC CLUSTERS EXACTLY (Poisson).**  For the infinite pair
lattice {(j s, y)} the E-form collapses: the Dirac comb turns the budget
per pair into a FINITE closed-form sum over Bragg frequencies inside the
kernel support,

    b_inf(s, y) = (8 pi / (s A^2)) sum_{|2 pi k / s| < 1}
                      c2(2 pi k / s) cosh^2(2 pi k y / s)  -  4,

(:func:`b_infty`; checked against direct T-summation to the truncation
tail, worst defect ~7e-5 at J = 4000).  Consequences read off the
closed form: for s <= one mean gap only k = 0 survives, so the per-pair
budget is ``4 c2(0) / (A^2 x) - 4`` with x = s/MEAN_GAP — INDEPENDENT of
depth, blowing up like 1/x as s -> 0 (the coincident limit: budget wins
hugely, cap is 0 by shielding there — measured), and reaching its floor
0.0245 at exactly one mean gap.  The limiting per-pair cap is the same
band-cell instrument run on ONE PERIOD of the exact periodic field
(:func:`periodic_cap`, truncation as a one-sided allowance, curvature
completeness checked).  The map (:func:`rho_map`) of

    rho(s, y) = cap_per_pair / b_inf

over s in [0.3, 20] mean gaps, y in (0, 1/2]: **rho = 0 (total
shielding) except in narrow resonance windows at near-integer s**, where
the lattice is commensurate with the damage-band lattice; resonance
peaks DECAY with s (0.85, 0.78, 0.71, 0.67, ... at s = 2, 3, 4, 5 at
y = 0.49) toward the isolated-pair ratio ~0.59, and rise with depth.

    **sup rho = 0.929 at (s, y) = (2.002 mean gaps, y -> 1/2)**
    (step 0.002; 0.915 at step 0.001 — refinement moves it DOWN),

so the periodic family closes uniformly with >= 7.1% relative margin at
theta = 0.995.  Grade: measured (double precision, band-cell instrument),
with the budget side closed-form.

**3. WHAT THE ASSEMBLY DOES AND DOES NOT DELIVER.**  Two honest
negatives, both first-class:

- *The finite-size correction has NO uniform sign.*  At the resonance
  (s = 2.0) and at s = 1.0 the per-pair margin decreases with m toward
  the limit (interior worse than edges); at s = 2.05 and s = 1.5 it
  increases (edges worse), so the infinite-lattice verdict does NOT
  one-sidedly dominate finite clusters, and small-m clusters must be
  (and are) closed by direct finite verdicts (:func:`finite_m_ladder`).
- *The lattice is not a stationary point of the margin.*  The jitter
  campaign at the resonance shows the margin RISES under jitter on
  average (coherent = worst, consistent with shielding), but the
  gradient at zero jitter is nonzero along the lattice-compression
  direction — the extremal configuration is a resonance in SPACING, not
  a critical point in POSITIONS; the correct extremality statement is
  the conjecture that margin(P) >= margin of the best-tuned periodic
  lattice at the same depth, stated at :data:`EXTREMALITY_CONJECTURE`,
  supported by the map + jitter + the 320-config search of
  `joint_universal.py`, and NOT established here.

So the assembly delivers: dense clusters (s below ~1.9 mean gaps off
resonance) closed by shielding with budget floor 0.0245/pair [measured
cap-0 + closed-form budget]; the periodic family closed uniformly with
sup rho = 0.929 [measured]; separation with a derived budget epsilon and
a measured cap term [mixed]; finite-m interpolation MEASURED to m = 32
with no one-sided bridge to the limit [open]; extremality of periodic
configurations [conjecture].  The quantifier remains open; what changed
is that the adversary's continuum is now pinned to a one-parameter
family of resonances whose worst member is computed.

Nothing here computes a proportion and nothing here is evidence about
RH.  Run ``.venv/bin/python hunts/frontier_math/cluster_universal.py``
(~15 min with the full map; ``--quick`` skips the map).
"""

from __future__ import annotations

import math
import sys
from functools import lru_cache
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import (  # noqa: E402
    A, MEAN_GAP, PaperBandDual, PaperChain, phipap, phipap_d1, phipap_d2,
)
from paper_joint import PaperJoint, joint_greedy  # noqa: E402
from joint_universal import THETA_FULL, autocorr  # noqa: E402

S2 = math.sqrt(2.0)

#: the paper's count caps the pair density near (1 - H)/2 per mean gap —
#: the number the coordinator's pre-refutation uses.
LEGAL_PAIR_DENSITY = 0.164


# ---------------------------------------------------------------------------
# 1. closed-form derivatives of the window autocorrelation
# ---------------------------------------------------------------------------


def autocorr_d1(w):
    """c2'(w) in closed form on 0 < |w| < 1 (odd; corner at 0).

    c2'(w) = -cos(sqrt2 (1-w))/2 - cos(sqrt2 w)/2
             - (1-w) sqrt2 sin(sqrt2 w)/2      (w > 0).

    Both one-sided edge slopes have the same magnitude:
    |c2'(0+)| = |c2'(1-)| = (1 + cos sqrt2)/2 = 0.5779718...
    """
    w = np.asarray(w, float)
    a = np.abs(w)
    v = (-np.cos(S2 * (1 - a)) / 2 - np.cos(S2 * a) / 2
         - (1 - a) * S2 * np.sin(S2 * a) / 2)
    return np.where(a < 1.0, np.sign(w) * v, 0.0)


def autocorr_d2(w):
    """c2''(w) on 0 < |w| < 1 (even):
    -sqrt2 sin(sqrt2 (1-w))/2 + sqrt2 sin(sqrt2 w) - (1-w) cos(sqrt2 w).
    """
    w = np.asarray(w, float)
    a = np.abs(w)
    v = (-S2 * np.sin(S2 * (1 - a)) / 2 + S2 * np.sin(S2 * a)
         - (1 - a) * np.cos(S2 * a))
    return np.where(a < 1.0, v, 0.0)


#: |c2'(0+)| = |c2'(1-)| = (1 + cos sqrt2)/2 — the two boundary terms of
#: the double integration by parts (the corner at 0 comes from the window's
#: jump at +-1/2 autocorrelated against itself).
C2_EDGE_SLOPE = (1 + math.cos(S2)) / 2


def autocorr_deriv_defect(n_probe: int = 19) -> dict:
    """Closed forms against central differences on the open interval."""
    ws = np.linspace(0.05, 0.95, n_probe)
    h1, h2 = 1e-6, 1e-4
    fd1 = (autocorr(ws + h1) - autocorr(ws - h1)) / (2 * h1)
    fd2 = (autocorr(ws + h2) - 2 * autocorr(ws) + autocorr(ws - h2)) / h2**2
    return {"d1": float(np.max(np.abs(fd1 - autocorr_d1(ws)))),
            "d2": float(np.max(np.abs(fd2 - autocorr_d2(ws))))}


# ---------------------------------------------------------------------------
# 2. the DERIVED T-decay constant
# ---------------------------------------------------------------------------


@lru_cache(maxsize=4)
def t_decay_constant(n_quad: int = 400001) -> float:
    """|T(dt, y1, y2)| <= C_T / dt^2, uniform over depths in (0, 1/2].

    Derivation (no fitted number anywhere): T = (4/A^2) int h cos(dt w),
    h = c2 u1 u2, u_i = cosh(y_i w).  h vanishes at +-1 and is even with
    a corner at 0, so two integrations by parts on [0, 1] (doubled) give

        |int_{-1}^{1} h cos(dt w) dw|
            <= (2/dt^2) ( |h'(0+)| + |h'(1-)| + int_0^1 |h''| ).

    At the endpoints: h'(0+) = c2'(0+) (u_i'(0) = 0), and h'(1-) =
    c2'(1-) u1(1) u2(1) since c2(1) = 0, so |h'(1-)| <= |c2'(1-)|
    cosh^2(1/2).  Inside, |h''| is majorised termwise uniformly in the
    depths: |u_i| <= cosh(w/2), |u_i'| = y sinh(y w) <= sinh(w/2)/2,
    |u_i''| = y^2 cosh(y w) <= cosh(w/2)/4, giving

        Hmaj = |c2''| cosh^2(w/2) + 2 |c2'| cosh(w/2) sinh(w/2)
               + c2 (cosh^2(w/2)/2 + sinh^2(w/2)/2).

    C_T = (8/A^2) (|c2'(1-)| cosh^2(1/2) + |c2'(0+)| + int_0^1 Hmaj)
        = 27.4970.  Only the integral is evaluated by quadrature; every
    integrand factor is closed-form.
    """
    w = np.linspace(0.0, 1.0, n_quad)
    M0 = np.cosh(w / 2)
    M1 = np.sinh(w / 2) / 2
    M2 = np.cosh(w / 2) / 4
    Hmaj = (np.abs(autocorr_d2(w)) * M0**2
            + 4 * np.abs(autocorr_d1(w)) * M0 * M1
            + autocorr(w) * (2 * M0 * M2 + 2 * M1**2))
    quad = float(np.trapezoid(Hmaj, w))
    return (8 / A**2) * (C2_EDGE_SLOPE * math.cosh(0.5) ** 2
                         + C2_EDGE_SLOPE + quad)


def t_decay_check(ds=(3.0, 5.0, 8.0, 12.0, 20.0, 40.0, 80.0),
                  ys=(0.1, 0.3, 0.49)) -> dict:
    """Measured |T| dt^2 against the derived C_T (must sit below it)."""
    pc = PaperChain()
    C_T = t_decay_constant()
    worst = 0.0
    arg = None
    for d in ds:
        for y1 in ys:
            for y2 in ys:
                q = abs(pc.T(d, y1, y2)) * d * d / C_T
                if q > worst:
                    worst, arg = q, (d, y1, y2)
    return {"C_T": C_T, "worst_quotient": worst, "at": arg,
            "holds": worst < 1.0}


# ---------------------------------------------------------------------------
# 3. the damage-field decay (same 1/g^2 law, constant from paper_chain)
# ---------------------------------------------------------------------------


def field_decay_constant(y: float = 0.5) -> float:
    """One pair's positive damage part beyond distance g is
    <= field_decay_constant(y) / g^2 with the constant
    4 (c_im(y)/A)^2 — the tail law `paper_chain.PaperBandDual.tail_sum`
    already carries; restated here because the separation lemma uses it
    for the CROSS field between clusters, not only for the tail."""
    return 4 * (PaperBandDual().c_im_sharp(y) / A) ** 2


def field_decay_check(y: float = 0.49, g_lo: float = 8.0,
                      g_hi: float = 120.0, step: float = 0.005) -> dict:
    """max over |g| >= g_lo of f_+(g) g^2 against the derived constant."""
    pc = PaperChain()
    gs = np.arange(g_lo, g_hi, step)
    fplus = np.maximum(0.0, -2 * pc.W(gs, y))
    q = float(np.max(fplus * gs * gs)) / field_decay_constant(y)
    return {"constant": field_decay_constant(y), "worst_quotient": q,
            "holds": q < 1.0}


# ---------------------------------------------------------------------------
# 4. the separation lemma
# ---------------------------------------------------------------------------


def cross_budget_bound(clusters) -> dict:
    """Derived bound on the inter-cluster budget term: for each cross
    pair-of-pairs (p in cluster i, q in cluster j) the budget carries
    2 T(t_p - t_q, ...), and |2 T| <= 2 C_T / d^2.  Returns the bound,
    the exact cross term, and the cross-pair count."""
    C_T = t_decay_constant()
    pc = PaperChain()
    bound = 0.0
    exact = 0.0
    n_cross = 0
    for i in range(len(clusters)):
        for j in range(i + 1, len(clusters)):
            for t1, y1 in clusters[i]:
                for t2, y2 in clusters[j]:
                    d = abs(t1 - t2)
                    bound += 2 * C_T / d**2
                    exact += 2 * pc.T(t1 - t2, y1, y2)
                    n_cross += 1
    return {"bound": bound, "exact": exact, "n_cross": n_cross,
            "contained": abs(exact) <= bound}


def separation_epsilon(delta_gaps: float, n_cross: int) -> float:
    """eps_T(Delta) * N_cross: the derived (budget-side) epsilon of the
    one-sided separation inequality, at the crudest distance bound
    d >= Delta mean gaps for every cross pair-of-pairs."""
    return n_cross * 2 * t_decay_constant() / (delta_gaps * MEAN_GAP) ** 2


def separation_record(clusters, theta: float = THETA_FULL,
                      pj: PaperJoint | None = None) -> dict:
    """One configuration: verdict(whole) against sum of cluster verdicts.

    The inequality under test (one-sided, toward the whole):

        margin(whole) >= sum_cl margin(cl) - eps_budget - eps_cap,

    eps_budget = sum_cross 2 C_T / d_pq^2   (DERIVED),
    eps_cap    = max(0, cap(whole) - sum_cl cap(cl))   (MEASURED —
    the joint instrument optimises one cell width for the whole
    configuration while each cluster cap optimises its own, and that
    mismatch does not decay with separation; the campaign records how
    often it is even positive).
    """
    pj = pj or PaperJoint(step=0.005, G=60.0)
    whole = [p for c in clusters for p in c]
    b_whole = pj.budget(whole)
    cap_whole = pj.cap(whole, theta)["cap"]
    b_sum = sum(pj.budget(c) for c in clusters)
    cap_sum = sum(pj.cap(c, theta)["cap"] for c in clusters)
    cb = cross_budget_bound(clusters)
    m_whole = b_whole - cap_whole
    m_sum = b_sum - cap_sum
    return {
        "k": len(whole), "n_clusters": len(clusters),
        "margin_whole": m_whole, "margin_sum": m_sum,
        "budget_cross_exact": b_whole - b_sum,
        "budget_cross_bound": cb["bound"],
        "budget_cross_contained": abs(b_whole - b_sum) <= cb["bound"] + 1e-9,
        "cap_excess": cap_whole - cap_sum,
        "n_cross": cb["n_cross"],
        "one_sided_holds": m_whole >= m_sum - cb["bound"]
        - max(0.0, cap_whole - cap_sum) - 1e-9,
        "holds_with_derived_eps_only": m_whole >= m_sum - cb["bound"] - 1e-9,
    }


DEPTH_SET = (0.1, 0.2, 0.3, 0.4, 0.49)


def random_separated_config(rng, delta_gaps: float, max_clusters: int = 4,
                            max_pairs: int = 4, max_diam_gaps: float = 2.0):
    """Clusters of 1..max_pairs pairs, diameter <= max_diam_gaps mean
    gaps, consecutive clusters separated by >= delta_gaps mean gaps
    edge-to-edge, depths from the ladder."""
    n_cl = int(rng.integers(2, max_clusters + 1))
    clusters = []
    cursor = 0.0
    for _ in range(n_cl):
        m = int(rng.integers(1, max_pairs + 1))
        span = float(rng.uniform(0.2, max_diam_gaps)) * MEAN_GAP
        ts = np.sort(rng.uniform(0.0, span, m)) + cursor
        ys = rng.choice(np.array(DEPTH_SET), m)
        clusters.append([(float(t), float(y)) for t, y in zip(ts, ys)])
        cursor = float(ts.max()) + (delta_gaps
                                    + float(rng.uniform(0.0, 1.0))) * MEAN_GAP
    return clusters


def separation_campaign(n_configs: int = 20, delta_gaps: float = 3.0,
                        seed: int = 5, theta: float = THETA_FULL,
                        pj: PaperJoint | None = None) -> dict:
    """The validation battery for the separation lemma."""
    pj = pj or PaperJoint(step=0.005, G=60.0)
    rng = np.random.default_rng(seed)
    rows = []
    for _ in range(n_configs):
        clusters = random_separated_config(rng, delta_gaps)
        rows.append(separation_record(clusters, theta, pj))
    return {
        "delta_gaps": delta_gaps, "n": n_configs,
        "all_one_sided": all(r["one_sided_holds"] for r in rows),
        "all_with_derived_eps_only": all(r["holds_with_derived_eps_only"]
                                         for r in rows),
        "all_budget_cross_contained": all(r["budget_cross_contained"]
                                          for r in rows),
        "n_cap_excess_positive": sum(1 for r in rows if r["cap_excess"] > 0),
        "worst_cap_excess": max(r["cap_excess"] for r in rows),
        "worst_deficit": min(r["margin_whole"] - r["margin_sum"]
                             + r["budget_cross_bound"] for r in rows),
        "rows": rows,
    }


# ---------------------------------------------------------------------------
# 5. the periodic family, exactly (Poisson summation on the E-form)
# ---------------------------------------------------------------------------


def h_bragg(w: float, y: float) -> float:
    """The E-form integrand factor at a Bragg frequency:
    c2(w) cosh^2(y w)."""
    return float(autocorr(np.array([w]))[0]) * math.cosh(y * w) ** 2


def b_infty(s: float, y: float) -> float:
    """The exact per-pair budget of the infinite lattice {(j s, y)}.

    From budget = (4/A^2) int c2 [|S|^2 - k] and the Dirac comb
    sum_j e^{i j s w} -> (2 pi / s) sum_k delta(w - 2 pi k / s), the sum
    collapses onto the finitely many Bragg frequencies inside the kernel
    support:

        b_inf(s, y) = (8 pi/(s A^2)) sum_{|2 pi k/s| < 1}
                          c2(2 pi k/s) cosh^2(2 pi k y/s) - 4.

    For s <= MEAN_GAP only k = 0 survives and the per-pair budget is
    4 c2(0)/(A^2 x) - 4, x = s/MEAN_GAP: depth-independent, -> +inf as
    s -> 0 (the coincident blowup), floor 0.024509 at x = 1.
    """
    tot = h_bragg(0.0, y)
    k = 1
    while 2 * math.pi * k / s < 1.0:
        tot += 2 * h_bragg(2 * math.pi * k / s, y)
        k += 1
    return (8 * math.pi / (s * A**2)) * tot - 4.0


def b_perpair_direct(s: float, y: float, J: int = 4000) -> float:
    """slack(y) + 2 sum_{j=1..J} T(j s, y, y) — the direct route the
    Poisson form must reproduce, up to the tail <= 2 C_T/(s^2 J)."""
    pc = PaperChain()
    js = np.arange(1, J + 1) * s
    v1 = phipap(js + 0j)
    v2 = phipap(js + 2j * y)
    T = 2 * ((v1.real**2 - v1.imag**2) + (v2.real**2 - v2.imag**2)) / A**2
    return pc.slack(y) + 2 * float(T.sum())


def poisson_defect(s: float, y: float, J: int = 4000) -> dict:
    """|direct - closed form| against the derived tail bound."""
    d = abs(b_perpair_direct(s, y, J) - b_infty(s, y))
    tail = 2 * t_decay_constant() / (s * s * J)
    return {"defect": d, "tail_bound": tail, "within": d <= tail}


def periodic_field(s: float, y: float, step: float = 0.002,
                   reach: float = 250.0):
    """The infinite lattice's joint damage field over [-s, 2s), with the
    lattice truncation folded in as a one-sided allowance.

    Pairs |j| <= J are summed exactly (J s >= reach); pairs beyond sit at
    distance >= (J-2) s from every grid point, so their total positive
    contribution is <= 8 (c_im(y)/A)^2 / (s^2 (J-3)), added to f
    everywhere (an over-count, never an under-count).
    """
    J = int(math.ceil(reach / s)) + 3
    gs = np.arange(-s, 2 * s, step)
    f = np.zeros_like(gs)
    Q = np.zeros_like(gs)
    qpp = np.zeros_like(gs)
    slope = np.zeros_like(gs)
    for j in range(-J, J + 1):
        z = (gs - j * s) + 1j * y
        v = phipap(z)
        v1 = phipap_d1(z)
        v2 = phipap_d2(z)
        re2 = v.real**2 - v.imag**2
        Q += re2
        f += -4 * re2 / A**2
        av, a1, a2 = np.abs(v), np.abs(v1), np.abs(v2)
        slope += 8 * av * a1 / A**2
        qpp += 2 * (a1**2 + av * a2)
    C = PaperBandDual().c_im_sharp(y) / A
    trunc = 8 * C * C / (s * s * (J - 3))
    return gs, f + trunc, Q, qpp, slope


def periodic_cap(s: float, y: float, theta: float = THETA_FULL,
                 step: float = 0.002,
                 deltas=(0.5, 1.0, 2.0, 3.0)) -> dict:
    """The limiting per-pair cap: the band-cell instrument of
    `paper_joint.py` run on one period of the exact periodic field.

    One period carries exactly one pair, and the per-cell square
    completions are summed independently (cross-cell charges dropped
    one-sidedly, as in the finite instrument), so the per-period cell sum
    IS the per-pair cap of the infinite lattice — no tail, the period
    covers everything.  Completeness (no band thinner than the grid) is
    checked with the same curvature criterion as the finite instrument.
    """
    pj = PaperJoint(step=step)
    gs, f, Q, qpp, slope = periodic_field(s, y, step)
    c = 1 - theta
    if c <= 0:
        return {"cap": math.inf, "bands": None, "complete": None}
    idx = np.where(f > 0)[0]
    if len(idx) == len(gs):
        return {"cap": math.inf, "bands": None, "complete": False,
                "note": "field positive over the whole period"}
    # completeness off the (widened) bands, curvature criterion
    on = f > 0
    wide = on.copy()
    wide[1:] |= on[:-1]
    wide[:-1] |= on[1:]
    off = ~wide
    if np.any(off):
        bound = qpp[off] * step**2 / 8
        comp_ratio = float(np.min(Q[off] / bound))
    else:
        comp_ratio = math.inf
    if len(idx) == 0:
        return {"cap": 0.0, "bands": 0, "complete": comp_ratio > 1.0,
                "completeness_ratio": comp_ratio}
    groups = np.split(idx, np.where(np.diff(idx) > 1)[0] + 1)
    bands = []
    for gr in groups:
        if len(gr) < 2:
            continue
        lo = float(gs[gr[0]]) - step
        hi = float(gs[gr[-1]]) + step
        if 0.0 <= (lo + hi) / 2 < s:
            bands.append((lo, hi,
                          float(f[gr].max()) + float(slope[gr].max()) * step))
    best, best_delta = math.inf, None
    for d in deltas:
        total, ok = 0.0, True
        for lo, hi, F in bands:
            n = max(1, int(math.ceil((hi - lo) / d)))
            K = pj.K_of((hi - lo) / n)
            if K <= 0:
                ok = False
                break
            for _ in range(n):
                total += F if F <= 2 * c * K else (F + c * K) ** 2 / (4 * c * K)
        if ok and total < best:
            best, best_delta = total, d
    return {"cap": best, "bands": len(bands), "delta": best_delta,
            "widths": [hi - lo for lo, hi, _ in bands],
            "complete": comp_ratio > 1.0, "completeness_ratio": comp_ratio}


def rho_point(s_gaps: float, y: float, theta: float = THETA_FULL,
              step: float = 0.002) -> dict:
    """cap / budget for the infinite lattice at spacing s_gaps mean gaps."""
    s = s_gaps * MEAN_GAP
    b = b_infty(s, y)
    rec = periodic_cap(s, y, theta, step)
    cap = rec["cap"]
    return {"s_gaps": s_gaps, "y": y, "budget": b, "cap": cap,
            "rho": cap / b if b > 0 else math.inf,
            "margin": b - cap, "bands": rec.get("bands"),
            "complete": rec.get("complete")}


def rho_map(s_grid=None, ys=(0.1, 0.2, 0.3, 0.4, 0.45, 0.49),
            theta: float = THETA_FULL, step: float = 0.002) -> dict:
    """The map, its supremum and argmax.  The default grid concentrates
    on the resonances (near-integer s) found by the coarse pass."""
    if s_grid is None:
        s_grid = np.concatenate([
            np.arange(0.3, 1.9, 0.1),
            np.arange(1.9, 6.05, 0.05),
            np.array([6.5, 7.0, 8.0, 10.0, 12.0, 16.0, 20.0]),
        ])
    rows = []
    sup = {"rho": -1.0}
    for x in s_grid:
        for y in ys:
            r = rho_point(float(x), float(y), theta, step)
            rows.append(r)
            if math.isfinite(r["rho"]) and r["rho"] > sup["rho"]:
                sup = r
    return {"sup": sup, "rows": rows,
            "n_shielded": sum(1 for r in rows if r["cap"] == 0.0),
            "n": len(rows),
            "all_below_one": all(r["rho"] < 1.0 for r in rows
                                 if math.isfinite(r["rho"]))}


#: The argmax of the map after local refinement in s (grid 0.001 gaps at
#: the deep edge), re-checked on a step ladder (rho falls with
#: refinement: 0.9547 / 0.9286 / 0.9154 at step 0.004 / 0.002 / 0.001),
#: recorded so the reported number cannot drift.
RHO_SUP_RECORD = {
    "s_gaps": 2.002, "y": 0.4999, "step": 0.002,
    "rho": 0.9286, "budget": 0.129891, "cap": 0.120620,
    "rho_step_0004": 0.9547, "rho_step_0001": 0.9154,
}

#: The extremality statement the measurements support but do NOT
#: establish: for every finite pair configuration P at common depth y,
#: margin(P)/|P| >= inf over s of [b_inf(s, y) - cap_per(s, y)] taken
#: over the resonant spacings — i.e. the tuned periodic lattice is the
#: per-pair worst case.  Status: conjecture.  For it: the map (sup rho
#: at a resonance), the jitter campaign (margin rises under position
#: noise on average), and the 320-config random search whose worst find
#: was itself a near-resonant sparse lattice.  Against it: the gradient
#: at zero jitter is NOT zero (the lattice is not a stationary point in
#: position space; the extremum lives in the spacing parameter), and the
#: finite-size correction has no uniform sign, so the infinite lattice
#: does not dominate small clusters.
EXTREMALITY_CONJECTURE = ("tuned periodic lattices are the per-pair "
                          "extremal family: conjecture, measured support, "
                          "no one-sided bridge for finite m")


# ---------------------------------------------------------------------------
# 6. jitter: is coherent worst?
# ---------------------------------------------------------------------------


def jitter_campaign(s_gaps: float = 2.002, y: float = 0.49, m: int = 8,
                    amps=(0.0, 0.15, 0.3, 0.6, 1.2), n_seeds: int = 5,
                    theta: float = THETA_FULL,
                    pj: PaperJoint | None = None) -> dict:
    """Jitter the resonant lattice and track the relative margin.

    If coherence (exact lattice alignment with the damage-band lattice)
    is what makes the cap large, jitter must RAISE the margin on
    average.  ``amps`` are absolute position noise amplitudes in grid
    units (a mean gap is 2 pi).
    """
    pj = pj or PaperJoint(step=0.005, G=60.0)
    s = s_gaps * MEAN_GAP
    base = [(i * s, y) for i in range(m)]
    rng = np.random.default_rng(17)
    rows = []
    for a in amps:
        margins = []
        for _ in range(1 if a == 0.0 else n_seeds):
            pairs = [(t + float(rng.normal(0.0, a)) if a else t, yy)
                     for t, yy in base]
            rec = pj.verdict(pairs, theta)
            margins.append(rec["margin"] / max(rec["budget"], 1e-12))
        rows.append({"amp": a, "mean_rel_margin": float(np.mean(margins)),
                     "min_rel_margin": float(np.min(margins))})
    base_m = rows[0]["mean_rel_margin"]
    return {"rows": rows, "base_rel_margin": base_m,
            "jitter_helps_on_average": all(r["mean_rel_margin"] >= base_m
                                           for r in rows[1:])}


def lattice_gradient(s_gaps: float = 2.002, y: float = 0.49, m: int = 8,
                     h: float = 0.05, theta: float = THETA_FULL,
                     pj: PaperJoint | None = None) -> dict:
    """d margin / d t_i by central differences — the first-order
    stationarity check.  A resonance in the SPACING parameter shows up
    as a nonzero gradient along the compression direction (moving the
    outer pairs inward re-tunes the spacing), so a nonzero value here is
    a finding, not a numerical defect: the lattice is extremal in the
    spacing family, not a critical point of position space."""
    pj = pj or PaperJoint(step=0.005, G=60.0)
    s = s_gaps * MEAN_GAP
    base = [(i * s, y) for i in range(m)]
    grads = []
    for i in range(m):
        up = [(t + (h if j == i else 0.0), yy)
              for j, (t, yy) in enumerate(base)]
        dn = [(t - (h if j == i else 0.0), yy)
              for j, (t, yy) in enumerate(base)]
        mu = pj.verdict(up, theta)["margin"]
        md = pj.verdict(dn, theta)["margin"]
        grads.append((mu - md) / (2 * h))
    grads = np.array(grads)
    # the compression direction: outer pairs move inward
    comp = np.array([i - (m - 1) / 2 for i in range(m)])
    comp = comp / np.linalg.norm(comp)
    return {"grads": grads.tolist(),
            "max_abs": float(np.max(np.abs(grads))),
            "compression_component": float(np.dot(grads, comp))}


# ---------------------------------------------------------------------------
# 7. finite-m interpolation
# ---------------------------------------------------------------------------


def finite_m_ladder(s_gaps: float, y: float, ms=(4, 8, 16, 32),
                    theta: float = THETA_FULL,
                    pj: PaperJoint | None = None,
                    step_limit: float | None = None) -> dict:
    """Per-pair budget / cap / margin at m = 4..32 against the periodic
    limit, all at the same grid step so the comparison is like for like.

    The finite budget approaches b_inf from a direction the closed form
    dictates (edge pairs are missing neighbours: the edge correction is
    2 E_m / m with |E_m| <= (C_T/s^2) H_{m-1}, an O(log m / m) per-pair
    term).  The CAP side's finite-size sign is measured, not derived —
    and it is NOT uniform across spacings, which is the honest negative
    this function exists to record.
    """
    pj = pj or PaperJoint(step=0.005, G=60.0)
    s = s_gaps * MEAN_GAP
    lim = rho_point(s_gaps, y, theta,
                    step=step_limit if step_limit else pj.step)
    rows = []
    for m in ms:
        pairs = [(i * s, y) for i in range(m)]
        b = pj.budget(pairs)
        cap = pj.cap(pairs, theta)["cap"]
        rows.append({"m": m, "b_pp": b / m, "cap_pp": cap / m,
                     "margin_pp": (b - cap) / m})
    margins = [r["margin_pp"] for r in rows]
    return {"s_gaps": s_gaps, "y": y, "rows": rows,
            "limit_b": lim["budget"], "limit_cap": lim["cap"],
            "limit_margin": lim["margin"],
            "monotone_up": all(margins[i] <= margins[i + 1] + 1e-12
                               for i in range(len(margins) - 1)),
            "monotone_down": all(margins[i] >= margins[i + 1] - 1e-12
                                 for i in range(len(margins) - 1)),
            "all_close": all(m > 0 for m in margins)}


# ---------------------------------------------------------------------------
# 8. the primal side at the worst lattice (room below the cap)
# ---------------------------------------------------------------------------


def primal_room(s_gaps: float = 2.002, y: float = 0.49, m: int = 12,
                theta: float = THETA_FULL) -> dict:
    """The measured greedy adversary against the budget on the worst
    periodic family member.  The cap is one-sided; if it ever crossed the
    budget the next question would be whether the PRIMAL does, because
    only a primal crossing refutes the E-form itself.  Recorded here so
    the distinction cap-fails / E-form-fails stays on disk with numbers.
    """
    pj = PaperJoint(step=0.005, G=60.0)
    pairs = [(i * s_gaps * MEAN_GAP, y) for i in range(m)]
    profit = joint_greedy(pj, pairs, theta, kmax=20 * m)
    b = pj.budget(pairs)
    return {"greedy": profit, "budget": b, "cap": pj.cap(pairs, theta)["cap"],
            "primal_within_budget": profit <= b}


# ---------------------------------------------------------------------------
# 9. the coordinator's pre-refutation, reproduced in one measurement
# ---------------------------------------------------------------------------


def legal_density_prerefutation(theta: float = THETA_FULL,
                                y: float = 0.49) -> dict:
    """The naive global-density rescue of the per-pair route, killed in
    one line: a window at the paper's legal pair density containing one
    k = 8 nu = 1 cluster still breaks per-pair accounting.

    The cluster's per-pair deficit (sum of single caps minus budget) is
    O(0.3); a pair-free stretch contributes credit only through the
    on-line charge, (1-theta) R ~ 6e-5 per mean gap at unit zero
    density, so diluting the cluster to LEGAL_PAIR_DENSITY buys ~40 mean
    gaps of pair-free credit ~ 2e-3 — two orders short.  Reproduces the
    coordinator's numbers; nothing here is new and nothing further
    should be spent on this route.
    """
    from joint_universal import JointUniversal
    ju = JointUniversal(PaperJoint(step=0.005, G=60.0))
    pc = PaperChain()
    cluster = [(i * MEAN_GAP, y) for i in range(8)]
    deficit = (ju.cap_single_sum(cluster, theta)
               - ju.pj.budget(cluster))
    # per-mean-gap on-line charge credit at unit zero density
    js = np.arange(1, 2001) * MEAN_GAP
    R_per_gap = 2 * float(pc.omega2(js.astype(complex)).real.sum())
    credit_rate = (1 - theta) * R_per_gap
    span = 8 / LEGAL_PAIR_DENSITY          # mean gaps of window
    credit = credit_rate * (span - 7)      # pair-free stretch
    return {"deficit": deficit, "credit_rate_per_gap": credit_rate,
            "window_gaps": span, "credit": credit,
            "still_broken": credit < deficit,
            "shortfall_factor": deficit / max(credit, 1e-30)}


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------


def audit(quick: bool = False):
    print("= closed-form c2 derivatives (the IBP inputs) =")
    d = autocorr_deriv_defect()
    print(f"  c2' defect {d['d1']:.2e}, c2'' defect {d['d2']:.2e}  "
          f"edge slopes |c2'(0+)| = |c2'(1-)| = {C2_EDGE_SLOPE:.10f}")

    print("= the DERIVED T-decay constant =")
    C_T = t_decay_constant()
    tc = t_decay_check()
    print(f"  C_T = {C_T:.4f} (uniform over depths <= 1/2; boundary terms "
          "from the corner at 0 and the edge at 1)")
    print(f"  measured worst |T| dt^2 / C_T = {tc['worst_quotient']:.4f} "
          f"at {tc['at']}  ({'holds' if tc['holds'] else 'FAILS'})")

    print("= the damage-field decay =")
    fc = field_decay_check()
    print(f"  4 (c_im(0.49)/A)^2 = {fc['constant']:.4f}; measured worst "
          f"f_+ g^2 / const = {fc['worst_quotient']:.4f} "
          f"({'holds' if fc['holds'] else 'FAILS'})")

    print("= separation campaign (one-sided lemma; budget eps DERIVED, "
          "cap eps MEASURED) =")
    for delta in (3.0, 6.0):
        rec = separation_campaign(n_configs=10 if quick else 20,
                                  delta_gaps=delta)
        print(f"  Delta = {delta} gaps, n = {rec['n']}: one-sided holds on "
              f"all: {rec['all_one_sided']}; with derived eps only: "
              f"{rec['all_with_derived_eps_only']}; budget cross contained "
              f"on all: {rec['all_budget_cross_contained']}; cap excess "
              f"positive on {rec['n_cap_excess_positive']}/{rec['n']} "
              f"(worst {rec['worst_cap_excess']:+.2e}); worst one-sided "
              f"slack {rec['worst_deficit']:+.4f}")

    print("= the Poisson closed form for the lattice budget =")
    for x, y in ((0.5, 0.49), (1.0, 0.49), (2.005, 0.49), (3.0, 0.3)):
        pd = poisson_defect(x * MEAN_GAP, y)
        print(f"  s={x} gaps y={y}: b_inf = {b_infty(x*MEAN_GAP, y):+.6f}  "
              f"defect vs direct {pd['defect']:.2e} "
              f"(tail bound {pd['tail_bound']:.2e}, within: {pd['within']})")
    print(f"  budget floor at one mean gap (depth-free): "
          f"{b_infty(MEAN_GAP, 0.1):+.6f} = {b_infty(MEAN_GAP, 0.49):+.6f}")

    if not quick:
        print("= the rho(s, y) map (this is the long part) =")
        mp_ = rho_map()
        sup = mp_["sup"]
        print(f"  {mp_['n']} lattice points, {mp_['n_shielded']} fully "
              f"shielded (cap exactly 0); all rho < 1: "
              f"{mp_['all_below_one']}")
        print(f"  sup rho = {sup['rho']:.4f} at s = {sup['s_gaps']} gaps, "
              f"y = {sup['y']} (budget {sup['budget']:.6f}, cap "
              f"{sup['cap']:.6f})")
        print("  resonance profile at y = 0.49: "
              + ", ".join(f"s={x}: {rho_point(x, 0.49)['rho']:.3f}"
                          for x in (2.0, 3.0, 4.0, 5.0, 6.0)))
        print("= the deep edge and the step ladder at the argmax =")
        for x in (2.000, 2.002, 2.004, 2.006, 2.008):
            r = rho_point(x, 0.4999, step=0.002)
            print(f"  s = {x:.3f} gaps, y = 0.4999: rho = {r['rho']:.4f}")
        for st in (0.004, 0.002, 0.001):
            r = rho_point(2.002, 0.4999, step=st)
            print(f"  step {st}: rho = {r['rho']:.4f} "
                  f"(cap {r['cap']:.6f} / budget {r['budget']:.6f})")

    print("= finite-m interpolation (the sign is NOT uniform) =")
    for x, y in ((2.05, 0.49), (2.0, 0.49), (1.0, 0.49), (1.5, 0.3)):
        rec = finite_m_ladder(x, y)
        rows = "  ".join(f"m={r['m']}: {r['margin_pp']:+.5f}"
                         for r in rec["rows"])
        print(f"  s={x} y={y}: {rows}  | limit {rec['limit_margin']:+.5f}  "
              f"up={rec['monotone_up']} down={rec['monotone_down']} "
              f"all close: {rec['all_close']}")

    print("= jitter at the resonance (coherent should be worst) =")
    jc = jitter_campaign()
    for r in jc["rows"]:
        print(f"  amp {r['amp']:4.2f}: mean rel margin "
              f"{r['mean_rel_margin']:+.5f}  min {r['min_rel_margin']:+.5f}")
    print(f"  jitter helps on average: {jc['jitter_helps_on_average']}")
    g = lattice_gradient()
    print(f"  gradient at zero jitter: max |dmargin/dt_i| = "
          f"{g['max_abs']:.5f}, compression component "
          f"{g['compression_component']:+.5f} (nonzero: the extremum "
          "lives in the spacing parameter, not in position space)")

    print("= the primal has room at the worst lattice =")
    pr = primal_room()
    print(f"  greedy {pr['greedy']:.5f} <= budget {pr['budget']:.5f} "
          f"(cap {pr['cap']:.5f}): {pr['primal_within_budget']}")

    print("= control: theta = 1 diverges on a cluster =")
    pj = PaperJoint(step=0.005, G=60.0)
    print(f"  finite cluster: cap = {pj.cap([(0.0, 0.49)] * 3, 1.0)['cap']}")
    print(f"  periodic: cap = {periodic_cap(2.0 * MEAN_GAP, 0.49, 1.0)['cap']}")

    print("= the coordinator's pre-refutation, one measurement =")
    lr = legal_density_prerefutation()
    print(f"  cluster deficit {lr['deficit']:.4f} vs pair-free credit "
          f"{lr['credit']:.2e} over a {lr['window_gaps']:.1f}-gap legal "
          f"window (rate {lr['credit_rate_per_gap']:.2e}/gap): short by "
          f"x{lr['shortfall_factor']:.0f} — still broken: "
          f"{lr['still_broken']}")


if __name__ == "__main__":
    audit(quick="--quick" in sys.argv)
