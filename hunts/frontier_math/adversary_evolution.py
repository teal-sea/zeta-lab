"""Adversarial global search against the multi-pair verdict at theta = 0.995.

`cluster_universal.py` closed the PERIODIC family (sup rho = 0.9286 at
spacing s = 2.002 mean gaps, depth y -> 1/2) and left one bridge open in
plain sight: at the resonance spacings the per-pair margin approaches its
m -> infinity limit **from below** (s = 2.0: m = 4 gives +0.0240, m = 32
gives +0.0056, the periodic limit +0.0135).  A finite cluster can
therefore be worse than both its own limit and its smaller siblings, and
the sequence is decreasing exactly where the map's supremum lives.  This
module asks the one question that leaves: **does any finite
configuration drive the margin to zero or below?**

It is an ADVERSARIAL search.  The instrument is not re-derived and not
re-tuned; the objective is the relative margin of an unmodified
`paper_joint.PaperJoint` verdict, and the search tries to make it
negative with global optimisers (`scipy.optimize.differential_evolution`,
`dual_annealing`, `basinhopping`) plus a hand-rolled coordinate-descent
polish, from structured seeds (resonance lattices, jittered lattices,
mixed depths, two-scale clusters, commensurate multi-lattices, depth
gradients) as well as random ones.

**THE ONE-SIDED FACT THAT MAKES THE SEARCH MEANINGFUL.**  The budget is
exact and resolution-free; the cap is one-sided and gets *smaller* as the
instrument gets finer (tighter band edges, smaller local slope margins,
smaller closed-form tail at larger resolved half-range G).  So

    margin(step = 0.005, G = 60)  <=  margin(step = 0.001, G = 400),

and a configuration whose FAST margin is positive has a positive margin
at the finer instrument too.  The search therefore minimises the fast
margin, and only a fast-negative candidate is a candidate at all, it is
then re-evaluated at the promotion instrument, where a real violation
would have to survive.  :func:`resolution_ladder` measures the gap on a
sample.

**AND THE REASON THAT DIRECTION IS NOT A FORMALITY HERE.**  The search
instrument's closed-form tail is a per-pair handicap of 0.02733 at
G = 60, while the per-pair margin at the resonance is 0.02 to 0.05.  The
handicap is therefore the same size as the quantity, and long resonant
lattices go NEGATIVE at the search instrument: at s = 2.002 mean gaps
the per-pair margin is +0.000131 at m = 16 and -0.00288 at m = 24, and
at s = 2.0 it turns at m = 24 as well.  328 of the campaign's 20421
scores were negative for that reason.  Every candidate is resolved by
the promotion ladder: the same s = 2.002 lattice at step 0.001, G = 400
has per-pair margin +0.0541 (m = 2) falling to +0.0219 (m = 96), and the
worst STRUCTURED seed of the campaign, a commensurate superposition of
the s = 2.002 lattice with its half-offset double, k = 18,
search-instrument relative margin -0.0741, promotes to +0.2556.  So:
search-instrument negatives are common, and none survived.  They are
reported as what they are (resolution artifacts of a 9.5-mean-gap
resolved window), not suppressed and not counted.

**WHAT IS NEW HERE AND WHAT IS BORROWED.**  Borrowed unchanged: the
field, the bands, the completeness criterion, the per-cell square
completion, `K_of`, the closed-form tail, and the budget
(`PaperJoint`, `paper_chain`).  New: (i) :func:`phipap_trio`, one pass of
complex sin/cos shared across Phi2, Phi2' and Phi2'', the same closed
forms as `paper_chain`, pinned to them at 1e-12 absolute (worst
measured defect ~2e-14, in Phi2'' just past the series threshold) by
`test_adversary_evolution.py`; (ii) :class:`Evaluator`, which computes
the whole cap from ONE field pass instead of `PaperJoint.cap`'s three,
with a depth-uniform conservative band period so depths can stay
continuous (`P_CONSERVATIVE <= band_period_lower(y)` makes the tail
larger, never smaller, pinned by a test); (iii) the search itself.  With
`tail_mode="exact"` the evaluator reproduces `PaperJoint.cap` to
1e-12 (also pinned), which is what licenses the speed.

**HEADLINE (recorded at :data:`CAMPAIGN_RECORD`).**  No configuration
survived promotion with a nonpositive margin.  The worst promoted
configuration is recorded at :data:`WORST_FOUND` with the evaluation
count, so the weight of the negative result can be judged, and every
candidate under :data:`NEAR_MISS_REL` relative margin at the search
instrument is recorded so it can be re-examined independently.  The
m-scaling law is at :data:`M_SCALING_RECORD`: the per-pair margin at the
resonance decreases with m at every instrument, and the fitted
a + b/m extrapolation at the promotion instrument is what says whether
that decrease has a positive floor.  Read that number before reading the
negative as reassurance, the decrease is real, it is just not headed
for zero on this evidence.

**WHAT THE CAMPAIGN ACTUALLY FOUND HARDEST** is worth stating, because
it is not what the seeds were built around.  The worst configuration is
not a lattice: it is a COMMENSURATE SUPERPOSITION, the s = 2.002
lattice together with its half-offset double, polished into unequal
gaps at the deep edge.  That family is periodic with a two-point basis,
which is exactly the case `cluster_universal.py`'s single-lattice
periodic analysis does not cover.  It still promotes positive, but it is
the direction a next attack should take.

Controls (all in the test file): the optimiser must walk back from
random starts to the deep edge, the coupled band and a score at or below
the best resonant lattice; a planted damage inflation must be found in
the first handful of scores; the search and promotion evaluators must
agree with `PaperJoint` and order the right way; theta = 1 must diverge;
and every recorded configuration must reproduce from its record.

Nothing here computes a proportion and nothing here is evidence about
RH.  Run ``.venv/bin/python hunts/frontier_math/adversary_evolution.py``
(``--quick`` for the short campaign, ~8 min; the full campaign is ~50
min, and the audit around it about 75).
"""

from __future__ import annotations

import argparse
import math
import sys
import time
from dataclasses import dataclass, field as dc_field
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import (  # noqa: E402
    A, MEAN_GAP, PaperBandDual, S2, _SMALL,
)
from paper_joint import PaperJoint, joint_greedy  # noqa: E402
from joint_universal import THETA_FULL, budget_fast  # noqa: E402

# ---------------------------------------------------------------------------
# 0. the shared-trigonometry kernel trio
# ---------------------------------------------------------------------------


def _s_trio(u):
    """``(s, s', s'')`` for ``s(u) = sin(u/2)/u`` with the two complex
    trigonometric calls shared across all three.

    Identical closed forms and identical series fallback (|u| < 1e-4) to
    `paper_chain._s`, `_s_d1`, `_s_d2`; the only change is that
    ``sin(u/2)`` and ``cos(u/2)`` are evaluated once instead of five
    times.  ``test_trio_matches_paper_chain`` pins the agreement.
    """
    u = np.asarray(u, complex)
    small = np.abs(u) < _SMALL
    us = np.where(small, 1.0, u)
    h = us / 2
    sn, cs = np.sin(h), np.cos(h)
    iu = 1.0 / us
    iu2 = iu * iu
    s = sn * iu
    s1 = cs * iu / 2 - sn * iu2
    s2 = -sn * iu / 4 - cs * iu2 + 2 * sn * iu2 * iu
    u2 = u * u
    s = np.where(small, 0.5 - u2 / 48 + u2 * u2 / 3840, s)
    s1 = np.where(small, -u / 24 + u2 * u / 960, s1)
    s2 = np.where(small, -1 / 24 + u2 / 320, s2)
    return s, s1, s2


def phipap_trio(z):
    """``(Phi2, Phi2', Phi2'')`` at the paper's field in one pass."""
    z = np.asarray(z, complex)
    a0, a1, a2 = _s_trio(z + S2)
    b0, b1, b2 = _s_trio(z - S2)
    return a0 + b0, a1 + b1, a2 + b2


# ---------------------------------------------------------------------------
# 1. the evaluator
# ---------------------------------------------------------------------------

#: A depth-uniform lower bound on `PaperBandDual.band_period_lower(y)`
#: over y in (0, 1/2].  The measured band period rises with depth
#: (6.1143 at y = 0.1 to 6.1588 at y = 0.4999) and the function returns
#: MEAN_GAP = 6.2832 when it resolves fewer than three bands, so 6.10 is
#: below every value it can take on the depth range.  A SMALLER period
#: makes the closed-form tail LARGER, i.e. the cap larger and the margin
#: smaller: using it is one-sided against the defender, and it is what
#: lets the search move depths continuously instead of on a ladder (the
#: per-depth band system costs a 800k-point field pass).
P_CONSERVATIVE = 6.10

#: The search instrument.  Coarser step and shorter resolved half-range
#: than the module default, both conservative (see the module docstring).
#:
#: **Read this before reading any negative margin off it.**  The tail is
#: a per-pair additive handicap that depends only on G: 0.02733 at
#: G = 60, 0.00767 at G = 200, 0.00378 at G = 400, at y = 0.4999.  At the
#: resonance the per-pair margin itself is of order 0.01-0.03, so at
#: G = 60 the handicap is comparable to or larger than the quantity being
#: measured, and long resonant lattices go negative AT THIS INSTRUMENT
#: for that reason alone (m >= 16 at s = 2.002; see
#: :data:`M_SCALING_RECORD`).  That is why the campaign never treats a
#: search-instrument negative as a finding: every candidate is PROMOTED
#: to :data:`PROMOTE_STEP` / :data:`PROMOTE_G` before it counts.  Within
#: one k the handicap is a constant offset, which is why the optimisers
#: are run at fixed k.
FAST_STEP, FAST_G = 0.005, 60.0
#: The promotion instrument: five times finer, resolved half-range
#: 400 grid units (~64 mean gaps each side).  What is left beyond it is
#: bounded by the closed-form tail, 0.00378 per pair, and the margin is
#: nondecreasing in G, so a per-pair margin above that at G = 400 stays
#: positive for every larger G.
PROMOTE_STEP, PROMOTE_G = 0.001, 400.0
#: `PaperJoint`'s own defaults, the middle rung of the ladder.
FINE_STEP, FINE_G = 0.001, 200.0

#: Grid point-pairs per chunk, so a 64-pair configuration does not
#: allocate a 900 MB complex array.
_CHUNK = 3_000_000


@dataclass
class Evaluator:
    """One-field-pass verdict on an unmodified `PaperJoint` instrument.

    ``tail_mode="conservative"`` uses :data:`P_CONSERVATIVE` (depths
    continuous, cap never smaller than the module's); ``"exact"`` uses
    ``PaperJoint.tail`` and then reproduces ``PaperJoint.cap`` bit for
    bit on the configurations the tests probe.
    """

    step: float = FAST_STEP
    G: float = FAST_G
    tail_mode: str = "conservative"
    delta_choices: tuple = (0.5, 1.0, 2.0, 3.0)
    n_evals: int = 0
    _pj: PaperJoint = dc_field(init=False, repr=False)
    _bd: PaperBandDual = dc_field(init=False, repr=False)

    def __post_init__(self):
        object.__setattr__(self, "_pj",
                           PaperJoint(step=self.step, G=self.G,
                                      delta_choices=self.delta_choices))
        object.__setattr__(self, "_bd", PaperBandDual())

    # -- pieces ------------------------------------------------------------

    def tail(self, pairs) -> float:
        """Closed-form band-damage majorant beyond the resolved window."""
        if self.tail_mode == "exact":
            return self._pj.tail(pairs)
        tot = 0.0
        for _, y in pairs:
            C = self._bd.c_im_sharp(y) / A
            tot += 8 * C * C * (1 / self.G**2 + 1 / (P_CONSERVATIVE * self.G))
        return tot

    def field_summary(self, pairs):
        """``(gs, f, Q, qpp, slope)``, the same five arrays
        `PaperJoint.field` returns, computed once, chunked over the grid
        and vectorised over pairs."""
        ts = np.array([t for t, _ in pairs], float)
        ys = np.array([y for _, y in pairs], float)
        gs = np.arange(ts.min() - self.G, ts.max() + self.G, self.step)
        k = len(ts)
        f = np.empty_like(gs)
        Q = np.empty_like(gs)
        qpp = np.empty_like(gs)
        slope = np.empty_like(gs)
        block = max(1, _CHUNK // max(1, k))
        for i0 in range(0, len(gs), block):
            sl = slice(i0, i0 + block)
            z = (gs[sl][None, :] - ts[:, None]) + 1j * ys[:, None]
            v, v1, v2 = phipap_trio(z)
            re2 = v.real**2 - v.imag**2
            Q[sl] = re2.sum(axis=0)
            f[sl] = -4 * Q[sl] / A**2
            av, a1, a2 = np.abs(v), np.abs(v1), np.abs(v2)
            slope[sl] = (8 * av * a1 / A**2).sum(axis=0)
            qpp[sl] = (2 * (a1**2 + av * a2)).sum(axis=0)
        return gs, f, Q, qpp, slope

    def verdict(self, pairs, theta: float = THETA_FULL) -> dict:
        """budget, cap, margin, relative margin, completeness ratio.

        Every step is `PaperJoint`'s, in `PaperJoint`'s order: band
        membership on the raw grid, F carrying only the local slope
        margin, per-cell square completion against ``K_of``, cross-cell
        charges dropped, best delta on the ladder, closed-form tail.
        """
        self.n_evals += 1
        pairs = [(float(t), float(y)) for t, y in pairs]
        b = budget_fast([t for t, _ in pairs], [y for _, y in pairs])
        c = 1.0 - theta
        if c <= 0:
            return {"budget": b, "cap": math.inf, "margin": -math.inf,
                    "rel_margin": -math.inf, "completeness": None,
                    "bands": None, "pairs": pairs, "theta": theta}
        gs, f, Q, qpp, slope = self.field_summary(pairs)
        on = f > 0
        wide = on.copy()
        wide[1:] |= on[:-1]
        wide[:-1] |= on[1:]
        off = ~wide
        if np.any(off):
            comp = float(np.min(Q[off] / (qpp[off] * self.step**2 / 8)))
        else:
            comp = math.inf
        off_allow = 0.0
        if not comp > 1.0:
            m = f <= 0
            off_allow = float(np.sum(qpp[m])) * self.step**2 / 8 * 4 / A**2
        idx = np.where(on)[0]
        bands = []
        if len(idx):
            for gr in np.split(idx, np.where(np.diff(idx) > 1)[0] + 1):
                if len(gr) < 2:
                    continue
                bands.append((float(gs[gr[0]]) - self.step,
                              float(gs[gr[-1]]) + self.step,
                              float(f[gr].max())
                              + float(slope[gr].max()) * self.step))
        if not bands:
            cap, delta, ncell = 0.0, self.delta_choices[0], 0
        else:
            widths = np.array([hi - lo for lo, hi, _ in bands])
            Fs = np.array([F for _, _, F in bands])
            best = (math.inf, None, None)
            for d in self.delta_choices:
                n = np.maximum(1, np.ceil(widths / d).astype(int))
                w = widths / n
                Ks = np.array([self._pj.K_of(float(x)) for x in w])
                if np.any(Ks <= 0):
                    continue
                comp_cell = np.where(Fs <= 2 * c * Ks, Fs,
                                     (Fs + c * Ks) ** 2 / (4 * c * Ks))
                tot = float(np.sum(n * comp_cell))
                if tot < best[0]:
                    best = (tot, d, int(n.sum()))
            if not math.isfinite(best[0]):
                return {"budget": b, "cap": math.inf, "margin": -math.inf,
                        "rel_margin": -math.inf, "completeness": comp,
                        "bands": len(bands), "pairs": pairs,
                        "theta": theta, "instrument_failure": True}
            cap = best[0] + self.tail(pairs) + off_allow
            delta, ncell = best[1], best[2]
        margin = b - cap
        return {"budget": b, "cap": cap, "margin": margin,
                "rel_margin": margin / max(b, 1e-12), "completeness": comp,
                "bands": len(bands), "delta": delta, "cells": ncell,
                "off_band_allowance": off_allow, "pairs": pairs,
                "theta": theta, "step": self.step, "G": self.G}

    def rel_margin(self, pairs, theta: float = THETA_FULL) -> float:
        return self.verdict(pairs, theta)["rel_margin"]


def resolution_ladder(pairs, theta: float = THETA_FULL,
                      rungs=((0.01, 40.0), (FAST_STEP, FAST_G),
                             (0.002, 100.0), (FINE_STEP, FINE_G),
                             (PROMOTE_STEP, PROMOTE_G))) -> list:
    """The same configuration down the instrument ladder.

    The margin must rise (weakly) as the instrument refines; a candidate
    that is negative at the coarse rung and positive at the fine one is
    an instrument artifact, and a candidate negative at the fine rung is
    the finding this module exists to look for.
    """
    out = []
    for st, G in rungs:
        rec = Evaluator(step=st, G=G).verdict(pairs, theta)
        out.append({"step": st, "G": G, "budget": rec["budget"],
                    "cap": rec["cap"], "margin": rec["margin"],
                    "rel_margin": rec["rel_margin"],
                    "completeness": rec["completeness"]})
    return out


# ---------------------------------------------------------------------------
# 2. parameterisations
# ---------------------------------------------------------------------------

#: Position gaps in the FREE parameterisation, grid units.  0.02 grid
#: units is a near-coincident pair.  The upper end is 20 = 3.18 mean
#: gaps, not the whole line, and the reason is where the adversary can
#: live: |2 T(dt)| <= 2 C_T / dt^2 = 0.137 at dt = 20 and 0.034 at
#: dt = 40, and every resonance the rho map found sits at 1 to 3 mean
#: gaps (6.3 to 18.8 grid units).  Beyond that the pairs decouple toward
#: the isolated-pair verdict, which is the easy case.  Sparser spacings
#: are not left unsearched, the structured seeds run lattices out to
#: s = 8 mean gaps and :func:`m_ladder` runs them to m = 64, but the
#: free optimisers spend their budget where the coupling is.
GAP_LO, GAP_HI = 0.02, 20.0
#: depth bounds; the deep edge stops just short of 1/2 (the field's
#: constants are stated on (0, 1/2]).
Y_LO, Y_HI = 0.02, 0.4999


def free_bounds(k: int):
    """Bounds for the free parameterisation: ``k-1`` gaps then ``k``
    depths.  Positions are cumulative sums of the gaps, so the ordering
    constraint is built in and the first pair sits at 0 (the verdict is
    translation invariant)."""
    return [(GAP_LO, GAP_HI)] * (k - 1) + [(Y_LO, Y_HI)] * k


def free_unpack(x, k: int):
    """Vector -> pair list."""
    x = np.asarray(x, float)
    gaps = x[:k - 1]
    ys = np.clip(x[k - 1:k - 1 + k], Y_LO, Y_HI)
    ts = np.concatenate([[0.0], np.cumsum(np.clip(gaps, GAP_LO, GAP_HI))])
    return [(float(t), float(y)) for t, y in zip(ts, ys)]


def free_pack(pairs):
    """Pair list -> vector (the inverse of :func:`free_unpack`)."""
    ts = np.array([t for t, _ in pairs], float)
    ys = np.array([y for _, y in pairs], float)
    order = np.argsort(ts)
    ts, ys = ts[order], ys[order]
    return np.concatenate([np.diff(ts), ys])


def lattice(s_gaps: float, y: float, m: int):
    """The periodic family member: ``m`` pairs at spacing ``s_gaps`` mean
    gaps, common depth ``y``."""
    s = s_gaps * MEAN_GAP
    return [(i * s, float(y)) for i in range(m)]


def jittered_lattice(s_gaps: float, y: float, m: int, amp: float, seed: int):
    rng = np.random.default_rng(seed)
    s = s_gaps * MEAN_GAP
    return [(i * s + float(rng.normal(0.0, amp)), float(y)) for i in range(m)]


def depth_gradient_lattice(s_gaps: float, m: int, y_lo: float, y_hi: float):
    s = s_gaps * MEAN_GAP
    ys = np.linspace(y_lo, y_hi, m)
    return [(i * s, float(ys[i])) for i in range(m)]


def two_scale(s_out: float, m_out: int, s_in: float, m_in: int, y: float):
    """A tight cluster of ``m_in`` pairs at spacing ``s_in`` mean gaps
    repeated ``m_out`` times at spacing ``s_out`` mean gaps."""
    out = []
    for i in range(m_out):
        base = i * s_out * MEAN_GAP
        for j in range(m_in):
            out.append((base + j * s_in * MEAN_GAP, float(y)))
    return sorted(out)


def commensurate(s1: float, m1: int, s2: float, m2: int, y: float,
                 offset: float = 0.0):
    """Superposition of two lattices at spacings ``s1`` and ``s2`` mean
    gaps (use s2 = 2 s1 or 3 s1 for the commensurate cases)."""
    ps = [(i * s1 * MEAN_GAP, float(y)) for i in range(m1)]
    ps += [(offset + i * s2 * MEAN_GAP, float(y)) for i in range(m2)]
    return sorted(ps)


# ---------------------------------------------------------------------------
# 3. the candidate book
# ---------------------------------------------------------------------------

#: any configuration whose relative margin falls below this at ANY
#: resolution is recorded in full, whether or not it is negative.
NEAR_MISS_REL = 0.02


@dataclass
class Book:
    """Every configuration the campaign scores, kept only if it is worth
    keeping: the running worst, and every near miss."""

    theta: float = THETA_FULL
    worst: dict = dc_field(default_factory=lambda: {"rel_margin": math.inf})
    near_misses: list = dc_field(default_factory=list)
    n_negative: int = 0
    n_instrument_failure: int = 0
    n_scored: int = 0
    #: how many scores had been taken when the first negative margin
    #: appeared, the detector-power number the planted control reports
    first_negative_at: int | None = None
    by_method: dict = dc_field(default_factory=dict)

    def absorb(self, rec: dict, method: str = "?"):
        self.by_method[method] = self.by_method.get(method, 0) + 1
        self.n_scored += 1
        if rec.get("instrument_failure"):
            self.n_instrument_failure += 1
            return rec
        if rec["margin"] < 0:
            self.n_negative += 1
            if self.first_negative_at is None:
                self.first_negative_at = self.n_scored
        if rec["rel_margin"] < self.worst["rel_margin"]:
            self.worst = dict(rec, method=method)
        if rec["rel_margin"] < NEAR_MISS_REL:
            self.near_misses.append(dict(rec, method=method))
        return rec

    def summary(self) -> dict:
        nm = sorted(self.near_misses, key=lambda r: r["rel_margin"])
        return {"worst": self.worst, "n_negative": self.n_negative,
                "n_instrument_failure": self.n_instrument_failure,
                "first_negative_at": self.first_negative_at,
                "n_near_miss": len(nm), "near_misses": nm[:25],
                "by_method": dict(self.by_method)}


# ---------------------------------------------------------------------------
# 4. structured seeds
# ---------------------------------------------------------------------------


#: A seed whose span exceeds this many mean gaps is skipped: the cost of
#: one score is proportional to (span + 2G) k, and the long sparse
#: lattices are the cheapest part of the configuration space to reason
#: about (the pair term decays like 1/dt^2), so spending the search
#: budget there buys nothing.  Long lattices are covered instead by
#: :func:`m_ladder`, which runs them deliberately and to m = 64.
SEED_SPAN_CAP_GAPS = 40.0


def structured_seeds(ms=(2, 3, 4, 6, 8, 12, 16),
                     deep_only: bool = False):
    """The families the campaign is required to hit, as (name, pairs).

    Resonance and near-integer spacings, jittered lattices at the
    amplitudes measured to HELP, mixed-depth and depth-gradient
    lattices, two-scale clusters, and commensurate superpositions.
    """
    ys = (0.4999,) if deep_only else (0.2, 0.35, 0.4999)
    for s in (0.5, 0.9, 1.0, 1.05, 1.5, 1.95, 2.0, 2.002, 2.05, 2.1,
              2.5, 3.0, 3.002, 4.0, 5.0, 6.0, 8.0):
        for y in ys:
            for m in ms:
                if s * (m - 1) > SEED_SPAN_CAP_GAPS:
                    continue
                yield (f"lattice s={s} y={y} m={m}", lattice(s, y, m))
    for amp in (0.15, 0.3, 0.6, 1.2):
        for seed in range(3):
            for m in (4, 8, 16):
                yield (f"jitter s=2.002 amp={amp} seed={seed} m={m}",
                       jittered_lattice(2.002, 0.4999, m, amp, seed))
    for m in (4, 8, 16):
        yield (f"depth gradient m={m}",
               depth_gradient_lattice(2.002, m, 0.05, 0.4999))
        yield (f"depth gradient reversed m={m}",
               depth_gradient_lattice(2.002, m, 0.4999, 0.05))
        yield (f"alternating depth m={m}",
               [(i * 2.002 * MEAN_GAP, 0.4999 if i % 2 else 0.1)
                for i in range(m)])
    for s_in in (0.05, 0.2, 0.5, 1.0):
        for m_in in (2, 3):
            for m_out in (2, 4, 8):
                yield (f"two-scale out=2.002 in={s_in} {m_out}x{m_in}",
                       two_scale(2.002, m_out, s_in, m_in, 0.4999))
    # the commensurate superpositions: a second lattice at a multiple of
    # the first spacing, offset into the first lattice's gaps.  The
    # half-offset x2 member was the worst STRUCTURED seed of the campaign
    # (worse than any plain lattice at the same k), so the offset grid is
    # refined around 1/2 and the sizes are varied.
    for s1 in (1.0, 1.5, 2.002, 2.05, 3.0):
        for mult in (2, 3):
            for off in (0.0, 0.125, 0.25, 0.375, 0.5, 0.625):
                for m1, m2 in ((8, 4), (6, 6), (12, 6)):
                    if s1 * max(m1, mult * m2) > SEED_SPAN_CAP_GAPS:
                        continue
                    yield (f"commensurate s={s1} x{mult} off={off} "
                           f"{m1}+{m2}",
                           commensurate(s1, m1, s1 * mult, m2, 0.4999,
                                        off * s1 * MEAN_GAP))


def seed_scan(ev: Evaluator, book: Book, theta: float = THETA_FULL,
              seeds=None, report_every: int = 0) -> dict:
    """Score the structured seeds; return the worst few."""
    seeds = list(structured_seeds()) if seeds is None else list(seeds)
    rows = []
    for i, (name, pairs) in enumerate(seeds):
        rec = book.absorb(ev.verdict(pairs, theta), "seed")
        rows.append((name, rec["rel_margin"], rec["margin"], len(pairs)))
        if report_every and (i + 1) % report_every == 0:
            print(f"    [seed {i+1}/{len(seeds)}] worst so far "
                  f"{book.worst['rel_margin']:+.6f}", flush=True)
    rows.sort(key=lambda r: r[1])
    return {"n": len(rows), "worst_rows": rows[:15]}


# ---------------------------------------------------------------------------
# 5. the global optimisers
# ---------------------------------------------------------------------------


def _objective(ev, book, k, theta, method):
    def obj(x):
        return book.absorb(ev.verdict(free_unpack(x, k), theta),
                           method)["rel_margin"]
    return obj


def run_differential_evolution(ev: Evaluator, book: Book, k: int,
                               theta: float = THETA_FULL, seed: int = 11,
                               maxiter: int = 25, popsize: int = 12,
                               init_pairs=None) -> dict:
    """scipy differential evolution over the free parameterisation."""
    from scipy.optimize import differential_evolution
    bounds = free_bounds(k)
    obj = _objective(ev, book, k, theta, f"de_k{k}")
    kw = {}
    if init_pairs:
        rng = np.random.default_rng(seed)
        n_init = max(popsize * len(bounds), 5 * len(bounds))
        rows = [free_pack(p) for p in init_pairs if len(p) == k]
        lo = np.array([b[0] for b in bounds])
        hi = np.array([b[1] for b in bounds])
        pop = [np.clip(r, lo, hi) for r in rows]
        while len(pop) < n_init:
            pop.append(lo + rng.random(len(bounds)) * (hi - lo))
        kw["init"] = np.array(pop[:n_init])
    n0 = ev.n_evals
    res = differential_evolution(obj, bounds, seed=seed, maxiter=maxiter,
                                 popsize=popsize, tol=0.0, polish=False,
                                 init=kw.get("init", "latinhypercube"))
    return {"k": k, "fun": float(res.fun), "x": res.x.tolist(),
            "pairs": free_unpack(res.x, k), "n_evals": ev.n_evals - n0,
            "method": f"differential_evolution k={k}"}


def run_dual_annealing(ev: Evaluator, book: Book, k: int,
                       theta: float = THETA_FULL, seed: int = 12,
                       maxfun: int = 800, x0=None) -> dict:
    from scipy.optimize import dual_annealing
    bounds = free_bounds(k)
    obj = _objective(ev, book, k, theta, f"anneal_k{k}")
    n0 = ev.n_evals
    res = dual_annealing(obj, bounds, seed=seed, maxfun=maxfun,
                         no_local_search=True,
                         x0=None if x0 is None else np.asarray(x0, float))
    return {"k": k, "fun": float(res.fun), "x": res.x.tolist(),
            "pairs": free_unpack(res.x, k), "n_evals": ev.n_evals - n0,
            "method": f"dual_annealing k={k}"}


def run_basinhopping(ev: Evaluator, book: Book, k: int,
                     theta: float = THETA_FULL, seed: int = 13,
                     niter: int = 12, x0=None) -> dict:
    from scipy.optimize import basinhopping
    bounds = free_bounds(k)
    lo = np.array([b[0] for b in bounds])
    hi = np.array([b[1] for b in bounds])
    obj = _objective(ev, book, k, theta, f"basin_k{k}")

    def clipped(x):
        return obj(np.clip(x, lo, hi))

    rng = np.random.default_rng(seed)
    if x0 is None:
        x0 = lo + rng.random(len(bounds)) * (hi - lo)
    n0 = ev.n_evals
    res = basinhopping(clipped, np.asarray(x0, float), niter=niter,
                       stepsize=1.5, seed=seed,
                       minimizer_kwargs={"method": "Powell",
                                         "options": {"maxiter": 30,
                                                     "maxfev": 120,
                                                     "xtol": 1e-2,
                                                     "ftol": 1e-4}})
    x = np.clip(res.x, lo, hi)
    return {"k": k, "fun": float(res.fun), "x": x.tolist(),
            "pairs": free_unpack(x, k), "n_evals": ev.n_evals - n0,
            "method": f"basinhopping k={k}"}


def coordinate_polish(ev: Evaluator, book: Book, pairs, theta=THETA_FULL,
                      sweeps: int = 4, seed: int = 14,
                      steps=(2.0, 0.5, 0.12, 0.03)) -> dict:
    """Hand-rolled coordinate descent with a shrinking step, on the raw
    (t, y) coordinates rather than the gap parameterisation, it can move
    one pair through another, which the gap vector cannot."""
    rng = np.random.default_rng(seed)
    cur = [(float(t), float(y)) for t, y in pairs]
    best = book.absorb(ev.verdict(cur, theta), "polish")["rel_margin"]
    n0 = ev.n_evals
    for h in steps:
        for _ in range(sweeps):
            improved = False
            order = rng.permutation(len(cur))
            for i in order:
                for dt in (h, -h):
                    cand = list(cur)
                    cand[i] = (cur[i][0] + dt, cur[i][1])
                    v = book.absorb(ev.verdict(cand, theta),
                                    "polish")["rel_margin"]
                    if v < best:
                        best, cur, improved = v, cand, True
                for dy in (h / 20, -h / 20):
                    yn = min(Y_HI, max(Y_LO, cur[i][1] + dy))
                    cand = list(cur)
                    cand[i] = (cur[i][0], yn)
                    v = book.absorb(ev.verdict(cand, theta),
                                    "polish")["rel_margin"]
                    if v < best:
                        best, cur, improved = v, cand, True
            if not improved:
                break
    return {"rel_margin": best, "pairs": cur, "n_evals": ev.n_evals - n0,
            "method": "coordinate_polish"}


def cmaes_lite(ev: Evaluator, book: Book, k: int, x0, sigma0: float = 2.0,
               theta: float = THETA_FULL, iters: int = 40,
               lam: int = 16, seed: int = 15) -> dict:
    """A small separable evolution strategy: isotropic-per-coordinate
    Gaussian sampling with weighted recombination and a per-coordinate
    step adapted from the spread of the selected offspring.  Not CMA
    proper (no full covariance), enough to follow a narrow valley that
    axis-aligned coordinate descent walks past."""
    bounds = np.array(free_bounds(k), float)
    lo, hi = bounds[:, 0], bounds[:, 1]
    m = np.clip(np.asarray(x0, float), lo, hi)
    # per-coordinate step scaled to that coordinate's own range: the gap
    # and depth coordinates differ by a factor of 40 in extent, and a
    # single absolute step size moves depths so slowly that the search
    # never reaches the deep edge where the binding family lives.
    sig = (hi - lo) * (sigma0 / 4.0)
    rng = np.random.default_rng(seed)
    mu = max(2, lam // 2)
    w = np.log(mu + 0.5) - np.log(np.arange(1, mu + 1))
    w /= w.sum()
    n0 = ev.n_evals
    best = (math.inf, m.copy())
    for _ in range(iters):
        X = np.clip(m[None, :] + sig[None, :] * rng.normal(size=(lam, len(m))),
                    lo, hi)
        vals = np.array([book.absorb(ev.verdict(free_unpack(x, k), theta),
                                     f"cmaes_k{k}")["rel_margin"] for x in X])
        order = np.argsort(vals)
        sel = X[order[:mu]]
        if vals[order[0]] < best[0]:
            best = (float(vals[order[0]]), X[order[0]].copy())
        m_new = (w[:, None] * sel).sum(axis=0)
        spread = np.sqrt((w[:, None] * (sel - m_new) ** 2).sum(axis=0))
        sig = 0.5 * sig + 0.5 * np.maximum(spread, 1e-4)
        m = m_new
    return {"k": k, "fun": best[0], "x": best[1].tolist(),
            "pairs": free_unpack(best[1], k), "n_evals": ev.n_evals - n0,
            "method": f"cmaes_lite k={k}"}


# ---------------------------------------------------------------------------
# 6. the m-scaling law at the resonance
# ---------------------------------------------------------------------------


def m_ladder(s_gaps: float = 2.002, y: float = 0.4999,
             ms=(2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64),
             theta: float = THETA_FULL, ev: Evaluator | None = None) -> list:
    """Per-pair budget / cap / margin along m at one spacing."""
    ev = ev or Evaluator()
    rows = []
    for m in ms:
        rec = ev.verdict(lattice(s_gaps, y, m), theta)
        rows.append({"m": m, "budget_pp": rec["budget"] / m,
                     "cap_pp": rec["cap"] / m,
                     "margin_pp": rec["margin"] / m,
                     "rel_margin": rec["rel_margin"],
                     "completeness": rec["completeness"]})
    return rows


def fit_m_law(rows) -> dict:
    """Least squares of ``margin_pp(m) = a + b/m + c log(m)/m``.

    ``a`` is the extrapolated m -> infinity per-pair margin at this
    instrument.  Also fits the two-term model and reports the m at which
    each fit would cross zero, if it ever does for m > max(m), that
    crossing, if positive and finite, is a PREDICTED counterexample and
    the audit prints it as such.
    """
    ms = np.array([r["m"] for r in rows], float)
    v = np.array([r["margin_pp"] for r in rows], float)
    out = {}
    for name, cols in (("a+b/m", (np.ones_like(ms), 1 / ms)),
                       ("a+b/m+c log m/m",
                        (np.ones_like(ms), 1 / ms, np.log(ms) / ms))):
        M = np.column_stack(cols)
        coef, *_ = np.linalg.lstsq(M, v, rcond=None)
        resid = float(np.max(np.abs(M @ coef - v)))
        a = float(coef[0])
        # the first m beyond the measured ladder at which the fitted
        # curve is nonpositive; None means the fit never crosses
        grid = np.exp(np.linspace(math.log(ms.max()), math.log(1e9), 4000))
        cols_g = ([np.ones_like(grid), 1 / grid]
                  + ([np.log(grid) / grid] if len(coef) == 3 else []))
        vals_g = np.column_stack(cols_g) @ coef
        neg = np.where(vals_g <= 0)[0]
        cross = float(grid[neg[0]]) if len(neg) else None
        out[name] = {"coef": coef.tolist(), "limit_a": a,
                     "max_resid": resid, "zero_crossing_m": cross}
    v_dec = all(v[i] >= v[i + 1] - 1e-12 for i in range(len(v) - 1))
    v_inc = all(v[i] <= v[i + 1] + 1e-12 for i in range(len(v) - 1))
    out["monotone_decreasing"] = v_dec
    out["monotone_increasing"] = v_inc
    out["shape"] = ("decreasing" if v_dec else
                    "increasing" if v_inc else "non-monotone")
    out["margins"] = v.tolist()
    out["ms"] = ms.tolist()
    return out


def m_scaling_study(spacings=(1.0, 2.0, 2.002, 2.05, 3.0),
                    y: float = 0.4999,
                    ms=(2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64),
                    theta: float = THETA_FULL,
                    ev: Evaluator | None = None) -> dict:
    ev = ev or Evaluator()
    out = {}
    for s in spacings:
        rows = m_ladder(s, y, ms, theta, ev)
        out[s] = {"rows": rows, "fit": fit_m_law(rows)}
    return out


# ---------------------------------------------------------------------------
# 7. controls
# ---------------------------------------------------------------------------


#: The resonances the rho map of `cluster_universal.py` finds: spacings
#: commensurate with the damage-band lattice, at near-integer multiples
#: of a mean gap, with the supremum at 2.002.  Measured directly here on
#: the finite lattice family, the k = 3 and k = 4 relative margins at the
#: three lowest are nearly degenerate (k = 3: 0.1624 at s = 2, 0.1759 at
#: s = 3, 0.1790 at s = 1, everything else above 0.30), so "rediscovered
#: the binding family" means LANDED ON A RESONANCE, deep, not
#: necessarily on s = 2 rather than its neighbours.
RESONANCES = (1.0, 2.0, 3.0)


def rediscovery_control(n_starts: int = 6, k: int = 4, seed: int = 21,
                        theta: float = THETA_FULL, iters: int = 40,
                        lam: int = 12, polish: bool = True,
                        ev: Evaluator | None = None) -> dict:
    """CONTROL (a): from RANDOM starts, does the optimiser walk back to
    the known binding regime, deep pairs a few mean gaps apart, scoring
    at or below the best resonant lattice?

    Load-bearing: if the optimiser cannot rediscover the configuration
    `cluster_universal.py` already knows binds, the failure to find a
    violation says nothing about the verdict and everything about the
    search.  The run is the campaign's own combination (the evolution
    strategy, then the coordinate polish), started from a uniform draw in
    the box with no hint of the answer.

    The criterion is deliberately NOT "the spacing equals 2 mean gaps".
    Measured, the search does better than that: it drives every start to
    the deep edge and then finds unequal-gap configurations in the
    1.5-3.0 mean gap band that score BELOW the best resonant lattice at
    the same k.  So the control asks for what a working search must do,
    reach the deep edge, stay in the coupled band, and beat the lattice
    reference, and records where the spacings actually land.
    """
    ev = ev or Evaluator()
    rng = np.random.default_rng(seed)
    bounds = np.array(free_bounds(k), float)
    lo, hi = bounds[:, 0], bounds[:, 1]
    # what "the known binding family" scores at this k: the best (worst
    # relative margin) resonant lattice at the deep edge.  A search that
    # ends at or below it has rediscovered the family; a search that ends
    # well above it has not, whatever it says about spacings.
    ref = min(ev.verdict(lattice(s, 0.4999, k), theta)["rel_margin"]
              for s in RESONANCES)
    rows = []
    for i in range(n_starts):
        book = Book(theta=theta)
        x0 = lo + rng.random(len(lo)) * (hi - lo)
        rec = cmaes_lite(ev, book, k, x0, sigma0=1.0, theta=theta,
                         iters=iters, lam=lam, seed=seed + i)
        pairs, rel = rec["pairs"], rec["fun"]
        if polish:
            pol = coordinate_polish(ev, book, pairs, theta, sweeps=3,
                                    seed=seed + 100 + i)
            if pol["rel_margin"] < rel:
                pairs, rel = pol["pairs"], pol["rel_margin"]
        pairs = sorted(pairs)
        ts = np.array([t for t, _ in pairs])
        ys = np.array([y for _, y in pairs])
        gaps = np.diff(ts) / MEAN_GAP
        med_gap = float(np.median(gaps))
        rows.append({"start": i, "rel_margin": rel,
                     "median_gap_mean_gaps": med_gap,
                     "resonance_distance": min(abs(med_gap - r)
                                               for r in RESONANCES),
                     "mean_depth": float(ys.mean()),
                     "pairs": pairs})
    med = np.array([r["median_gap_mean_gaps"] for r in rows])
    dep = np.array([r["mean_depth"] for r in rows])
    dist = np.array([r["resonance_distance"] for r in rows])
    rel = np.array([r["rel_margin"] for r in rows])
    return {"rows": rows, "n_evals": ev.n_evals, "k": k,
            "lattice_reference_rel_margin": float(ref),
            "median_spacing": float(np.median(med)),
            "median_depth": float(np.median(dep)),
            "median_resonance_distance": float(np.median(dist)),
            "frac_on_resonance": float(np.mean(dist < 0.25)),
            "frac_in_coupled_band": float(np.mean((med > 0.8)
                                                  & (med < 3.4))),
            "frac_near_two_gaps": float(np.mean(np.abs(med - 2.0) < 0.35)),
            "frac_deep": float(np.mean(dep > 0.40)),
            "frac_beating_the_lattice": float(np.mean(rel <= ref)),
            "best_rel_margin": float(rel.min())}


@dataclass
class InflatedEvaluator(Evaluator):
    """CONTROL (b) instrument: the damage field of every pair scaled by
    ``inflate``, budget untouched, a planted violation the search must
    find.  Mirrors `joint_universal.InflatedJoint` (which inflates ONE
    pair) with a uniform factor, so the planted fault is reachable from
    every configuration rather than only from configurations that happen
    to weight pair 0."""

    inflate: float = 1.0

    def field_summary(self, pairs):
        gs, f, Q, qpp, slope = super().field_summary(pairs)
        return (gs, self.inflate * f, self.inflate * Q,
                self.inflate * qpp, self.inflate * slope)


def planted_detection_control(inflate: float = 3.0, k: int = 3,
                              theta: float = THETA_FULL, seed: int = 31,
                              iters: int = 10, lam: int = 8) -> dict:
    """CONTROL (b): with the damage field inflated by ``inflate`` (the
    budget untouched), the same search must find a negative margin, and
    find it quickly.

    The control runs a MINIATURE OF THE CAMPAIGN, not a different
    procedure: a handful of structured seeds first, then the same
    evolution strategy from the same kind of start.  A control that gave
    the detector a shape of search the campaign never uses would measure
    the wrong instrument's power.  ``first_negative_at`` is the number of
    scores taken before the first violation appeared.
    """
    ev = InflatedEvaluator(inflate=inflate)
    book = Book(theta=theta)
    seeds = [p for _, p in structured_seeds(ms=(k,), deep_only=True)
             if len(p) == k][:8]
    for pairs in seeds:
        book.absorb(ev.verdict(pairs, theta), "planted_seed")
    bounds = np.array(free_bounds(k), float)
    lo, hi = bounds[:, 0], bounds[:, 1]
    rng = np.random.default_rng(seed)
    x0 = lo + rng.random(len(lo)) * (hi - lo)
    rec = cmaes_lite(ev, book, k, x0, sigma0=1.0, theta=theta, iters=iters,
                     lam=lam, seed=seed)
    return {"inflate": inflate, "found": book.n_negative > 0,
            "n_negative": book.n_negative,
            "n_scored": book.n_scored,
            "first_negative_at": book.first_negative_at,
            "n_evals": ev.n_evals,
            "best_rel_margin": min(rec["fun"], book.worst["rel_margin"]),
            "worst": book.worst if book.n_negative else None}


def theta_one_control(pairs=None) -> dict:
    """CONTROL (d): at theta = 1 the internal charge vanishes and the cap
    must report infinity (an unbounded multiplicity stack costs nothing)."""
    pairs = pairs or lattice(2.002, 0.4999, 3)
    rec = Evaluator().verdict(pairs, 1.0)
    return {"cap": rec["cap"], "diverges": not math.isfinite(rec["cap"])}


def promote(pairs, theta: float = THETA_FULL) -> dict:
    """Re-evaluate one candidate at the promotion instrument.

    The promoted margin is the one that counts.  ``headroom_per_pair`` is
    the promoted per-pair margin minus the closed-form tail at
    ``PROMOTE_G``: since the margin is nondecreasing in G and the total
    unresolved band damage beyond G is at most that tail, a positive
    headroom says the configuration stays positive at EVERY larger
    resolved half-range, not only at this one.
    """
    ev = Evaluator(step=PROMOTE_STEP, G=PROMOTE_G)
    rec = ev.verdict(pairs, theta)
    k = len(pairs)
    tail_pp = ev.tail(pairs) / k
    return {"pairs": [(float(t), float(y)) for t, y in pairs], "k": k,
            "budget": rec["budget"], "cap": rec["cap"],
            "margin": rec["margin"], "rel_margin": rec["rel_margin"],
            "margin_per_pair": rec["margin"] / k,
            "tail_per_pair": tail_pp,
            "headroom_per_pair": rec["margin"] / k - tail_pp,
            "completeness": rec["completeness"],
            "step": PROMOTE_STEP, "G": PROMOTE_G}


def promote_candidates(book: Book, n: int = 8,
                       theta: float = THETA_FULL) -> dict:
    """Promote the ``n`` worst configurations the search reached.

    This is the stage that turns a search-instrument number into a
    statement.  Nothing the search says is treated as a finding until it
    has been through here.
    """
    ranked = sorted(book.near_misses, key=lambda r: r["rel_margin"])
    if book.worst.get("pairs") is not None:
        ranked = [book.worst] + ranked
    # DEDUPLICATE.  The coordinate polish writes a near-miss on every
    # improving step, so the top of the ranking is a run of nearly
    # identical configurations; promoting ten of those is promoting one.
    # Positions are rounded to 1e-3 grid units and depths to 1e-4, which
    # is far below any scale the verdict resolves.
    seen = set()
    cands = []
    for c in ranked:
        key = tuple((round(t, 3), round(y, 4)) for t, y in c["pairs"])
        if key in seen:
            continue
        seen.add(key)
        cands.append(c)
        if len(cands) >= n:
            break
    rows = []
    for c in cands:
        p = promote(c["pairs"], theta)
        p["search_rel_margin"] = c["rel_margin"]
        p["search_margin"] = c["margin"]
        p["method"] = c.get("method")
        rows.append(p)
    rows.sort(key=lambda r: r["rel_margin"])
    return {"rows": rows, "n": len(rows),
            "n_negative_promoted": sum(1 for r in rows if r["margin"] < 0),
            "n_negative_headroom": sum(1 for r in rows
                                       if r["headroom_per_pair"] < 0),
            "worst": rows[0] if rows else None}


def primal_check(pairs, theta: float = THETA_FULL) -> dict:
    """The measured greedy adversary against the budget: only a PRIMAL
    crossing would touch the E-form itself; a cap crossing alone would
    be an instrument statement.  Reported for every candidate.

    ``joint_greedy`` builds the on-line multiset X site by site, so this
    is the search over X that the cap merely bounds, the same machinery
    `paper_joint.py` uses, not a second one.
    """
    pj = PaperJoint(step=FAST_STEP, G=FAST_G)
    g = joint_greedy(pj, pairs, theta, kmax=20 * len(pairs))
    b = budget_fast([t for t, _ in pairs], [y for _, y in pairs])
    return {"greedy": g, "budget": b, "ratio": g / max(b, 1e-12),
            "primal_within_budget": g <= b}


def primal_sweep(configs=None, theta: float = THETA_FULL) -> dict:
    """The primal side over a family: the greedy on-line adversary
    against the exact budget.

    The cap is one-sided, so a cap crossing is a statement about the
    instrument; only the PRIMAL sup crossing the budget would say
    anything about the E-form.  This sweep records how much room the
    primal actually has on the families the cap finds hardest, so the
    two failure modes never get confused in the report.
    """
    if configs is None:
        configs = [(f"lattice s={s} m={m}", lattice(s, 0.4999, m))
                   for s in (1.0, 2.0, 2.002, 3.0) for m in (2, 4, 8)]
        configs.append(("commensurate half-offset x2",
                        commensurate(2.002, 8, 4.004, 4, 0.4999,
                                     0.5 * 2.002 * MEAN_GAP)))
    rows = []
    for name, pairs in configs:
        rec = primal_check(pairs, theta)
        rows.append(dict(rec, name=name, k=len(pairs)))
    return {"rows": rows,
            "worst_ratio": max(r["ratio"] for r in rows),
            "all_within_budget": all(r["primal_within_budget"]
                                     for r in rows)}


# ---------------------------------------------------------------------------
# 8. the campaign
# ---------------------------------------------------------------------------


def campaign(quick: bool = False, theta: float = THETA_FULL,
             verbose: bool = True) -> dict:
    """The whole adversarial run: seeds, then four global methods over
    k = 2..8, then polish from the worst finds.  Returns the book plus
    the per-method evaluation counts."""
    t0 = time.time()
    ev = Evaluator()
    book = Book(theta=theta)
    log = []

    def say(*a):
        if verbose:
            print(*a, flush=True)

    say("== structured seeds ==")
    ss = seed_scan(ev, book, theta,
                   seeds=(list(structured_seeds(ms=(2, 4, 8), deep_only=True))
                          if quick else None),
                   report_every=0 if quick else 100)
    log.append(("seeds", ss["n"], ev.n_evals))
    say(f"   {ss['n']} seeds, worst rel margin "
        f"{book.worst['rel_margin']:+.6f}")
    for name, rel, mar, k in ss["worst_rows"][:8]:
        say(f"     {name:44s} k={k:3d} rel {rel:+.6f} abs {mar:+.6f}")

    ks = (2, 4) if quick else (2, 3, 4, 6, 8)
    seeds_by_k = {}
    for k in ks:
        seeds_by_k[k] = [p for _, p in structured_seeds(ms=(k,),
                                                        deep_only=True)]

    #: per-k generation counts, set so the evaluation budget is spread
    #: rather than eaten by the expensive large-k scores (one k = 8 score
    #: costs about seven k = 2 scores).
    DE_ITERS = {2: 60, 3: 40, 4: 30, 6: 12, 8: 8}
    DE_POP = {2: 14, 3: 14, 4: 12, 6: 10, 8: 8}
    ANNEAL_FUN = {2: 1200, 3: 1200, 4: 1200, 6: 600, 8: 400}
    #: 0 = skip.  Basin hopping's Powell inner solver is the most
    #: expensive evaluation per unit of progress at large k, and DE and
    #: the annealer already cover k = 6 and 8.
    BASIN_ITERS = {2: 10, 3: 10, 4: 8, 6: 0, 8: 0}
    CMAES_ITERS = {2: 45, 3: 45, 4: 40, 6: 20, 8: 14}

    for k in ks:
        n0 = ev.n_evals
        de = run_differential_evolution(
            ev, book, k, theta, seed=100 + k,
            maxiter=6 if quick else DE_ITERS[k],
            popsize=8 if quick else DE_POP[k], init_pairs=seeds_by_k[k])
        say(f"== differential evolution k={k}: best rel {de['fun']:+.6f} "
            f"({de['n_evals']} evals) ==")
        log.append((f"de_k{k}", ev.n_evals - n0, ev.n_evals))

    for k in ks:
        n0 = ev.n_evals
        da = run_dual_annealing(ev, book, k, theta, seed=200 + k,
                                maxfun=200 if quick else ANNEAL_FUN[k])
        say(f"== dual annealing k={k}: best rel {da['fun']:+.6f} "
            f"({da['n_evals']} evals) ==")
        log.append((f"anneal_k{k}", ev.n_evals - n0, ev.n_evals))

    for k in ks:
        niter = 4 if quick else BASIN_ITERS[k]
        if niter <= 0:
            continue
        n0 = ev.n_evals
        bh = run_basinhopping(ev, book, k, theta, seed=300 + k, niter=niter)
        say(f"== basin hopping k={k}: best rel {bh['fun']:+.6f} "
            f"({bh['n_evals']} evals) ==")
        log.append((f"basin_k{k}", ev.n_evals - n0, ev.n_evals))

    for k in ks:
        n0 = ev.n_evals
        x0 = free_pack(lattice(2.002, 0.4999, k))
        cm = cmaes_lite(ev, book, k, x0, sigma0=0.6, theta=theta,
                        iters=8 if quick else CMAES_ITERS[k],
                        lam=10 if quick else 16, seed=400 + k)
        say(f"== cmaes-lite k={k} from the resonance: best rel "
            f"{cm['fun']:+.6f} ({cm['n_evals']} evals) ==")
        log.append((f"cmaes_k{k}", ev.n_evals - n0, ev.n_evals))

    n0 = ev.n_evals
    ranked = sorted(book.near_misses, key=lambda r: r["rel_margin"])
    # the global worst always gets polished; the rest of the polish budget
    # goes to configurations small enough that a full coordinate sweep is
    # affordable (one k = 16 score costs about eight k = 2 scores)
    picks = [ranked[0]] if ranked else []
    picks += [c for c in ranked[1:] if len(c["pairs"]) <= 8][:2 if quick
                                                             else 7]
    for i, cand in enumerate(picks):
        k = len(cand["pairs"])
        coordinate_polish(ev, book, cand["pairs"], theta,
                          sweeps=2 if (quick or k > 8) else 4,
                          steps=((2.0, 0.5, 0.12, 0.03) if k <= 8
                                 else (1.0, 0.2, 0.05)),
                          seed=500 + i)
    say(f"== coordinate polish from the near misses "
        f"({ev.n_evals - n0} evals) ==")
    log.append(("polish", ev.n_evals - n0, ev.n_evals))

    say("== promotion: the worst finds at the promotion instrument ==")
    prom = promote_candidates(book, n=3 if quick else 10, theta=theta)
    for r in prom["rows"]:
        say(f"   k={r['k']:2d} search rel {r['search_rel_margin']:+.6f} -> "
            f"promoted rel {r['rel_margin']:+.6f} (margin "
            f"{r['margin']:+.6f}, per pair {r['margin_per_pair']:+.6f}, "
            f"headroom {r['headroom_per_pair']:+.6f})")

    out = book.summary()
    out.update({"n_evals": ev.n_evals, "log": log, "theta": theta,
                "seconds": time.time() - t0, "quick": quick,
                "promotion": prom,
                "instrument": {"step": ev.step, "G": ev.G,
                               "tail_mode": ev.tail_mode}})
    return out


# ---------------------------------------------------------------------------
# 9. the record
# ---------------------------------------------------------------------------

#: The worst configuration the full campaign reached, as data, so a
#: reader can re-check it without rerunning the search and so the number
#: cannot drift silently.  It is a SEARCH result: it bounds the adversary
#: from below and the quantifier not at all.
#:
#: Its shape is worth reading.  The campaign did not find it from a
#: random start: the STRUCTURED seed "commensurate s = 2.002 x2 off = 0.5,
#: 12 + 6" (the resonant lattice superposed with its half-offset double)
#: was the worst seed, and the coordinate polish then moved one pair by
#: -0.1 grid units and re-tuned the rest, taking the search-instrument
#: relative margin from -0.0741 to -0.1631.  So the hardest thing the
#: campaign found is a commensurate two-lattice, not a single lattice,
#: which is the one family `cluster_universal.py`'s periodic analysis
#: does not cover, since it is periodic with a two-point basis.
WORST_FOUND = {
    "theta": THETA_FULL,
    "method": "coordinate_polish from the commensurate x2 half-offset seed",
    "pairs": [
        (-0.1, 0.4999), (6.139468492486765, 0.4999),
        (12.378936984973532, 0.4999), (25.15787396994706, 0.4999),
        (31.397342462433826, 0.4999), (37.58681095492059, 0.4999),
        (50.36574793989412, 0.4999), (56.605216432380885, 0.4999),
        (62.84468492486765, 0.4999), (75.62362190984119, 0.4999),
        (81.81309040232794, 0.4999), (88.00255889481473, 0.4999),
        (100.78149587978825, 0.4999), (107.020964372275, 0.4999),
        (113.21043286476177, 0.4999), (126.0393698497353, 0.4999),
        (132.27883834222206, 0.4999), (138.51830683470882, 0.4999),
    ],
    #: at the SEARCH instrument (step 0.005, G = 60), negative, and an
    #: artifact of that instrument's 0.02733/pair tail handicap
    "search": {
        "step": FAST_STEP, "G": FAST_G,
        "budget": 1.4390673698229364, "cap": 1.6738063386896622,
        "margin": -0.23473896886672585,
        "rel_margin": -0.163118818332743,
        "completeness": 669.5215266673817,
    },
    #: at the PROMOTION instrument (step 0.001, G = 400), the number
    #: that counts.  ``headroom_per_pair`` is the per-pair margin minus
    #: the residual closed-form tail, so a positive value says the
    #: configuration stays positive at every larger G as well.
    "promoted": {
        "step": PROMOTE_STEP, "G": PROMOTE_G,
        "budget": 1.4390673698229364, "cap": 1.2148159697883012,
        "margin": 0.22425140003463517,
        "rel_margin": 0.15583106443600844,
        "margin_per_pair": 0.012458411113035287,
        "tail_per_pair": 0.0037783462326360182,
        "headroom_per_pair": 0.008680064880399269,
        "completeness": 3472.3599130214398,
    },
    #: the greedy on-line adversary at this configuration, against the
    #: exact budget: the primal has 76% of the budget spare, so even the
    #: search-instrument cap crossing was nowhere near an E-form crossing
    "primal_greedy": 0.3481896878220711,
}

#: The campaign, as data.  Produced by ``campaign(quick=False)`` at the
#: recorded seeds; 20421 scored configurations in 2219 s, plus the
#: promotion pass.  Read ``n_negative_search_instrument`` and
#: ``n_negative_promoted`` together, the first is large and means
#: nothing on its own, the second is the result.
CAMPAIGN_RECORD = {
    "n_evals": 20421,
    "seconds": 2219.08,
    "theta": THETA_FULL,
    "search_instrument": {"step": FAST_STEP, "G": FAST_G},
    "promotion_instrument": {"step": PROMOTE_STEP, "G": PROMOTE_G},
    "n_negative_search_instrument": 328,
    "n_negative_promoted": 0,
    "n_negative_headroom": 0,
    "n_instrument_failure": 0,
    "n_near_miss": 330,
    "n_promoted": 10,
    "worst_search_rel_margin": -0.163118818332743,
    "worst_promoted_rel_margin": 0.15583106443600844,
    "by_method": {
        "seed": 558,
        "de_k2": 2562, "de_k3": 2870, "de_k4": 2604, "de_k6": 1430,
        "de_k8": 1080,
        "anneal_k2": 1200, "anneal_k3": 1200, "anneal_k4": 1200,
        "anneal_k6": 600, "anneal_k8": 400,
        "basin_k2": 164, "basin_k3": 488, "basin_k4": 1080,
        "cmaes_k2": 720, "cmaes_k3": 720, "cmaes_k4": 640,
        "cmaes_k6": 320, "cmaes_k8": 224,
        "polish": 361,
    },
    #: The distinct families that went under NEAR_MISS_REL at the search
    #: instrument, each with its promotion.  The campaign's own near-miss
    #: list is dominated by near-duplicates from the polish (330 entries,
    #: 10 distinct, all variants of WORST_FOUND), so the table below is
    #: built from the DISTINCT families instead: the commensurate
    #: superpositions and the long resonant lattices.  Every one of them
    #: promotes to a positive margin with positive headroom.
    #: Every DISTINCT family that went under NEAR_MISS_REL at the search
    #: instrument, with its promotion.  ``build`` reconstructs the
    #: configuration exactly, ``("lattice", s_gaps, m)`` is
    #: ``lattice(s, 0.4999, m)`` and
    #: ``("commensurate", s1, m1, mult, m2, off)`` is
    #: ``commensurate(s1, m1, s1*mult, m2, 0.4999, off*s1*MEAN_GAP)``,
    #: so a reader can re-score any row without a stored coordinate list.
    #: The campaign's own near-miss list is 330 entries but only 10
    #: distinct, all polish variants of WORST_FOUND; this table is the
    #: distinct families instead.  Every one promotes positive with
    #: positive headroom.
    "near_misses": [
        {"name": "commensurate s=2.002 x2 off=0.5 12+6", "k": 18,
         "build": ('commensurate', 2.002, 12, 2, 6, 0.5),
         "search_rel_margin": -0.0740583150555920,
         "promoted_rel_margin": 0.2555511893837238,
         "promoted_margin_per_pair": 0.0193573618384501,
         "headroom_per_pair": 0.0155790156058141},
        {"name": "lattice s=2.002 m=64", "k": 64,
         "build": ('lattice', 2.002, 64),
         "search_rel_margin": -0.0544534536123341,
         "promoted_rel_margin": 0.1718689694678164,
         "promoted_margin_per_pair": 0.0223565972776200,
         "headroom_per_pair": 0.0185782510449840},
        {"name": "lattice s=2.002 m=48", "k": 48,
         "build": ('lattice', 2.002, 48),
         "search_rel_margin": -0.0479402700171089,
         "promoted_rel_margin": 0.1763862453514455,
         "promoted_margin_per_pair": 0.0230149311368337,
         "headroom_per_pair": 0.0192365849041977},
        {"name": "lattice s=2.0 m=64", "k": 64,
         "build": ('lattice', 2.0, 64),
         "search_rel_margin": -0.0371978867091159,
         "promoted_rel_margin": 0.1882665219224584,
         "promoted_margin_per_pair": 0.0244753859934536,
         "headroom_per_pair": 0.0206970397608176},
        {"name": "lattice s=2.002 m=32", "k": 32,
         "build": ('lattice', 2.002, 32),
         "search_rel_margin": -0.0345206995569684,
         "promoted_rel_margin": 0.1861578013626803,
         "promoted_margin_per_pair": 0.0244363001204870,
         "headroom_per_pair": 0.0206579538878510},
        {"name": "lattice s=2.0 m=48", "k": 48,
         "build": ('lattice', 2.0, 48),
         "search_rel_margin": -0.0288256674105367,
         "promoted_rel_margin": 0.1945791325373339,
         "promoted_margin_per_pair": 0.0253842479858459,
         "headroom_per_pair": 0.0216059017532099},
        {"name": "commensurate s=2.002 x3 off=0.5 12+6", "k": 18,
         "build": ('commensurate', 2.002, 12, 3, 6, 0.5),
         "search_rel_margin": -0.0279522230524115,
         "promoted_rel_margin": 0.2419951539862038,
         "promoted_margin_per_pair": 0.0235685025496498,
         "headroom_per_pair": 0.0197901563170138},
        {"name": "commensurate s=2.002 x2 off=0.5 8+4", "k": 12,
         "build": ('commensurate', 2.002, 8, 2, 4, 0.5),
         "search_rel_margin": -0.0221468935864494,
         "promoted_rel_margin": 0.2890188772924955,
         "promoted_margin_per_pair": 0.0227749459967809,
         "headroom_per_pair": 0.0189965997641448},
        {"name": "lattice s=2.002 m=24", "k": 24,
         "build": ('lattice', 2.002, 24),
         "search_rel_margin": -0.0218161968859600,
         "promoted_rel_margin": 0.1956858240765856,
         "promoted_margin_per_pair": 0.0258331303766394,
         "headroom_per_pair": 0.0220547841440034},
        {"name": "lattice s=2.0 m=32", "k": 32,
         "build": ('lattice', 2.0, 32),
         "search_rel_margin": -0.0139655565578130,
         "promoted_rel_margin": 0.2057989938516814,
         "promoted_margin_per_pair": 0.0270202655328012,
         "headroom_per_pair": 0.0232419193001652},
        {"name": "lattice s=2.0 m=24", "k": 24,
         "build": ('lattice', 2.0, 24),
         "search_rel_margin": -0.0009106038903459,
         "promoted_rel_margin": 0.2156884823593588,
         "promoted_margin_per_pair": 0.0284849162028975,
         "headroom_per_pair": 0.0247065699702615},
        {"name": "lattice s=2.002 m=16", "k": 16,
         "build": ('lattice', 2.002, 16),
         "search_rel_margin": 0.0009786397231266,
         "promoted_rel_margin": 0.2130238808564721,
         "promoted_margin_per_pair": 0.0284163463889875,
         "headroom_per_pair": 0.0246380001563515},
        {"name": "commensurate s=2.002 x3 off=0.5 8+4", "k": 12,
         "build": ('commensurate', 2.002, 8, 3, 4, 0.5),
         "search_rel_margin": 0.0079636233831849,
         "promoted_rel_margin": 0.2764740525678425,
         "promoted_margin_per_pair": 0.0263918696180508,
         "headroom_per_pair": 0.0226135233854148},
        {"name": "lattice s=1.0 m=64", "k": 64,
         "build": ('lattice', 1.0, 64),
         "search_rel_margin": 0.0175579829512367,
         "promoted_rel_margin": 0.7466572083096474,
         "promoted_margin_per_pair": 0.0234868600524667,
         "headroom_per_pair": 0.0197085138198307},
    ],
    #: the campaign's own promotion pass, before the deduplication that
    #: :func:`promote_candidates` now applies: ten promotions of ten
    #: near-identical polish variants of WORST_FOUND, promoted relative
    #: margins +0.15583 and +0.15609, none negative
    "promotion_pass": {"n": 10, "n_negative_promoted": 0,
                       "n_negative_headroom": 0,
                       "distinct_configurations": 2},
}

#: The m-scaling law, which is what the open bridge was actually about.
#:
#: **The shape is real and it is decreasing.**  At every instrument, at
#: the resonant spacings, the per-pair margin falls with m.  What changes
#: with the instrument is the LEVEL, because the closed-form tail is a
#: per-pair constant handicap that depends only on G (0.02733 at G = 60,
#: 0.00378 at G = 400).  At the search instrument the fall crosses zero
#: (measured: m = 24 at s = 2.0, m = 16 at s = 2.002) and the fitted
#: limits are negative; at the promotion instrument nothing crosses and
#: the fitted limits are positive with room.
#:
#: **The honest caveat on the extrapolation**: the two-term a + b/m fit
#: is NOT conservative here.  Fitted on m <= 64 at s = 2.002 it gives a
#: limit of +0.02339, and the measured m = 96 value is +0.021884,
#: BELOW its own extrapolated limit.  The three-term fit (residual
#: 2.4e-4 against the two-term's 3.7e-3) gives +0.01878 and is not
#: violated by m = 96.  Both stay above the residual tail 0.00378, which
#: is the only thing left to recover as G grows; that is the margin the
#: verdict has at the resonance in the m -> infinity limit, and it is
#: about 2% of the budget per pair, not 20%.
M_SCALING_RECORD = {
    "y": 0.4999,
    "search_instrument": {"step": FAST_STEP, "G": FAST_G},
    "promotion_instrument": {"step": PROMOTE_STEP, "G": PROMOTE_G},
    "tail_per_pair": {"G=60": 0.02733302536072022,
                      "G=200": 0.007670201019909218,
                      "G=400": 0.0037783462326360187},
    #: per-pair margins at the SEARCH instrument, m = 2 .. 64
    "ms": [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64],
    "margin_pp": {
        "1.0": [0.022474, 0.017195, 0.014355, 0.010706, 0.008828,
                0.006571, 0.005188, 0.003506, 0.002483, 0.001269,
                0.000552],
        "2.0": [0.029753, 0.023611, 0.019221, 0.013472, 0.009851,
                0.005484, 0.002884, -0.000120, -0.001834, -0.003761,
                -0.004836],
        "2.002": [0.028664, 0.021991, 0.017278, 0.011211, 0.007365,
                  0.002798, 0.000131, -0.002880, -0.004531, -0.006255,
                  -0.007083],
        "2.05": [0.015076, 0.008562, 0.008835, 0.017111, 0.027339,
                 0.045992, 0.059142, 0.072287, 0.079093, 0.087034,
                 0.091374],
        "3.0": [0.031181, 0.027002, 0.024201, 0.020631, 0.018434,
                0.015817, 0.014281, 0.012533, 0.011547, 0.010438,
                0.009829],
    },
    "shape": {"1.0": "decreasing", "2.0": "decreasing",
              "2.002": "decreasing", "2.05": "non-monotone",
              "3.0": "decreasing"},
    #: fitted two-term limits at the SEARCH instrument, negative at the
    #: two-mean-gap resonances, which is what the promotion instrument
    #: then resolves
    "search_limit_two_term": {"1.0": 0.001803662800560941,
                              "2.0": -0.0023380762737941394,
                              "2.002": -0.005090899841723055,
                              "2.05": 0.07171967398498498,
                              "3.0": 0.011119362417187239},
    #: the crossing the SEARCH-instrument fits predict.  63.99... means
    #: the fit is already nonpositive at the end of the measured ladder
    #: (the measured values there are negative too); the s = 1.0 entry is
    #: the one genuine forward prediction, at m ~ 148, and it was checked
    #: at the promotion instrument, where it does not happen.
    "search_zero_crossing": {"1.0": {"two_term": None,
                                     "three_term": 147.76062859476087},
                             "2.0": {"two_term": 64.0, "three_term": 64.0},
                             "2.002": {"two_term": 64.0,
                                       "three_term": 64.0},
                             "2.05": {"two_term": None,
                                      "three_term": None},
                             "3.0": {"two_term": None,
                                     "three_term": None}},
    #: THE DECIDING LADDER: per-pair margins at the promotion instrument
    "promote_ms": {"2.002": [2, 4, 8, 16, 24, 32, 48, 64, 96],
                   "2.0": [2, 8, 32],
                   "1.0": [2, 4, 8, 16, 32, 64]},
    "promote_margin_pp": {
        "2.002": [0.054077, 0.043691, 0.034769, 0.028416, 0.025833,
                  0.024436, 0.023015, 0.022357, 0.021884],
        "2.0": [0.055137, 0.037182, 0.027020],
        "1.0": [0.045990, 0.037022, 0.031157, 0.027549, 0.025110,
                0.023487],
    },
    "promote_limit_two_term": {"2.002": 0.023011701577476038,
                               "2.0": 0.02741502613124649,
                               "1.0": 0.024272875932679783},
    "promote_limit_three_term": {"2.002": 0.019058441136709636,
                                 "2.0": 0.021111600475529874,
                                 "1.0": 0.021920181336647103},
    "promote_zero_crossing": {"2.002": None, "2.0": None, "1.0": None},
    "verdict": ("decreasing in m at every instrument and every resonance; "
                "at the deciding instrument the decrease has a positive "
                "floor (three-term limit +0.0191 per pair at s = 2.002, "
                "+0.0211 at s = 2.0, +0.0219 at s = 1.0), all above the "
                "0.00378 per-pair residual tail, and no fit crosses "
                "zero.  The two-term fit is not conservative: m = 96 at "
                "s = 2.002 measured +0.021884, below its own +0.02339 "
                "extrapolation."),
}

def build_config(spec):
    """Rebuild a recorded near miss from its ``build`` tuple.

    ``("lattice", s_gaps, m)`` and
    ``("commensurate", s1, m1, mult, m2, off)``: the two families the
    campaign's distinct near misses come from.  Everything in
    ``CAMPAIGN_RECORD["near_misses"]`` re-scores through here, so the
    table carries no stored coordinate lists and cannot drift from the
    configurations it names.
    """
    kind = spec[0]
    if kind == "lattice":
        _, s, m = spec
        return lattice(s, 0.4999, m)
    if kind == "commensurate":
        _, s1, m1, mult, m2, off = spec
        return commensurate(s1, m1, s1 * mult, m2, 0.4999,
                            off * s1 * MEAN_GAP)
    raise ValueError(f"unknown build spec {spec!r}")


#: The controls, as data (the runs behind them are in the test file).
CONTROL_RECORD = {
    #: (a) six random starts, k = 4, 40 ES generations then the polish
    "rediscovery": {
        "k": 4, "n_starts": 6, "n_evals": 3545,
        "lattice_reference_rel_margin": 0.13493498747169005,
        "median_spacing_mean_gaps": 3.014349735588019,
        "median_depth": 0.4999,
        "median_resonance_distance": 0.014349735588019108,
        "frac_on_resonance": 1.0, "frac_in_coupled_band": 1.0,
        "frac_deep": 0.6666666666666666,
        "frac_beating_the_lattice": 0.5,
        "best_rel_margin": 0.09330923940340742,
        "per_start": [(3.0140, 0.4999, 0.093309), (3.0203, 0.4999, 0.118066),
                      (3.0147, 0.4999, 0.093455), (3.0213, 0.4999, 0.928406),
                      (3.0087, 0.3799, 0.172780), (1.9868, 0.2600, 0.157147)],
    },
    #: (b) the planted damage inflation, found at the third score every
    #: time, down to an inflation of 1.5
    "planted": [{"inflate": 1.5, "first_negative_at": 3, "n_scored": 88,
                 "n_negative": 3, "best_rel_margin": -0.5112794460938176},
                {"inflate": 2.0, "first_negative_at": 3, "n_scored": 88,
                 "n_negative": 24, "best_rel_margin": -1.3992834003739134},
                {"inflate": 3.0, "first_negative_at": 3, "n_scored": 88,
                 "n_negative": 33, "best_rel_margin": -3.859550532938048},
                {"inflate": 4.0, "first_negative_at": 3, "n_scored": 88,
                 "n_negative": 33, "best_rel_margin": -7.228657983740207}],
    #: (c) the worst find down the resolution ladder
    "resolution_ladder_at_worst": [
        (0.010, 40.0, -0.577693, -0.401436),
        (0.005, 60.0, -0.234739, -0.163119),
        (0.002, 100.0, 0.008188, 0.005690),
        (0.001, 200.0, 0.160115, 0.111263),
        (0.001, 400.0, 0.224251, 0.155831),
    ],
    #: (d) theta = 1 diverges
    "theta_one_cap": math.inf,
}


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------


def audit(quick: bool = False):
    t0 = time.time()
    print("= instrument: the fast evaluator against PaperJoint =")
    ev_x = Evaluator(tail_mode="exact")
    pj = PaperJoint(step=FAST_STEP, G=FAST_G)
    worst = 0.0
    for pairs in (lattice(2.002, 0.4999, 2), lattice(1.0, 0.3, 4),
                  two_scale(2.002, 2, 0.2, 2, 0.45)):
        a = pj.cap(pairs, THETA_FULL)["cap"]
        b = ev_x.verdict(pairs, THETA_FULL)["cap"]
        worst = max(worst, abs(a - b) / max(abs(a), 1e-30))
    print(f"  exact-tail evaluator vs PaperJoint.cap: worst relative "
          f"defect {worst:.2e}")
    ev_c = Evaluator()
    d = [(ev_c.verdict(p, THETA_FULL)["cap"]
          - pj.cap(p, THETA_FULL)["cap"])
         for p in (lattice(2.002, 0.4999, 4), lattice(1.0, 0.1, 4))]
    print(f"  conservative-tail cap minus module cap: "
          + ", ".join(f"{x:+.6f}" for x in d) + " (must be >= 0)")

    print("= the m-scaling law at the resonance (the open bridge) =")
    ms = (2, 4, 8, 16, 32) if quick else (2, 3, 4, 6, 8, 12, 16, 24, 32,
                                          48, 64)
    study = m_scaling_study(spacings=(2.002,) if quick
                            else (1.0, 2.0, 2.002, 2.05, 3.0), ms=ms)
    for s, rec in study.items():
        row = "  ".join(f"m={r['m']}:{r['margin_pp']:+.5f}"
                        for r in rec["rows"])
        fit = rec["fit"]
        f1 = fit["a+b/m"]
        f2 = fit["a+b/m+c log m/m"]
        print(f"  s={s} gaps: {row}")
        print(f"     shape {fit['shape']}; a+b/m limit "
              f"{f1['limit_a']:+.6f} (resid {f1['max_resid']:.1e}, "
              f"crossing m {f1['zero_crossing_m']}); with log term limit "
              f"{f2['limit_a']:+.6f} (resid {f2['max_resid']:.1e}, "
              f"crossing m {f2['zero_crossing_m']})")
        for nm, f in (("a+b/m", f1), ("a+b/m+c log m/m", f2)):
            if f["zero_crossing_m"] is not None:
                print(f"     !! PREDICTED CROSSING under {nm} at m = "
                      f"{f['zero_crossing_m']:.3g}, a predicted "
                      "counterexample AT THIS INSTRUMENT; the promotion "
                      "ladder below is what decides it.")

    print("= the same ladder at the promotion instrument (the one that "
          "decides) =")
    ev_p = Evaluator(step=PROMOTE_STEP, G=PROMOTE_G)
    p_ms = (2, 4, 8, 16) if quick else (2, 4, 8, 16, 32)
    for s in ((2.002,) if quick else (2.0, 2.002)):
        rows = m_ladder(s, 0.4999, p_ms, THETA_FULL, ev_p)
        fit = fit_m_law(rows)
        print(f"  s={s} gaps: "
              + "  ".join(f"m={r['m']}:{r['margin_pp']:+.5f}" for r in rows))
        print(f"     shape {fit['shape']}; a+b/m limit "
              f"{fit['a+b/m']['limit_a']:+.6f}, crossing "
              f"{fit['a+b/m']['zero_crossing_m']}; with log term "
              f"{fit['a+b/m+c log m/m']['limit_a']:+.6f}, crossing "
              f"{fit['a+b/m+c log m/m']['zero_crossing_m']}")
        print(f"     tail handicap still inside the cap at G={PROMOTE_G}: "
              f"{ev_p.tail([(0.0, 0.4999)]):.6f} per pair (the margin is "
              "nondecreasing in G, so this much is recoverable and no "
              "more)")

    print("= the adversarial campaign =")
    rec = campaign(quick=quick)
    w = rec["worst"]
    print(f"  {rec['n_evals']} evaluations in {rec['seconds']:.0f} s across "
          f"{len(rec['by_method'])} method instances")
    print(f"  configurations with margin < 0 AT THE SEARCH INSTRUMENT: "
          f"{rec['n_negative']} (first at score "
          f"{rec['first_negative_at']}); every one of them is promoted "
          "below, and the promoted number is the one that counts")
    print(f"  instrument failures (cap not finite): "
          f"{rec['n_instrument_failure']}")
    print(f"  WORST: rel margin {w['rel_margin']:+.6f}, abs margin "
          f"{w['margin']:+.6f} (budget {w['budget']:.6f}, cap "
          f"{w['cap']:.6f}), k = {len(w['pairs'])}, method {w['method']}, "
          f"completeness {w['completeness']:.3g}")
    print(f"    pairs: {[(round(t, 6), round(y, 6)) for t, y in w['pairs']]}")
    print(f"  near misses under rel {NEAR_MISS_REL}: {rec['n_near_miss']}")
    for r in rec["near_misses"][:10]:
        print(f"    rel {r['rel_margin']:+.6f} abs {r['margin']:+.6f} "
              f"k={len(r['pairs'])} [{r['method']}] "
              f"{[(round(t, 4), round(y, 4)) for t, y in r['pairs']][:6]}")

    prom = rec["promotion"]
    print(f"= promotion of the {prom['n']} worst finds (step "
          f"{PROMOTE_STEP}, G {PROMOTE_G}) =")
    print(f"  promoted margins below zero: {prom['n_negative_promoted']}; "
          f"below zero after subtracting the residual tail: "
          f"{prom['n_negative_headroom']}")
    for r in prom["rows"]:
        print(f"  k={r['k']:2d} search rel {r['search_rel_margin']:+.6f} -> "
              f"promoted rel {r['rel_margin']:+.6f}  margin "
              f"{r['margin']:+.6f}  per pair {r['margin_per_pair']:+.6f}  "
              f"headroom {r['headroom_per_pair']:+.6f}")

    print("= the worst candidate down the resolution ladder =")
    for row in resolution_ladder(w["pairs"]):
        print(f"  step {row['step']:.3f} G {row['G']:5.1f}: margin "
              f"{row['margin']:+.6f} rel {row['rel_margin']:+.6f} "
              f"(completeness {row['completeness']:.3g})")
    pr = primal_check(w["pairs"])
    print(f"  primal greedy {pr['greedy']:.6f} <= budget "
          f"{pr['budget']:.6f}: {pr['primal_within_budget']}")

    print("= the primal side (the sup over X, measured) =")
    ps = primal_sweep()
    print(f"  worst greedy / budget over the family sweep: "
          f"{ps['worst_ratio']:.4f}; all within budget: "
          f"{ps['all_within_budget']}")
    for r in sorted(ps["rows"], key=lambda r: -r["ratio"])[:5]:
        print(f"    {r['name']:32s} k={r['k']:2d} greedy {r['greedy']:8.4f} "
              f"budget {r['budget']:8.4f} ratio {r['ratio']:.4f}")

    print("= control (a): rediscovery of the binding regime =")
    rc = rediscovery_control(n_starts=3 if quick else 6, k=3,
                             iters=15 if quick else 30)
    print(f"  {len(rc['rows'])} random starts, k = {rc['k']}: median "
          f"spacing {rc['median_spacing']:.3f} mean gaps, median depth "
          f"{rc['median_depth']:.4f}; deep on {rc['frac_deep']:.0%}, in "
          f"the coupled band on {rc['frac_in_coupled_band']:.0%}, on a "
          f"resonance on {rc['frac_on_resonance']:.0%}")
    print(f"  best relative margin found {rc['best_rel_margin']:+.6f} "
          f"against the resonant-lattice reference "
          f"{rc['lattice_reference_rel_margin']:+.6f}; beat it on "
          f"{rc['frac_beating_the_lattice']:.0%} of starts")
    for r in rc["rows"]:
        print(f"    start {r['start']}: spacing "
              f"{r['median_gap_mean_gaps']:.3f} gaps, depth "
              f"{r['mean_depth']:.4f}, rel {r['rel_margin']:+.6f}")

    print("= control (b): a planted damage inflation must be found =")
    for infl in (1.5, 2.0, 4.0):
        pc_ = planted_detection_control(inflate=infl)
        print(f"  inflate {infl}: found {pc_['found']} at score "
              f"{pc_['first_negative_at']} of {pc_['n_scored']}; "
              f"{pc_['n_negative']} negatives, best rel "
              f"{pc_['best_rel_margin']:+.6f}")

    print("= control (d): theta = 1 must diverge =")
    tc = theta_one_control()
    print(f"  cap = {tc['cap']} (diverges: {tc['diverges']})")

    print("= HEADLINE =")
    if prom["n_negative_promoted"]:
        print("  A CONFIGURATION WITH A NONPOSITIVE MARGIN SURVIVED "
              "PROMOTION.  Parameters above; re-examine before reading "
              "anything else in this file.")
    else:
        print(f"  No configuration reached a nonpositive margin at the "
              f"promotion instrument in {rec['n_evals']} scored "
              f"configurations.  Worst promoted relative margin "
              f"{prom['worst']['rel_margin']:+.6f}.  This bounds the "
              "adversary from below and the quantifier not at all.")
    print(f"= total runtime {time.time() - t0:.0f} s =")
    return rec


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    audit(quick=ap.parse_args().quick)
