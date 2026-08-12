"""The negative per-pair margin at the rho argmax: instrument, or mathematics?

`truncation_bridge.py` gap (G1)/(G3) records a ladder that, read at face
value, would kill the multi-pair verdict at ``theta = 0.995``.  At the
argmax of `cluster_universal`'s rho map — the periodic pair lattice at
spacing ``s = 2.002`` mean gaps, depth ``y = 0.4999`` — the finite-cluster
per-pair margin (budget minus cap) crosses zero as the cluster grows:

    m =   2:  +0.02890      m =  24:  -0.00264   <- crosses
    m =   8:  +0.00760      m =  32:  -0.00429
    m =  16:  +0.00037      m =  64:  -0.00685

This module answers the only question that ladder poses: **is the sign
real, or is it the instrument?**  It reproduces the ladder at
`truncation_bridge`'s own settings, re-runs it up a two-dimensional
refinement ladder (grid step *and* resolved window), decomposes the cap
into the four channels that carry the m-dependence, and re-runs the
decisive configuration under ball arithmetic.

**THE ANSWER: the crossing is a property of the instrument's SETTINGS,
not of the configuration — and the decisive knob is the resolved window
``G``, not the grid step.**  At the crossing configuration itself:

    m = 24   step 0.005  G =  60:  -0.00264      (the reported number)
             step 0.002  G =  60:  +0.00195
             step 0.001  G =  60:  +0.00347
             step 0.002  G = 200:  +0.02076
             step 0.001  G = 200:  +0.02227
             step 0.001  G = 400:  +0.02587

The margin is monotone increasing under refinement in each knob
separately, at every m on the ladder.  But the two knobs are not
interchangeable, and saying so is the honest half of the answer:

  * **the grid step alone does not clear the ladder at G = 60.**  It
    moves the crossing point out — m* = 24 / 48 / 64 / beyond 64 at
    step 0.005 / 0.002 / 0.001 / 0.0005 — but at G = 60 the
    m -> infinity per-pair margin stays NEGATIVE at every step measured:
    -0.00229 at step 0.002 and -0.00079 at step 0.001
    (:func:`asymptotic_margin`, both readings of the limit agreeing in
    sign).  Anyone reading the ladder at G = 60 and refining only the
    grid would keep finding a crossing, further and further out.  At the
    reported window this instrument is at its limit for unbounded m, and
    that is stated rather than extrapolated away.
  * **the window clears it.**  At G = 120 and above no m on the ladder
    is negative, and the m -> infinity margin is +0.0134 (G = 120),
    +0.0187 (G = 200), +0.0226 (G = 400) at step 0.001, rising toward
    +0.0263 as G -> infinity.  Every G is a valid instrument — the cap
    is an upper bound at each of them and a larger G is a *smaller*
    upper bound — so widening the window is refinement, not tuning.

So the reported crossing is not a property of the configuration: the
cluster sizes it names close under refinement, and the m -> infinity
statement it suggests holds only at the window it was read at.  With the
window resolved past ~100 grid units the configuration closes at
``theta = 0.995`` at every cluster size measured, with roughly 14%
relative room at the limit (rho -> 0.856 at G = 200, 0.826 at G = 400).
The limit statements rest on the interior sequence's measured
convergence out to m = 128, not on a derived rate — a named gap below.

**WHY THE CAP RISES WITH m** — the diagnosis the ladder needs, measured
band by band (:func:`cap_split`).  The finite per-pair cap splits into
exactly four pieces, and only one of them is about the cluster:

    cap_pp(m) = interior_pp(m) + exterior_pp(m) + tail_pp(G)

  1. **interior** — the (m-1) bands sitting between the outermost pairs.
     Their per-band square completion RISES with m and saturates:
     0.0721 / 0.0848 / 0.0937 / 0.0994 / 0.1017 / 0.1029 at
     m = 2/4/8/16/24/32 (step 0.002).  This is the one genuine effect:
     an interior band of a longer cluster sees more neighbours, and at
     this commensurate spacing their damage adds rather than averaging
     away.  It converges from BELOW and its limit stays under the
     periodic instrument's own per-period number, so it cannot by itself
     push the finite cap past the infinite-lattice cap.
  2. **exterior** — the 18 bands of the two far fields inside the
     window (9 per side at G = 60, 31 per side at G = 200).  Their total
     is nearly m-independent, so per pair they decay like 1/m:
     0.0546 / 0.0302 / 0.0160 / 0.0082 / 0.0055 / 0.0042.
  3. **tail** — `paper_joint.PaperJoint.tail`, the closed-form majorant
     for the bands beyond the window.  It is charged PER PAIR and is
     exactly independent of m and of the grid step:

         tail_pp(G) = 8 (c_im(y)/A)^2 (1/G^2 + 1/(P G)),

     = 0.027096 at G = 60, 0.012918 at G = 120, 0.007599 at G = 200,
     0.003743 at G = 400.  At G = 60 that single term is 20.9% of
     ``b_inf = 0.129891``, and it is larger than the whole reported
     deficit at every m on the ladder.  The periodic instrument
     (`cluster_universal.periodic_cap`) pays NO tail: one period covers
     everything.  So the two caps compared in (G1) are not the same
     functional, and the difference is dominated by a term the periodic
     side does not carry at all.
  4. **the step channel**, inside 1 and 2: the band height is
     ``F = max f + max|f'| * step`` and the square completion is
     superlinear in F, ``(F + cK)^2/(4 c K)`` with ``c = 1-theta``, so a
     slope margin measured at ``0.319 * step`` (linear to three digits
     over step 0.005 -> 0.001) on ``F ~ 0.040`` is amplified by
     ``d comp/dF ~ 4.8``.  Measured at m = 32: the interior F falls
     0.041019 -> 0.040061 -> 0.039742 at step 0.005 -> 0.002 -> 0.001,
     and the per-pair interior cap falls 0.10418 -> 0.09968 -> 0.09819
     with it.  ``K_of`` also deflates by ``(L1/A) * step``, a much
     smaller effect (~0.3% of K at step 0.005).

So the m-dependence of (G1) is channel 1 (real, bounded, saturating at
0.10592 against the periodic instrument's 0.12062 at the same step)
riding on top of channels 3 and 4 (settings, removable), and the
reported crossing is what you get when the removable part is left at
0.005/60.  The whole reported deficit at m = 64, -0.00685, is smaller
than the tail channel alone.

**BALL ARITHMETIC.**  Channels 3 and 4 are exactly what a float
instrument's discretization hides, so the decisive configuration is
re-run with `hardened_paper`'s acb machinery (:class:`HardenedCluster`):
an interval cover of the window, band heights as UPPER endpoints of the
enclosure over each cell (no slope margin is owed to a cover), the
repulsion floor as a LOWER endpoint, the budget as a ball.  At
``theta = 0.995``, 128 bits, coarse cover 0.02 (:data:`HARDENED_RECORD`):

     m    G   fine   cap_up_pp    margin_lo_pp   decided
     8   60  0.002   0.1232704      +0.0136469   yes
    24   60  0.002   0.1281915      +0.0038218   yes
    24  200  0.002   0.1093634      +0.0226499   yes
    64   60  0.002   0.1302901      -0.0002108   NO
    64   60  0.001   0.1297343      +0.0003450   yes
    64  200  0.002   0.1110532      +0.0190261   yes

``margin_lo_pp`` is one-sided (budget LOWER endpoint minus cap UPPER
endpoint), so a positive value is a closure at that instrument and a
negative one means the cover did not decide it.  Two readings matter:

  * the ball instrument decides POSITIVE, at the reported window, the
    very cluster the coarse float instrument reported at -0.00264;
  * at ``m = 64``, ``G = 60`` it comes back **undecided at cover 0.002**
    and positive at cover 0.001 — the honest shape of a case sitting on
    the boundary, and the same shape the float readings show there
    (-0.00057 at step 0.001, +0.00019 at step 0.0005).  It is recorded
    as undecided, not resolved.

The budget ball is width ~1e-35 and the float budget lands 6 ulp outside
it — the float instrument's own accumulation error, reported rather than
absorbed (:func:`hardened_brackets_float`).

**WHAT THIS DOES NOT SAY**, in four named gaps:

  (N1) It does not close `truncation_bridge`'s gap (G1).  There is still
       no DERIVED finite-size estimate on the cap side — the four
       channels above are measured, and channel 1's saturation is an
       observed convergence out to m = 128, not a rate with a constant.
       Gap (G2) (m checked on a ladder, not exhaustively) is untouched.
  (N2) The m -> infinity readings are extrapolations of a measured
       sequence.  They are reported in two directions (optimistic =
       largest m measured, pessimistic = ``c - a/m`` on the last two)
       and only used where both agree in sign.
  (N3) At the reported window G = 60 the instrument genuinely does not
       close unbounded clusters at this configuration, at any grid step
       measured.  That is a statement about the instrument at G = 60,
       since the cap at every G is an upper bound and G = 200 is a
       tighter one; but it is not softened here.
  (N4) The ball-arithmetic pass covers m = 8, 24 and 64 at two windows,
       not the whole ladder, and one of its six rows is undecided.

What is withdrawn is only the reading that the ladder exhibits a failure
of the ``theta = 0.995`` verdict at this configuration.  Nothing here
computes a proportion and nothing here is evidence about RH.

Run ``.venv/bin/python hunts/frontier_math/negative_margin_probe.py``
(~20 min; ``--quick`` is ~5 min and skips the ball-arithmetic pass, the
two finest grids and the widest windows).  The m = 64 hardened rows are
pinned rather than re-run there — 3 to 6 minutes each.
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import MEAN_GAP  # noqa: E402
from paper_joint import PaperJoint  # noqa: E402
from joint_universal import THETA_FULL  # noqa: E402
from cluster_universal import b_infty, periodic_cap  # noqa: E402

# ---------------------------------------------------------------------------
# the configuration under test, and the instrument that reported the crossing
# ---------------------------------------------------------------------------

#: the argmax of `cluster_universal.rho_map`: spacing in mean gaps.
S_GAPS = 2.002
#: the depth there (the map's sup is approached as y -> 1/2).
Y = 0.4999
#: the retention under test.
THETA = THETA_FULL

#: the settings `truncation_bridge.small_m_ladder` and
#: `truncation_bridge.cap_side_probe` run at: ``PaperJoint(step=0.005,
#: G=60.0)``.  Both are far from `paper_joint.PaperJoint`'s own defaults
#: (step 0.001, G 200.0) — that difference is the whole finding.
BRIDGE_STEP = 0.005
BRIDGE_G = 60.0

#: the ladder as `truncation_bridge` computes it, per pair, reproduced
#: here to the last recorded digit (:func:`reproduce_bridge_ladder`).
BRIDGE_LADDER = {
    2: 0.028900985079485048,
    4: 0.017514869424866367,
    8: 0.007601544487238376,
    16: 0.00036722098515831747,
    24: -0.0026433528095678636,
    32: -0.004294739356383498,
    48: -0.006018585845244377,
    64: -0.00684659255326997,
}

#: the same ladder's per-pair caps, for the (G1) comparison.
BRIDGE_CAPS = {
    2: 0.1212529569243935,
    4: 0.12486353653714923,
    8: 0.12931571800511438,
    16: 0.13302790013806132,
    24: 0.1346566475821566,
    32: 0.1355613311490062,
    48: 0.13649889110361105,
    64: 0.13692590440837746,
}

#: the closed-form per-pair budget of the infinite lattice here.
B_INF = 0.12989108051851783


def config_pairs(m: int, s_gaps: float = S_GAPS, y: float = Y):
    """The configuration: ``m`` pairs on a lattice of spacing ``s_gaps``
    mean gaps at depth ``y``."""
    s = s_gaps * MEAN_GAP
    return [(j * s, y) for j in range(m)]


# ---------------------------------------------------------------------------
# 1. reproduction, at the instrument's own settings
# ---------------------------------------------------------------------------


def ladder(ms=(2, 4, 8, 16, 24, 32, 48, 64), step: float = BRIDGE_STEP,
           G: float = BRIDGE_G, theta: float = THETA,
           s_gaps: float = S_GAPS, y: float = Y) -> dict:
    """Per-pair budget / cap / margin at a ladder of cluster sizes.

    The instrument is `paper_joint.PaperJoint` unchanged; only ``step``
    and ``G`` move.  ``step`` is the field grid, ``G`` the half-window
    resolved beyond the outermost pair (everything past it is charged to
    the closed-form tail).
    """
    pj = PaperJoint(step=step, G=G)
    rows = []
    for m in ms:
        rec = pj.verdict(config_pairs(m, s_gaps, y), theta)
        rows.append({"m": m, "step": step, "G": G,
                     "budget_pp": rec["budget"] / m,
                     "cap_pp": rec["cap"] / m,
                     "margin_pp": rec["margin"] / m,
                     "delta": rec["delta"], "cells": rec["cells"]})
    return {"step": step, "G": G, "theta": theta, "rows": rows,
            "crossing_m": crossing_m(rows),
            "min_margin_pp": min(r["margin_pp"] for r in rows)}


def crossing_m(rows) -> int | None:
    """The smallest ``m`` on the ladder whose per-pair margin is < 0, or
    ``None`` if the ladder never crosses."""
    for r in sorted(rows, key=lambda r: r["m"]):
        if r["margin_pp"] < 0:
            return r["m"]
    return None


def reproduce_bridge_ladder(tol: float = 1e-12) -> dict:
    """Re-run of the exact ladder `truncation_bridge` reports.

    Settings are stated rather than inherited: ``step = 0.005``,
    ``G = 60.0``, ``theta = 0.995``, no slicing, delta ladder
    ``(0.5, 1.0, 2.0, 3.0)`` (`PaperJoint`'s default), pairs
    ``{(j s, y)}`` with ``s = 2.002 * 2 pi`` and ``y = 0.4999``.
    """
    lad = ladder(tuple(sorted(BRIDGE_LADDER)), BRIDGE_STEP, BRIDGE_G)
    worst = 0.0
    for r in lad["rows"]:
        worst = max(worst, abs(r["margin_pp"] - BRIDGE_LADDER[r["m"]]))
    return {"worst_abs_defect": worst, "matches": worst <= tol,
            "crossing_m": lad["crossing_m"], "rows": lad["rows"]}


# ---------------------------------------------------------------------------
# 2. the refinement ladder, in both knobs
# ---------------------------------------------------------------------------

#: grid steps, coarse to fine.
STEPS = (0.005, 0.002, 0.001, 0.0005)
#: resolved half-windows, narrow to wide.
GS = (30.0, 60.0, 120.0, 200.0, 400.0)
#: cluster sizes.
MS = (2, 4, 8, 16, 24, 32, 48, 64)

#: every (m, step, G) actually run for the report, per-pair margin.
#: Reproduced by :func:`refinement_table`; pinned so a reader can check
#: the trend without paying the ~40 min the full grid costs.
REFINEMENT_RECORD = {
    # (m, step, G): margin_pp
    (16, 0.002, 30.0): -0.026431173146730907,
    (24, 0.002, 30.0): -0.02960025377885948,
    (32, 0.002, 30.0): -0.03134109552066969,
    (2, 0.0005, 60.0): 0.03420011533986986,
    (4, 0.0005, 60.0): 0.02341485211531745,
    (8, 0.0005, 60.0): 0.013976109899897823,
    (16, 0.0005, 60.0): 0.007080011289120114,
    (24, 0.0005, 60.0): 0.004206903534036299,
    (32, 0.0005, 60.0): 0.0026269233634965417,
    (48, 0.0005, 60.0): 0.0009827587774794237,
    (64, 0.0005, 60.0): 0.00019099886711163028,
    (2, 0.001, 60.0): 0.03362677335498232,
    (4, 0.001, 60.0): 0.022778322177948243,
    (8, 0.001, 60.0): 0.013287376214109178,
    (16, 0.001, 60.0): 0.006354599316403781,
    (24, 0.001, 60.0): 0.0034671422779467,
    (32, 0.001, 60.0): 0.0018790897012354868,
    (48, 0.001, 60.0): 0.00022662780835260485,
    (64, 0.001, 60.0): -0.000568650433838247,
    (2, 0.002, 60.0): 0.03245230587477088,
    (4, 0.002, 60.0): 0.021474041658085377,
    (8, 0.002, 60.0): 0.011876212671358022,
    (16, 0.002, 60.0): 0.004869850236339901,
    (24, 0.002, 60.0): 0.0019508288722369094,
    (32, 0.002, 60.0): 0.00034543322606794824,
    (48, 0.002, 60.0): -0.001324933091359189,
    (64, 0.002, 60.0): -0.002128398251412783,
    (2, 0.005, 60.0): 0.028900985079485048,
    (4, 0.005, 60.0): 0.017514869424866367,
    (8, 0.005, 60.0): 0.007601544487238376,
    (16, 0.005, 60.0): 0.00036722098515831747,
    (24, 0.005, 60.0): -0.0026433528095678636,
    (32, 0.005, 60.0): -0.004294739356383498,
    (48, 0.005, 60.0): -0.006018585845244377,
    (64, 0.005, 60.0): -0.00684659255326997,
    (16, 0.002, 120.0): 0.018455430489354066,
    (24, 0.002, 120.0): 0.015704595860522346,
    (32, 0.002, 120.0): 0.01419788522842294,
    (2, 0.0005, 200.0): 0.051383476672655165,
    (8, 0.0005, 200.0): 0.03207479305027873,
    (16, 0.0005, 200.0): 0.025661281782010464,
    (24, 0.0005, 200.0): 0.023028384861613682,
    (32, 0.0005, 200.0): 0.021593695155821768,
    (2, 0.001, 200.0): 0.050792840929372515,
    (8, 0.001, 200.0): 0.03136901813874435,
    (16, 0.001, 200.0): 0.024919233644701208,
    (24, 0.001, 200.0): 0.022272253355447264,
    (32, 0.001, 200.0): 0.02082966549851141,
    (48, 0.001, 200.0): 0.019346070056952897,
    (64, 0.001, 200.0): 0.018646675270386368,
    (16, 0.002, 200.0): 0.02343875865435295,
    (24, 0.002, 200.0): 0.020761763496646712,
    (32, 0.002, 200.0): 0.019302745469047103,
    (16, 0.001, 400.0): 0.028451847672100475,
    (24, 0.001, 400.0): 0.025868631659751895,
    (32, 0.001, 400.0): 0.02447180140360103,
}


def refinement_table(ms=MS, steps=STEPS, G: float = BRIDGE_G,
                     theta: float = THETA) -> dict:
    """The ladder re-run at each grid step, window fixed."""
    cols = {}
    for step in steps:
        cols[step] = ladder(ms, step, G, theta)
    return {"G": G, "columns": cols,
            "crossings": {s: cols[s]["crossing_m"] for s in steps}}


def window_table(ms=(16, 24, 32), Gs=(30.0, 60.0, 120.0, 200.0),
                 step: float = 0.002, theta: float = THETA) -> dict:
    """The ladder re-run at each resolved window, grid step fixed."""
    cols = {}
    for G in Gs:
        cols[G] = ladder(ms, step, G, theta)
    return {"step": step, "columns": cols,
            "crossings": {G: cols[G]["crossing_m"] for G in Gs}}


def monotone_in_step(m: int, steps=STEPS, G: float = BRIDGE_G,
                     theta: float = THETA) -> dict:
    """Is the per-pair margin monotone increasing as the grid refines?

    The direction is the claim: a coarser grid inflates the cap (band
    heights carry a ``slope * step`` margin, the repulsion floor carries
    a ``-(L1/A) * step`` deflation), so refinement can only move the
    margin UP.  Measured, not assumed.
    """
    pj_rows = [{"step": s,
                "margin_pp": ladder((m,), s, G, theta)["rows"][0]["margin_pp"]}
               for s in sorted(steps, reverse=True)]
    inc = all(pj_rows[i + 1]["margin_pp"] > pj_rows[i]["margin_pp"]
              for i in range(len(pj_rows) - 1))
    return {"m": m, "G": G, "rows": pj_rows, "increasing_as_step_falls": inc,
            "total_move": pj_rows[-1]["margin_pp"] - pj_rows[0]["margin_pp"]}


def monotone_in_window(m: int, Gs=(30.0, 60.0, 120.0, 200.0),
                       step: float = 0.002, theta: float = THETA) -> dict:
    """Same question for the resolved window: wider window, larger margin."""
    rows = [{"G": G,
             "margin_pp": ladder((m,), step, G, theta)["rows"][0]["margin_pp"]}
            for G in sorted(Gs)]
    inc = all(rows[i + 1]["margin_pp"] > rows[i]["margin_pp"]
              for i in range(len(rows) - 1))
    return {"m": m, "step": step, "rows": rows,
            "increasing_as_window_grows": inc,
            "total_move": rows[-1]["margin_pp"] - rows[0]["margin_pp"]}


# ---------------------------------------------------------------------------
# 3. the diagnosis: where the cap's m-dependence lives
# ---------------------------------------------------------------------------


def tail_per_pair(G: float = BRIDGE_G, y: float = Y) -> float:
    """``PaperJoint.tail`` divided by the number of pairs — a closed form.

    ``2 * 4 (c_im(y)/A)^2 (1/G^2 + 1/(P G))`` with ``P`` the band-period
    lower bound: the same number for every pair and every cluster size,
    and independent of the grid step.  This is the term the periodic
    instrument does not pay at all.
    """
    pj = PaperJoint(step=0.002, G=G)
    return pj.tail([(0.0, y)])


def cap_split(m: int, step: float = BRIDGE_STEP, G: float = BRIDGE_G,
              theta: float = THETA, s_gaps: float = S_GAPS,
              y: float = Y) -> dict:
    """The finite cap, band by band, split into its four channels.

    Reproduces `PaperJoint.cap` exactly (same delta ladder, same
    per-cell square completion, same one-sided drop of cross-cell
    charges) while bucketing each band's contribution by whether its
    centre lies BETWEEN the outermost pairs (interior) or beyond them
    (exterior), and reporting the tail separately.
    """
    pairs = config_pairs(m, s_gaps, y)
    pj = PaperJoint(step=step, G=G)
    c = 1 - theta
    lo_c, hi_c = pairs[0][0], pairs[-1][0]
    bands = pj.bands(pairs)
    best = None
    for delta in pj.delta_choices:
        inte = ext = 0.0
        n_int = n_ext = 0
        ok = True
        for lo, hi, F in bands:
            n = max(1, int(math.ceil((hi - lo) / delta)))
            w = (hi - lo) / n
            K = pj.K_of(w)
            if K <= 0:
                ok = False
                break
            comp = 0.0
            for _ in range(n):
                comp += F if F <= 2 * c * K else (F + c * K) ** 2 / (4 * c * K)
            if lo_c - 1e-9 <= (lo + hi) / 2 <= hi_c + 1e-9:
                inte += comp
                n_int += 1
            else:
                ext += comp
                n_ext += 1
        if ok and (best is None or inte + ext < best[0] + best[1]):
            best = (inte, ext, delta, n_int, n_ext)
    if best is None:
        raise RuntimeError("no admissible cell width on the ladder")
    inte, ext, delta, n_int, n_ext = best
    tail = pj.tail(pairs)
    off = pj.off_band_allowance(pairs)
    F_int = [F for lo, hi, F in bands
             if lo_c - 1e-9 <= (lo + hi) / 2 <= hi_c + 1e-9]
    w_int = [hi - lo for lo, hi, _ in bands
             if lo_c - 1e-9 <= (lo + hi) / 2 <= hi_c + 1e-9]
    return {"m": m, "step": step, "G": G, "delta": delta,
            "n_interior": n_int, "n_exterior": n_ext,
            "interior_pp": inte / m, "exterior_pp": ext / m,
            "tail_pp": tail / m,
            "interior_per_band": inte / n_int if n_int else math.nan,
            "cap_pp": (inte + ext + tail + off) / m,
            "off_band_allowance": off,
            "F_interior_max": max(F_int) if F_int else math.nan,
            "w_interior_mean": float(np.mean(w_int)) if w_int else math.nan}


#: the diagnosis, pinned: per-interior-band square completion at
#: step 0.002, G = 60 (the interior channel is independent of G).
INTERIOR_PER_BAND = {
    2: 0.07204638964581603,
    4: 0.08481122484045568,
    8: 0.09366949056902449,
    16: 0.09941862972965118,
    24: 0.10167919798877852,
    32: 0.10289025789921338,
}

#: the exterior channel's TOTAL (not per pair) at step 0.002, G = 60 —
#: nearly m-independent, hence 1/m per pair.
EXTERIOR_TOTAL = {
    2: 0.10916418233247142,
    4: 0.12079838213449795,
    8: 0.12787116346507496,
    16: 0.1315832860058846,
    24: 0.1325652245074035,
    32: 0.13279587477529198,
}

#: the tail channel, per pair, at three windows (step-independent).
TAIL_PER_PAIR = {60.0: 0.02709635013996395,
                 120.0: 0.012917571988664299,
                 200.0: 0.007599198453682338,
                 400.0: 0.0037428449495225786}


def partition_and_multiplicity(m: int, step: float = 0.002,
                               G: float = BRIDGE_G) -> dict:
    """The two rival explanations for the cap's m-dependence, as numbers.

    Candidate (i), *the finite cluster's band partition differs from the
    periodic one — more, narrower bands at the ends*: reported as the
    band count per pair and the interior width statistics against the
    periodic instrument's single period.  Measured, it goes the WRONG
    way for the story: bands per pair FALL with m (``1 + 17/m`` at
    G = 60), and the interior widths are narrower than the periodic
    band, not wider — a narrower cell has a HIGHER repulsion floor K and
    so a cheaper completion.

    Candidate (ii), *the square-completion multiplicity m* rises with
    cluster size*: reported as ``max_band (F + cK)/(2 c K)``, the
    optimiser of ``max_k [k F - c k(k-1) K]``.  It does rise, but only
    from 4 to 5 over m = 2 -> 32, and it rises BECAUSE F rises — it is
    downstream of channel 1, not a separate channel.
    """
    pj = PaperJoint(step=step, G=G)
    pairs = config_pairs(m)
    c = 1 - THETA
    lo_c, hi_c = pairs[0][0], pairs[-1][0]
    bands = pj.bands(pairs)
    widths, mstars, Fs = [], [], []
    for lo, hi, F in bands:
        K = pj.K_of(hi - lo)
        mstars.append((F + c * K) / (2 * c * K))
        if lo_c - 1e-9 <= (lo + hi) / 2 <= hi_c + 1e-9:
            widths.append(hi - lo)
            Fs.append(F)
    per = periodic_cap(S_GAPS * MEAN_GAP, Y, THETA, step)
    return {"m": m, "step": step, "G": G, "n_bands": len(bands),
            "bands_per_pair": len(bands) / m,
            "interior_width_min": min(widths), "interior_width_max": max(widths),
            "periodic_width": per["widths"][0], "periodic_bands": per["bands"],
            "m_star_max": max(mstars), "interior_F_max": max(Fs)}


def interior_saturates(ms=(2, 4, 8, 16, 24, 32), step: float = 0.002,
                       G: float = BRIDGE_G) -> dict:
    """The one genuine channel, measured: does the per-interior-band cap
    keep rising, or does it saturate below the periodic instrument's
    per-period cap?

    Reports the sequence, its increments, and a Richardson-style
    ``c_inf - a/m`` extrapolation of the limit.  The comparison number is
    `cluster_universal.periodic_cap` at the same grid step.
    """
    rows = [cap_split(m, step, G) for m in ms]
    seq = [(r["m"], r["interior_per_band"]) for r in rows]
    incs = [seq[i + 1][1] - seq[i][1] for i in range(len(seq) - 1)]
    (m1, v1), (m2, v2) = seq[-2], seq[-1]
    # v(m) = c - a/m  =>  c = (m2 v2 - m1 v1)/(m2 - m1)
    c_extrap = (m2 * v2 - m1 * v1) / (m2 - m1)
    per = periodic_cap(S_GAPS * MEAN_GAP, Y, THETA, step)
    return {"sequence": seq, "increments": incs, "rising": all(i > 0 for i in incs),
            "decelerating": all(incs[i + 1] < incs[i] for i in range(len(incs) - 1)),
            "extrapolated_limit": c_extrap,
            "periodic_cap": per["cap"], "periodic_bands": per["bands"],
            "below_periodic": c_extrap < per["cap"]}


#: per-interior-band square completion at large cluster size, measured
#: with the cheap window ``G = 20``.  The interior channel is window-free
#: up to where the field grid starts: G = 60 against G = 200 agree to
#: 6e-12 relative, while G = 20 against G = 60 differ by 1.8e-5 absolute
#: (the arange origin moves the sample points inside the bands).  That
#: 1.8e-5 is a stated systematic on the limit below, two orders under the
#: 1e-3 scale of the margins it feeds.  This is the sequence the
#: m -> infinity statement rests on.
INTERIOR_LARGE_M = {
    0.002: {8: 0.09365164235639116, 16: 0.09939941831298756,
            32: 0.1028702226251831, 64: 0.10466625094827237,
            96: 0.10508422670715843},
    0.001: {8: 0.09226702081880704, 16: 0.09794050928696033,
            32: 0.10136402347169467, 64: 0.10313541576627594,
            96: 0.10354605001086237, 128: 0.10357991744229264},
}


def large_m_interior(ms=(8, 16, 32, 64), step: float = 0.002,
                     G: float = 20.0) -> dict:
    """Per-interior-band completion at large m, cheaply.

    Only the interior channel is wanted, and it does not depend on the
    resolved window, so this runs at ``G = 20`` and skips the off-band
    allowance recomputation that :func:`cap_split` pays.
    """
    pj = PaperJoint(step=step, G=G)
    c = 1 - THETA
    out = {}
    for m in ms:
        pairs = config_pairs(m)
        lo_c, hi_c = pairs[0][0], pairs[-1][0]
        total, n = 0.0, 0
        for lo, hi, F in pj.bands(pairs):
            if not (lo_c - 1e-9 <= (lo + hi) / 2 <= hi_c + 1e-9):
                continue
            K = pj.K_of(hi - lo)
            total += F if F <= 2 * c * K else (F + c * K) ** 2 / (4 * c * K)
            n += 1
        out[m] = total / n
    return out


def interior_limit(seq: dict) -> dict:
    """Two readings of ``lim_m c_band(m)`` from a measured sequence.

    ``last`` is the largest m actually measured — a LOWER bound on the
    limit, since the sequence is measured increasing, hence an
    optimistic reading of the margin.  ``richardson`` is ``c`` from
    ``v(m) = c - a/m`` on the two largest m; the measured increments
    collapse faster than ``1/m`` (3.4e-5 from m = 96 to 128 at step
    0.001, against 4.1e-4 from 64 to 96), so that reading OVERSHOOTS and
    is the pessimistic one.  Both are reported; neither is called the
    answer, and the sequence's convergence is measured to m = 128 rather
    than derived — a named gap, not a derivation of a limit.
    """
    ms = sorted(seq)
    m1, m2 = ms[-2], ms[-1]
    return {"last_m": m2, "last": seq[m2],
            "last_increment": seq[m2] - seq[m1],
            "richardson": (m2 * seq[m2] - m1 * seq[m1]) / (m2 - m1)}


def asymptotic_margin(step: float = 0.002, G: float = BRIDGE_G,
                      seq: dict | None = None) -> dict:
    """The m -> infinity per-pair margin at a given instrument setting.

    ``cap_pp(m) = (1 - 1/m) c_band(m) + exterior_total/m + tail_pp(G)``,
    and both m-dependent pieces are measured to converge, so

        margin_pp(infinity) = b_inf - c_band(infinity) - tail_pp(G).

    This is what decides whether a ladder crosses at SOME m rather than
    at whichever m happen to be on it.  At ``G = 60`` the answer is
    negative at both readings and at every grid step measured — the
    reported window cannot close arbitrarily large clusters here — and
    at ``G >= 120`` it is positive at both readings with room.
    """
    seq = seq or INTERIOR_LARGE_M.get(step) or large_m_interior(step=step)
    lim = interior_limit(seq)
    tail = tail_per_pair(G)
    opt = B_INF - lim["last"] - tail
    pess = B_INF - lim["richardson"] - tail
    return {"step": step, "G": G, "interior": lim, "tail_pp": tail,
            "b_inf": B_INF, "margin_pp_optimistic": opt,
            "margin_pp_pessimistic": pess,
            "closes_for_all_m": pess > 0,
            "sign_agrees": (opt > 0) == (pess > 0)}


def channel_budget(m: int = 24, step: float = BRIDGE_STEP,
                   G: float = BRIDGE_G) -> dict:
    """The whole deficit at the reported settings, attributed.

    Compares ``cap_pp`` at (step, G) with ``cap_pp`` at the refined
    corner and names how much of the difference each knob carries, by
    moving one knob at a time.
    """
    base = cap_split(m, step, G)
    fine_step = cap_split(m, 0.001, G)
    wide_G = cap_split(m, step, 200.0)
    both = cap_split(m, 0.001, 200.0)
    return {"m": m, "cap_pp_base": base["cap_pp"],
            "cap_pp_fine_step": fine_step["cap_pp"],
            "cap_pp_wide_window": wide_G["cap_pp"],
            "cap_pp_both": both["cap_pp"],
            "step_channel": base["cap_pp"] - fine_step["cap_pp"],
            "window_channel": base["cap_pp"] - wide_G["cap_pp"],
            "b_inf": b_infty(S_GAPS * MEAN_GAP, Y),
            "margin_pp_both": (ladder((m,), 0.001, 200.0)["rows"][0]
                               ["margin_pp"])}


# ---------------------------------------------------------------------------
# 4. the same configuration under ball arithmetic
# ---------------------------------------------------------------------------

#: the ball instrument's settings, named because an enclosure without
#: its cover is not a statement.
HARDENED_INSTRUMENT = {"coarse": 0.02, "fine": 0.002, "k_step": 0.002,
                       "theta": 0.995, "prec_bits": 128}

#: the hardened readings, ``(m, G) -> record``.  ``margin_lo_pp`` is
#: ONE-SIDED (budget lower endpoint minus cap upper endpoint), so a
#: positive value is a closure at that instrument and a negative one is
#: "this cover does not decide it" — NOT a failure of the configuration.
#: Reproduced by :func:`hardened_margin`; a row costs 6 s to 6 min.
HARDENED_RECORD = {
    (8, 60.0, 0.002): {"cap_up_pp": 0.12327036236937076,
     "margin_lo_pp": 0.013646900122982128,
     "decided": True, "bands": 25, "m_star": 4, "secs": 6},
    (24, 60.0, 0.002): {"cap_up_pp": 0.1281915265438082,
     "margin_lo_pp": 0.0038217682287813117,
     "decided": True, "bands": 41, "m_star": 5, "secs": 29},
    (24, 200.0, 0.002): {"cap_up_pp": 0.10936343681620612,
     "margin_lo_pp": 0.022649857956383374,
     "decided": True, "bands": 85, "m_star": 5, "secs": 54},
    (64, 60.0, 0.002): {"cap_up_pp": 0.13029011934228152,
     "margin_lo_pp": -0.00021080748717425268,
     "decided": False, "bands": 81, "m_star": 5, "secs": 152},
    (64, 60.0, 0.001): {"cap_up_pp": 0.12973428450168847,
     "margin_lo_pp": 0.000345027353418792,
     "decided": True, "bands": 81, "m_star": 5, "secs": 218},
    (64, 200.0, 0.002): {"cap_up_pp": 0.11105321258565679,
     "margin_lo_pp": 0.01902609926945048,
     "decided": True, "bands": 125, "m_star": 5, "secs": 220},
}


@dataclass(frozen=True)
class HardenedCluster:
    """`paper_joint.PaperJoint`'s cap for a finite cluster, every step a ball.

    The float instrument grants a Lipschitz margin (``F = max f over grid
    points + max|f'| * step``) because a point grid cannot see between
    its points.  An interval cover can: each cell's enclosure covers the
    continuum inside it, so the band height is simply the UPPER endpoint
    and no margin is owed.  That is the whole reason the hardened cap can
    be SMALLER than the float one at a comparable resolution.

    Directions, all one-sided against the defender: band heights up,
    repulsion floor down, budget down, tail up, square completion
    inflated by ``infl``.  Off-band cells are those whose enclosure has a
    nonpositive upper endpoint, i.e. ``f <= 0`` throughout the cell, so
    the off-band allowance is exactly 0 by construction.
    """

    #: coarse interval cover: locates band candidates, carries the
    #: off-band statement.
    coarse: float = 0.02
    #: fine cover inside each candidate: band edges and heights.
    fine: float = 0.002
    #: cover step for the same-band repulsion floor.
    k_step: float = 0.002
    #: resolved half-window beyond the outermost pair.
    G: float = 200.0
    #: sub-cell width ladder inside bands (grid units).
    deltas: tuple = (0.5, 1.0, 2.0, 3.0)
    #: inflation covering the double-precision square completion.
    infl: float = 1.0 + 1e-9
    #: cell-radius inflation.  Cell midpoints are floats, so consecutive
    #: midpoints can differ from the nominal spacing by a couple of ulp
    #: and two nominally adjacent balls can fail to meet by ~4e-13.  A
    #: cover with a gap is not a cover, so every radius is widened by
    #: this factor (1e-8 absolute at the coarse cells, ~1e-9 at the fine
    #: ones) — six orders above the ulp scale of the midpoints and small
    #: enough that the band heights move by ~3e-9.
    overlap: float = 1.0 + 1e-6

    _cache: dict = field(default_factory=dict, repr=False, compare=False)

    # -- the joint field, as an enclosure -----------------------------------

    def f_cell_up(self, mid: float, rad: float, pairs) -> float:
        """UPPER endpoint of the JOINT ``f = -sum_r 4 q_r / A^2`` over
        ``[mid-rad, mid+rad]`` — the positive part is taken of the sum,
        never of the summands (`paper_joint`'s first discipline)."""
        from flint import acb, arb  # local: the module must import w/o flint
        from hardened_paper import A_BALL, f_up, phipap_ball

        r = rad * self.overlap
        tot = arb(0)
        for t, y in pairs:
            v = phipap_ball(acb(arb(mid - t, r), arb(y)))
            tot = tot - 4 * (v.real * v.real - v.imag * v.imag)
        return f_up(tot / (A_BALL * A_BALL))

    def bands(self, pairs) -> list:
        """[(lo, hi, F_up)] over the resolved window, from a two-pass
        interval cover.  Raises if a band reaches a padded edge."""
        key = ("bands", tuple(pairs))
        if key in self._cache:
            return self._cache[key]
        lo_w = min(t for t, _ in pairs) - self.G
        hi_w = max(t for t, _ in pairs) + self.G
        n = int(math.ceil((hi_w - lo_w) / self.coarse))
        r = self.coarse / 2
        flagged = [i for i in range(n)
                   if self.f_cell_up(lo_w + (i + 0.5) * self.coarse, r,
                                     pairs) > 0.0]
        runs = []
        for i in flagged:
            if runs and i - runs[-1][1] <= 2:
                runs[-1][1] = i
            else:
                runs.append([i, i])
        bands = []
        rf = self.fine / 2
        for i0, i1 in runs:
            lo = lo_w + (i0 - 1) * self.coarse
            hi = lo_w + (i1 + 2) * self.coarse
            k = int(math.ceil((hi - lo) / self.fine))
            on = []
            for j in range(k):
                fu = self.f_cell_up(lo + (j + 0.5) * self.fine, rf, pairs)
                on.append(fu if fu > 0.0 else None)
            idx = [j for j, v in enumerate(on) if v is not None]
            if not idx:
                continue
            if idx[0] == 0 or idx[-1] == k - 1:
                raise AssertionError(
                    "a band reached the padded window edge; widen the padding")
            groups = []
            for j in idx:
                if groups and j - groups[-1][-1] == 1:
                    groups[-1].append(j)
                else:
                    groups.append([j])
            for gr in groups:
                bands.append((lo + gr[0] * self.fine,
                              lo + (gr[-1] + 1) * self.fine,
                              max(on[j] for j in gr)))
        self._cache[key] = bands
        return bands

    # -- the pieces of the cap ----------------------------------------------

    def K_lo(self, width: float) -> float:
        """LOWER endpoint of ``min omega^2`` over ``[0, width]``, width
        rounded UP to whole cover cells (reused from `hardened_paper`)."""
        from hardened_paper import HardenedPaper

        key = ("hp", self.k_step, self.G, self.coarse, self.fine)
        hp = self._cache.get(key)
        if hp is None:
            hp = HardenedPaper(coarse=self.coarse, fine=self.fine,
                               k_step=self.k_step, G=self.G)
            self._cache[key] = hp
        return hp.band_charge_lo(width)

    def tail_up(self, pairs) -> float:
        """UPPER bound on the band damage beyond the window, charged per
        pair and per side exactly as `PaperJoint.tail` does."""
        from hardened_paper import HardenedPaper

        key = ("hp", self.k_step, self.G, self.coarse, self.fine)
        hp = self._cache.get(key)
        if hp is None:
            hp = HardenedPaper(coarse=self.coarse, fine=self.fine,
                               k_step=self.k_step, G=self.G)
            self._cache[key] = hp
        return sum(2 * hp.tail_up(y) for _, y in pairs)

    def cap_up(self, pairs, theta: float) -> dict:
        """UPPER bound on the joint adversary's value for this cluster."""
        c = 1 - theta
        if c <= 0:
            return {"cap": math.inf, "delta": None, "bands": None,
                    "m_star": None}
        bs = self.bands(pairs)
        if not bs:
            return {"cap": 0.0, "delta": None, "bands": 0, "m_star": 0}
        best = (math.inf, None, None)
        for delta in self.deltas:
            total, ok, mstar = 0.0, True, 1
            for lo, hi, F in bs:
                n = max(1, int(math.ceil((hi - lo) / delta)))
                K = self.K_lo((hi - lo) / n)
                if K <= 0:
                    ok = False
                    break
                for _ in range(n):
                    if F <= 2 * c * K:
                        total += F
                    else:
                        total += (F + c * K) ** 2 / (4 * c * K)
                        mstar = max(mstar,
                                    int(round((F + c * K) / (2 * c * K))))
            if ok and total < best[0]:
                best = (total, delta, mstar)
        if not math.isfinite(best[0]):
            return {"cap": math.inf, "delta": None, "bands": len(bs),
                    "m_star": None}
        return {"cap": best[0] * self.infl + self.tail_up(pairs),
                "delta": best[1], "bands": len(bs), "m_star": best[2],
                "off_band": 0.0}

    # -- the budget, as a ball ----------------------------------------------

    def budget_ball(self, pairs):
        """``sum_r slack(y_r) + T_signed``, every term an arb ball."""
        from flint import acb, arb  # noqa: F401  (arb used via helpers)
        from hardened_paper import HardenedPaper

        hp = HardenedPaper(coarse=self.coarse, fine=self.fine,
                           k_step=self.k_step, G=self.G)
        tot = arb(0)
        for _, y in pairs:
            s2 = hp.sigma2_ball(y)
            tot = tot + 8 * s2 + 8 * s2 * s2
        for i, (t1, y1) in enumerate(pairs):
            for j in range(i + 1, len(pairs)):
                t2, y2 = pairs[j]
                tot = tot + 2 * _T_ball(t1 - t2, y1, y2)
        return tot

    def margin(self, pairs, theta: float) -> dict:
        """``budget_lo - cap_up``, per pair: a one-sided lower bound.

        Positive => the configuration closes at this instrument.
        A value <= 0 does NOT say the configuration fails; it says this
        cover does not decide it.
        """
        from hardened_paper import f_lo, f_up

        b = self.budget_ball(pairs)
        rec = self.cap_up(pairs, theta)
        m = len(pairs)
        blo, bhi = f_lo(b), f_up(b)
        return {"m": m, "theta": theta,
                "budget_lo_pp": blo / m, "budget_up_pp": bhi / m,
                "budget_rad": float(b.rad()),
                "cap_up_pp": rec["cap"] / m,
                "margin_lo_pp": (blo - rec["cap"]) / m,
                "decided": blo - rec["cap"] > 0,
                "bands": rec["bands"], "delta": rec["delta"],
                "m_star": rec["m_star"],
                "coarse": self.coarse, "fine": self.fine, "G": self.G}


def _T_ball(dt: float, y1: float, y2: float):
    """``T(dt, y1, y2) = W(dt, |y1-y2|) + W(dt, y1+y2)`` as an arb ball."""
    from flint import acb, arb
    from hardened_paper import A_BALL, phipap_ball

    tot = arb(0)
    for y in (abs(y1 - y2), y1 + y2):
        v = phipap_ball(acb(arb(dt), arb(y)))
        tot = tot + 2 * (v.real * v.real - v.imag * v.imag)
    return tot / (A_BALL * A_BALL)


def hardened_margin(m: int = 24, theta: float = THETA, coarse: float = 0.02,
                    fine: float = 0.002, k_step: float = 0.002,
                    G: float = 200.0, s_gaps: float = S_GAPS,
                    y: float = Y) -> dict:
    """The decisive configuration, re-read under ball arithmetic."""
    hc = HardenedCluster(coarse=coarse, fine=fine, k_step=k_step, G=G)
    return hc.margin(config_pairs(m, s_gaps, y), theta)


def hardened_brackets_float(m: int = 8, theta: float = THETA,
                            coarse: float = 0.02, fine: float = 0.002,
                            k_step: float = 0.002, G: float = 60.0) -> dict:
    """Control (c): how the ball reading and the float reading relate.

    Two comparisons, and the first of them does NOT come out as a clean
    bracket, which is itself the useful reading:

    * **budget**.  The ball is a width-1e-36 enclosure of the exact
      value; ``PaperJoint.budget`` sums the same O(m^2) terms in double
      precision.  At m = 8 the float lands 6 ulp BELOW the ball's lower
      endpoint — the float instrument's own accumulation error, made
      visible by the ball rather than hidden by it.  So what is recorded
      is the agreement in ulp, and ``budget_bracketed`` is reported
      honestly (it is False at this m) instead of being widened until it
      passes.
    * **band heights**.  The float ``max f`` over grid points is a lower
      bound on the true band maximum; the ball ``F`` is an upper bound on
      it.  That comparison IS one-sided and must hold band by band.
    """
    pairs = config_pairs(m)
    hc = HardenedCluster(coarse=coarse, fine=fine, k_step=k_step, G=G)
    from hardened_paper import f_lo, f_up

    b = hc.budget_ball(pairs)
    pj = PaperJoint(step=fine, G=G)
    b_float = pj.budget(pairs)
    lo_b, hi_b = f_lo(b), f_up(b)
    mid = (lo_b + hi_b) / 2
    ulp = math.ulp(mid)
    hb = hc.bands(pairs)
    # raw grid maxima of the float instrument, per band
    lo_w = min(t for t, _ in pairs) - G
    hi_w = max(t for t, _ in pairs) + G
    gs, f, _, _, _ = pj.field(pairs, lo_w, hi_w)
    worst = -math.inf
    for lo, hi, F in hb:
        sel = (gs >= lo) & (gs <= hi)
        if not np.any(sel):
            continue
        worst = max(worst, float(f[sel].max()) - F)
    return {"budget_float": b_float, "budget_lo": lo_b, "budget_up": hi_b,
            "budget_bracketed": lo_b <= b_float <= hi_b,
            "budget_ball_width": hi_b - lo_b,
            "float_defect_ulp": (b_float - mid) / ulp,
            "float_agrees_to_1e14": abs(b_float - mid) <= 1e-14 * abs(mid),
            "worst_float_minus_hardened_F": worst,
            "heights_dominate": worst <= 0.0,
            "n_bands_hardened": len(hb)}


# ---------------------------------------------------------------------------
# 5. what retention this configuration actually permits
# ---------------------------------------------------------------------------


def theta_probe(m: int = 24, thetas=(0.9, 0.95, 0.98, 0.99, 0.995, 0.999),
                step: float = 0.001, G: float = 200.0) -> dict:
    """Per-pair margin against theta at the refined instrument.

    Recorded whichever way the headline goes: if the crossing had been
    real this is the retention the configuration would have capped, and
    since it is not, it is the room the configuration actually has.
    """
    pairs = config_pairs(m)
    pj = PaperJoint(step=step, G=G)
    rows = []
    for th in thetas:
        rec = pj.verdict(pairs, th)
        rows.append({"theta": th, "margin_pp": rec["margin"] / m,
                     "cap_pp": rec["cap"] / m, "closes": rec["closes"]})
    closing = [r["theta"] for r in rows if r["closes"]]
    return {"m": m, "step": step, "G": G, "rows": rows,
            "largest_closing_theta": max(closing) if closing else None}


def theta_one_diverges(m: int = 4, step: float = 0.002,
                       G: float = 60.0) -> dict:
    """Control (e): at ``theta = 1`` the internal charge vanishes and an
    unbounded multiplicity stack costs nothing, so the cap MUST be
    infinite on this configuration — for both instruments."""
    pairs = config_pairs(m)
    pj = PaperJoint(step=step, G=G)
    float_cap = pj.cap(pairs, 1.0)["cap"]
    return {"m": m, "float_cap": float_cap,
            "float_infinite": not math.isfinite(float_cap)}


def theta_one_diverges_hardened(m: int = 2, coarse: float = 0.02,
                                fine: float = 0.002, G: float = 60.0) -> dict:
    """The same control at the ball instrument."""
    hc = HardenedCluster(coarse=coarse, fine=fine, G=G)
    cap = hc.cap_up(config_pairs(m), 1.0)["cap"]
    return {"m": m, "hardened_cap": cap,
            "hardened_infinite": not math.isfinite(cap)}


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------


def audit(quick: bool = False) -> None:
    print("= the configuration =")
    s = S_GAPS * MEAN_GAP
    print(f"  s = {S_GAPS} mean gaps = {s:.6f} grid units, y = {Y}, "
          f"theta = {THETA}")
    print(f"  b_inf = {b_infty(s, Y):.6f} (closed form, per pair)")

    print("= 1. reproduction at truncation_bridge's own settings "
          f"(step {BRIDGE_STEP}, G {BRIDGE_G}, delta ladder "
          "(0.5, 1.0, 2.0, 3.0), no slicing) =")
    rep = reproduce_bridge_ladder()
    for r in rep["rows"]:
        print(f"  m={r['m']:3d}  budget_pp {r['budget_pp']:.6f}  cap_pp "
              f"{r['cap_pp']:.6f}  margin_pp {r['margin_pp']:+.5f}  "
              f"(cells {r['cells']}, delta {r['delta']})")
    print(f"  worst defect vs the recorded ladder: "
          f"{rep['worst_abs_defect']:.2e}; crossing at m = "
          f"{rep['crossing_m']}")

    print("= 2. refinement in the grid step (G = 60) =")
    steps = STEPS if not quick else (0.005, 0.002)
    for step in steps:
        lad = ladder(MS if step >= 0.002 else
                     (2, 8, 16, 24, 32) if step >= 0.001 else
                     (2, 8, 16, 24), step, BRIDGE_G)
        cells = ", ".join(f"m={r['m']}: {r['margin_pp']:+.5f}"
                          for r in lad["rows"])
        print(f"  step {step:<7}: {cells}")
        print(f"             crossing m* = {lad['crossing_m']}")

    print("= 2b. refinement in the resolved window (step = 0.002) =")
    Gs = (30.0, 60.0, 120.0, 200.0) if not quick else (30.0, 60.0)
    for G in Gs:
        lad = ladder((16, 24, 32), 0.002, G)
        cells = ", ".join(f"m={r['m']}: {r['margin_pp']:+.5f}"
                          for r in lad["rows"])
        print(f"  G {G:<6}: {cells}   crossing m* = {lad['crossing_m']}")

    print("= 3. the diagnosis: the cap's four channels (step 0.002) =")
    for G in ((BRIDGE_G, 200.0) if not quick else (BRIDGE_G,)):
        for m in (2, 8, 16, 24, 32):
            d = cap_split(m, 0.002, G)
            print(f"  G={G:<5} m={m:3d}: interior {d['interior_pp']:.6f} "
                  f"({d['n_interior']} bands, {d['interior_per_band']:.6f} "
                  f"each) + exterior {d['exterior_pp']:.6f} "
                  f"({d['n_exterior']} bands) + tail {d['tail_pp']:.6f} "
                  f"= cap_pp {d['cap_pp']:.6f}")
    print(f"  tail_pp is m-free and step-free: G=60 "
          f"{tail_per_pair(60.0):.6f}, G=200 {tail_per_pair(200.0):.6f}, "
          f"G=400 {tail_per_pair(400.0):.6f}  "
          f"(b_inf = {b_infty(s, Y):.6f})")
    for m in (2, 16):
        pm = partition_and_multiplicity(m, 0.002, BRIDGE_G)
        print(f"  rivals at m={m:3d}: {pm['n_bands']} bands "
              f"({pm['bands_per_pair']:.3f} per pair), interior widths "
              f"[{pm['interior_width_min']:.3f}, "
              f"{pm['interior_width_max']:.3f}] vs periodic band "
              f"{pm['periodic_width']:.3f}; worst completion multiplicity "
              f"m* = {pm['m_star_max']:.3f}, interior F max "
              f"{pm['interior_F_max']:.5f}")
    sat = interior_saturates()
    print(f"  interior per band: {[round(v, 5) for _, v in sat['sequence']]}"
          f" rising={sat['rising']} decelerating={sat['decelerating']}; "
          f"extrapolated limit {sat['extrapolated_limit']:.5f} vs periodic "
          f"instrument {sat['periodic_cap']:.5f} "
          f"(below: {sat['below_periodic']})")
    print("= 3b. the m -> infinity margin, per instrument setting =")
    for step in (0.002, 0.001):
        for G in (BRIDGE_G, 120.0, 200.0, 400.0):
            a = asymptotic_margin(step, G)
            print(f"  step {step} G {G:<6}: interior limit "
                  f"[{a['interior']['last']:.5f}, "
                  f"{a['interior']['richardson']:.5f}] (m<={a['interior']['last_m']}) "
                  f"+ tail {a['tail_pp']:.6f} -> margin_pp in "
                  f"[{a['margin_pp_pessimistic']:+.5f}, "
                  f"{a['margin_pp_optimistic']:+.5f}]  closes for all m: "
                  f"{a['closes_for_all_m']}")
    ch = channel_budget()
    print(f"  attribution at m=24: cap_pp {ch['cap_pp_base']:.6f} -> "
          f"{ch['cap_pp_fine_step']:.6f} (step) -> "
          f"{ch['cap_pp_wide_window']:.6f} (window) -> "
          f"{ch['cap_pp_both']:.6f} (both); step channel "
          f"{ch['step_channel']:+.6f}, window channel "
          f"{ch['window_channel']:+.6f}")

    if not quick:
        print("= 4. the decisive configurations under ball arithmetic "
              f"(cover {HARDENED_INSTRUMENT['coarse']}/"
              f"{HARDENED_INSTRUMENT['fine']}, "
              f"{HARDENED_INSTRUMENT['prec_bits']} bits) =")
        for m, G in ((8, 60.0), (24, 60.0), (24, 200.0)):
            hm = hardened_margin(m=m, G=G,
                                 coarse=HARDENED_INSTRUMENT["coarse"],
                                 fine=HARDENED_INSTRUMENT["fine"],
                                 k_step=HARDENED_INSTRUMENT["k_step"])
            print(f"  m={hm['m']:3d} G={hm['G']:<6}: budget_pp in "
                  f"[{hm['budget_lo_pp']:.9f}, {hm['budget_up_pp']:.9f}], "
                  f"cap_up_pp {hm['cap_up_pp']:.6f}, margin_lo_pp "
                  f"{hm['margin_lo_pp']:+.6f}  (one-sided; decided "
                  f"positive: {hm['decided']}), {hm['bands']} bands, "
                  f"m* {hm['m_star']}")
        print("  pinned, not re-run here (each ~3-6 min): "
              + "; ".join(
                  f"m={m} G={G} fine={fine}: margin_lo_pp "
                  f"{r['margin_lo_pp']:+.6f} (decided {r['decided']})"
                  for (m, G, fine), r in HARDENED_RECORD.items() if m == 64))
        br = hardened_brackets_float()
        print(f"  bracket control: float budget {br['budget_float']:.9f} in "
              f"[{br['budget_lo']:.9f}, {br['budget_up']:.9f}]: "
              f"{br['budget_bracketed']}; worst (float raw F - hardened F) "
              f"= {br['worst_float_minus_hardened_F']:+.2e} "
              f"(dominated: {br['heights_dominate']})")

        print("= 5. what retention this configuration permits (refined) =")
        tp = theta_probe()
        for r in tp["rows"]:
            print(f"  theta {r['theta']:<6}: margin_pp {r['margin_pp']:+.6f} "
                  f"cap_pp {r['cap_pp']:.6f}  "
                  f"{'closes' if r['closes'] else 'OPEN'}")
        print(f"  largest scanned theta that closes: "
              f"{tp['largest_closing_theta']}")

    print("= controls =")
    d1 = theta_one_diverges()
    print(f"  theta = 1 must diverge: float cap {d1['float_cap']} "
          f"({d1['float_infinite']})")
    if not quick:
        d2 = theta_one_diverges_hardened()
        print(f"                          ball cap {d2['hardened_cap']} "
              f"({d2['hardened_infinite']})")

    print("= verdict =")
    print("  the crossing at (step 0.005, G 60) is a property of the "
          "instrument's settings, not of the configuration.  The "
          "dominant channel is the per-pair tail allowance at G = 60 "
          "(0.027096, i.e. 20.9% of b_inf), which the periodic "
          "instrument it is compared against does not pay at all.")
    print("  Refining the GRID STEP alone moves the crossing out "
          "(m* = 24 / 48 / 64 / beyond 64) but leaves the m -> infinity "
          "margin at G = 60 negative at every step measured.  Refining "
          "the WINDOW clears it: no negative m on the ladder at "
          "G >= 120, and the m -> infinity margin is positive there at "
          "both readings of the limit.")


if __name__ == "__main__":
    audit(quick="--quick" in sys.argv)
