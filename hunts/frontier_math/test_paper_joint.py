"""Controls for paper_joint.py, the joint cap at the paper's field.

Fast versions of the mandatory controls: completeness (>100, off-band
allowance exactly 0), band widths below the kernel zero (no merging),
cap divergence at theta = 1, greedy adversary dominated at the reported
theta_full, dense-lattice shielding (cap exactly 0), and distinctness
against mt_joint's numbers at a matched configuration.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_joint import (  # noqa: E402
    A, MEAN_GAP, PaperJoint, first_kernel_zero, joint_greedy,
    soft_window_nu, worst_dipole_sep,
)

PJ = PaperJoint()

#: fast probe set: sparse (the binding family), the worst dipole, one
#: soft-window lattice and one dense lattice
ISOLATED = [(0.0, 0.49)]
ISOLATED_SHALLOW = [(0.0, 0.1)]
DIPOLE = [(0.0, 0.49), (worst_dipole_sep(0.49), 0.49)]
SOFT = [(k * MEAN_GAP / soft_window_nu(0.49), 0.49) for k in range(4)]
DENSE = [(k * MEAN_GAP / 3.0, 0.49) for k in range(12)]

#: theta_full measured by the audit sweep (the scan's grid answer); the
#: domination control below runs at this value
THETA_FULL = 0.995


def test_completeness_clears_100_and_allowance_is_zero():
    """No-missed-band on the JOINT field: worst Q / curvature ratio must
    clear 100, and then the off-band allowance is exactly 0."""
    for pairs in (ISOLATED, ISOLATED_SHALLOW, DIPOLE, SOFT):
        r = PJ.no_missed_band(pairs)
        assert r["clear"], pairs
        assert r["worst_ratio"] > 100, (pairs, r["worst_ratio"])
        assert PJ.off_band_allowance(pairs) == 0.0


def test_joint_bands_stay_below_the_kernel_zero():
    """No band merging: every joint band stays narrower than the paper
    kernel's first zero (1.0573 mean gaps = 6.643 grid units).  A wider
    band would put omega's zero inside a single band and void the
    same-band charge floor, if this fails the run must stop."""
    z1 = first_kernel_zero()
    assert abs(z1 / MEAN_GAP - 1.0573) < 5e-4
    for pairs in (ISOLATED, DIPOLE, SOFT):
        bs = PJ.bands(pairs)
        assert bs, pairs
        widest = max(hi - lo for lo, hi, _ in bs)
        assert widest < z1, (pairs, widest, z1)


def test_cap_diverges_at_theta_one():
    """At theta = 1 the internal charge vanishes: an unbounded stack
    costs nothing and the cap MUST report infinity."""
    for pairs in (ISOLATED, DIPOLE):
        assert PJ.cap(pairs, 1.0)["cap"] == math.inf


def test_cap_dominates_joint_greedy_at_theta_full():
    """The measured joint adversary (a lower bound on the supremum) must
    sit inside the cap at the reported theta_full."""
    for pairs in (ISOLATED, DIPOLE, SOFT):
        g = joint_greedy(PJ, pairs, THETA_FULL, kmax=25)
        cap = PJ.cap(pairs, THETA_FULL)["cap"]
        assert g <= cap + 1e-9, (pairs, g, cap)


def test_dense_lattice_caps_exactly_zero():
    """nu = 3 shielding: the joint positive part vanishes (one pair's
    positive hump covers its neighbours' bands), so the cap is exactly
    0, and the budget stays positive, so the verdict closes."""
    rec = PJ.cap(DENSE, 0.9)
    assert rec["cap"] == 0.0
    assert PJ.bands(DENSE) == ()
    v = PJ.verdict(DENSE, 0.9)
    assert v["budget"] > 0 and v["closes"]


def test_positive_part_is_of_the_joint_field_not_per_pair():
    """The discipline check: sum of per-pair positive parts must exceed
    the joint positive part somewhere in a shielded configuration (else
    the clipping order would not matter and this control has no power)."""
    lo, hi = -10.0, 10.0 + DENSE[-1][0]
    gs = np.arange(lo, hi, 0.01)
    joint = np.zeros_like(gs)
    per_pair = np.zeros_like(gs)
    for t, y in DENSE:
        w = -2 * PJ.pc.W(gs - t, y)
        joint += w
        per_pair += np.maximum(0.0, w)
    assert float(np.maximum(0.0, joint).sum()) < float(per_pair.sum())
    assert float(np.maximum(0.0, joint).max()) == 0.0  # fully shielded


def test_theta_full_scan_on_the_fast_probe_set():
    """The scan on the fast probe set reports the audit's grid point,
    and 0.999 fails (the isolated pair already fails there in
    paper_chain's single-pair dual)."""
    configs = [("iso", ISOLATED), ("iso_shallow", ISOLATED_SHALLOW),
               ("dip", DIPOLE), ("soft", SOFT), ("dense", DENSE)]
    star, margins = PJ.theta_full_scan(configs)
    assert star == THETA_FULL
    assert margins[0.999][0] < 0


def test_distinct_from_mt_joint_at_matched_configuration():
    """This module is not a re-run of the T1 joint numbers: at the same
    matched configuration the caps and budgets differ clearly."""
    from mt_joint import MTJoint
    mj = MTJoint()
    pairs = [(0.0, 0.49)]
    cap_p = PJ.cap(pairs, 0.9)["cap"]
    cap_t1 = mj.cap(pairs, 0.9)["cap"]
    assert abs(cap_p - cap_t1) / max(cap_p, cap_t1) > 0.05
    b_p = PJ.budget(pairs)
    b_t1 = mj.mt.budget(pairs)
    assert abs(b_p - b_t1) / max(b_p, b_t1) > 0.05


def test_soft_window_density_is_derived_not_copied():
    """nu_p comes from THIS field's first band centre (~1.044 mean gaps
    => nu_p ~ 0.958), not the T1 value 0.97 and not the bare kernel-zero
    reciprocal 1/1.0573 = 0.9458."""
    nu = soft_window_nu(0.49)
    assert 0.94 < nu < 0.97
    assert abs(nu - 0.97) > 5e-3
    centre = MEAN_GAP / nu
    bs = PJ.bands([(0.0, 0.49)])
    first = min((lo + hi) / 2 for lo, hi, _ in bs if lo > 0)
    assert abs(centre - first) < 1e-9


def test_off_band_allowance_nonzero_branch_reports_when_not_clear():
    """The allowance is the failure detector, not a margin: a coarse
    instance whose completeness does not clear must report a positive
    allowance rather than silently passing 0."""
    coarse = PaperJoint(step=1.2, G=40.0)
    r = coarse.no_missed_band(ISOLATED)
    assert not r["clear"]
    assert coarse.off_band_allowance(ISOLATED) > 0.0
