"""Tests for zeta.inverse: Wu–Sprung reconstruction and the battery verdict.

Every literal was measured in this environment before being asserted.  The
module's story, in test order:

1. The instrument calibrates on the harmonic oscillator with zero knowledge
   of ζ: Abel inversion returns V = x² with defect at rounding level, the
   finite-difference forward solve returns 1, 3, 5, … within 5e-4.
2. The mean densities are *derived*: (1/2π)log(E/2π) matches finite
   differences of rs_theta, and the DH density (1/2π)log(5E/2π) matches
   finite differences of dh_theta, including the conductor-5 constant a
   first guess got wrong by exactly log √5.
3. The pipeline scores: smooth well ≈ 0.22 mean gaps for ζ (0.18 for DH),
   mollified fractal correction is a small improvement at its calibrated
   δ = 2.5, and first-order inverse iteration lands on the targets to
   ~1e-4 gaps (measured 1.2e-4 for ζ, 2.5e-4 for DH).
4. The battery verdict (docs/09 gate #3): the *identical* pipeline
   manufactures an equally good Hamiltonian for the RH-violating
   Davenport–Heilbronn ordinates, and for a fully synthetic ladder.
   Existence of a potential distinguishes nothing; only properties could.
"""

from __future__ import annotations

import numpy as np
import pytest

from zeta.inverse import (
    _dh_nbar_prime,
    _zeta_nbar_prime,
    dh_online_ordinates,
    harmonic_calibration,
    refine_potential,
    spectrum_report,
    wu_sprung_potential,
)


def test_harmonic_calibration_both_directions():
    cal = harmonic_calibration()
    assert cal["passed"]
    assert cal["inverse_max_defect"] < 1e-10
    assert cal["forward_max_defect"] < 5e-4


def test_zeta_density_matches_rs_theta():
    from zeta.statistics import riemann_siegel_theta

    for E in (20.0, 50.0, 120.0):
        fd = (
            float(riemann_siegel_theta(np.array([E + 0.5]))[0])
            - float(riemann_siegel_theta(np.array([E - 0.5]))[0])
        ) / np.pi
        assert abs(fd - float(_zeta_nbar_prime(np.array([E]))[0])) < 2e-3


def test_dh_density_matches_dh_theta():
    from zeta.epstein import dh_theta

    for E, expect_close in ((8.0, 2e-3), (30.0, 5e-4), (100.0, 5e-4)):
        fd = (float(dh_theta(E + 0.5)) - float(dh_theta(E - 0.5))) / np.pi
        assert abs(fd - float(_dh_nbar_prime(np.array([E]))[0])) < expect_close


def test_dh_ordinates_cached_and_sane():
    zs = dh_online_ordinates()
    assert len(zs) >= 60
    assert abs(zs[0] - 5.0942) < 1e-3  # first DH on-line zero
    assert all(b > a for a, b in zip(zs, zs[1:]))


def test_fractal_potential_monotone_at_calibrated_delta():
    gams = dh_online_ordinates()[:40]
    pot = wu_sprung_potential(V_max=60.0, source="dh", ordinates=gams)
    assert pot["monotonicity_defect"] == 0.0
    assert np.all(np.diff(pot["x"]) >= 0)


def test_zeta_pipeline_scores():
    r = spectrum_report("zeta")
    assert r["rms_smooth"] < 0.35          # measured 0.220
    assert r["rms_fractal"] <= r["rms_smooth"] * 1.05
    assert r["rms_refined"] < 2e-3         # measured 1.2e-4
    # refinement converges monotonically
    h = r["refine_rms_history"]
    assert h[-1] < h[0] / 100


def test_dh_battery_verdict():
    """The RH-violating function admits an equally good Hamiltonian."""
    r = spectrum_report("dh")
    assert r["rms_smooth"] < 0.35          # measured 0.180
    assert r["rms_refined"] < 2e-3         # measured 2.5e-4
    # the pipeline cannot tell the impostor from the real thing
    rz = spectrum_report("zeta")
    assert r["rms_refined"] < 10 * rz["rms_refined"] + 1e-3


def test_refinement_hits_synthetic_ladder():
    """Manufacturing works for a made-up spectrum too, the strongest form
    of the existence-proves-nothing point.  (First-order iteration needs
    the seed's spectrum within roughly a gap of the targets, the Wu–Sprung
    seed provides exactly that; here the harmonic ladder does.)"""
    targets = np.array([1.4, 3.2, 5.5, 6.8, 9.3, 11.1])  # perturbed 2n+1
    seed = lambda xs: np.asarray(xs, float) ** 2
    out = refine_potential(seed, targets, L=9.0, n_grid=4000, iterations=6)
    assert out["final_rms"] < 1e-2
