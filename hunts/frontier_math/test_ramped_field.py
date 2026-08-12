"""Controls for ramped_field.py (the band dual at the ramp-mollified
paper window).

Fast versions: the dual instances use G = 120 (vs the audit's 400), so
the tail majorant grows ~3x, which only tightens every inequality being
tested.  The three eps fields are built once per module.

Every control here is mandatory in the sense of the discipline suite: a
failing control is itself a result and must be reported, never blanketed
past.  All grades are measured/observed; nothing here is evidence about
RH and no proportion is claimed.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import explicit_single_pair_adversary, phipap  # noqa: E402
from ramped_field import (  # noqa: E402
    PSI7,
    PSI9,
    RampedBandDual,
    RampedField,
    c_psi,
    eps_zero_convergence,
)

EPS_LIST = (0.125, 0.0625, 0.03125)
YS = (0.02, 0.1, 0.3, 0.49)


@pytest.fixture(scope="module")
def duals() -> dict[float, RampedBandDual]:
    return {eps: RampedBandDual(RampedField(eps, gmax_pin=120.0), G=120.0)
            for eps in EPS_LIST}


# ---------------------------------------------------------------------------
# 1. the shape: Psi is the C^3 smoothstep it claims to be (sympy pin)
# ---------------------------------------------------------------------------


def test_psi_endpoint_derivatives_pinned_by_sympy():
    """Psi = 35x^4 - 84x^5 + 70x^6 - 20x^7 has Psi(0)=0, Psi(1)=1 and
    vanishing first, second and third derivatives at BOTH endpoints, so
    the extension by 0/1 outside [0,1] is C^3.  Also nondecreasing:
    Psi' factors as 140 x^3 (1-x)^3."""
    import sympy as sp

    x = sp.symbols("x")
    psi = 35 * x**4 - 84 * x**5 + 70 * x**6 - 20 * x**7
    assert psi.subs(x, 0) == 0 and psi.subs(x, 1) == 1
    d = psi
    for _ in range(3):
        d = sp.diff(d, x)
        assert d.subs(x, 0) == 0, "derivative at 0 must vanish"
        assert d.subs(x, 1) == 0, "derivative at 1 must vanish"
    assert sp.simplify(sp.diff(psi, x) - 140 * x**3 * (1 - x) ** 3) == 0
    # the module's coefficient vector is this polynomial
    vals = np.polyval(PSI7, np.linspace(0, 1, 7))
    sym = [float(psi.subs(x, t)) for t in np.linspace(0, 1, 7)]
    assert np.allclose(vals, sym, atol=1e-14)


def test_alt_shape_is_admissible_too():
    """The spot-check shape (degree-9 smoothstep) is also C^3-admissible:
    endpoint values 0/1 and three vanishing derivatives at each end."""
    import sympy as sp

    x = sp.symbols("x")
    psi = 126 * x**5 - 420 * x**6 + 540 * x**7 - 315 * x**8 + 70 * x**9
    assert psi.subs(x, 0) == 0 and psi.subs(x, 1) == 1
    d = psi
    for _ in range(3):
        d = sp.diff(d, x)
        assert d.subs(x, 0) == 0 and d.subs(x, 1) == 0
    vals = np.polyval(PSI9, np.linspace(0, 1, 5))
    sym = [float(psi.subs(x, t)) for t in np.linspace(0, 1, 5)]
    assert np.allclose(vals, sym, atol=1e-14)


# ---------------------------------------------------------------------------
# 2. the quadrature: ladder and mpmath oracle
# ---------------------------------------------------------------------------


def test_quadrature_ladder_and_oracle_pins(duals):
    """The Gauss-Legendre rule at the working node counts agrees with the
    doubled rule and with the mp.workdps(30) tanh-sinh oracle to well
    under any margin used downstream (probe set includes the largest
    resolved g)."""
    for eps, bd in duals.items():
        rf = bd.rf
        assert max(rf.ladder_worst) < 1e-11, f"eps={eps}: {rf.ladder_worst}"
        assert max(rf.oracle_worst) < 1e-11, f"eps={eps}: {rf.oracle_worst}"
        # the one-sided bounds actually carry the safety factor
        assert rf.e0 >= 10 * max(rf.ladder_worst[0], rf.oracle_worst[0])


def test_mpmath_state_does_not_leak():
    """All mpmath work sits in mp.workdps context managers."""
    from mpmath import mp

    before = mp.dps
    rf = RampedField(0.125, gmax_pin=50.0)
    rf._oracle(3.0 + 0.2j, order=2)
    assert mp.dps == before


# ---------------------------------------------------------------------------
# 3. eps -> 0: the ramped field converges to the paper's closed form
# ---------------------------------------------------------------------------


def test_eps_to_zero_matches_closed_form_with_measured_constant():
    """At eps = 1e-3 and 1e-4 the field matches paper_chain.phipap inside
    the derived bound 2 eps c_psi cosh(|Im z|/2); the measured constant
    defect/eps is stable across the decade (O(eps), constant ~0.88
    against the derived cap ~1.23)."""
    rec = eps_zero_convergence()
    for eps, r in rec.items():
        assert r["inside_bound"], f"eps={eps}: defect above the derived bound"
        assert r["worst_defect"] < 10 * eps
    c3, c4 = rec[1e-3]["constant"], rec[1e-4]["constant"]
    assert 0.5 < c4 / c3 < 2.0, "defect is not scaling like O(eps)"
    assert 0.5 < c4 < 1.3


def test_derivatives_converge_too():
    """Same control for d1/d2 at one point: the taper differs from 1 on a
    2 eps fraction where |u| <= 1/2, so the derivative defects are O(eps)
    with constants at most c_psi/2^(k-1)-sized; measured directly."""
    from paper_chain import phipap_d1, phipap_d2

    eps = 1e-4
    rf = RampedField(eps, pin=False)
    z = 7.3 + 0.3j
    d1 = abs(complex(rf.d1(z)[0]) - complex(phipap_d1(z)))
    d2 = abs(complex(rf.d2(z)[0]) - complex(phipap_d2(z)))
    assert d1 < 2 * eps * c_psi()
    assert d2 < eps * c_psi()


# ---------------------------------------------------------------------------
# 4. completeness at every (eps, y): no missed band, no allowance
# ---------------------------------------------------------------------------


def test_no_missed_band_completeness_every_eps_and_depth(duals):
    """worst_ratio > 100 and off-band allowance exactly 0 at EVERY
    (eps, y).  If this fails at large eps that failure is the result;
    nothing may blanket past it (cap() would report inf there)."""
    for eps, bd in duals.items():
        for y in YS:
            rec = bd.no_missed_band(y)
            assert rec["clear"], f"eps={eps}, y={y}: completeness FAILED"
            assert rec["worst_ratio"] > 100, (
                f"eps={eps}, y={y}: ratio {rec['worst_ratio']:.1f} <= 100")
            assert bd.off_band_allowance(y) == 0.0


def test_cross_band_drop_is_one_sided(duals):
    """omega^2 >= 0 (a square): dropping cross-band charges cannot help."""
    bd = duals[0.125]
    rs = np.arange(0.0, 120.0, 0.02)
    assert float(np.min(bd.omega2(rs.astype(complex)))) >= 0.0


def test_band_lattice_is_recomputed_not_reused(duals):
    """The eps = 1/8 band edges genuinely shift from the eps = 0 lattice
    (paper_chain's): first-band centre moves by more than the grid step,
    so no eps = 0 band data could stand in for the ramped geometry."""
    from paper_chain import PaperBandDual

    b0 = PaperBandDual(G=120.0).bands(0.3)
    b8 = duals[0.125].bands(0.3)
    c0 = (b0[0][0] + b0[0][1]) / 2
    c8 = (b8[0][0] + b8[0][1]) / 2
    assert abs(c8 - c0) > 0.001


# ---------------------------------------------------------------------------
# 5. the dual: divergence at theta = 1, retention, adversary domination
# ---------------------------------------------------------------------------


def test_theta_one_diverges_at_every_eps(duals):
    """At theta = 1 the internal charge vanishes and band stacking is
    unbounded: the cap must be infinite at every eps."""
    for eps, bd in duals.items():
        assert not math.isfinite(bd.cap(1.0, 0.49)["cap"]), f"eps={eps}"


def test_theta_star_is_0995_at_every_eps(duals):
    """The measured headline: cap <= slack at theta = 0.995 at every
    probe depth for eps in {1/8, 1/16, 1/32}, and the next grid theta
    (0.999) fails at the deep end — same grid point as the eps = 0 box
    at every ramp fraction tried."""
    for eps, bd in duals.items():
        for y in YS:
            rec = bd.cap(0.995, y)
            assert rec["cap"] <= bd.slack(y), f"eps={eps}, y={y}"
        assert bd.cap(0.999, 0.49)["cap"] > bd.slack(0.49), f"eps={eps}"


def test_adversary_stays_inside_cap(duals):
    """paper_chain's greedy band-riding adversary (reused unchanged, the
    primal side) stays inside the dual cap at theta = 0.995, at the
    worst allowed eps = 1/8."""
    bd = duals[0.125]
    for y in (0.3, 0.49):
        rec = explicit_single_pair_adversary(bd, y, theta=0.995,
                                             halfrange=110.0)
        measured = rec["D"] - (1 - 0.995) * rec["R"]
        cap = bd.cap(0.995, y)["cap"]
        assert measured < cap, f"y={y}: {measured} !< {cap}"


# ---------------------------------------------------------------------------
# 6. shape dependence (the caveat, measured)
# ---------------------------------------------------------------------------


def test_shape_spot_check_moves_little():
    """Swapping Psi for the degree-9 smoothstep at (eps=1/8, y=0.49)
    moves the cap by ~1.6% and the slack by ~0.5%, and the margin sign
    is unchanged.  A caveat-measurer at one point, not a supremum."""
    from ramped_field import shape_spot_check

    sc = shape_spot_check()
    assert sc["rel_move_cap"] < 0.05
    assert sc["rel_move_slack"] < 0.05
    assert sc["margin_sign_same"]


# ---------------------------------------------------------------------------
# 7. the field itself: even, real on the real axis, below the box mass
# ---------------------------------------------------------------------------


def test_field_basic_geometry():
    rf = RampedField(0.125, pin=False)
    z = np.array([0.7, 3.1, 5.9 + 0.2j])
    assert np.allclose(rf.phi2(z), rf.phi2(-z), atol=1e-14)  # even
    assert float(np.max(np.abs(rf.phi2(np.array([0.7, 3.1])).imag))) < 1e-14
    # tapering removes mass: A_eps < A_box, and by about 2 eps c_psi cos-avg
    assert rf.A < float(phipap(0j).real)
    assert rf.A > float(phipap(0j).real) - 2 * 0.125 * c_psi()
