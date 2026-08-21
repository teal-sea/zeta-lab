"""Pins for the gap A bandwidth question.

The load-bearing test is not that a wider bandwidth failed. It is
`test_the_harness_reproduces_the_case_whose_answer_is_known`: section 6a
records an LP that returned `4.908534` on that same case, 40% above its proved
ceiling, because it sampled a continuum constraint. A harness that cannot
reproduce the known answer cannot be trusted about the unknown one, so the
calibration is what licenses reading anything else here.

The second load-bearing test is `test_wide_bandwidth_solutions_do_not_verify`.
Solutions above the bandwidth-1 ceiling *are* returned, at up to 100% of the
value needed, and every one of them collapses to zero under verification. The
number the solver prints is not the number the point achieves, and this file
exists so that distinction cannot quietly rot.

`cvxpy` is not in `requirements.txt`: it is a tool this hunt installed, so
everything that needs a solver skips without it.
"""

import numpy as np
import pytest

import sparse_sdp as sp

cvxpy = pytest.importorskip("cvxpy", reason="the SDP needs a conic solver")


def test_the_constant_row_transform_is_exact():
    """`A_00 = shat`, the identity the frequency-domain route is built on.

    In x-space this integral decays like `1/x^2` and its truncation ripple
    swamped the constraint region; here it is exact to machine precision.
    """
    xis = np.linspace(0.0, 1.6, 33)
    A, _, _, _ = sp.transforms(0.5, 0, xis)
    shat = sp.TWOPI * np.clip(1.0 - np.abs(xis), 0.0, None)
    assert np.max(np.abs(A[0, 0, :] - shat)) < 1e-12


def test_the_constant_is_in_the_basis():
    """Without it the family excludes `u = a*s`, the one solution known to
    exist, and the SDP correctly reports zero for every input."""
    rows = sp.basis(np.array([0.0, 1.0, 5.0]), 0.5, 0)
    assert rows.shape[0] == 1
    assert np.allclose(rows[0], 1.0)


def test_the_harness_reproduces_the_case_whose_answer_is_known():
    """Bandwidth 1, where section 6a proves the ceiling `(cap - c)*2*pi`.

    Verified rather than reported: projected onto the PSD cone, scaled to
    feasibility on a fine grid, and only then compared.
    """
    status, G = sp.solve(0.5, 0)
    assert status == "optimal"
    result = sp.verified(0.5, 0, G)
    assert result["scale"] == pytest.approx(1.0, abs=1e-9)
    assert result["residual"] <= 1e-9
    assert result["verified_u0"] == pytest.approx(sp.BANDWIDTH_ONE_U0, rel=1e-4)


def test_the_known_case_needs_no_psd_repair():
    """The calibration solves cleanly; every wider case does not, and that
    difference is the signal rather than a nuisance."""
    _, G = sp.solve(0.5, 0)
    assert sp.verified(0.5, 0, G)["psd_repair"] < 1e-12


@pytest.mark.parametrize("bandwidth,m", [(1.0, 4), (2.0, 6)])
def test_wide_bandwidth_solutions_do_not_verify(bandwidth: float, m: int) -> None:
    """The negative result, pinned.

    These solves return points above the bandwidth-1 ceiling, and the points
    are not feasible: `uhat` comes back strictly positive somewhere in
    `|xi| > 1`, where `M` vanishes and no positive scaling can rescue it. The
    verified value is therefore zero, not an improvement.
    """
    status, G = sp.solve(bandwidth, m)
    if G is None:
        pytest.skip(f"solver did not return a matrix ({status})")
    result = sp.verified(bandwidth, m, G)
    assert result["scale"] == 0.0
    assert result["verified_u0"] == 0.0


def test_nothing_here_beats_bandwidth_one():
    """The summary claim of this module, kept honest by a test.

    If a wider bandwidth ever does verify above the ceiling, this fails, and
    that failure is the discovery.
    """
    best = 0.0
    for bandwidth, m in ((0.5, 0), (1.0, 4), (2.0, 6)):
        status, G = sp.solve(bandwidth, m)
        if G is not None:
            best = max(best, sp.verified(bandwidth, m, G)["verified_u0"])
    assert best <= sp.BANDWIDTH_ONE_U0 * (1 + 1e-4)
    assert best < sp.NEEDED_U0
