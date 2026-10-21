"""Pins for the gap A bandwidth question.

The load-bearing test is not that a wider bandwidth failed. It is
`test_the_harness_reproduces_the_case_whose_answer_is_known`: section 6a
records an LP that returned `4.908534` on that same case, 40% above its proved
ceiling, because it sampled a continuum constraint. A harness that cannot
reproduce the known answer cannot be trusted about the unknown one, so the
calibration is what licenses reading anything else here.

The second load-bearing test is `test_wide_bandwidth_solutions_do_not_verify`.
Solutions above the bandwidth-1 ceiling *are* returned, at up to 100.00% of
the value needed in the stored scan (`raw_u0` at `B = 4, m = 8` in
`results_sparse_sdp.json`), and every one of them collapses to zero under
verification. The number the solver prints is not the number the point
achieves, and this file exists so that distinction cannot quietly rot.

`cvxpy` is not in `requirements.txt`: it is a tool this hunt installed, so
everything that needs a solver skips without it. The pin on the stored scan
reads only the JSON and runs without a solver, as do the two basis checks.
"""

import json
from pathlib import Path

import numpy as np
import pytest

import sparse_sdp as sp

try:
    import cvxpy  # noqa: F401
    HAVE_SOLVER = True
except ImportError:
    HAVE_SOLVER = False

needs_solver = pytest.mark.skipif(not HAVE_SOLVER, reason="the SDP needs a conic solver")

_SCAN = Path(__file__).resolve().parent / "results_sparse_sdp.json"


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


@needs_solver
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


@needs_solver
def test_the_known_case_needs_no_psd_repair():
    """The calibration solves cleanly; every wider case does not, and that
    difference is the signal rather than a nuisance."""
    _, G = sp.solve(0.5, 0)
    assert sp.verified(0.5, 0, G)["psd_repair"] < 1e-12


@needs_solver
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


@needs_solver
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


def test_the_stored_scan_records_how_close_each_wide_solve_came_and_why_it_failed():
    """Section 6b's figures, pinned to the artifact they are read from.

    Needs no solver: it reads `results_sparse_sdp.json` rather than solving.
    The calibration row verifies at scale 1. Every wider row has a raw
    objective above what bandwidth 1 reaches, verifies to zero, and fails by an
    out-of-band `uhat` of the order of the solver tolerance, which is why 6b
    reads those verdicts as undecided rather than as a negative answer. A
    re-run that stores different figures fails here, and 6b must then be
    re-read against the new file.
    """
    rows = json.loads(_SCAN.read_text(encoding="utf-8"))
    for row in rows:
        assert row["needed_u0"] == pytest.approx(sp.NEEDED_U0, rel=1e-12)
        assert row["bandwidth_one_u0"] == pytest.approx(sp.BANDWIDTH_ONE_U0, rel=1e-12)

    calibration, *wide = rows
    assert (calibration["bandwidth_q"], calibration["m"]) == (0.5, 0)
    assert calibration["status"] == "optimal"
    assert calibration["scale"] == 1.0
    assert calibration["verified_u0"] == pytest.approx(sp.BANDWIDTH_ONE_U0, rel=1e-4)
    assert calibration["raw_u0"] == pytest.approx(calibration["verified_u0"], rel=1e-12)
    assert calibration["max_uhat_out_of_band"] == 0.0

    assert [(r["bandwidth_q"], r["m"]) for r in wide] == [(1.0, 4), (1.0, 6), (2.0, 6), (4.0, 8)]
    for row in wide:
        assert row["status"] == "optimal_inaccurate"
        assert row["scale"] == 0.0
        assert row["verified_u0"] == 0.0
        assert sp.BANDWIDTH_ONE_U0 < row["raw_u0"] <= sp.NEEDED_U0
        assert 0.0 < row["max_uhat_out_of_band"] < 1e-7

    # The figures as 6b states them.
    assert [round(100 * r["raw_u0"] / sp.NEEDED_U0, 2) for r in wide] == [82.25, 85.52, 94.11, 100.0]
    out_of_band = [r["max_uhat_out_of_band"] for r in wide]
    assert (f"{min(out_of_band):.1e}", f"{max(out_of_band):.1e}") == ("2.1e-08", "4.8e-08")
    repair = [r["psd_repair"] for r in wide]
    assert (f"{min(repair):.1e}", f"{max(repair):.1e}") == ("1.2e-07", "1.2e-06")
