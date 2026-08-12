"""Controls for depth_uniform.py (the depth-UNIFORM retention at the paper field).

Fast versions: the instance here uses G = 120 (vs the audit's 200) and a
coarser offset grid, which makes every bound in the file LARGER (a shorter
resolved region hands more mass to the 1/g^2 tail majorant, a coarser grid
inflates more) and every inequality tested therefore harder to satisfy.  A
control that passes here passes at the audit's settings.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from depth_uniform import (  # noqa: E402
    A,
    C_IM_UNIT,
    EDGE,
    L1,
    L2,
    NSLACK_0,
    TV,
    DepthUniform,
    bound_attainment,
    c_im,
    c_im_normalised,
    c_im_unit_control,
    convexity_control,
    curvature,
    curvature_bound_control,
    degenerate_vs_paper_chain,
    derivative_bound_control,
    dominates_measured_adversary,
    lam_Cg,
    lam_Cy,
    lam_Sg,
    lam_Sy,
    lesion_no_inflation,
    monotonicity_control,
    nesting_control,
    nslack,
    one_sidedness_control,
    shallow_one_sidedness_control,
    sigma,
)
from paper_chain import S2, PaperChain, phipap  # noqa: E402

_PC = PaperChain()

#: the four depths the existing chain samples, and whose gap this module closes
SAMPLED = (0.02, 0.1, 0.3, 0.49)


@pytest.fixture(scope="module")
def du() -> DepthUniform:
    return DepthUniform(G=120.0, step=0.005, slices=2)


@pytest.fixture(scope="module")
def profs(du) -> list:
    return du.profiles()


# ---------------------------------------------------------------------------
# (a) the derivative bounds: closed forms and finite differences
# ---------------------------------------------------------------------------


def test_window_constants_match_quadrature():
    """L1, L2, EDGE, TV in closed form against direct quadrature."""
    ts = np.linspace(-0.5, 0.5, 200001)
    p = np.cos(S2 * ts)
    assert abs(float(np.trapezoid(p, ts)) - A) < 1e-9
    assert abs(float(np.trapezoid(np.abs(ts) * p, ts)) - L1) < 1e-9
    assert abs(float(np.trapezoid(ts * ts * p, ts)) - L2) < 1e-9
    assert abs(EDGE - math.cos(S2 / 2)) < 1e-15
    assert abs(TV - float(np.abs(np.diff(p)).sum())) < 1e-6


def test_derivative_bounds_hold_against_finite_differences():
    """(a) THE control on the four constants.

    At 24 scattered (g, y) spanning g in (0.05, 200) and y in (0.002, 0.5),
    every one of |dC/dg|, |dS/dg|, |dC/dy|, |dS/dy| measured by central
    differences must sit below its derived bound, and the closed-form
    identification dC/dg = Re Phi2', dS/dg = -Im Phi2', dC/dy = dS/dg,
    dS/dy = -dC/dg must reproduce the same differences.
    """
    rec = derivative_bound_control()
    assert rec["n_points"] >= 20
    for key, ratio in rec["worst_ratio"].items():
        assert ratio < 1.0, f"bound {key} violated: ratio {ratio}"
    assert rec["identification_defect"] < 1e-8


def test_derivative_bounds_are_not_decorative():
    """A bound nothing approaches would hide a defect: each constant must be
    attained to within a factor of two somewhere on a dense scan."""
    for y in (0.05, 0.25, 0.5):
        att = bound_attainment(y)
        assert 0.5 < att["Cg"] < 1.0, att
        assert 0.5 < att["Sg"] < 1.0, att


def test_derivative_bound_identities_hold_pointwise():
    """dC/dy = dS/dg and dS/dy = -dC/dg (Cauchy-Riemann), so two constants
    suffice for four derivatives."""
    for y in (0.01, 0.2, 0.5):
        assert lam_Cy(y) == lam_Sg(y)
        assert lam_Sy(y) == lam_Cg(y)
    rng = np.random.default_rng(3)
    h = 1e-5
    for _ in range(8):
        g = float(rng.uniform(0.5, 50.0))
        y = float(rng.uniform(0.01, 0.5))

        def CS(gg, yy):
            v = phipap(np.array([complex(gg, yy)]))
            return float(v.real[0]), float(-v.imag[0])

        dCdy = (CS(g, y + h)[0] - CS(g, y - h)[0]) / (2 * h)
        dSdg = (CS(g + h, y)[1] - CS(g - h, y)[1]) / (2 * h)
        dSdy = (CS(g, y + h)[1] - CS(g, y - h)[1]) / (2 * h)
        dCdg = (CS(g + h, y)[0] - CS(g - h, y)[0]) / (2 * h)
        assert abs(dCdy - dSdg) < 1e-7
        assert abs(dSdy + dCdg) < 1e-7


def test_curvature_bound_holds():
    """|Phi2''(g+iy)| <= -Phi2''(iy), the Taylor remainder constant."""
    assert curvature_bound_control() < 1.0
    for y in (0.05, 0.5):
        assert curvature(y) > 0


def test_c_im_normalised_bound_holds():
    """|S(g,y)| <= y cosh(y0/2) C_IM_UNIT / g, the shallow cell's tail."""
    assert c_im_unit_control() < 1.0
    # and it must dominate the unnormalised paper_chain constant it replaces
    for y in (0.01, 0.05, 0.2, 0.5):
        assert y * c_im_normalised(0.5) >= c_im(y)


# ---------------------------------------------------------------------------
# (b) the cells tile (0, 1/2]
# ---------------------------------------------------------------------------


def test_depth_cells_tile_the_open_interval_exactly(du):
    """(b) No gap and no overlap, with endpoints checked as exact floats.

    The shallow cell is closed at y0 and open at 0; every regular cell shares
    its endpoint object with its neighbour, so adjacency is exact rather than
    within a tolerance.
    """
    cells = du.depth_cells()
    assert cells[0][0] == 0.0 and cells[0][2] == "shallow"
    assert cells[0][1] == du.y0
    for lo, hi, _ in cells:
        assert hi > lo
    for k in range(len(cells) - 1):
        assert cells[k][1] == cells[k + 1][0], (
            f"gap between cell {k} and {k+1}: {cells[k][1]!r} != "
            f"{cells[k+1][0]!r}")
    assert cells[-1][1] == du.y_max == 0.5
    assert len(cells) == du.n_cells + 1


def test_every_depth_lands_in_exactly_one_cell(du):
    cells = du.depth_cells()
    rng = np.random.default_rng(17)
    ys = list(rng.uniform(1e-9, 0.5, 200)) + [1e-300, 0.5, du.y0]
    for y in ys:
        hits = [c for c in cells if c[0] < y <= c[1]]
        assert len(hits) == 1, f"y={y} landed in {len(hits)} cells"


# ---------------------------------------------------------------------------
# (c) consistency with the four sampled depths
# ---------------------------------------------------------------------------


def test_cell_sups_dominate_the_true_field(du):
    """(c), the load-bearing half: the cell sup really is a sup.

    The per-bin F_up must exceed the true f_+ everywhere inside the bin AND
    everywhere inside the depth cell.  This is what makes a bin with F_up = 0
    a statement about the whole bin, which is why no missed-band allowance
    appears anywhere in this module.
    """
    edges = du.cell_edges()
    for cell in ((edges[0], edges[1]), (edges[-2], edges[-1])):
        rec = one_sidedness_control(du, *cell)
        assert rec["one_sided"], rec
        assert rec["worst_rel_excess"] <= 0.0, rec
    rec = shallow_one_sidedness_control(du)
    assert rec["one_sided"], rec
    assert rec["worst_rel_excess"] <= 0.0, rec


def test_degenerate_cell_reproduces_the_sampled_depth_caps(du):
    """(c), the comparison half: the degenerate cell [y, y] at the four
    sampled depths against paper_chain's point cap, at matched G.

    MEASURED, and reported rather than tuned: the ratio is 0.941 / 0.988 /
    0.996 / 0.997 at y = 0.02 / 0.1 / 0.3 / 0.49.  Strict domination of
    paper_chain's number therefore FAILS at all four, by most at the shallow
    end.  The difference is a margin convention, not a disagreement:
    paper_chain inflates each band by a band-level slope margin
    8 max|Phi2||Phi2'| * step / A^2, while this module inflates each bin by its
    own centre gradient plus a curvature remainder, which is smaller
    everywhere and smallest where the band is narrow (shallow y).  Both
    dominate the true field -- that is the test above -- so the tighter one is
    not the weaker one.  The test pins the agreement band and the direction.
    """
    rows = degenerate_vs_paper_chain(du, ys=SAMPLED)
    for row in rows:
        assert 0.90 <= row["ratio"] <= 1.02, row
        assert row["both_close"], row
    assert rows[0]["ratio"] < 1.0  # the recorded shallow-end deficit
    assert rows[-1]["ratio"] > rows[0]["ratio"]


def test_shallow_cell_dominates_the_point_caps_inside_it(du):
    """The homogeneity cell must cover the depths it claims: its normalised
    cap has to sit above cap(y)/y^2 computed directly at depths inside it."""
    shallow = du.shallow_cell(0.995)
    for y in (0.01, 0.03, du.y0):
        point = du.regular_cell(0.995, y, y)
        assert shallow["cap_up"] >= point["cap_up"] / (y * y) - 1e-12, (
            f"y={y}: shallow {shallow['cap_up']} < point "
            f"{point['cap_up']/(y*y)}")


def test_cell_caps_dominate_the_measured_adversary(du):
    """Dual over primal: paper_chain's greedy band-riding adversary, run at
    the paper field, must sit under the cap of the cell containing its depth."""
    for row in dominates_measured_adversary(du, theta=0.995, ys=(0.3, 0.49)):
        assert row["dominated"], row


def test_cell_sups_nest(du):
    """A cell's sups dominate any sub-cell's and the deep-lip point values."""
    edges = du.cell_edges()
    rec = nesting_control(du, edges[-2], edges[-1])
    assert rec["inner_excess"] <= 0.0, rec
    assert rec["deep_point_excess"] <= 0.0, rec


# ---------------------------------------------------------------------------
# (d) the convention control: theta = 1 must diverge
# ---------------------------------------------------------------------------


def test_theta_one_diverges_on_every_cell(du, profs):
    """(d) At theta = 1 the internal charge vanishes, stacking is unbounded
    and the cap must be infinite -- on the shallow cell too, where the y^2
    scaling could otherwise hide it."""
    for prof in (profs[0], profs[len(profs) // 2], profs[-1]):
        rec = du.cell_verdict(1.0, prof)
        assert not math.isfinite(rec["cap_up"]), rec
    for prof in (profs[0], profs[-1]):
        assert math.isfinite(du.cell_verdict(0.995, prof)["cap_up"])


def test_cap_is_monotone_in_theta(du, profs):
    """More retention claimed = less charge = a larger cap, on every cell."""
    for prof in (profs[0], profs[-1]):
        caps = [du.cell_verdict(t, prof)["cap_up"]
                for t in (0.9, 0.95, 0.99, 0.995, 0.996)]
        assert all(caps[i] <= caps[i + 1] + 1e-15 for i in range(len(caps) - 1)), caps


# ---------------------------------------------------------------------------
# (e) the direction of the worst corner
# ---------------------------------------------------------------------------


def test_worst_corner_directions_are_measured_not_assumed():
    """(e) sigma^2, E and c_im increase in y, so the damage-side constants are
    taken at the DEEP lip; slack/y^2 increases in y, so the budget is taken at
    the SHALLOW lip and NSLACK_0 = 8 L2/A is its floor over (0, 1/2]."""
    rec = monotonicity_control()
    assert rec["sigma2_increasing"]
    assert rec["E_increasing"]
    assert rec["c_im_increasing"]
    assert rec["nslack_increasing"]
    assert rec["nslack_floor"] >= NSLACK_0 - 1e-9
    assert abs(rec["NSLACK_0"] - 8 * L2 / A) < 1e-15
    # the floor is the y -> 0+ limit, and it is a genuine floor, not the value
    assert rec["nslack_at_half"] > NSLACK_0


def test_slack_is_smallest_at_the_shallow_lip(du):
    """The corner choice, restated on the cells actually used."""
    for lo, hi, kind in du.depth_cells():
        if kind != "regular":
            continue
        ys = np.linspace(lo, hi, 25)
        vals = [_PC.slack(float(y)) for y in ys]
        assert min(vals) == vals[0]


def test_normalised_slack_floor_is_the_shallow_budget():
    """slack(y)/y^2 >= 8 L2 / A on (0, 1/2], the inequality the shallow cell
    compares against; sinh(t) >= t is the whole content.

    The limit is checked through the CANCELLATION-FREE form
    sigma^2(y)/y^2 = (1/A) int p (sinh(yu)/y)^2 du, not through
    PaperChain.sigma2's difference (Phi2(2iy) - A)/(2A): that difference loses
    about four digits by y ~ 1e-4 and is worthless by y ~ 1e-6 (measured
    below), which is a second reason the shallow end cannot be handled by
    evaluating the point bound at ever smaller depths.
    """
    for y in (1e-3, 0.02, 0.2, 0.5):
        assert nslack(y) >= NSLACK_0 - 1e-12
    ts = np.linspace(-0.5, 0.5, 200001)
    p = np.cos(S2 * ts)
    for y in (1e-6, 1e-4, 1e-2):
        stable = 8 * float(np.trapezoid(p * (np.sinh(y * ts) / y) ** 2, ts)) / A
        assert stable >= NSLACK_0 - 1e-12
        if y <= 1e-4:
            assert abs(stable - NSLACK_0) < 1e-8
    # the difference form's own noise floor, recorded rather than relied on
    assert abs(nslack(1e-6) - NSLACK_0) > 1e-9


# ---------------------------------------------------------------------------
# the shallow cell's own machinery
# ---------------------------------------------------------------------------


def test_capacity_is_convex_through_the_origin():
    """B(lambda F) <= lambda B(F) for lambda in [0,1]: the step that lets the
    shallow cell's y^2 scaling pass through the square completion."""
    assert convexity_control() <= 0.0


def test_shallow_remainders_are_the_integrated_derivative_bounds():
    """eps_S and eps_C are integrals of the SAME two constants, so they cannot
    drift from the derivative bounds they inherit."""
    rec = DepthUniform(G=60.0, step=0.02, slices=1, y0=0.05).shallow_cell(0.995)
    y0 = 0.05
    ch = math.cosh(y0 / 2)
    assert abs(rec["eps_S"] - 2 * L2 * (ch - 1)) < 1e-18
    assert abs(rec["eps_C"] - 2 * L1 * (ch - 1)) < 1e-18
    # the integral form: int_0^{y0} sinh(t/2) L1 dt = 2 L1 (cosh(y0/2) - 1)
    ts = np.linspace(0.0, y0, 20001)
    assert abs(float(np.trapezoid(np.sinh(ts / 2) * L1, ts))
               - rec["eps_C"]) < 1e-12


def test_shallow_cell_covers_arbitrarily_small_depths(du):
    """The point of the homogeneity cell: no smallest depth is assumed."""
    F = du.shallow_damage_sups()
    gs = du.bin_centres()
    sel = np.where((gs > 5.0) & (gs < 40.0))[0]
    for y in (1e-6, 1e-4, 1e-2):
        v = phipap(gs[sel] + 1j * y)
        f = np.maximum(0.0, 4 * (v.imag**2 - v.real**2)) / A**2
        assert float((f - y * y * F[sel]).max()) <= 0.0, y


# ---------------------------------------------------------------------------
# the lesion and the precision response
# ---------------------------------------------------------------------------


def test_lesion_without_inflation_stops_majorising(du):
    """Plant the fault the construction exists to prevent: take each bin's
    value at the cell's shallow lip with no inflation and the cover stops
    dominating the field inside the cell."""
    edges = du.cell_edges()
    rec = lesion_no_inflation(du, edges[-2], edges[-1])
    assert rec["lesion_fires"], rec
    assert rec["worst_excess"] > 1e-4, rec


def test_precision_response_settles(du):
    """A finer offset grid and more depth slices must LOWER the cap (less
    inflation) and a longer resolved region must lower it further (less mass
    in the tail majorant) -- and the movement must be small."""
    edges = du.cell_edges()
    cell = (edges[-2], edges[-1])
    coarse = DepthUniform(G=120.0, step=0.01, slices=1)
    fine = DepthUniform(G=120.0, step=0.0025, slices=4)
    longer = DepthUniform(G=200.0, step=0.005, slices=2)
    c0 = coarse.regular_cell(0.995, *cell)["cap_up"]
    c1 = du.regular_cell(0.995, *cell)["cap_up"]
    c2 = fine.regular_cell(0.995, *cell)["cap_up"]
    c3 = longer.regular_cell(0.995, *cell)["cap_up"]
    assert c0 > c1 > c2, (c0, c1, c2)
    assert (c0 - c2) / c2 < 0.05, (c0, c2)
    assert c3 < c1, (c3, c1)


# ---------------------------------------------------------------------------
# the headline
# ---------------------------------------------------------------------------


def test_every_depth_cell_closes_at_the_secured_theta(du, profs):
    """THE claim: cap_up <= slack_lo on every cell of a cover of (0, 1/2],
    at theta = 0.995 -- the same grid point the four sampled depths give."""
    rows = du.scan(0.995, profs)
    assert len(rows) == du.n_cells + 1
    for row in rows:
        assert row["margin"] >= 0.0, row
        assert row["tail_single_occupancy"], row
    assert min(r["rel_margin"] for r in rows) > 0.05


def test_secured_theta_is_the_grid_maximum(du, profs):
    star, table = du.secured_theta(profs=profs)
    assert star == 0.995
    assert all(table[t]["all_closed"] for t in (0.9, 0.95, 0.99, 0.995))
    assert table[0.995]["worst_rel_margin"] < table[0.99]["worst_rel_margin"]


def test_the_binding_cells_are_the_deep_ones(du, profs):
    """Which cells bind, as a test rather than a remark: the worst margin sits
    in the deepest cells, where the square completion turns on (m* > 1)."""
    rows = du.scan(0.995, profs)
    worst = min(rows, key=lambda r: r["rel_margin"])
    assert worst["y_hi"] == du.y_max
    assert worst["m_star"] >= 2
    assert rows[0]["rel_margin"] > worst["rel_margin"]


def test_the_construction_stops_short_of_theta_one(du, profs):
    """It is a bound, not a tautology: it fails somewhere below 1."""
    _, table = du.secured_theta(thetas=(0.997, 0.999), profs=profs)
    assert not table[0.999]["all_closed"]
