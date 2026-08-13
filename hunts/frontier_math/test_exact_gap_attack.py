"""Controls for ``exact_gap_attack.py``.

Five families, in the order the module's claims are made:

(a) **the form**.  The gap by three independent routes — closed forms, the
    single functional against ``c2 dw``, and the two energies it is defined
    from — must agree, and must agree with the existing quadrature
    evaluators in ``spectral_gap.py``, on eight configurations including
    coincident points and a tight cluster;
(b) **the kernel**.  ``K = phiR^2`` must be numerically PSD on a fine grid
    (it is a square of a transform, so anything else is a bug), pointwise
    nonnegative, and decreasing across the first period — the three facts
    the closing argument rests on;
(c) **the relaxation is a lower bound, and it is too weak**.  The convex QP
    must lower-bound every integer configuration supported on its grid; and
    its infimum over the line must go negative and keep going, at the rate
    the dust mechanism predicts;
(d) **planted faults**.  A wrong coefficient in the identity must break the
    route agreement; inflated damage and a degraded cluster price must each
    turn the window bound negative, and the inflated-damage case must come
    with an explicit configuration that really is negative — a bound that
    could not say no would be worthless;
(e) **the small cases against Lean**.  For ``n <= 3`` the extension package
    has a kernel-checked retention theorem with no separation hypothesis
    (``Retention.retention_le_three``); the measured minima must be positive
    there, and the two constants that proof rests on must hold as measured.

Nothing here is a proof.  The window table, the window width and the price
``kappa`` are measured, and the tail beyond the scan is bounded by a
measured envelope.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exact_gap_attack import (  # noqa: E402
    A, A2, COEF, CONFIGS, KAPPA_FAR, KAPPA_NEAR, LEAN_BUDGET, K, Wt,
    adversary_design, atomic_minimum, c2, damage, damage_profile,
    damage_windows, diffuse_value, energy, gap_energy, gap_kernel,
    gap_spectral, gram_eigenvalues, grid_objective, integer_deficit,
    kernel_is_decreasing, phi_r, qim, qim_envelope, qre, rational_certificate,
    relaxed_infimum, relaxed_minimum, shq, window_bound,
)

#: the y the whole argument is worst at, and the one the Lean files fix.
Y_HALF = 0.5
#: Lean's ``no_damage`` radius, ``28/5``.
LEAN_NO_DAMAGE_RADIUS = 28 / 5
#: Lean's ``uniform_damage`` constant, ``383/10000``.
LEAN_UNIFORM_DAMAGE = 383 / 10000
#: Lean's ``Shq_half_lower``: ``Shq y / 2 >= 12986/100000 * y^2``.
LEAN_SHQ_HALF_LOWER = 12986 / 100000


# ---------------------------------------------------------------------------
# (a) the form: three routes, and the existing evaluators
# ---------------------------------------------------------------------------


def test_the_three_routes_agree_on_every_configuration() -> None:
    """Closed form, one-functional, two-energies: the same number to 1e-10."""
    assert len(CONFIGS) >= 6
    worst = 0.0
    for xs, y, t in CONFIGS:
        a = gap_kernel(xs, y, t)
        b = gap_spectral(xs, y, t)
        c = gap_energy(xs, y, t)
        worst = max(worst, abs(a - b), abs(a - c))
    assert worst < 1e-10, f"routes disagree by {worst:.2e}"


def test_the_form_matches_the_existing_evaluator() -> None:
    """Against ``spectral_gap.gap_direct``, which is built on quadrature."""
    import spectral_gap as sg

    worst = 0.0
    for xs, y, t in CONFIGS:
        worst = max(worst, abs(gap_kernel(xs, y, t) - sg.gap_direct(xs, y, t)))
    assert worst < 1e-10, f"disagrees with spectral_gap.gap_direct by {worst:.2e}"


@pytest.mark.slow
def test_the_spectral_form_matches_the_existing_spectral_evaluator() -> None:
    """``spectral_gap.gap_spectral`` integrates ``c2`` by nested quadrature."""
    import spectral_gap as sg

    for xs, y, t in CONFIGS[:3]:
        assert abs(gap_spectral(xs, y, t) - sg.gap_spectral(xs, y, t)) < 1e-9


def test_the_closed_forms_reproduce_the_defining_integrals() -> None:
    from scipy.integrate import quad

    g = lambda u: math.cos(math.sqrt(2) * u)
    assert abs(A - quad(g, -0.5, 0.5)[0]) < 1e-14
    for w in (0.0, 0.3, 0.77, 0.999):
        ref = quad(lambda u: g(u) * g(u + w), -0.5, min(0.5, 0.5 - w))[0]
        assert abs(float(c2(w)) - ref) < 1e-12
    for a, b in ((0.5, 3.0), (0.25, 6.517), (0.0, 12.7), (1.0, 0.0)):
        ref_re = quad(lambda u: g(u) * math.cosh(a * u) * math.cos(b * u), -0.5, 0.5)[0]
        ref_im = quad(lambda u: g(u) * math.sinh(a * u) * math.sin(b * u), -0.5, 0.5)[0]
        assert abs(float(qre(a, b)) - ref_re) < 1e-12
        assert abs(float(qim(a, b)) - ref_im) < 1e-12
    assert abs(quad(c2, -1, 1, limit=200)[0] - A2) < 1e-12


def test_both_sums_are_transforms_of_the_same_weight() -> None:
    """The master identity: this is what makes the gap ONE functional."""
    from scipy.integrate import quad

    for y, s in ((0.5, 7.1), (0.3, 0.0), (0.5, 6.517), (0.1, 13.0)):
        ref = quad(lambda w: float(c2(w)) * math.cosh(y * w) * math.cos(s * w),
                   -1, 1, limit=400)[0]
        assert abs(float(damage_profile(y, s)) - ref) < 1e-10
    for u in (0.0, 1.0, 6.28):
        ref = quad(lambda w: float(c2(w)) * math.cos(u * w), -1, 1, limit=400)[0]
        assert abs(float(K(u)) - ref) < 1e-10
    ref = quad(lambda w: float(c2(w)) * 4.0 * math.sinh(0.5 * w) ** 2, -1, 1, limit=400)[0]
    assert abs(2 * shq(0.5) - ref) < 1e-10


def test_the_diagonal_of_the_double_sum_is_the_subtracted_self_energy() -> None:
    """``K(0) = A^2``: the ``- n A^2`` of the identity is exactly the diagonal."""
    assert abs(float(K(0.0)) - A2) < 1e-14
    assert abs(float(phi_r(0.0)) - A) < 1e-14


def test_energy_of_the_on_line_sum_is_at_least_n() -> None:
    """``Retention.energy_F_ge``, measured: every off-diagonal pair is >= 0."""
    rng = np.random.default_rng(3)
    for n in (1, 3, 7):
        for _ in range(5):
            xs = rng.uniform(-30, 30, n)
            assert energy(xs, None, 0.0) >= n - 1e-12


# ---------------------------------------------------------------------------
# (b) the kernel: PSD, nonnegative, decreasing
# ---------------------------------------------------------------------------


def test_the_pair_kernel_is_numerically_psd() -> None:
    """It is the square of a transform, so its Gram matrices must be PSD."""
    for grid in (np.arange(-20.0, 20.0001, 0.2),
                 np.arange(-6.0, 6.0001, 0.05),
                 np.sort(np.random.default_rng(0).uniform(-40, 40, 400))):
        ev = gram_eigenvalues(grid)
        assert ev.min() > -1e-9 * max(ev.max(), 1.0), f"min eigenvalue {ev.min():.3e}"


def test_the_pair_kernel_is_pointwise_nonnegative() -> None:
    u = np.arange(0.0, 200.0, 1e-3)
    assert float(K(u).min()) >= 0.0


def test_the_pair_kernel_decreases_across_the_first_period() -> None:
    """So ``min_{|u| <= w} K = K(w)``, which is the cluster price."""
    assert kernel_is_decreasing(step=1e-4) <= 0.0
    assert float(K(1.0)) > 0.75


# ---------------------------------------------------------------------------
# (c) the relaxation: a valid lower bound, and too weak to close anything
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_the_relaxation_lower_bounds_integer_configurations_on_its_grid() -> None:
    """The QP is convex over a set containing every on-grid configuration."""
    rng = np.random.default_rng(5)
    half, step = 30.0, 0.25
    grid = np.arange(-half, half + step / 2, step)
    for n in (3, 8):
        relaxed = relaxed_minimum(n, Y_HALF, half_width=half, step=step)
        for _ in range(25):
            idx = rng.integers(0, len(grid), n)
            masses = np.bincount(idx, minlength=len(grid)).astype(float)
            value = grid_objective(masses, grid, Y_HALF)
            assert relaxed.value <= value + 1e-7, (
                f"relaxed {relaxed.value:.8f} exceeds an integer configuration "
                f"{value:.8f} on its own grid")
            # and the grid objective is the gap of the repeated configuration
            xs = np.repeat(grid, masses.astype(int))
            assert abs(value - gap_kernel(xs, Y_HALF, 0.0)) < 1e-10


@pytest.mark.slow
def test_the_relaxation_goes_negative_and_keeps_going() -> None:
    """Dust: the relaxed infimum falls by exactly 1/200 per extra atom."""
    values = {n: relaxed_infimum(n, Y_HALF, half_width=35.0, step=0.1)[0]
              for n in (10, 20, 30, 40, 60)}
    assert values[10] > 0.0
    assert values[40] < 0.0, "the relaxation should not survive n = 40"
    for lo, hi in ((20, 30), (30, 40), (40, 60)):
        slope = (values[lo] - values[hi]) / (hi - lo)
        assert abs(slope - COEF) < 1e-6, f"slope {slope:.8f} is not 1/200"


@pytest.mark.slow
def test_the_relaxed_minimiser_is_not_a_configuration() -> None:
    """Fractional occupation: the reason the relaxation is too weak."""
    _, _, masses, grid = relaxed_infimum(20, Y_HALF, half_width=35.0, step=0.05)
    peak = float(masses.max())
    assert peak > 1.5, "expected a heavily occupied damage peak"
    assert abs(peak - round(peak)) > 0.02, (
        f"peak mass {peak:.4f} is an integer; the relaxation would be realizable")


def test_the_dust_limit_is_what_the_relaxation_chases() -> None:
    """``2 Shq/A^2 - n/200``: below zero from n = 33, for every kernel."""
    assert diffuse_value(1, Y_HALF) > 0
    assert diffuse_value(40, Y_HALF) < 0
    assert 32 <= min(n for n in range(1, 60) if diffuse_value(n, Y_HALF) < 0) <= 33


# ---------------------------------------------------------------------------
# (d) planted faults
# ---------------------------------------------------------------------------


def test_a_wrong_quadratic_coefficient_breaks_the_route_agreement() -> None:
    """The lesion the route-agreement control exists to catch."""
    def lesioned(xs, y, t, coef):
        x = np.asarray(xs, dtype=float)
        rep = float(K(x[:, None] - x[None, :]).sum()) - len(x) * A2
        dam = float(np.sum(damage_profile(y, x - t)))
        return (coef * rep + 4.0 * dam + 2.0 * shq(y)) / A2

    xs, y, t = CONFIGS[2]
    assert abs(lesioned(xs, y, t, COEF) - gap_spectral(xs, y, t)) < 1e-10
    assert abs(lesioned(xs, y, t, 1 / 100) - gap_spectral(xs, y, t)) > 1e-3


def test_inflated_damage_turns_the_window_bound_negative() -> None:
    honest = window_bound(Y_HALF, s_max=120.0, step=1e-3)
    assert honest.bound_gap > 0
    lesion = window_bound(Y_HALF, s_max=120.0, step=1e-3, damage_scale=2.0)
    assert lesion.bound_gap < 0, "the bound cannot say no, so it says nothing"


def test_the_inflated_damage_lesion_is_a_real_violation_not_a_lossy_bound() -> None:
    """Detector power: at ``damage_scale = 2`` a configuration really is negative."""
    xs = adversary_design(24, Y_HALF, reach=60.0)
    x = np.asarray(xs, dtype=float)
    rep = float(K(x[:, None] - x[None, :]).sum()) - len(x) * A2
    dam = float(np.sum(damage_profile(Y_HALF, x)))
    lesioned = (COEF * rep + 4.0 * 2.0 * dam + 2.0 * shq(Y_HALF)) / A2
    assert lesioned < 0.0, f"the planted violation is not visible ({lesioned:+.6f})"
    honest = (COEF * rep + 4.0 * dam + 2.0 * shq(Y_HALF)) / A2
    assert honest > 0.0


def test_a_degraded_cluster_price_turns_the_window_bound_negative() -> None:
    """If ``kappa`` were small the argument would not close, and must say so."""
    assert window_bound(Y_HALF, s_max=120.0, step=1e-3, kappa_override=0.05).bound_gap < 0


def test_a_wrong_window_width_is_visible_in_the_bound() -> None:
    """Widening the windows past the first period destroys the price."""
    wide = window_bound(Y_HALF, s_max=120.0, step=1e-3, width_override=6.0)
    assert wide.kappa < 0.01
    assert wide.bound_gap < 0


# ---------------------------------------------------------------------------
# (e) the small cases, against the Lean files
# ---------------------------------------------------------------------------


def test_small_configurations_agree_with_retention_le_three() -> None:
    """``Retention.retention_le_three``: ``n <= 3``, no separation, gap >= 0."""
    for n in (1, 2, 3):
        value, _ = atomic_minimum(n, Y_HALF, seed=n, n_random=8, reach=30.0)
        assert value > 0.0, f"n={n} minimum {value:+.8f} contradicts Lean"
    assert abs(atomic_minimum(1, Y_HALF, seed=1, n_random=8, reach=30.0)[0]
               - 0.13912712) < 1e-5
    assert abs(atomic_minimum(2, Y_HALF, seed=2, n_random=8, reach=30.0)[0]
               - 0.11829567) < 1e-5


def test_the_two_constants_the_lean_proof_rests_on() -> None:
    """``uniform_damage``, ``no_damage`` and ``Shq_half_lower``, as measured."""
    s = np.arange(0.0, 400.0, 1e-3)
    worst = float(damage(Y_HALF, s).max()) / Y_HALF ** 2
    assert worst < LEAN_UNIFORM_DAMAGE, f"measured {worst:.6f}"
    near = np.arange(0.0, LEAN_NO_DAMAGE_RADIUS, 1e-4)
    assert float(damage(Y_HALF, near).max()) == 0.0
    for y in (0.5, 0.3, 0.1, 0.01):
        assert shq(y) / 2 >= LEAN_SHQ_HALF_LOWER * y ** 2
    # the Lean route for n <= 3 is the budget alone; it stops working at n = 8
    assert 3 * worst * Y_HALF ** 2 < shq(Y_HALF) / 2
    assert 8 * worst * Y_HALF ** 2 > shq(Y_HALF) / 2


# ---------------------------------------------------------------------------
# the bound itself
# ---------------------------------------------------------------------------


def test_the_window_bound_is_positive_at_every_measured_y() -> None:
    for y in (0.5, 0.4, 0.3, 0.2, 0.1, 0.05):
        wb = window_bound(y, s_max=120.0, step=1e-3)
        assert wb.bound_gap > 0, f"y={y}: {wb}"
        assert wb.margin > 1.5


def test_the_window_bound_is_worst_at_y_one_half() -> None:
    margins = {y: window_bound(y, s_max=120.0, step=1e-3).margin
               for y in (0.5, 0.4, 0.3, 0.2, 0.1)}
    assert margins[0.5] == min(margins.values())
    assert margins[0.5] > 1.7


def test_the_window_bound_is_stable_under_refinement() -> None:
    """Discretisation ladder: scan step, then scan reach."""
    values = [window_bound(Y_HALF, s_max=120.0, step=st).bound_gap
              for st in (2e-3, 1e-3, 5e-4)]
    assert max(values) - min(values) < 1e-9
    reaches = [window_bound(Y_HALF, s_max=sm, step=1e-3).bound_gap
               for sm in (60.0, 120.0, 240.0)]
    assert all(b > 0.066 for b in reaches)
    assert reaches[0] <= reaches[1] <= reaches[2]      # the tail bound only shrinks


def test_the_window_bound_does_not_exceed_any_measured_configuration() -> None:
    """A lower bound above a measured value would be a bug, not a result."""
    bound = window_bound(Y_HALF, s_max=120.0, step=1e-3).bound_gap
    rng = np.random.default_rng(11)
    for n in (1, 2, 5, 9):
        assert gap_kernel(adversary_design(n, Y_HALF, reach=40.0), Y_HALF, 0.0) >= bound
        for _ in range(15):
            assert gap_kernel(rng.uniform(-40, 40, n), Y_HALF, 0.0) >= bound


def test_the_windows_are_where_the_far_field_exchange_says_they_are() -> None:
    wins = damage_windows(Y_HALF, s_max=60.0, step=1e-4)
    assert len(wins) == 9
    assert abs(wins[0].lo - 6.0653187731) < 1e-4
    assert max(w.width for w in wins) < 0.99
    peaks = [w.cap for w in wins[:6]]
    expected = [4.396424e-3, 9.750553e-4, 4.232798e-4, 2.361108e-4, 1.505230e-4, 1.043081e-4]
    for got, want in zip(peaks, expected):
        assert abs(got - want) < 1e-8
    # spacing approaches 2 pi from below, which is what the tail bound assumes
    lows = [w.lo for w in wins]
    assert all(6.0 < b - a < 2 * math.pi for a, b in zip(lows, lows[1:]))


def test_the_integer_trade_is_where_the_argument_lives() -> None:
    """Over the reals the deficit is unbounded in the mass; over Z it is not."""
    q = float(K(0.986)) / 200
    cap = 4.396424e-3
    deficit, m = integer_deficit(cap, q)
    assert m == 3 and abs(deficit - 0.02928588) < 1e-6
    real_opt = (0.5 + 2 * cap / q)
    assert 4 * cap * real_opt - q * real_opt * (real_opt - 1) > deficit


def test_the_rational_certificate_closes_exactly() -> None:
    """The same bound in exact rationals, on Lean's constants: surplus > 0."""
    rc = rational_certificate()
    assert len(rc.windows) == 9
    assert rc.surplus > 0                      # a statement about Fractions
    assert rc.margin > 1.6
    assert rc.gap_bound > 0.0597
    assert float(rc.deficit) < float(rc.budget)


def test_the_rational_constants_hold() -> None:
    """Every number the rational bound is allowed to use, measured."""
    u = np.arange(0.0, 1.0 + 1e-9, 1e-4)
    assert float(K(u).min()) >= float(KAPPA_NEAR)
    u6 = np.arange(0.0, 6.0 + 1e-9, 1e-4)
    assert float(K(u6).min()) >= float(KAPPA_FAR)
    for y in (0.5, 0.37, 0.2, 0.05, 0.01):
        assert 2 * shq(y) >= float(LEAN_BUDGET) * y ** 2
        s = np.arange(5.6, 400.0, 1e-3)
        maj = y ** 2 * np.array([float(Wt(F(int(round(v * 1000)), 1000) ** 2 - 2))
                                 for v in (5.6, 20.0, 100.0, 399.0)])
        got = np.array([float(qim(y, v)) ** 2 for v in (5.6, 20.0, 100.0, 399.0)])
        assert np.all(got <= maj)


def test_the_window_table_covers_every_y_below_one_half() -> None:
    """Windows nest and caps dominate: one table serves all ``y <= 1/2``."""
    rc = rational_certificate()
    base = damage_windows(Y_HALF, s_max=60.0, step=1e-4)
    assert len(base) == len(rc.windows)
    for y in (0.45, 0.3, 0.15, 0.05):
        wins = damage_windows(y, s_max=60.0, step=1e-4)
        assert len(wins) <= len(base)
        for w, (lo, hi, cap) in zip(wins, rc.windows):
            assert float(lo) <= w.lo and w.hi <= float(hi), "windows stopped nesting"
            assert w.cap <= float(cap) * y ** 2, "a cap stopped dominating"
    # and nothing outside the nine intervals damages, on the range they cover
    s = np.arange(28 / 5, 60.0, 1e-3)
    inside = np.zeros_like(s, dtype=bool)
    for lo, hi, _ in rc.windows:
        inside |= (s >= float(lo)) & (s <= float(hi))
    for y in (0.5, 0.25):
        assert float(damage(y, s[~inside]).max()) == 0.0


def test_the_tail_envelope_decreases_in_the_scan_reach() -> None:
    envs = [qim_envelope(Y_HALF, s0) for s0 in (50.0, 120.0, 400.0)]
    assert envs[0] >= envs[1] >= envs[2] > 0.7


# ---------------------------------------------------------------------------
# vocabulary
# ---------------------------------------------------------------------------


def test_these_files_keep_the_hunt_vocabulary() -> None:
    """The reserved word belongs to ``zeta/rigor.py``; the other four to no one
    here.  Spelled in pieces so this file does not itself trip the scan."""
    banned = ("certi" + "fied", "veri" + "fied", "con" + "firmed",
              "defini" + "tively", "pro" + "ves")
    here = Path(__file__).resolve().parent
    for name in ("exact_gap_attack.py", "test_exact_gap_attack.py"):
        text = (here / name).read_text(encoding="utf-8").lower()
        for word in banned:
            assert word not in text, f"{name} uses the banned word {word!r}"
