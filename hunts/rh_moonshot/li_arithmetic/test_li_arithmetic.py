"""Tests for hunt #150 mechanism 3 (li_arithmetic): the split of lambda_n.

Each test can fail.  They pin:

* the split lambda_n = A(n) + T(n) at small n: closed forms at n = 1, the
  binomial and series routes for A(n), the Stieltjes and Cauchy routes for
  T(n), for zeta and for DH, and a planted fault (the Euler factor of 2
  removed) that the cross-check must see;
* the prime-side form: the Laguerre generating identity behind it, the
  elementary piece on [1, 2), and the regularized prime sum against T(n);
* the numbers NOTES.md quotes from the committed artifacts (split_zeta,
  split_dh, wa_quarter, prime_side), so a regenerated artifact that moved
  them turns a test red;
* the absolute-value route at small scale, recomputed: the pointwise bound
  exceeds the margin at every n <= 40 where the margin is positive.

Nothing here writes into the tree.
Run: .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/li_arithmetic/test_li_arithmetic.py
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np
from mpmath import mp

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from hunts.rh_moonshot.li_arithmetic import li_arith_prime as P  # noqa: E402
from hunts.rh_moonshot.li_arithmetic import li_arith_split as S  # noqa: E402
from hunts.rh_moonshot.li_arithmetic import li_arith_wa as W  # noqa: E402

ART = _HERE / "artifacts"


def _load(name):
    return json.loads((ART / name).read_text())


def _floats(xs):
    return np.array([float(x) for x in xs])


# ---------------------------------------------------------------------------
# the split at small n
# ---------------------------------------------------------------------------


def test_n1_closed_forms():
    with mp.workdps(40):
        A1 = S.zeta_archimedean(1, 35)[0]
        T1 = S.zeta_arithmetic_stieltjes(1, 35)[0]
        assert abs(T1 - mp.euler) < mp.mpf(10) ** -30
        assert abs(A1 - (1 - (mp.euler + mp.log(4 * mp.pi)) / 2)) < mp.mpf(10) ** -30
        lam1 = 1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2
        assert abs(A1 + T1 - lam1) < mp.mpf(10) ** -30


def test_archimedean_two_routes_agree():
    A = S.zeta_archimedean(60, 30)
    Ad = S.dh_archimedean(60, 30)
    with mp.workdps(30):
        for n in (1, 2, 3, 5, 10, 20, 60):
            assert abs(A[n - 1] - S.zeta_archimedean_series(n, 30)) < mp.mpf(10) ** -20
            assert abs(Ad[n - 1] - S.dh_archimedean_series(n, 30)) < mp.mpf(10) ** -20


def _cauchy_T(evaluator, n_max, radius="0.5", dps=30):
    wd = S.work_digits(n_max, dps, radius)
    N = S.node_count(n_max, wd, radius)
    res = S.cauchy_log_coefficients(evaluator, n_max, radius, wd, N)
    assert res["imag_residue_over_floor"] < 1.0
    return res["coefficients"]


def test_arithmetic_two_routes_agree_zeta_and_dh():
    n_max = 16
    Tz_st = S.zeta_arithmetic_stieltjes(n_max, 30)
    Tz_ca = _cauchy_T(S.zeta_arith_evaluator, n_max)
    Td_st = S.dh_arithmetic_stieltjes(n_max, 30)
    Td_ca = _cauchy_T(S.dh_f_evaluator(80), n_max)
    with mp.workdps(30):
        for n in range(1, n_max + 1):
            assert abs(Tz_st[n - 1] - Tz_ca[n - 1]) < mp.mpf(10) ** -18
            assert abs(Td_st[n - 1] - Td_ca[n - 1]) < mp.mpf(10) ** -18


def test_planted_fault_removing_the_euler_factor_of_2_is_seen():
    """(s-1) zeta(s) (1 - 2^-s) is not the arithmetic factor; T moves by O(1)."""

    def faulted(s):
        from flint import acb

        return (s - 1) * s.zeta() * (1 - acb(2) ** (-s))

    good = S.zeta_arithmetic_stieltjes(6, 30)
    bad = _cauchy_T(faulted, 6)
    # log(1 - 2^-s) at s = 1 is log(1/2): every coefficient shifts
    assert all(abs(float(bad[n] - good[n])) > 1e-3 for n in range(6))


def test_split_identity_against_the_li_dh_onset_tables():
    z = _load("split_zeta.json")
    d = _load("split_dh.json")
    assert float(z["max_abs_identity_defect"]) < 1e-25
    assert float(z["max_rel_lambda_vs_li_dh_onset_table"]) < 1e-28
    assert float(d["max_abs_identity_defect_vs_li_dh_onset_table"]) < 1e-24
    # and recompute the identity on the first 40 entries from the stored strings
    ref = S.load_lambda("dh")
    with mp.workdps(35):
        for n in range(1, 41):
            assert abs(ref[n - 1] - mp.mpf(d["A"][n - 1]) - mp.mpf(d["T"][n - 1])) < mp.mpf(10) ** -25
        # stored A(n) agrees with a fresh binomial computation
        A = S.zeta_archimedean(40, 30)
        for n in range(1, 41):
            assert abs(A[n - 1] - mp.mpf(z["A"][n - 1])) < mp.mpf(10) ** -25


# ---------------------------------------------------------------------------
# the prime-side form
# ---------------------------------------------------------------------------


def test_laguerre_generating_identity():
    """n [z^n] p^{-k s} at s = 1/(1-z) equals n p^{-k} L_n^{(-1)}(k log p)."""
    with mp.workdps(40):
        for p, k in ((2, 1), (3, 2), (5, 1)):
            x = k * mp.log(p)
            coeffs = mp.taylor(lambda z: mp.power(p, -k / (1 - z)), 0, 8)
            for n in range(1, 9):
                lhs = n * coeffs[n]
                rhs = n * mp.power(p, -k) * mp.laguerre(n, -1, x)
                assert abs(lhs - rhs) < mp.mpf(10) ** -30
                # and the form the module uses: L_n^{(-1)} = -(x/n) L_{n-1}^{(1)}
                assert abs(rhs + x * mp.power(p, -k) * mp.laguerre(n - 1, 1, x)) < mp.mpf(10) ** -30


def test_elementary_piece_on_1_2():
    """int_0^{log 2} L_{n-1}^{(2)}(u) du = n + 1 - L_n^{(1)}(log 2)."""
    L1 = P.laguerre1_at_log2(30)
    with mp.workdps(30):
        for n in (1, 2, 5, 12, 30):
            lhs = mp.quad(lambda u: mp.laguerre(n - 1, 2, u), [0, mp.log(2)])
            assert abs(lhs - (n + 1 - mp.laguerre(n, 1, mp.log(2)))) < mp.mpf(10) ** -20
            assert abs(L1[n - 1] - float(mp.laguerre(n, 1, mp.log(2)))) < 1e-10


def test_regularized_prime_sum_converges_to_T():
    m, lam = P.von_mangoldt_table(10**6)
    assert len(m) == 78734  # prime powers below 10^6
    T = _floats(_load("split_zeta.json")["T"][:6])
    r = P.prime_side_T(range(1, 7), 10**6, m, lam)
    for n in range(1, 7):
        assert abs(r[n]["integrated"] - T[n - 1]) < 2e-3  # measured at most 1.1e-3
    # the boundary term matters: the sharp sum is worse at every n here
    worse = sum(abs(r[n]["sharp"] - T[n - 1]) > abs(r[n]["integrated"] - T[n - 1]) for n in range(1, 7))
    assert worse == 6


def test_pointwise_route_fails_at_every_small_n_recomputed():
    """B(n) > M(n) wherever M(n) > 0, n <= 40, recomputed at x0 = 10^6."""
    m, lam = P.von_mangoldt_table(10**6)
    kb = P.kernel_bounds(40, m, lam, 10**6, du_fine=2e-4)
    A = _floats(_load("split_zeta.json")["A"][:40])
    M = A + 1.0 - np.array(P.laguerre1_at_log2(40))
    B = np.array(kb["B_pointwise"])
    pos = M > 0
    assert pos.sum() >= 35
    assert (B[pos] > 5 * M[pos]).all()


# ---------------------------------------------------------------------------
# the numbers NOTES.md quotes
# ---------------------------------------------------------------------------


def test_split_rival_gate_numbers():
    z = _load("split_zeta.json")
    d = _load("split_dh.json")
    Tz, Td = _floats(z["T"]), _floats(d["T"])
    Az, Ad = _floats(z["A"]), _floats(d["A"])
    Lz, Ld = _floats(z["lambda"]), _floats(d["lambda_from_li_dh_onset"])
    assert len(Tz) == len(Td) == 5000
    # |T(n)| stays small for both, against A(n) of order 10^4 at n = 5000
    assert 13.0 < np.abs(Tz).max() < 14.0 and int(np.abs(Tz).argmax()) + 1 == 3298
    assert 19.0 < np.abs(Td).max() < 19.5 and int(np.abs(Td).argmax()) + 1 == 2799
    assert Az[-1] > 15000 and Ad[-1] > 19000
    assert (Lz > 0).all() and (Ld > 0).all()
    n = np.arange(100, 5001)
    for T in (Tz, Td):
        assert np.abs(T[99:] / (n / 2 * np.log(n))).max() < 0.012


def test_wa_quarter_numbers():
    w = _load("wa_quarter.json")
    L = _floats(w["lambda"])
    assert w["first_negative_index"] == 8260
    assert (L[:8259] > 0).all() and L[8259] < 0
    assert float(w["radius_control"]["max_rel_difference"]) < 1e-40
    zs = w["zero_side"]["8260"]
    assert float(zs["cauchy"]) < -100 and float(zs["zeros"]) < -100
    sp = w["split"]
    assert abs(float(sp["5000"]["T_W"])) < 30
    assert float(sp["8258"]["T_W"]) < -5e4


def test_wa_split_three_routes_small_n():
    """lambda_n(F_a) from the stored r = 0.95 table equals A_W(n) + T_W(n),
    with T_W by a Cauchy integral at r = 0.5 on the arithmetic factor."""
    w = _load("wa_quarter.json")
    TW = W.wa_arithmetic_cauchy(8, radius="0.5", dps=25)
    with mp.workdps(25):
        for n in range(1, 9):
            lhs = mp.mpf(w["lambda"][n - 1])
            assert abs(lhs - W.wa_archimedean(n, dps=25) - TW[n - 1]) < mp.mpf(10) ** -12


def test_radius_admissibility_rule():
    assert W.radius_admissible(0.95) and W.radius_admissible(0.998)
    assert not W.radius_admissible(0.999)


def test_prime_side_artifact_numbers():
    d = _load("prime_side.json")
    assert d["x0"] == 10**8 and d["n_max"] == 5000
    assert d["prime_powers_below_x0"] == 5762859
    assert d["pointwise_route_succeeds_at"] == []
    assert d["min_ratio_B_over_M_where_M_positive"] > 11.0
    assert d["meansquare_route_succeeds_range"] == [32, 1258]
    assert d["meansquare_route_succeeds_at_count"] == 1227
    assert d["margin_negative_up_to"] == 4
    M = np.array(d["margin_M"])
    Pn = np.array(d["P_exact"])
    assert (Pn[4:] / M[4:]).max() < 0.46  # measured 0.4538 at n = 8
    BL = np.array(d["B_meansquare"])
    assert BL[-1] / M[-1] > 3.0  # measured 3.05 at n = 5000
    U = np.array(d["B_unconditional_shape"])
    assert (U > M[:200]).all()


def _onset_heuristic(delta, gamma):
    """Root of n log R = log((n/4) log n), R = 1/|1 - 1/(1/2 + delta + i gamma)|:
    where 2 R^n from one off-line quadruple reaches the baseline (n/2) log n."""
    with mp.workdps(30):
        s0 = mp.mpc(mp.mpf(1) / 2 + delta, gamma)
        lR = mp.log(1 / abs(1 - 1 / s0))
        return float(mp.findroot(lambda n: n * lR - mp.log(n * mp.log(n) / 4), 10 / lR))


def test_onset_heuristic_against_wa_and_dh():
    """NOTES.md section 5: the heuristic is within 6 percent of W_{1/4}'s measured
    first negative index and within 1 percent of DH's extrapolated one."""
    n_wa = _onset_heuristic(mp.mpf(1) / 4, mp.mpf("14.134725141734694"))
    n_dh = _onset_heuristic(mp.mpf("0.30851718245663738"), mp.mpf("85.69934848537759"))
    assert 7800 < n_wa < 7850 and abs(n_wa / 8260 - 1) < 0.06
    assert 329000 < n_dh < 331000 and abs(n_dh / 328997 - 1) < 0.01
    onset = json.loads((_ROOT / "hunts" / "li_dh_onset" / "artifacts" / "onset.json").read_text())
    assert "328997" in json.dumps(onset["onset"])
