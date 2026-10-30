"""read_rows.py: the reading of the rebuilt rows (PREREG s2 to s4), each step against a planted fault."""
from __future__ import annotations

import os
import sys

import pytest
from flint import acb, acb_mat, arb, ctx, fmpq

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import read_rows as RR  # noqa: E402


@pytest.fixture(autouse=True)
def _prec():
    old = ctx.prec
    ctx.prec = 133
    yield
    ctx.prec = old


def _diag(vals):
    n = len(vals)
    return [[fmpq(vals[i]) if i == j else fmpq(0) for j in range(n)] for i in range(n)]


def test_eps_shift_counts_surviving_negatives_only():
    import run_checker_inertia as RI

    A = _diag([fmpq(-2, 100), fmpq(-5, 1000), 1, 1, 1])
    assert RI.inertia_both(RI.shifted(A, fmpq(1, 100)))[0] == 1  # -0.005 does not survive eps = 0.01
    assert RI.inertia_both(RI.shifted(A, fmpq(1, 1000)))[0] == 2  # planted: a smaller eps keeps both


def test_h_is_the_sum_zero_space():
    import run_checker_inertia as RI

    n = 5
    # I - (2/n) J: the all-ones vector has eigenvalue -1, every vector of H has +1
    A = [[(fmpq(1) if i == j else fmpq(0)) - fmpq(2, n) for j in range(n)] for i in range(n)]
    assert RI.inertia_both(A)[0] == 1
    assert RI.inertia_both(RR.compress(A, RR.h_basis(n))) == (0, 0, n - 1)
    # planted: a negative direction inside H (e_1 - e_2) is seen there
    B = [row[:] for row in A]
    for (i, j), v in {(1, 1): -3, (2, 2): -3, (1, 2): 3, (2, 1): 3}.items():
        B[i][j] += v
    assert RI.inertia_both(RR.compress(B, RR.h_basis(n)))[0] == 1
    assert all(sum(col) == 0 for col in RR.h_basis(n)) and len(RR.h_basis(n)) == n - 1


def test_the_row_rule_d0_d1_d2():
    s = RR.SCALE
    assert s == fmpq(118, 10000)
    assert RR.row(s - fmpq(1, 10 ** 9), True, True) == "D1"
    assert RR.row(s, True, True) == "D2"  # at the scale is D2 (PREREG s3: "at or above")
    assert RR.row(fmpq(1, 10 ** 6), False, True) == "D0"  # not finite
    assert RR.row(fmpq(1, 10 ** 6), True, False) == "D0"  # a provider that is not a bound


def test_ball_to_rational_bounds():
    x = arb("0.3") + arb(0, 1e-10)
    up = RR.arb_up_q(x)
    assert arb(up) >= x.upper() and up > fmpq(3, 10)
    m = RR.arb_mid_q(arb(2) ** -70 * 3)
    assert m == fmpq(3, 2 ** 70)
    with pytest.raises(ArithmeticError):
        RR.arb_up_q(arb("nan"))


def test_r_centre_bounds_the_imaginary_part_and_the_asymmetry():
    N = 2
    n = 2 * N + 1
    D = acb_mat(n, n)
    R, e_im, e_asym = RR.r_centre(D, "2.9", N)
    assert e_im == 0 and e_asym == 0 and all(R[i][j] == R[j][i] for i in range(n) for j in range(n))
    D[0, 1] = acb(0, arb("1e-3"))  # planted: an imaginary part
    D[1, 0] = acb(0, arb("-1e-3"))
    _, e_im, _ = RR.r_centre(D, "2.9", N)
    assert e_im >= fmpq(14, 10 ** 4)  # sqrt(2) * 1e-3
    D = acb_mat(n, n)
    D[0, 1] = acb(arb("1e-3"))  # planted: an asymmetric real part
    R2, _, e_asym = RR.r_centre(D, "2.9", N)
    assert e_asym >= fmpq(7, 10 ** 4) and R2[0][1] == R2[1][0]


# The full run 40371181784 (RUNS.md s11.6, RESULTS fourth unit): its rows and the exact centres
RUN_ROWS = os.path.join(HERE, "rows_40371181784.json")
RUN_CENTRES = os.path.join(HERE, "centres_40371181784.json")
PINNED = {  # cell: (full, H, V4) = C_N(eps) on the three spaces
    "2.2|8": (4, 4, 2), "2.2|16": (7, 6, 4), "2.2|32": (18, 18, 16),
    "2.5|8": (5, 5, 3), "2.5|16": (10, 9, 8), "2.5|32": (21, 20, 20),
    "2.9|8": (5, 5, 3), "2.9|16": (11, 10, 8), "2.9|32": (23, 22, 20),
}


def _sha(path):
    import hashlib

    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def _run():
    import json

    return json.load(open(RUN_ROWS))


def test_the_full_run_files_by_digest():
    assert _sha(RUN_ROWS) == "6c367e44fc96ac5784ebc33c1817a06d0c28602cbcaae74baa0844d324ae4311"
    assert _sha(RUN_CENTRES) == "1b5bf15b58d61c805e973f90a78f5544723dc27f46ee771b8c1e6e22aa0aa366"
    assert len(_run()["checkpoints_sha256"]) == 34  # shards 34 and 35 hold no block


def test_the_full_run_reads_d1_at_every_c():
    r = _run()
    assert r["is_bound"] is True
    eq = {"2.2": 9.219e-4, "2.5": 7.826e-4, "2.9": 6.662e-4}
    for c, v in eq.items():
        row = r["rows"][c]
        assert row["row"] == "D1" and abs(row["eps_q_max"] - v) < 1e-7
        # the rule re-applied to the recorded eps_q; planted: the same eps_q at the scale reads D2
        q = max(fmpq(*r["cells"][f"{c}|{N}"]["eps"]) for N in (8, 16, 32))
        assert RR.row(q, True, True) == "D1" and RR.row(q + RR.SCALE, True, True) == "D2"
    for kk, (f, h, v4) in PINNED.items():
        C = r["cells"][kk]["C"]
        assert (C["full"], C["H"], C["V4"]) == (f, h, v4) and C["V4_by"] == "balls"
        assert f - 1 <= h <= f and f - 3 <= v4 <= f  # interlacing (codim 1 and 3)
        assert r["cells"][kk]["e_asym"] == 0 and r["cells"][kk]["e_im"] < 1e-35
    sc = r["stored_comparison"]
    assert abs(sc["norm2"] - 5.148e-3) < 1e-6 and sc["exceeds"] is False
    assert sc["norm2"] < sc["band_plus_eps_q"] < 1.8 * sc["norm2"]  # planted: 1.8 times the norm exceeds


def _recount(kk, shift=None):
    import json

    D = RR.centres_from({kk: json.load(open(RUN_CENTRES))[kk]})[kk]
    c, N = kk.split("|")
    R, _, _ = RR.r_centre(D, c, int(N))
    if shift is not None:
        R = [[R[i][j] + (shift if i == j else 0) for j in range(len(R))] for i in range(len(R))]
    C = RR.counts(R, fmpq(*_run()["cells"][kk]["eps"]), int(N), c)
    return C["full"], C["H"], C["V4"]


def test_n8_counts_recomputed_from_the_centres():
    for c in ("2.2", "2.5", "2.9"):
        assert _recount(f"{c}|8") == PINNED[f"{c}|8"]
    # planted: R_centre shifted by -1e-2 (the scale's size) raises the counts
    assert _recount("2.9|8", fmpq(-1, 100))[0] == 6
    assert _recount("2.2|8", fmpq(-1, 100))[0] == 5


@pytest.mark.slow
@pytest.mark.parametrize("kk", [k for k in PINNED if not k.endswith("|8")])
def test_n16_n32_counts_recomputed_from_the_centres(kk):
    assert _recount(kk) == PINNED[kk]
