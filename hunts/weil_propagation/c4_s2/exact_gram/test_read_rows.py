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
