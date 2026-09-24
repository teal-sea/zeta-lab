"""Follow-up 3 tests (checker/, RESULTS s7.9): exact inertia of the stored
c = 2.9 matrices.

PRE-REGISTERED. This file was committed before any inertia of a stored
matrix was computed (the commit that adds it; s7.9 names it). Two groups.

1. The exact routes, on planted matrices whose inertia is known by
   construction. These ran before the commit; they touch no stored matrix.
2. The reading, on checker_inertia.json (run_checker_inertia.py). They skip,
   with the reason, while that file is absent. What they assert was fixed
   before the numbers: the shift is the band stored in
   checker_ts_cells.json (read, never re-derived), the matrix is the one
   whose float64 eigenvalues gave the count, the two exact routes agree
   everywhere, and the count HOLDS on a build when the exact negative count
   of R + band I equals the stored float count, no eigenvalue sits exactly
   at -band, and every counted eigenvalue's bracket ends at or below -band.
   The sensitivity row (2x, 5x, 10x band) and the class count are reported
   and checked for consistency, not judged.

Numbers are pinned in the analysis commit, in the pins section at the end;
nothing above that section changes after the numbers.
"""

from __future__ import annotations

import functools
import hashlib
import json
import os
import sys

import numpy as np
import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from flint import arb, fmpq  # noqa: E402

import checker_q as CQ  # noqa: E402
import run_checker_inertia as RI  # noqa: E402

INERTIA_JSON = RI.OUT
CELLS_JSON = RI.CELLS_JSON

# s7.9 clauses 2 and 7, fixed before the run: the eight builds and where
# their band and float count are read.
EXPECTED_BUILDS = ["80|1200|8", "120|1600|16", "160|1600|16", "200|2400|32",
                   "240|2400|32", "280|2266|32", "319|2633|32", "364|3060|32"]


# ------------------------------------------------ 1. the routes, planted


def _planted(diag, seed=0):
    """P^T D P with P a random unimodular integer matrix: inertia of D, exactly."""
    rng = np.random.default_rng(seed)
    n = len(diag)
    P = np.eye(n, dtype=object)
    for _ in range(3 * n):
        i, j = rng.choice(n, 2, replace=False)
        P[i, :] = P[i, :] + int(rng.integers(-2, 3)) * P[j, :]
    D = [[fmpq(diag[i]) if i == j else fmpq(0) for j in range(n)] for i in range(n)]
    Pq = [[fmpq(int(P[i, j])) for j in range(n)] for i in range(n)]
    PT = [list(r) for r in zip(*Pq)]
    DP = [[sum((D[i][k] * Pq[k][j] for k in range(n)), fmpq(0)) for j in range(n)] for i in range(n)]
    return [[sum((PT[i][k] * DP[k][j] for k in range(n)), fmpq(0)) for j in range(n)] for i in range(n)]


def test_backend_lists_python_flint():
    from zeta import rigor
    assert "python-flint" in rigor.available_backends()


@pytest.mark.parametrize("diag,expected", [
    ([-3, -1, 0, 0, 2], (2, 2, 1)),
    ([fmpq(-1, 7), fmpq(1, 3), 5, -2, 0, 1, 1], (2, 1, 4)),
    ([1, 2, 3, 4], (0, 0, 4)),
    ([-1, -2, -3], (3, 0, 0)),
])
def test_routes_on_planted_inertia(diag, expected):
    A = _planted(diag)
    assert RI.inertia_ldl(A) == expected
    assert RI.inertia_charpoly(A) == expected
    assert RI.inertia_both(A) == expected


@pytest.mark.parametrize("A,expected", [
    ([[0, 1], [1, 0]], (1, 0, 1)),
    ([[0, 0, 1], [0, 0, 0], [1, 0, 0]], (1, 1, 1)),
    ([[0, 2, 0], [2, 0, 0], [0, 0, -5]], (2, 0, 1)),
    ([[0, 0], [0, 0]], (0, 2, 0)),
])
def test_zero_diagonal_takes_the_congruence(A, expected):
    Aq = [[fmpq(x) for x in r] for r in A]
    assert RI.inertia_ldl(Aq) == expected
    assert RI.inertia_charpoly(Aq) == expected


def test_routes_match_numpy_on_a_random_float_matrix():
    rng = np.random.default_rng(1)
    X = rng.standard_normal((33, 33)) * 0.05
    R = (X + X.T) / 2 + np.diag(rng.standard_normal(33) * 0.3)
    w = np.linalg.eigvalsh(R)
    A = RI.exact_matrix(R)
    for t in (-0.2, 0.0, 0.1):
        assert np.min(np.abs(w - t)) > 1e-6  # far from every eigenvalue
        assert RI.count_below(A, RI.to_q(t)) == int((w < t).sum())


def test_float_to_rational_is_exact():
    for x in (0.1, -8.179786419034496e-03, 1e-300, 2.0 ** -1074):
        q = RI.to_q(x)
        assert q == fmpq(*x.as_integer_ratio()) and float(q) == x


def test_count_below_is_strict_and_bracket_contains_the_eigenvalue():
    # a diagonal matrix: its eigenvalues are its entries, -3/4 twice
    ev = [fmpq(1, 2), fmpq(-3, 4), fmpq(2), fmpq(-1, 8), fmpq(-3, 4)]
    A = [[ev[i] if i == j else fmpq(0) for j in range(5)] for i in range(5)]
    assert RI.count_below(A, fmpq(-3, 4)) == 0  # strict: -3/4 is not below -3/4
    assert RI.count_below(A, fmpq(-1, 8)) == 2
    srt = sorted(ev)
    for k in range(1, 6):
        b = RI.bracket(A, k, float(srt[k - 1]) + 1e-9)
        assert b["lo"] <= srt[k - 1] < b["hi"] and b["hi"] - b["lo"] <= RI.WIDTH
        assert RI.count_below(A, b["lo"]) <= k - 1 and RI.count_below(A, b["hi"]) >= k
    # a far seed still ends in a correct bracket (the seed only saves work)
    b = RI.bracket(A, 3, 0.9)
    assert b["lo"] <= srt[2] < b["hi"]


def test_bracket_never_straddles_the_split():
    ev = [fmpq(-1, 2), fmpq(1)]
    A = [[ev[i] if i == j else fmpq(0) for j in range(2)] for i in range(2)]
    t = fmpq(-1, 2) + fmpq(1, 2 ** 45)  # inside the first bracket, above the eigenvalue
    b = RI.bracket(A, 1, -0.5, split=t)
    assert b["hi"] == t and b["lo"] <= fmpq(-1, 2) < b["hi"]


def test_ball_inertia_on_planted_and_undecided():
    A = _planted([-2, fmpq(1, 3), 4, -1], seed=3)
    balls = [[arb(x) for x in r] for r in A]
    assert RI.inertia_balls(balls) == (2, 0, 2)
    wide = [[arb(0, 1) if i == j == 0 else arb(0) for j in range(2)] for i in range(2)]
    assert RI.inertia_balls(wide) is None


@functools.lru_cache(maxsize=None)
def _rows(N):
    return CQ.transform_rows(RI.CELL, N, 40)


@pytest.mark.parametrize("N", [8, 32])
def test_class_V4_is_the_transform_rows_kernel(N):
    """Derivation check (s7.9 clause 6): Re "plus" is a real multiple of h,
    Im "plus" a real multiple of n h, "minus" a real multiple of the complex
    conjugate of "plus", and "zero" a multiple of e_0; so the three vanish
    together exactly on the orthogonal complement of h, n h and e_0. Checked
    at dps 40 against checker_q.transform_rows."""
    from mpmath import mp
    rows = _rows(N)
    h, nh, e0 = RI.class_constraints(N, 256)
    with mp.workdps(40):
        hm = [mp.mpf(x.mid().str(50, radius=False)) for x in h]
        nhm = [mp.mpf(x.mid().str(50, radius=False)) for x in nh]
        p, m, z = rows["plus"], rows["minus"], rows["zero"]
        # Re p = a h, Im p = b n h with real a, b; m_n / conj(p_n) is one real constant
        a = mp.re(p[N]) / hm[N]
        b = mp.im(p[N + 1]) / nhm[N + 1]
        scale = max(abs(x) for x in p)
        assert max(abs(mp.re(p[i]) - a * hm[i]) for i in range(2 * N + 1)) < mp.mpf("1e-35") * scale
        assert max(abs(mp.im(p[i]) - b * nhm[i]) for i in range(2 * N + 1)) < mp.mpf("1e-35") * scale
        ratio = [m[i] / mp.conj(p[i]) for i in range(2 * N + 1)]
        assert max(abs(r - ratio[0]) for r in ratio) < mp.mpf("1e-35")
        assert abs(mp.im(ratio[0])) < mp.mpf("1e-35")
        assert all(z[i] == 0 for i in range(2 * N + 1) if i != N) and z[N] != 0


@pytest.mark.parametrize("N", [8, 16, 32])
def test_class_basis_satisfies_the_three_constraints(N):
    Z, free = RI.class_basis(N, 256)
    h, nh, e0 = RI.class_constraints(N, 256)
    assert Z.ncols() == 2 * N + 1 - RI.CODIM_V4 == len(free)
    with RI.arb_prec(256):
        for j in range(Z.ncols()):
            for row in (h, nh, e0):
                s = sum((row[i] * Z[i, j] for i in range(2 * N + 1)), arb(0))
                assert s.contains(0) and s.rad() < 1e-60
    # and against the dps 40 transform rows of checker_q, in float: |r . z| tiny
    rows = _rows(N)
    for j in (0, Z.ncols() // 2, Z.ncols() - 1):
        z = [complex(float(Z[i, j].mid())) for i in range(2 * N + 1)]
        for key in ("plus", "minus", "zero"):
            r = [complex(x) for x in rows[key]]
            assert abs(sum(a * b for a, b in zip(r, z))) < 1e-13 * max(abs(x) for x in r)


# ----------------------------------------- 2. the reading, on the JSON


def _load(path):
    if not os.path.exists(path):
        pytest.skip(f"{os.path.basename(path)} absent (run run_checker_inertia.py)")
    with open(path) as fh:
        return json.load(fh)


@functools.lru_cache(maxsize=None)
def _inertia():
    return _load(INERTIA_JSON)


@functools.lru_cache(maxsize=None)
def _cells():
    return _load(CELLS_JSON)["cells"][RI.CELL]


def _q(pair):
    return fmpq(int(pair[0]), int(pair[1]))


@functools.lru_cache(maxsize=None)
def _snap():
    with open(RI.RT.SNAP) as fh:
        return json.load(fh)


@functools.lru_cache(maxsize=None)
def _Qfull():
    return CQ.Q_matrix(RI.CELL, 32, 40)


@functools.lru_cache(maxsize=None)
def _R(key):
    nv, S, N = (int(x) for x in key.split("|"))
    return RI.stored_R(_snap(), _Qfull(), nv, S, N)


def test_reading_covers_every_c29_build():
    d = _inertia()
    assert list(d["builds"]) == EXPECTED_BUILDS
    assert [RI.build_key(nv, S, N) for nv, S, N, _, _ in RI.BUILDS] == EXPECTED_BUILDS
    assert d["meta"]["ts_inputs_digest"] == RI.DIGEST == _snap()["meta"]["ts_inputs_digest"]


def test_shift_is_the_stored_band():
    """Clause 2: the band read from checker_ts_cells.json, bitwise, never re-derived."""
    d, c = _inertia(), _cells()
    for nv, S, N, band_path, count_path in RI.BUILDS:
        b = d["builds"][RI.build_key(nv, S, N)]
        assert b["band"] == RI.dig(c, band_path)
        assert _q(b["band_exact"]) == RI.to_q(RI.dig(c, band_path))
        assert b["float_count"] == RI.dig(c, count_path)
    # one threshold per N: every N = 32 build at band(2.9, 32), both N = 16 builds at band(2.9, 16)
    assert c["modes_N32"]["band"] == c["32"]["band"]


def test_matrix_is_the_counted_one():
    """Clause 1: R rebuilt here is bitwise the analysed matrix, and its float64
    eigenvalues give the stored count."""
    d = _inertia()
    for key, b in d["builds"].items():
        R = _R(key)
        RL = RI.lower_mirrored(R)
        assert hashlib.sha256(np.ascontiguousarray(R).tobytes()).hexdigest() == b["R_sha256"]
        assert hashlib.sha256(np.ascontiguousarray(RL).tobytes()).hexdigest() == b["RL_sha256"]
        assert int((np.linalg.eigvalsh(R) < -b["band"]).sum()) == b["float_count"] == b["float_count_here"]
        assert b["symmetric_defect"] == float(np.abs(R - R.T).max())
        if b["symmetric_defect"] != 0.0:
            assert "exact_upper_mirror_at_band" in b


def test_routes_agree_and_counts_add_up():
    d = _inertia()
    for b in d["builds"].values():
        for m in RI.MULTIPLES:
            neg, zero, pos = b["exact"][f"x{m}"]
            assert neg + zero + pos == b["dim"]


def test_exact_count_recomputed_here():
    """Clause 3, independently of the run: route (b) at the band, from R rebuilt here."""
    d = _inertia()
    for key, b in d["builds"].items():
        A = RI.exact_matrix(RI.lower_mirrored(_R(key)))
        assert list(RI.inertia_charpoly(RI.shifted(A, _q(b["band_exact"])))) == b["exact"]["x1"]


def test_the_count_holds():
    """Clause 7, THE PRE-REGISTERED TEST. On every build: exact n_0 = 0 at
    -band, exact n_- = the stored float count, and every counted eigenvalue's
    bracket ends at or below -band (lambda_k < hi <= -band). A failure lists
    the builds and the counted eigenvalues that are not below -band."""
    d = _inertia()
    bad = {}
    for key, b in d["builds"].items():
        neg, zero, _ = b["exact"]["x1"]
        beta = _q(b["band_exact"])
        not_below = [br["k"] for br in b["brackets"] if not _q(br["hi"]) <= -beta]
        not_below += list(range(neg + 1, b["float_count"] + 1))
        if zero != 0 or neg != b["float_count"] or not_below:
            bad[key] = {"exact": b["exact"]["x1"], "float_count": b["float_count"], "not_below": not_below}
        assert b["holds"] == (key not in bad)
        assert b["float_counted_not_below_band"] == (bad[key]["not_below"] if key in bad else [])
    assert not bad, f"the count does not hold on {bad}"


def test_brackets_as_read():
    """Clause 4: widths, invariants, and a recheck of the last counted and the
    first not counted eigenvalue of every build by exact counts here."""
    d = _inertia()
    for key, b in d["builds"].items():
        beta = _q(b["band_exact"])
        brs = b["brackets"] + [b["first_not_counted"]]
        assert [br["k"] for br in brs] == list(range(1, len(brs) + 1))
        for br in brs:
            lo, hi = _q(br["lo"]), _q(br["hi"])
            assert lo < hi and hi - lo <= RI.WIDTH
            assert not (lo < -beta < hi)  # never straddles the threshold
            assert br["margin_low"] == float(-beta - hi) and br["margin_high"] == float(-beta - lo)
        assert _q(b["first_not_counted"]["lo"]) >= -beta
        A = RI.exact_matrix(RI.lower_mirrored(_R(key)))
        for br in brs[-2:]:
            k = br["k"]
            assert RI.count_below(A, _q(br["lo"]), both=False) <= k - 1
            assert RI.count_below(A, _q(br["hi"]), both=False) >= k


def test_sensitivity_row_is_nonincreasing():
    """Clause 5: reported, not a criterion."""
    d = _inertia()
    for b in d["builds"].values():
        counts = [b["exact"][f"x{m}"][0] for m in RI.MULTIPLES]
        assert counts == sorted(counts, reverse=True)


def test_class_count_within_the_codimension_bound():
    """Clause 6: n_-(A) - 3 <= n_-(A on V_4) <= n_-(A), at every multiple where
    the ball elimination decided; an undecided class count is listed, not hidden."""
    d = _inertia()
    for b in d["builds"].values():
        cls = b["class_V4"]
        assert cls["x1"]["dim"] == b["dim"] - RI.CODIM_V4
        for m in RI.MULTIPLES:
            c = cls[f"x{m}"]
            k = b["exact"][f"x{m}"][0]
            if c["n_minus"] is not None:
                assert k - RI.CODIM_V4 <= c["n_minus"] <= k
                assert c["n_minus"] + c["n_plus"] == c["dim"]


# ----------------------------------------------------------------- pins
# (added in the analysis commit, after the numbers)
