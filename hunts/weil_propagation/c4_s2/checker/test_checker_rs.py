"""Phase 2 tests (checker/), WRITTEN AFTER ROUTING (kernel/ af756a5,
two_adic/ c7e9f57, cutoff/ 22f6e1c). They add to the phase 1 properties in
test_checker_props.py and change none of them.

- the shift form H: an independent route to cutoff/'s product-side claim;
- the refusal at 2 reads the tower outside the window (control 2 detail);
- the arithmetic behind two_adic/'s Gamma_C framework limit (control 3);
- pins of checker_rs_cells.json (run_checker_rs.py): kernel/ T_inf, the
  product-side remainder Q - T_inf, and the Connes-Consani Thm 6.11 margins.
"""

from __future__ import annotations

import json
import os
import sys

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import checker_gate as CG  # noqa: E402
import checker_glue as GLUE  # noqa: E402
import checker_props as CP  # noqa: E402
import checker_q as CQ  # noqa: E402

CELLS = ["2.2", "2.5", "2.9"]
CALIB = ["1.5", "1.9"]
JSON = os.path.join(HERE, "checker_rs_cells.json")


def _json():
    with open(JSON) as fh:
        return json.load(fh)["cells"]


# ------------------------------------------------- the shift form (cutoff/)


CUTOFF_COUNTS = {"2.2": [2, 3, 7], "2.5": [4, 8, 15], "2.9": [5, 11, 23]}


@pytest.mark.parametrize("c", CELLS)
def test_shift_form_counts_match_cutoff(c):
    """#eig(H) > 1/4 at N = 8, 16, 32 from the checker's own atom block
    (H = -prime / (sqrt 2 log 2)) equals cutoff/'s measured counts, and the
    spectrum stays in [-1/2, 1/2] (compression of an operator of norm 1/2)."""
    got = []
    for N in (8, 16, 32):
        e = CQ.eigvals_hermitian(CQ.shift_form(c, N, 40), 40)
        with mp.workdps(40):
            assert e[0] >= -mp.mpf(1) / 2 - mp.mpf("1e-35")
            assert e[-1] <= mp.mpf(1) / 2 + mp.mpf("1e-35")
        got.append(sum(1 for x in e if x > mp.mpf(1) / 4))
    assert got == CUTOFF_COUNTS[c]


def test_shift_form_is_the_atom_block():
    """Q - pole - arch = -sqrt 2 log 2 H exactly (the atom block is H)."""
    R = CQ.q_parts("2.5", 6, 40)
    H = CQ.shift_form("2.5", 6, 40)
    with mp.workdps(40):
        assert CP.entry_drift(R["prime"], -mp.sqrt(2) * mp.log(2) * H) < mp.mpf("1e-38")


# -------------------------------------------- kill-control 2, the whole tower


def test_refusal_reads_the_tower_outside_the_window():
    """On c in [2, 3) the only atom is n = 2, where Epstein has s_1(2) = 0.
    The tower cut at k = 2 (n = 4, already outside the window) is a unitary
    tower (alpha = +-1) and two_adic/'s validator accepts it; the whole tower
    (the checker's exact s_1..s_7) is refused at s_3(2) = 6 (n = 8)."""
    lam = CG.lambda_vectors(CG.coeffs_epstein_116())
    tower = {k: lam[2**k].get(2, 0) for k in range(1, 8)}
    assert [str(tower[k]) for k in range(1, 8)] == ["0", "2", "6", "2", "0", "2", "0"]
    try:
        GLUE.validate_local(("tower", {1: 0, 2: 2}), degree=2)
    except GLUE.NotRouted as e:
        pytest.skip(f"NotRouted: {e}")
    with pytest.raises(GLUE.Refused, match="s_3"):
        GLUE.validate_local(("tower", tower), degree=2)


# -------------------------------------------- kill-control 3, the argument


def test_gamma_c_framework_limit_arithmetic():
    """two_adic/'s argument, checked independently: chi_{-23} is odd
    (discriminant < 0) and unramified at 2 (2 does not divide 23; chi(2) = +1,
    2 splits), while -1 in Gamma_S = {+-2^n} sits diagonally in R* x Q_2*, so a
    character trivial on Gamma_S has chi_inf(-1) chi_2(-1) = 1. Odd at inf
    would need chi_2(-1) = -1, impossible for chi_2 unramified (-1 in Z_2^*).
    So L(s, chi_{-23}) has no component on L^2(X_S) for S = {inf, 2}."""
    assert CG.kronecker_m23(2) == 1  # split at 2, unramified
    assert 23 % 2 == 1  # 2 does not divide the conductor
    # odd: chi(-1) = sign of the discriminant; checked through chi(n) for
    # n = 22 = -1 mod 23 against the Legendre symbol (-1/23) = -1 (23 = 3 mod 4)
    assert CG.jacobi(22, 23) == -1
    # the Dedekind tower at 2 is unitary (alpha = (1, 1)): the refusal is not
    # about the local data, it is about the archimedean parity
    lam = CG.lambda_vectors(CG.coeffs_dedekind_m23())
    assert all(lam[2**k] == {2: 2} for k in range(1, 8))


# ---------------------------------------------------- pins of the JSON


def test_T_inf_pinned_and_psd():
    J = _json()
    for c in CALIB + CELLS:
        for N in ("8", "16", "32"):
            r = J[c][N]
            assert mp.mpf(r["T_inf_herm_defect"]) == 0
            assert mp.mpf(r["T_inf_low"][0]) > 0, (c, N)
        for N in ("8", "16"):
            assert mp.mpf(J[c][N]["T_inf_submatrix_defect_vs_N32"]) < mp.mpf("1e-35"), c


@pytest.mark.parametrize("c", CALIB + CELLS)
def test_T_inf_recomputed_N8(c):
    ev = CP.lowest(GLUE.T_inf(c, 8, 40), 3, 40)
    with mp.workdps(40):
        for x, y in zip(ev, _json()[c]["8"]["T_inf_low"]):
            assert abs(x - mp.mpf(y)) <= mp.mpf("1e-23") * abs(x)  # JSON keeps 25 digits


def test_cc611_margins_pinned():
    """P7 margins at c = 1.5, 1.9 (N = 8, 16), with their dps 40/60 drift."""
    J = _json()
    for c in CALIB:
        for N in ("8", "16"):
            m, d = J[c][N]["cc611"], J[c][N]["cc611_drift"]
            for key in ("min_minus_with_kappa", "min_minus_zero", "min_plus_zero"):
                assert mp.mpf(m[key]) > 10 * mp.mpf(d[key]), (c, N, key)
            ks = mp.mpf(m["kappa_star"])
            assert 0 <= ks < mp.mpf(m["kappa_cc"]), (c, N)


def test_product_side_negative_index_grows():
    """With the product-side term alone, R = Q - T_inf: n_- on the full space
    strictly increases with N on every cell (cutoff/'s refutation of
    product-side C4, measured here through the checker's Q and kernel/'s
    T_inf). The counts are pinned in RESULTS.md."""
    J = _json()
    for c in CELLS:
        negs = [J[c][N]["R_full_inertia"][0] for N in ("8", "16", "32")]
        assert negs[0] < negs[1] < negs[2], (c, negs)
        for N in ("8", "16", "32"):
            assert J[c][N]["R_full_inertia"][1] == 0, (c, N)


def test_calibration_remainder_inertia():
    """S = {inf} (c < 2): R_inf = Q - T_inf = P - E. On C2 = V_- n {v_0 = 0}
    it is positive (CC Theorem 1 up to reflection); on the full space the
    negative index stays bounded in N."""
    J = _json()
    for c in CALIB:
        full = [J[c][N]["R_full_inertia"][0] for N in ("8", "16", "32")]
        assert len(set(full)) == 1, (c, full)
        for N in ("8", "16", "32"):
            assert J[c][N]["R_minus_zero_inertia"][0] == 0, (c, N)


def _rows(section):
    import re

    out = []
    for r in section.splitlines():
        m = re.match(r"\| (1\.5|1\.9|2\.2|2\.5|2\.9) \| (8|16|32) \|", r)
        if m:
            out.append((m.group(1), m.group(2), [x.strip() for x in r.strip("|").split("|")]))
    return out


def _close(a, b):
    a, b = mp.mpf(a), mp.mpf(b)
    return abs(a - b) <= mp.mpf("6e-5") * abs(b) + mp.mpf("1e-40")


def test_results_tables_match_json():
    """Every number in RESULTS.md s5.2 and s5.3 is the JSON value to 5 digits."""
    J = _json()
    with open(os.path.join(HERE, "RESULTS.md")) as fh:
        text = fh.read()
    s52 = _rows(text[text.index("### 5.2"):text.index("### 5.3")])
    s53 = _rows(text[text.index("### 5.3"):text.index("### 5.4")])
    assert len(s52) == 15 and len(s53) == 4
    for c, N, cells in s52:
        x = J[c][N]
        assert _close(cells[2], x["T_inf_low"][0]), (c, N)
        for col, key in ((3, "R_full"), (4, "R_minus"), (5, "R_minus_zero")):
            neg, low = [t.strip() for t in cells[col].split(",")]
            assert int(neg) == x[f"{key}_inertia"][0], (c, N, key)
            assert _close(low, x[f"{key}_low"][0]), (c, N, key)
        if c in CELLS:
            assert int(cells[6]) == x["H_count_above_quarter"], (c, N)
    for c, N, cells in s53:
        m_ = J[c][N]["cc611"]
        assert _close(cells[2], m_["min_minus_with_kappa"])
        assert _close(cells[3], m_["min_minus_zero"])
        assert _close(cells[4], m_["min_plus_zero"])
        ks = mp.mpf(m_["kappa_star"])
        assert abs(mp.mpf(cells[5]) - ks) <= mp.mpf("1e-3") * (1 + abs(ks))


@pytest.mark.parametrize("c", CELLS)
def test_theta_gram_is_three_halves_minus_sqrt2_H(c):
    """cutoff/ b547d3b and two_adic/: Gram(Theta_1) = 3/2 - W_2 / log 2. With D
    (shift by log 2) unitary, Theta^* Theta = 3/2 - 2^{-1/2}(D + D^*), and
    (D + D^*)/2 compressed to the window is the checker's H. two_adic/'s
    ta_es.theta_gram against 3/2 I - sqrt2 H: measured 2.3e-41 at dps 40."""
    ta_es = GLUE._import(GLUE.TWO_ADIC, "ta_es")
    G = ta_es.theta_gram(c, 8, [1], 40)
    H = CQ.shift_form(c, 8, 40)
    with mp.workdps(40):
        X = mp.mpf(3) / 2 * mp.eye(17) - mp.sqrt(2) * H
    assert CP.entry_drift(G, X) < mp.mpf("1e-38")
