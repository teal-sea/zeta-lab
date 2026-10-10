"""Pins for `hunts/rh_resolve/`: the numbers its documents state.

The hunt's Li rows are graded **measured**. Its own audit (`AUDIT.md`,
2026-10-04) withdrew their enclosure grade: the complex modulus bound, the
outward rounding of the remainder and the angle coverage are unproved. So these
tests pin what the saved JSON files contain and what `RESULTS.md`, `AUDIT.md`,
`EQUIVALENCE.md` and `superseded/CORRECTION.md` quote from them. A green run
says the documents match the artifacts. It does not make any row an enclosure.

Everything here reads committed files or does a few seconds of mpmath work
under `mp.workdps`; nothing reruns the quadrature.
"""

from __future__ import annotations

import ast
import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path

import pytest
from mpmath import cos, diff, euler, exp, findroot, log, mp, mpc, mpf, pi, psi, quad, sqrt, zeta

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(ROOT))

HUNT = ROOT / "hunts" / "rh_resolve"

#: The three range-stamped midpoint files the corrected n <= 58 record rests on.
MID_FILES = (
    "enclosure_mid_R0.7_n1-16_K16384_p128.json",
    "enclosure_mid_R0.8_n17-40_K65536_p128.json",
    "enclosure_mid_R0.8_n41-60_K65536_p128.json",
)

#: Float Cauchy values from zeta/li.py's committed cache (radius 0.5, dps 30).
LI_CACHE = ROOT / "data" / "li_lambda_dps30_methodcauchy_n208_radius0.5.json"

_BALL = re.compile(r"^\[\s*(\S+)?\s*\+/-\s*(\S+?)\s*\]$")


def _bounds(text: str) -> tuple[Fraction, Fraction]:
    """Exact lower and upper bound of an Arb ball string or a plain decimal."""
    text = text.strip()
    m = _BALL.match(text)
    if m:
        mid = Fraction(m.group(1)) if m.group(1) else Fraction(0)
        rad = Fraction(m.group(2))
        return mid - rad, mid + rad
    value = Fraction(text)
    return value, value


def _window(row: dict) -> tuple[Fraction, Fraction]:
    return _bounds(row["re_lo"])[0], _bounds(row["re_hi"])[1]


def _imag_window(row: dict) -> tuple[Fraction, Fraction]:
    return _bounds(row["im_lo"])[0], _bounds(row["im_hi"])[1]


def _load(name: str) -> dict:
    return json.loads((HUNT / name).read_text(encoding="utf-8"))


def _rows_by_n(names, folder: Path | None = None) -> dict[int, dict]:
    folder = HUNT if folder is None else folder
    rows: dict[int, dict] = {}
    for name in names:
        for row in json.loads((folder / name).read_text(encoding="utf-8"))["rows"]:
            assert row["n"] not in rows, f"n = {row['n']} saved twice"
            rows[row["n"]] = row
    return rows


def _g2(n: int, R: float, rho: float, M: float) -> tuple[float, float]:
    """(G2, M2c) exactly as enclose_li_mid.py computes them, in floats."""
    gap = rho - R
    M1 = M / gap
    M2c = 2 * M / gap**2
    F1 = R * M1
    F2 = R * M1 + R**2 * M2c
    return F2 + 2 * n * F1 + n**2 * M, M2c


def _li_float() -> list[Fraction]:
    data = json.loads(LI_CACHE.read_text(encoding="utf-8"))
    return [Fraction(v) for v in data["values"]]


def _lambda1_closed_form() -> Fraction:
    with mp.workdps(60):
        return Fraction(mp.nstr(1 + euler / 2 - log(4 * pi) / 2, 55, strip_zeros=False))


# --------------------------------------------------------------------------
# Phase 4: the midpoint rows, n = 1..60
# --------------------------------------------------------------------------


def test_midpoint_rows_cover_one_to_sixty_once() -> None:
    rows = _rows_by_n(MID_FILES)
    assert sorted(rows) == list(range(1, 61))
    assert all(row["finite"] for row in rows.values())


def test_lower_endpoints_are_positive_for_exactly_n_up_to_58() -> None:
    rows = _rows_by_n(MID_FILES)
    positive = [n for n, row in sorted(rows.items()) if _window(row)[0] > 0]
    assert positive == list(range(1, 59))
    # AUDIT.md: "Row 59 starts at -0.06481890146."
    assert float(_window(rows[59])[0]) == pytest.approx(-0.06481890146, abs=1e-11)
    assert _window(rows[60])[0] < 0


def test_contour_parameters_and_saved_M() -> None:
    rows = _rows_by_n(MID_FILES)
    for n, row in rows.items():
        assert row["prec"] == 128
        if n <= 16:
            assert (row["R"], row["K"]) == ("0.7", 16384)
            assert row["M"] == 1.196816073730588
        else:
            assert (row["R"], row["K"]) == ("0.8", 65536)
            assert row["M"] == 0.9714775364845991


def test_saved_remainder_is_the_corrected_G2_with_the_stated_rho() -> None:
    """The JSON omits rho; the saved M2 pins it (rho = 0.85 at R = 0.7, 0.88 at R = 0.8)."""
    rows = _rows_by_n(MID_FILES)
    for n, row in rows.items():
        rho = 0.85 if row["R"] == "0.7" else 0.88
        g2, _ = _g2(n, float(row["R"]), rho, row["M"])
        assert row["M2"] == pytest.approx(g2, rel=1e-12), n


def test_superseded_rows_and_the_scope_of_the_correction() -> None:
    folder = HUNT / "superseded"
    rows = _rows_by_n(sorted(p.name for p in folder.glob("*.json")), folder)
    assert sorted(rows) == list(range(1, 73))
    # The withdrawn record: positive lower endpoints to n = 71, n = 72 the boundary.
    positive = [n for n, row in sorted(rows.items()) if _window(row)[0] > 0]
    assert positive == list(range(1, 72))
    # The superseded runs used M2c alone: 106.38 at R = 0.7, 303.59 at R = 0.8.
    for R, rho, M, m2c in ((0.7, 0.85, 1.196816073730588, 106.38),
                           (0.8, 0.88, 0.9714775364845991, 303.59)):
        stored = {row["M2"] for row in rows.values() if float(row["R"]) == R}
        assert len(stored) == 1
        (value,) = stored
        assert value == pytest.approx(_g2(1, R, rho, M)[1], rel=1e-12)
        assert round(value, 2) == m2c
    # CORRECTION.md: G2 first exceeds M2c at n = 4 (R = 0.7) and n = 5 (R = 0.8).
    for R, rho, M, first in ((0.7, 0.85, 1.196816073730588, 4),
                             (0.8, 0.88, 0.9714775364845991, 5)):
        over = [n for n in range(1, 73) if _g2(n, R, rho, M)[0] > _g2(n, R, rho, M)[1]]
        assert over == list(range(first, 73))
        # ... and at that first row the n^2 M term is not yet the largest piece.
        gap = rho - R
        F2 = R * M / gap + R**2 * 2 * M / gap**2
        assert first**2 * M < F2


def test_sample_windows_and_the_boundary() -> None:
    rows = _rows_by_n(MID_FILES)
    stated = {16: (5.70, 5.73), 40: (30.19, 30.77), 58: (11.72, 97.04), 59: (-0.06, 111.57)}
    for n, (lo, hi) in stated.items():
        a, b = _window(rows[n])
        assert (round(float(a), 2), round(float(b), 2)) == (lo, hi), n


def test_width_growth_at_the_boundary() -> None:
    """RESULTS.md: width grows about 1.31x from n = 58 to 59, so roughly 1.13x the panels."""
    rows = _rows_by_n(MID_FILES)
    (a58, b58), (a59, b59) = _window(rows[58]), _window(rows[59])
    ratio = float((b59 - a59) / (b58 - a58))
    assert round(ratio, 2) == 1.31
    lam58, lam59 = float(a58 + b58) / 2, float(a59 + b59) / 2
    assert round(math.sqrt(ratio * lam58 / lam59), 2) == 1.13


def test_imaginary_windows_contain_zero() -> None:
    names = list(MID_FILES) + [p.name for p in HUNT.glob("enclosure_li_*.json")]
    for name in names:
        for row in _load(name)["rows"]:
            lo, hi = _imag_window(row)
            assert lo <= 0 <= hi, (name, row["n"])


def test_float_cauchy_values_lie_inside_all_58_windows() -> None:
    """AUDIT.md C2, against zeta/li.py's committed float Cauchy table."""
    rows = _rows_by_n(MID_FILES)
    values = _li_float()
    for n in range(1, 59):
        lo, hi = _window(rows[n])
        assert lo <= values[n - 1] <= hi, n


def test_lambda_1_closed_form_lies_in_every_saved_lambda_1_window() -> None:
    """AUDIT.md C1 and the closed form it quotes."""
    closed = _lambda1_closed_form()
    quoted = Fraction("0.0230957089661210338143102479064952916")
    assert abs(closed - quoted) < Fraction(1, 10**37)
    assert closed > 0
    names = list(MID_FILES) + [p.name for p in HUNT.glob("enclosure_*.json")]
    seen = 0
    for name in set(names):
        for row in _load(name)["rows"]:
            if row["n"] == 1:
                lo, hi = _window(row)
                assert lo <= closed <= hi, name
                seen += 1
    assert seen >= 6


# --------------------------------------------------------------------------
# Phases 2 and 3: the panel-covering rows
# --------------------------------------------------------------------------


def _rounded(row: dict) -> tuple[float, float]:
    a, b = _window(row)
    return round(float(a), 6), round(float(b), 6)


def test_phase_2_table() -> None:
    p128 = _rows_by_n(["enclosure_li_K32768_p128.json"])
    p192 = _rows_by_n(["enclosure_li_K32768_p192.json"])
    assert [_rounded(p128[n]) for n in (1, 2, 3)] == [
        (0.018865, 0.027334), (0.075364, 0.10933), (0.155621, 0.259678)]
    assert [_rounded(p192[n]) for n in (1, 2)] == [(0.018519, 0.027681), (0.074007, 0.110687)]
    assert sorted(p192) == [1, 2]  # n = 3 at prec 192: "(not run)"
    for n in (1, 2):  # prec 128 and 192 windows overlap
        (a, b), (c, d) = _window(p128[n]), _window(p192[n])
        assert max(a, c) <= min(b, d)
    # The float-check column, against the committed Cauchy table.
    values = _li_float()
    assert abs(values[1] - Fraction("0.09234573522804667039")) < Fraction(1, 10**19)
    assert abs(values[2] - Fraction("0.20763892055432480379")) < Fraction(1, 10**19)


def test_phase_3_table_and_radius_tradeoff() -> None:
    r07 = _rows_by_n(["enclosure_li_R0.7_K131072_p128.json"])
    assert [_rounded(r07[n]) for n in range(6, 11)] == [
        (0.77644, 0.878693), (1.038326, 1.210599), (1.32352, 1.607997),
        (1.619875, 2.081962), (1.908723, 2.649964)]
    values = _li_float()
    for n, stated in zip(range(6, 11), ("0.8275660122823793", "1.1244601175709595",
                                         "1.4657556771470606", "1.8509160483825342",
                                         "2.2793393631931577")):
        assert abs(values[n - 1] - Fraction(stated)) < Fraction(1, 10**15)
    r05 = _rows_by_n(["enclosure_li_K131072_p128.json"])
    assert sorted(r05) == [1, 2, 3, 4, 5]
    assert all(_window(row)[0] > 0 for row in r05.values())
    widths = [float(_window(row)[1] - _window(row)[0]) for row in r05.values()]
    assert (round(min(widths), 3), round(max(widths), 2)) == (0.002, 0.18)
    r03 = _rows_by_n(["enclosure_li_R0.3_K131072_p128.json"])
    assert sorted(r03) == list(range(6, 11))
    assert all(_window(row)[0] < 0 for row in r03.values())  # R = 0.3 "loses badly"
    # Ceiling note: n = 20 at R = 0.7 needs about three times K = 131072.
    a10, b10 = _window(r07[10])
    half20 = float(b10 - a10) / 2 * (20 / 10) * 0.7 ** -10
    assert round(half20 / float(values[19])) == 3


def test_midpoint_scheme_is_about_9000x_narrower_for_lambda_1_at_K_4096() -> None:
    (panel,) = _load("enclosure_li_K4096_p128.json")["rows"]
    mid = _rows_by_n(["enclosure_mid_R0.5_K4096_p128.json"])[1]
    assert mid["R"] == "0.5" and panel["K"] == mid["K"] == 4096
    a, b = _window(panel)
    c, d = _window(mid)
    assert 8500 < float((b - a) / (d - c)) < 9500


# --------------------------------------------------------------------------
# Branch, disproof, phase 1 and rival artifacts
# --------------------------------------------------------------------------


def test_branch_artifacts() -> None:
    for name, R, stated in (("branch_R0.5_K32768.json", "0.5", 0.4951),
                            ("branch_R0.7_K32768.json", "0.7", 0.4854)):
        data = _load(name)
        assert data["ok"] is True and data["contour"] == R and data["K0"] == 32768
        assert round(data["min_re_lower"], 4) == stated


def test_disproof_artifacts() -> None:
    li = _load("disproof_li100.json")
    assert (li["nmax"], li["violations"]) == (100, 0)
    assert li["min_margin"] == 0.023095708966121033
    assert li["lambda_100"] == "118.603775376791"
    jensen = _load("disproof_jensen16x25.json")
    assert (jensen["rows"], jensen["violations"]) == (416, 0)
    assert round(jensen["min_gap"], 4) == 0.0432


def test_phase_1_artifact() -> None:
    routes = _load("results_phase1.json")["routes"]
    li = routes["A_li"]
    lam = [float(v) for v in li["lambda_1_20_dps30"]]
    assert len(lam) == 20 and li["all_positive"] is True and min(lam) > 0
    assert li["min_margin"] == 0.023095708966121033
    assert f"{li['max_abs_dps30_minus_dps20']:.2e}" == "3.33e-21"
    diffs = li["cauchy_minus_zeros_n8"]
    assert len(diffs) == 8
    assert (f"{min(diffs):.1e}", f"{max(diffs):.1e}") == ("2.4e-10", "1.5e-08")
    assert "n_zeros=1000" in (HUNT / "probe_phase1.py").read_text(encoding="utf-8")
    assert round(li["asymptotic_n20"], 4) == 8.3507
    assert round(lam[19], 4) == 8.7693
    weil = routes["B_weil"]
    assert weil["gaussian_a1"]["zero_side"] == "0.0"
    assert f"{weil['gaussian_a1']['abs_diff_float']:.2e}" == "1.63e-21"
    assert f"{weil['fejer_b1']['abs_diff_float']:.2e}" == "1.33e-04"
    heat = routes["C_heat"]
    defects = [float(v) for v in ast.literal_eval(heat["phi_even_defect"]).values()]
    assert (f"{min(defects):.1e}", f"{max(defects):.1e}") == ("4.8e-32", "3.5e-31")
    assert f"{float(heat['H0_vs_Xi']['max_residual']):.2e}" == "3.77e-32"


def test_rival_artifact() -> None:
    data = _load("rival_weil.json")
    assert data["dh_online_count"] == 87
    assert [row["a"] for row in data["rows"]] == [0.5, 1.0, 2.0]
    assert all(row["both_positive"] for row in data["rows"])
    source = (HUNT / "probe_rival.py").read_text(encoding="utf-8")
    assert "first_n_zeros(400" in source and "t_max=150" in source


# --------------------------------------------------------------------------
# EQUIVALENCE.md spot checks
# --------------------------------------------------------------------------


def _explicit_L(s):
    return 1 / s + 1 / (s - 1) - log(pi) / 2 + psi(0, s / 2) / 2 + zeta(s, derivative=1) / zeta(s)


def test_poisson_spot_check_and_its_tail_beyond_gamma_200() -> None:
    from zeta.core import xi
    from zeta.zeros import first_n_zeros

    with mp.workdps(40):
        # D3: the s -> 0 limit of the explicit L is the stated closed form of b.
        b = -euler / 2 - 1 + log(2) + log(pi) / 2
        assert abs(_explicit_L(mpf("1e-20")) - b) < mpf("1e-15")
        assert abs(-2 * b - (2 + euler - log(4 * pi))) < mpf("1e-35")

    with mp.workdps(25):
        s = mpc(2)
        h = mpf("1e-8")
        quotient = (xi(s + h) - xi(s - h)) / (2 * h) / xi(s)
        assert abs(quotient - _explicit_L(s)) < mpf("1e-18")

        zeros = first_n_zeros(200)
        assert len(zeros) == 200
        gamma_200 = zeros[-1]
        assert abs(gamma_200 - mp.im(mp.zetazero(200))) < mpf("1e-15")
        assert round(float(gamma_200), 2) == 396.38

        d, t = mpf("0.3"), mpf(10)
        re_L = _explicit_L(mpc("0.8", 10)).real
        poisson = sum(d / (d * d + (t - g) ** 2) + d / (d * d + (t + g) ** 2) for g in zeros)
        residual = re_L - poisson
        tail = d / pi * (log(gamma_200 / (2 * pi)) + 1) / gamma_200
        assert round(float(re_L), 5) == 0.03177
        assert round(float(poisson), 5) == 0.03054
        assert round(float(residual), 5) == 0.00124
        assert round(float(tail), 5) == 0.00124


def test_near_cancellation_inside_the_strip() -> None:
    with mp.workdps(25):
        s = mpc("0.51", "17.5")
        log_deriv_zeta = zeta(s, derivative=1) / zeta(s)
        archimedean = _explicit_L(s) - log_deriv_zeta
        assert round(float(archimedean.real), 3) == 0.512
        assert round(float(log_deriv_zeta.real), 3) == -0.510


def _f(n, u):
    return (2 * pi**2 * n**4 * exp(9 * u) - 3 * pi * n**2 * exp(5 * u)) * exp(-pi * n**2 * exp(4 * u))


def test_log_concavity_numbers() -> None:
    with mp.workdps(25):
        # The closed form for (log f_n)'' against a numerical second derivative.
        for n, u in ((1, mpf(0)), (1, mpf("0.4")), (2, mpf("0.1"))):
            v = n**2 * exp(4 * u)
            closed = 16 * pi * n**2 * exp(4 * u) * (-4 * pi**2 * v**2 + 12 * pi * v - 15) / (2 * pi * v - 3) ** 2
            assert abs(diff(lambda x: log(_f(n, x)), u, 2) - closed) < mpf("1e-12") * abs(closed)
        # N(v) is (log f_1)'' + 70 times the positive (2 pi v - 3)^2, with v = exp(4u).
        def N(v):
            return -64 * pi**3 * v**3 + 472 * pi**2 * v**2 - 1080 * pi * v + 630

        for u in (mpf(0), mpf("0.2"), mpf("0.7")):
            v = exp(4 * u)
            cleared = (diff(lambda x: log(_f(1, x)), u, 2) + 70) * (2 * pi * v - 3) ** 2
            assert abs(cleared - N(v)) < mpf("1e-10") * abs(N(v))
        # N(1) < 0, and both roots of N' sit below 1.
        N1 = N(1)
        assert N1 < 0
        disc = (118 * pi) ** 2 - 4 * 24 * pi**2 * 135
        roots = [(118 * pi - sqrt(disc)) / (48 * pi**2), (118 * pi + sqrt(disc)) / (48 * pi**2)]
        assert all(0 < r < 1 for r in roots)
        # "a few thousandths near u = 0"; "+3.3 near u = 0"; negligible at u >= 0.3.
        ratio = _f(2, 0) / _f(1, 0)
        assert 0.001 < float(ratio) < 0.01

        def phi(u):
            return sum(_f(n, u) for n in range(1, 12))

        def extra(u):
            return diff(lambda x: log(phi(x)), u, 2) - diff(lambda x: log(_f(1, x)), u, 2)

        assert round(float(extra(mpf(0))), 1) == 3.3
        assert abs(extra(mpf("0.3"))) < mpf("1e-6")


def test_positive_weight_witness_has_the_stated_non_real_zero() -> None:
    with mp.workdps(20):
        def phi(u):
            def bump(c, w):
                return exp(-((u - c) ** 2) / w)
            return (bump(mpf("0.3"), mpf("0.02")) + bump(mpf("-0.3"), mpf("0.02"))
                    + mpf("0.3") * (bump(mpf(2), mpf("0.05")) + bump(mpf(-2), mpf("0.05"))))

        def H(z):
            return quad(lambda u: phi(u) * cos(z * u), [0, 8])

        root = findroot(H, mpc("1.62", "0.64"))
        assert abs(root - mpc("1.620045852500311", "0.641606247831350")) < mpf("1e-12")
        assert abs(H(root)) < mpf("1e-15")


# --------------------------------------------------------------------------
# The documents carry the audit's grade
# --------------------------------------------------------------------------


def test_the_hunt_documents_carry_the_audit_grade() -> None:
    assert (HUNT / "AUDIT.md").is_file()
    assert not (HUNT / "THEOREM.md").exists()
    assert not (HUNT / "NOTE-shared-checkout.md").exists()
    results = (HUNT / "RESULTS.md").read_text(encoding="utf-8")
    for phrase in ("proved finite positivity", "this is a theorem", "This is a theorem"):
        assert phrase not in results, phrase
    correction = (HUNT / "superseded" / "CORRECTION.md").read_text(encoding="utf-8").lower()
    assert "certif" not in correction
    equivalence = (HUNT / "EQUIVALENCE.md").read_text(encoding="utf-8")
    assert "hunts/epp_herglotz/RESULTS.md" in equivalence
    assert "Acta Arith. 89 (1999), 217-234" in equivalence
