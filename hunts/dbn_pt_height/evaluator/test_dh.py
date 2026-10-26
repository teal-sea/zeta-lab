"""Tests for dh.py: the Davenport-Heilbronn side of the refusal gate (DH.md).

Every comparison with H_t here is measured (floating-point oracle, no error
theorem for DH yet).  Run from the repository root:

    .venv/bin/python -m pytest -q -n0 hunts/dbn_pt_height/evaluator/test_dh.py
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for p in (str(HERE), str(ROOT)):
    if p not in sys.path:
        sys.path.insert(0, p)

from flint import acb, arb  # noqa: E402
from mpmath import mp  # noqa: E402

import dh  # noqa: E402
from effective import workprec  # noqa: E402

# hunt #61's located zero at narrow-frame t = 0.0576 (its winding_results.json,
# "locating_pass_measured"), mapped to the wide frame: z = 2 z_n, t = 4 t_n
Z61_NARROW = ("240.3451714460939", "0.01018313776460141")
T61_NARROW = "0.0576"


def _wide(zn: tuple[str, str]) -> tuple[str, str]:
    with mp.workdps(30):
        return mp.nstr(2 * mp.mpf(zn[0]), 22), mp.nstr(2 * mp.mpf(zn[1]), 22)


def _ratio(x: str, y: str, t: str) -> float:
    """|H - (A + B)| / |B|: how much the main terms leave for a correction and error."""
    h = dh.H_oracle(x, y, t, dps=30)
    m = dh.main_terms(x, y, t)
    with workprec(192), mp.workdps(40):
        H = acb(arb(mp.nstr(h.real, 30)), arb(mp.nstr(h.imag, 30)))
        return float((abs(H - m["H_main"]) / abs(m["B"])).mid())


def test_hunt61_record_is_what_this_file_reads() -> None:
    import json

    rec = json.loads((ROOT / "hunts" / "lambda_dh_bounds" / "winding_results.json").read_text())
    loc = rec["locating_pass_measured"][T61_NARROW]
    assert (repr(loc["zstar_re"]), repr(loc["zstar_im"])) == Z61_NARROW
    assert rec["t1_run"]["box"]["floats"][0] < loc["zstar_re"] < rec["t1_run"]["box"]["floats"][1]


def test_kappa_is_derived_real_and_agrees_with_the_lab_pin() -> None:
    from zeta import epstein

    with mp.workdps(50):
        k = dh.kappa(45)
        assert abs(mp.im(k)) < mp.mpf("1e-44")
        assert abs(mp.re(k) - mp.mpf(epstein.KAPPA_REF)) < mp.mpf("1e-38")
        # a second base point gives the same constant
        k2 = dh.kappa(45, s0=("-1.3", "23.9"))
        assert abs(k - k2) < mp.mpf("1e-42")
        # the closed form, as an observation only (dh.py never uses it)
        closed = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
        assert abs(mp.re(k) - closed) < mp.mpf("1e-42")


@pytest.mark.parametrize("s", [(0.2, 3.0), (-0.7, 11.3), (1.4, 40.0)])
def test_functional_equation_defect(s: tuple[float, float]) -> None:
    with mp.workdps(40):
        z = mp.mpc(*s)
        a, b = dh.F_mp(z), dh.F_mp(1 - z)
        assert abs(a - b) < mp.mpf("1e-40") * abs(a)


def test_lesion_a_perturbed_kappa_breaks_the_functional_equation(monkeypatch: pytest.MonkeyPatch) -> None:
    real = dh.coefficients

    def off(dps: int = 40):
        a = real(dps)
        a[2] += mp.mpf("1e-6")
        a[3] -= mp.mpf("1e-6")
        return a

    monkeypatch.setattr(dh, "coefficients", off)
    with mp.workdps(40):
        z = mp.mpc(0.2, 3.0)
        a, b = dh.F_mp(z), dh.F_mp(1 - z)
        assert abs(a - b) > mp.mpf("1e-9") * abs(a)


def test_H0_is_real_on_the_real_axis() -> None:
    with mp.workdps(40):
        for x in ("300.3", "1000.7"):
            h = dh.H_oracle(x, "0", "0", dps=40)
            assert abs(mp.im(h)) < mp.mpf("1e-35") * abs(h)


def test_the_offline_zero_in_the_wide_frame() -> None:
    """t = 0: rho = sigma + i gamma maps to z = 2 gamma + i (2 sigma - 1) (the mate
    1 - conj(rho) of the lab's pinned zero lies in the upper half-plane)."""
    from zeta import epstein

    with mp.workdps(40):
        x = mp.nstr(2 * mp.mpf(epstein.OFFLINE_ZERO_IM), 30)
        y = mp.nstr(2 * mp.mpf(epstein.OFFLINE_ZERO_RE) - 1, 30)
        at = abs(dh.H_oracle(x, y, "0", dps=40))
        near = abs(dh.H_oracle(x, "0.3", "0", dps=40))
        assert at < mp.mpf("1e-18") * near


def test_hunt61_zero_at_t_02304_is_a_zero_of_the_wide_frame_flow() -> None:
    """The frame conversion, checked by a route sharing no code with hunt #61:
    Gauss-Hermite quadrature of the heat kernel over mpmath's Hurwitz-based F
    vanishes at 2 z_n and t = 4 t_n, to 1e-10 of its size 0.3 above.
    About 30 s."""
    x, y = _wide(Z61_NARROW)
    t = "0.2304"
    with mp.workdps(30):
        assert mp.mpf(t) == 4 * mp.mpf(T61_NARROW)
        at = abs(dh.H_oracle(x, y, t, n_nodes=80))
        near = abs(dh.H_oracle(x, "0.3", t, n_nodes=80))
        assert at < mp.mpf("1e-10") * near


def test_lesion_the_narrow_frame_point_is_not_a_zero() -> None:
    """The control for the previous test: the same numbers read in the wrong
    frame (z_n itself at t_n) are not a zero of the wide-frame flow."""
    x, y = Z61_NARROW
    with mp.workdps(30):
        at = abs(dh.H_oracle(x, y, T61_NARROW, n_nodes=40))
        near = abs(dh.H_oracle(x, "0.3", T61_NARROW, n_nodes=40))
        assert at > mp.mpf("1e-3") * near


# measured 2026-10-26: |H - (A+B)| / |B| at t = 0, and that ratio times (5x/(4 pi))^{1/4}
RESIDUALS = [
    ("300.3", "0", 0.2177), ("300.3", "0.5", 0.1416), ("1000.7", "0", 0.0519), ("1000.7", "0.5", 0.0319),
    ("3000.1", "0", 0.1866), ("3000.1", "0.5", 0.0711), ("10000.9", "0", 0.0213), ("10000.9", "0.5", 0.0109),
]


@pytest.mark.parametrize("x,y,r", RESIDUALS)
def test_main_terms_leave_a_correction_of_size_x_to_the_minus_quarter(x: str, y: str, r: float) -> None:
    got = _ratio(x, y, "0")
    assert abs(got - r) < 5e-5
    # the envelope seen on these points: below 1.1 (5x/(4 pi))^{-1/4}, the scale of a
    # Riemann-Siegel correction (measured, not a bound)
    assert got * (5 * float(x) / (4 * 3.141592653589793)) ** 0.25 < 1.1


def test_lesion_a_negated_kappa_in_the_main_terms_is_seen() -> None:
    with mp.workdps(60):
        k = mp.nstr(-mp.re(dh.kappa(60)), 55)
    h = dh.H_oracle("1000.7", "0.5", "0", dps=30)
    m = dh.main_terms("1000.7", "0.5", "0", kappa_value=k)
    with workprec(192), mp.workdps(40):
        H = acb(arb(mp.nstr(h.real, 30)), arb(mp.nstr(h.imag, 30)))
        assert float((abs(H - m["H_main"]) / abs(m["B"])).mid()) > 0.3


def test_the_main_terms_alone_do_not_see_the_gate_zeros() -> None:
    """The point of the gate.  At both off-line zeros, A + B is still about a
    quarter of |B|: a pipeline that used the main terms with error terms smaller
    than that would declare these points zero-free.  The DH correction and
    error terms (DH.md, steps 2 and 3) must cover this, or the gate fails."""
    from zeta import epstein

    with mp.workdps(40):
        x0 = mp.nstr(2 * mp.mpf(epstein.OFFLINE_ZERO_IM), 30)
        y0 = mp.nstr(2 * mp.mpf(epstein.OFFLINE_ZERO_RE) - 1, 30)
    x1, y1 = _wide(Z61_NARROW)
    seen = {}
    for key, (x, y, t) in {"t=0": (x0, y0, "0"), "t=0.2304": (x1, y1, "0.2304")}.items():
        m = dh.main_terms(x, y, t)
        seen[key] = (m["N"], float(m["ratio_to_B"].mid()))
    assert seen["t=0"][0] == 8 and 0.25 < seen["t=0"][1] < 0.28
    assert seen["t=0.2304"][0] == 13 and 0.25 < seen["t=0.2304"][1] < 0.28
