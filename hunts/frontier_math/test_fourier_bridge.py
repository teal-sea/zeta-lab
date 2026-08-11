"""Controls for level 6c: LAW M and the Fourier bridge.

Run from the repo root:

    .venv/bin/python -m pytest -q -o addopts='' \
        hunts/frontier_math/test_fourier_bridge.py
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from fourier_bridge import FourierBridge  # noqa: E402

FB = FourierBridge()


def test_law_m_is_depth_blind_and_positive() -> None:
    """int W dg = 4 pi b / (a^2 L) at every depth, exactly."""
    exact = FB.law_m_exact()
    assert exact > 0
    for y in (0.0, 0.1, 0.3, 0.49):
        assert abs(FB.law_m_measured(y) - exact) < 1e-6


def test_law_m_reproduces_law_j() -> None:
    """The periodized mean is level 2's exact constant 2b/a^2."""
    h = 2 * math.pi / FB.L
    law_j = 2 * (FB.bL() / FB.L) / (FB.aL / FB.L) ** 2
    assert abs(FB.law_m_exact() / h - law_j) < 1e-8
    assert abs(law_j - 2.2959062623) < 1e-6  # the level-2 measured value


def test_kernel_is_nonnegative_and_band_limited() -> None:
    for v in (0.0, 1.5, 4.0, 7.9):
        assert FB.K(v) >= 0
    assert FB.K(8.0) == 0.0
    assert FB.K(9.0) == 0.0
    assert abs(FB.K(0.0) - 0.8317481182 * FB.L) < 1e-4  # K(0) = bL


def test_bridge_representation_is_exact() -> None:
    """The whole term dictionary equals the one-variable quadratic form."""
    assert FB.bridge_check() < 1e-9


def test_bridge_covers_every_law_in_one_identity() -> None:
    """Pure on-line, pure pair, and mixed configs all reconcile."""
    for online, pairs in (
        ([0.1, 0.9, 2.3], []),          # LAW D + R(P) only
        ([], [(0.0, 0.3), (0.7, 0.45)]),  # LAW K + LAW L only
        ([0.5], [(1.2, 0.2)]),           # one W cross term
    ):
        direct = FB.energy_direct(online, pairs)
        fourier = FB.energy_fourier(online, pairs)
        assert abs(direct - fourier) / abs(direct) < 1e-9


def test_conjugate_closure_makes_the_form_real() -> None:
    """|F|^2 with the cosh weights is the conjugate-closed reduction."""
    v = 3.7
    val = FB.F(v, [0.4], [(1.1, 0.3)])
    manual = (
        complex(math.cos(0.4 * v), math.sin(0.4 * v))
        + complex(math.cos(1.1 * v), math.sin(1.1 * v)) * 2 * math.cosh(0.3 * v)
    )
    assert abs(val - manual) < 1e-12


def test_pinch_spectrum_localises_the_battle() -> None:
    """The fluctuation deficit lives mid-band; the mean lives at v ~ 0."""
    bins = FB.pinch_spectrum()
    assert bins[0] > 0            # the LAW M mean, at low frequency
    assert min(bins[3:7]) < -50   # the pinch's deficit, mid-band
    assert abs(bins[-1]) < 5      # K vanishes at the band edge
