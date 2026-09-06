"""Controls pinning the case studies of docs/17-the-falsification-harness.md.

Each test pins the *structural* verdict on one rogue-lab claim from
2026-08-05, at sizes reduced from the originals so the whole file stays in
the fast tier.  The headline percentages quoted in docs/17 were measured at
the original sizes (N=50, M=300 for the dust torus; N=300 for the Dirichlet
gauntlet) and are hedged there as session measurements; what is asserted
here is the part that must never regress:

* the dust-torus "calibration" is a two-parameter affine fit that works
  equally well when the geometry is replaced by noise (docs/17 case 1);
* the Dirichlet xp "imposter gauntlet" is a realness detector: any real
  coefficient sequence, including the true Davenport-Heilbronn one,
  yields a real antisymmetric matrix and therefore a purely imaginary
  spectrum (docs/17 case 2);
* the Sierra-Townsend discretization has an equally spaced ladder
  (linear density), not the E log E density of the zeros (docs/17 case 3).

The scripts under review live in ontology/ and are loaded by file path:
ontology/ is not a package of the editable install.
"""

from __future__ import annotations

import importlib.util
import pathlib
import sys

import numpy as np
import pytest

REPO = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from zeta.epstein import dh_coefficient  # noqa: E402


def _load(name: str, relpath: str):
    spec = importlib.util.spec_from_file_location(name, REPO / relpath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


RIEMANN_T = np.array([14.1347, 21.0220, 25.0108, 30.4249, 32.9351, 37.5862, 40.9187])


def _affine_fit_error(lam: np.ndarray, target: np.ndarray) -> float:
    """Mean |relative error| in % of the best affine map alpha*lam + beta."""
    A = np.vstack([lam, np.ones_like(lam)]).T
    coeffs, *_ = np.linalg.lstsq(A, target, rcond=None)
    cal = A @ coeffs
    return float(np.mean(np.abs(cal - target) / target * 100))


class TestGeometricDustTorus:
    """Case 1: ontology/10_geometric_dust_torus.py."""

    N, M, SIGMA = 30, 150, 0.2

    @pytest.fixture(scope="class")
    def dust(self):
        return _load("dust10", "ontology/10_geometric_dust_torus.py")

    @pytest.fixture(scope="class")
    def laplacian(self, dust):
        return dust.torus_laplacian(self.N, 2 * np.pi / self.N)

    def _low_modes(self, dust, laplacian, k=7):
        P = dust.build_dust_potential(self.N, self.M, sigma=self.SIGMA)
        return np.sort(np.linalg.eigvalsh(laplacian + P))[:k]

    def test_min_eigenvalue_bound_is_trivial(self, dust, laplacian):
        # "All eigenvalues >= 1/4" is a consequence of a large positive
        # potential plus a positive semidefinite Laplacian, not of RH
        # structure: the minimum clears 1/4 by an order of magnitude.
        lam = self._low_modes(dust, laplacian, k=1)
        assert lam[0] > 1.0

    def test_fit_to_riemann_zeros_is_poor(self, dust, laplacian):
        lam = self._low_modes(dust, laplacian)
        err = _affine_fit_error(lam, 0.25 + RIEMANN_T**2)
        assert err > 8.0  # measured ~20% at full size; anything near 1% would be news

    def test_geometry_is_not_load_bearing(self, dust, laplacian):
        # Replace the polygon "dust" with noise and with a constant: the
        # fit quality must stay within a few points of the original, which
        # is the ablation-failure that rejects the claim.
        target = 0.25 + RIEMANN_T**2
        err_real = _affine_fit_error(self._low_modes(dust, laplacian), target)

        rng = np.random.default_rng(1)
        orig = dust.geometric_dust
        try:
            dust.geometric_dust = lambda n: float(rng.uniform(0, 40))
            err_noise = _affine_fit_error(self._low_modes(dust, laplacian), target)
            dust.geometric_dust = lambda n: 20.0
            err_const = _affine_fit_error(self._low_modes(dust, laplacian), target)
        finally:
            dust.geometric_dust = orig

        assert abs(err_noise - err_real) < 6.0
        assert abs(err_const - err_real) < 6.0


class TestDirichletGauntlet:
    """Case 2: ontology/13_dirichlet_polya_hilbert.py."""

    N = 200

    @pytest.fixture(scope="class")
    def s13(self):
        return _load("gauntlet13", "ontology/13_dirichlet_polya_hilbert.py")

    def _max_real_drift(self, s13, coeff) -> float:
        M = s13.build_dirichlet_xp_operator(self.N, coeff)
        return float(np.max(np.abs(np.real(np.linalg.eigvals(M)))))

    def test_true_davenport_heilbronn_passes(self, s13):
        # The actual counterexample has REAL coefficients (1, kappa,
        # -kappa, -1, 0 mod 5), so the operator is real antisymmetric and
        # every eigenvalue is purely imaginary: the gauntlet certifies the
        # imposter.  This false negative is what makes the test vacuous.
        drift = self._max_real_drift(s13, lambda n: complex(dh_coefficient(n)))
        assert drift < 1e-8

    def test_random_real_coefficients_pass(self, s13):
        rng = np.random.default_rng(0)
        coeffs = {k: complex(rng.choice([-1.0, 1.0]) * rng.uniform(0.5, 2.0))
                  for k in range(1, self.N + 1)}
        drift = self._max_real_drift(s13, lambda n: coeffs[n])
        assert drift < 1e-8

    def test_raw_character_fails_despite_being_on_line(self, s13):
        # What the script called "DH" is the raw chi mod 5, i.e. L(s, chi),
        # whose zeros lie on the critical line; the gauntlet flags it
        # anyway.  Misclassification in both directions.
        drift = self._max_real_drift(s13, s13.get_dh_coefficient)
        assert drift > 1.0


class TestSierraTownsendDensity:
    """Case 3: ontology/15_fixing_the_density.py."""

    def test_spectrum_is_a_linear_ladder(self):
        s15 = _load("density15", "ontology/15_fixing_the_density.py")
        H = s15.build_sierra_townsend_matrix(800, 0.1, 50.0)
        g = np.sort([x for x in np.real(np.linalg.eigvals(H)) if x > 1e-4])
        gaps = np.diff(g[:30])
        # Equal spacing == linear counting function, the opposite of the
        # claimed E log E density (whose local gap ~ 2*pi/log(E/2*pi)
        # shrinks by ~2x over this range).
        assert np.std(gaps) / np.mean(gaps) < 0.05
        assert gaps[-1] / gaps[0] > 0.8  # E log E would put this near 0.5
