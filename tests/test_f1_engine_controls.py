"""Controls pinning the Reality Check of docs/15-the-f1-discovery-engine.md.

`docs/15` writes up the seven F1 prototypes and closes with five critiques
that dial its own rhetoric back.  The critiques were prose, and nothing in
this tree checked them.  `hunts/f1_engine_controls/` measured them; this file
is what keeps the measurements from drifting.

Three of the five are pinned here, being the three that make checkable
assertions:

* **the ln 2 degeneracy** (`docs/15` §4).  It is a truncation artifact, as
  the Reality Check says.  Its multiplicity is `dim ker C` for the hub
  incidence matrix `C` of the dead-end nodes, *not* the quoted
  `pi(N/2) - pi(N/3) - 1`, which is the special case in which every dead end
  is prime and which undercounts from `N = 338` on;
* **the density failure** (`docs/15` §6).  At 400 nodes the prototype puts
  159 modes below zeta's first ordinate, where zeta has none, and refining
  the truncation widens that gap rather than closing it;
* **the imposter gauntlet** (`docs/15` §7).  The operator is input-free, so
  the geometry rejects nothing; the coefficient predicate `07` actually runs
  does discriminate on the standing battery; and the two mod-5 L-functions
  whose combination is Davenport-Heilbronn pass that predicate, so
  "immune to false positives" is false.

The prototypes live in `ontology/` and are read, never modified: `AGENTS.md`
freezes them as historical exploratory work.
"""

from __future__ import annotations

import importlib.util
import pathlib
import sys

import numpy as np
import pytest

REPO = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(REPO / "hunts" / "f1_engine_controls"))

import density  # noqa: E402
import gauntlet  # noqa: E402
import ln2_law  # noqa: E402


# ---------------------------------------------------------------------------
# 1. The ln 2 multiplicity
# ---------------------------------------------------------------------------


class TestLn2Multiplicity:
    """docs/15 §4 and its Reality Check item 5."""

    @pytest.mark.parametrize("n_max", [60, 100, 180, 260, 338, 340, 360])
    def test_the_law_predicts_the_measured_multiplicity(self, n_max: int) -> None:
        """`|D| - rank C` is the multiplicity, at every size tested."""
        assert ln2_law.predicted_multiplicity(n_max) == ln2_law.measured_multiplicity(n_max)

    @pytest.mark.parametrize("n_max", [100, 260, 338, 360])
    def test_both_rank_routes_agree(self, n_max: int) -> None:
        """40-digit elimination and double-precision LAPACK give one rank.

        The entries are logarithms of primes, so a rank here is a numerical
        judgment however it is taken; two independent routes agreeing is what
        stands in for exactness.
        """
        assert ln2_law.rank_agrees_with_numpy(n_max)

    def test_the_cluster_really_sits_at_ln_2(self) -> None:
        """Not a near-degeneracy: the modes are at ln 2 to machine precision."""
        module = ln2_law.load_prototype()
        gammas = np.imag(np.linalg.eigvals(module.build_antisymmetric_matrix(200)))
        near = gammas[np.abs(gammas - ln2_law.LN2) < 1e-3]
        assert near.size > 0
        assert float(np.max(np.abs(near - ln2_law.LN2))) < 1e-12

    @pytest.mark.parametrize("n_max", [100, 200, 300, 330])
    def test_the_quoted_formula_is_right_below_the_departure(self, n_max: int) -> None:
        """Which is why it survived: it is correct on everything it was seen on."""
        assert ln2_law.quoted_multiplicity(n_max) == ln2_law.measured_multiplicity(n_max)

    @pytest.mark.parametrize("n_max", [338, 340, 350, 360])
    def test_the_quoted_formula_undercounts_from_338(self, n_max: int) -> None:
        measured = ln2_law.measured_multiplicity(n_max)
        assert ln2_law.quoted_multiplicity(n_max) == measured - 1

    def test_the_first_departure_is_where_docs15_says_it_is(self) -> None:
        assert ln2_law.first_departure() == ln2_law.FIRST_DEPARTURE == 338

    def test_the_extra_mode_at_338_comes_from_the_semiprime_pattern(self) -> None:
        """The mechanism, not just the count.

        At `N = 338` the dead ends include `121 = 11^2`, `143 = 11*13` and
        `169 = 13^2`: three columns sharing the two hubs `11` and `13`, so
        one coefficient vector survives that no prime dead end supplies.
        """
        ends = ln2_law.dead_end_nodes(338)
        assert {121, 143, 169}.issubset(set(ends))
        matrix, columns, hubs = ln2_law.hub_incidence(338)
        for semiprime in (121, 143, 169):
            reached = {hubs[i] for i, row in enumerate(matrix) if row[columns.index(semiprime)]}
            assert reached.issubset({11, 13})


# ---------------------------------------------------------------------------
# 2. The density failure
# ---------------------------------------------------------------------------


class TestSpectralDensity:
    """docs/15 §6 and its Reality Check item 2."""

    def test_docs15_mode_20_reproduces(self) -> None:
        """The number the write-up quotes, still produced by the code."""
        assert density.counts(400)["mode_20"] == pytest.approx(1.937, abs=5e-4)

    def test_hundreds_of_modes_sit_below_zetas_first_zero(self) -> None:
        row = density.counts(400)
        assert row["modes_below_gamma_1"] == 159
        assert row["zeta_zeros_below_gamma_1"] == 0

    def test_zeta_has_one_zero_where_the_prototype_has_a_crowd(self) -> None:
        """The Reality Check's own comparison height, as counts: it says
        "dozens", and at 400 nodes it is 171 against 1."""
        row = density.counts(400)
        assert row["zeta_zeros_below_docs15_height"] == 1
        assert row["modes_below_docs15_height"] == 171

    def test_refinement_widens_the_gap(self) -> None:
        """The hunts precision-response control, answered in the wrong
        direction: more nodes means more spurious low modes, not fewer."""
        below = [density.counts(n)["modes_below_gamma_1"] for n in (100, 200, 400)]
        assert below == sorted(below) and below[0] < below[-1]

    def test_the_top_of_the_spectrum_crawls(self) -> None:
        """Doubling the nodes buys a few units of frequency, so the top mode
        is still an order of magnitude below the 20th ordinate."""
        top = [density.counts(n)["top_mode"] for n in (100, 400)]
        assert top[1] - top[0] < 10.0
        assert top[1] < density.GAMMA_20 / 3


# ---------------------------------------------------------------------------
# 3. The imposter gauntlet
# ---------------------------------------------------------------------------


class TestImposterGauntlet:
    """docs/15 §7 and its Reality Check item 4."""

    def test_the_operator_is_input_free(self) -> None:
        """So "the geometry rejects the imposter" is not about the geometry."""
        geometry = gauntlet.geometry_is_input_free()
        assert geometry["takes_only_the_truncation"]
        assert geometry["rebuild_is_identical"]

    def test_the_predicate_discriminates_on_the_standing_battery(self) -> None:
        """Which is why the "ignores its input" charge does not land on 07."""
        from zeta.epstein import battery, claim_multiplicativity

        verdict = battery(claim_multiplicativity)
        assert verdict["riemann_zeta"] is True
        assert verdict["davenport_heilbronn"] is False
        assert verdict["distinguishes"] is True
        assert verdict["shared_with"] == ()

    def test_the_dh_summands_pass_the_same_predicate(self) -> None:
        """The refutation of "immune to false positives": the two mod-5
        L-functions the imposter is built from are admitted."""
        from zeta.epstein import claim_multiplicativity

        for conjugate in (False, True):
            assert claim_multiplicativity(gauntlet.l_function_interface(conjugate))
