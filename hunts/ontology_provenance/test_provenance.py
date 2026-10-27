"""Acceptance for the Requirement A scan: planted lesions must go red.

A scanner that cannot fail is not a scanner (`AGENTS.md`, "a cross-check that
cannot fail is not a cross-check"). Every case below is written to break one
specific part of the rule set, and the expected verdict is the one a reader
should reject the tool for getting wrong.
"""

from __future__ import annotations

import pytest

from provenance import (
    CLEAN,
    TAINTED,
    UNDECIDED,
    Analysis,
    analyse_source,
    propagate_symbol_taint,
    resolve,
)


def verdict(src: str) -> tuple[str, str]:
    a = analyse_source(src)
    return a.status, a.tier


# --- lesions: each must be caught -------------------------------------------


@pytest.mark.parametrize(
    "src, why",
    [
        ("from mpmath import zetazero\nx = zetazero(1)\n", "ordinate producer"),
        ("import mpmath\nx = mpmath.zetazero(1)\n", "dotted ordinate producer"),
        ("from zeta.zeros import verify_rh_up_to\n", "zero verification"),
        ("from zeta.epstein import find_offline_zero\n", "zero locator"),
        ("from zeta.explicit import psi_from_zeros\n", "explicit formula zero side"),
        ("def f(b):\n    return b.bump_pair(3, 0.25)\n", "Weil zero-side pair"),
        ("x = grampoint(10)\n", "bare Gram point, no import"),
        ("from zeta.statistics import pair_correlation\n", "ordinate statistics"),
        ("from zeta.heatflow import H_t\n", "flow acting on Xi"),
        ("import zeta.zeros as z\n", "zero module by alias"),
    ],
)
def test_zero_derived_ingredients_are_tainted(src: str, why: str) -> None:
    status, tier = verdict(src)
    assert status == TAINTED, why
    assert tier == "direct", why


def test_dynamic_execution_is_undecided_not_clean() -> None:
    status, tier = verdict("exec('from mpmath import zetazero')\n")
    assert status == UNDECIDED
    assert tier == ""


def test_syntax_error_is_undecided_not_clean() -> None:
    status, _ = verdict("def broken(:\n    pass\n")
    assert status == UNDECIDED


# --- the other direction: a clean construction must stay clean ---------------


@pytest.mark.parametrize(
    "src",
    [
        # prime-power data only, which is exactly what Requirement A asks for
        "from zeta.factorization import factorization_defect\ndef D(a):\n    return factorization_defect(a)\n",
        # the word 'zero' in an unrelated identifier must not trip a substring rule
        "def zero_free_region(sigma):\n    return sigma > 1.0\n",
        # an arithmetic-side explicit formula is prime data, not the zero side
        "from zeta.explicit import prime_spectrum\n",
        # importing the package is not importing the zeros (deliberate decision)
        "import zeta\nx = zeta.__name__\n",
    ],
)
def test_prime_derived_constructions_stay_clean(src: str) -> None:
    status, _ = verdict(src)
    assert status == CLEAN


# --- reachability: the tier that a single-file read cannot see ---------------


def _is_edge_path(universe: dict[str, Analysis], trail: list[str]) -> bool:
    return all(trail[i + 1] in universe[trail[i]].edges for i in range(len(trail) - 1))


def test_reachability_names_the_path() -> None:
    universe = {
        "lab.candidate": Analysis(path="lab/candidate.py", edges={"lab.helper", "lab.data"}),
        "lab.helper": Analysis(path="lab/helper.py", edges={"lab.data"}),
        "lab.data": Analysis(
            path="lab/data.py",
            status=TAINTED,
            tier="direct",
            witness="uses nzeros: zero-counting function",
        ),
    }
    got = resolve("lab.candidate", universe)
    assert got.status == TAINTED
    assert got.tier == "reachable"
    assert got.path_to_taint[0] == "lab.candidate"
    assert got.path_to_taint[-1] == "lab.data"
    assert _is_edge_path(universe, got.path_to_taint), got.path_to_taint
    assert "nzeros" in got.witness


def test_reachability_through_an_intermediate_when_it_is_the_only_route() -> None:
    universe = {
        "lab.candidate": Analysis(path="lab/candidate.py", edges={"lab.helper"}),
        "lab.helper": Analysis(path="lab/helper.py", edges={"lab.data"}),
        "lab.data": Analysis(path="lab/data.py", status=TAINTED, tier="direct", witness="x"),
    }
    got = resolve("lab.candidate", universe)
    assert got.path_to_taint == ["lab.candidate", "lab.helper", "lab.data"]


def test_unreadable_dependency_is_undecided_not_clean() -> None:
    universe = {
        "lab.candidate": Analysis(path="lab/candidate.py", edges={"lab.mystery"}),
        "lab.mystery": Analysis(
            path="lab/mystery.py", status=UNDECIDED, reason="dynamic execution: exec"
        ),
    }
    assert resolve("lab.candidate", universe).status == UNDECIDED


def test_order_independence() -> None:
    universe = {
        "a": Analysis(path="a.py", edges={"b"}),
        "b": Analysis(path="b.py", edges={"c"}),
        "c": Analysis(path="c.py", status=TAINTED, tier="direct", witness="x"),
        "d": Analysis(path="d.py", edges={"b"}),
    }
    first = resolve("a", universe)
    resolve("d", universe)
    second = resolve("a", universe)
    assert first.status == second.status
    assert first.path_to_taint == second.path_to_taint


def test_a_clean_symbol_is_not_tainted_by_a_sibling() -> None:
    helper = analyse_source(
        "from mpmath import zetazero\n"
        "def uses_zero():\n"
        "    return zetazero(1)\n"
        "def coefficients_only(n):\n"
        "    return n + 1\n",
        path="lab/helper.py",
        module="lab.helper",
    )
    assert helper.status == TAINTED
    assert helper.symbols["uses_zero"] == TAINTED
    assert helper.symbols["coefficients_only"] == CLEAN
    candidate = analyse_source(
        "from lab.helper import coefficients_only\n"
        "def build(n):\n"
        "    return coefficients_only(n)\n",
        path="lab/candidate.py",
        module="lab.candidate",
    )
    assert candidate.status == CLEAN
    universe = {"lab.helper": helper, "lab.candidate": candidate}
    got = resolve("lab.candidate", universe)
    assert got.status == CLEAN, got.witness or got.reason


def test_importing_the_tainted_sibling_is_reachable() -> None:
    helper = analyse_source(
        "def uses_zero():\n"
        "    return zetazero(1)\n"
        "def coefficients_only(n):\n"
        "    return n + 1\n",
        path="lab/helper.py",
    )
    candidate = analyse_source(
        "from lab.helper import uses_zero\n",
        path="lab/candidate.py",
    )
    got = resolve(
        "lab.candidate",
        {"lab.helper": helper, "lab.candidate": candidate},
    )
    assert got.status == TAINTED
    assert got.tier == "reachable"
    assert "uses_zero" in got.witness


def test_a_wrapper_around_an_imported_tainted_symbol_is_tainted() -> None:
    helper = analyse_source(
        "def uses_zero():\n"
        "    return zetazero(1)\n",
        path="lab/helper.py",
        module="lab.helper",
    )
    mid = analyse_source(
        "from lab.helper import uses_zero\n"
        "def wrap():\n"
        "    return uses_zero()\n",
        path="lab/mid.py",
        module="lab.mid",
    )
    universe = {"lab.helper": helper, "lab.mid": mid}
    propagate_symbol_taint(universe)
    assert universe["lab.mid"].symbols["wrap"] == TAINTED
    outer = analyse_source(
        "from lab.mid import wrap\n",
        path="lab/outer.py",
        module="lab.outer",
    )
    universe["lab.outer"] = outer
    got = resolve("lab.outer", universe)
    assert got.status == TAINTED
    assert got.tier == "reachable"


def test_frame_07_is_clean_and_the_numbered_frames_match_the_reading() -> None:
    """The known false positive stays out of the verdict table.

    07 imports only ``dh_coefficient``. A module-level read of ``zeta.epstein``
    flagged it; symbol-level resolution must not.
    """
    from pathlib import Path

    from provenance import collect

    root = Path(__file__).resolve().parents[2]
    universe = collect(root)
    assert universe["zeta.epstein"].symbols["dh_coefficient"] == CLEAN
    expected = {
        "ontology.01_f1_geometry": CLEAN,
        "ontology.02_acoustic_f1_matrix": CLEAN,
        "ontology.03_inverse_spectral_geometry": TAINTED,
        "ontology.04_transcendental_matrix": CLEAN,
        "ontology.05_berry_keating_grid": TAINTED,
        "ontology.06_the_polya_hilbert_prototype": TAINTED,
        "ontology.07_the_imposter_gauntlet": CLEAN,
        "ontology.08_riemann_beats_audio": TAINTED,
        "ontology.09_hermite_prime_waves": CLEAN,
        "ontology.10_geometric_dust_torus": CLEAN,
        "ontology.11_quantum_chaos_gue": TAINTED,
        "ontology.13_dirichlet_polya_hilbert": CLEAN,
        "ontology.14_hunting_ln2": CLEAN,
        "ontology.15_fixing_the_density": CLEAN,
        "ontology.16_adelic_acoustic_absorber": CLEAN,
    }
    for module, status in expected.items():
        got = resolve(module, universe)
        assert got.status == status, (module, got.status, got.witness or got.reason)
