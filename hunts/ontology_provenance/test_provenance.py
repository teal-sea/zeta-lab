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
