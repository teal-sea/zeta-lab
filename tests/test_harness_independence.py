"""Tests for ``harness.independence``, the cross-check's bound, measurable.

Three layers of pinning:

1. **The structural semantics**: radius as the aligned shared prefix,
   reconvergence as shared-past-divergence, the distinct segments as the only
   content of an agreement, and the refusal modes (undeclared paths rejected,
   no aggregate boolean).
2. **The worked subject**: the rigor two-backend declaration in
   ``harness.departments.zeta_department`` reproduces docs/25's standing
   consequence, radius 3 of 5, one reconvergent summation layer, exactly one
   layer implemented twice.
3. **The declaration's anchor**: the declared parsing layer names
   ``zeta.rigor._exact``, and that attribute must still exist, a declaration
   that names a function the code no longer has is stale, and this test is
   what notices.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from harness.independence import (  # noqa: E402
    IndependenceError,
    VerificationPath,
    agreement_bounds,
    compare,
)

# ---------------------------------------------------------------------------
# 1. path declaration: what is refused
# ---------------------------------------------------------------------------


def test_a_path_with_no_layers_is_refused() -> None:
    with pytest.raises(IndependenceError, match="unmeasured"):
        VerificationPath(name="empty", layers=())


def test_a_blank_layer_is_refused() -> None:
    with pytest.raises(IndependenceError, match="blank layer"):
        VerificationPath(name="p", layers=("input", "  "))


def test_a_repeated_layer_within_one_path_is_refused() -> None:
    with pytest.raises(IndependenceError, match="twice"):
        VerificationPath(name="p", layers=("input", "input"))


def test_a_nameless_path_is_refused() -> None:
    with pytest.raises(IndependenceError, match="name"):
        VerificationPath(name="  ", layers=("input",))


def test_layer_names_are_stripped() -> None:
    path = VerificationPath(name="p", layers=(" input ", "verdict"))
    assert path.layers == ("input", "verdict")


# ---------------------------------------------------------------------------
# 2. radius, sharing, reconvergence
# ---------------------------------------------------------------------------


def _paths(a: tuple[str, ...], b: tuple[str, ...]):
    return VerificationPath(name="A", layers=a), VerificationPath(name="B", layers=b)


def test_divergence_at_the_input_gives_radius_zero() -> None:
    report = compare(*_paths(("parse a", "check a"), ("parse b", "check b")))
    assert report.radius == 0
    assert report.shared == ()
    assert report.reconvergent == ()
    assert report.distinct_a == ("parse a", "check a")
    assert report.distinct_b == ("parse b", "check b")


def test_a_shared_prefix_is_counted_as_the_radius() -> None:
    report = compare(
        *_paths(("parse", "grid", "backend a"), ("parse", "grid", "backend b"))
    )
    assert report.radius == 2
    assert report.shared == ("parse", "grid")
    assert report.reconvergent == ()
    assert report.distinct_a == ("backend a",)
    assert report.distinct_b == ("backend b",)


def test_reconvergence_is_shared_past_the_divergence() -> None:
    report = compare(
        *_paths(("parse", "backend a", "sum"), ("parse", "backend b", "sum"))
    )
    assert report.radius == 1
    assert report.shared == ("parse", "sum")
    assert report.reconvergent == ("sum",)


def test_identical_paths_are_one_path() -> None:
    layers = ("parse", "check", "sum")
    report = compare(*_paths(layers, layers))
    assert report.radius == 3
    assert report.distinct_a == report.distinct_b == ()
    reasons = agreement_bounds(report)
    assert len(reasons) == 1
    assert "one path" in reasons[0]


def test_out_of_order_sharing_is_shared_but_not_prefix() -> None:
    # The same two stages, run in opposite orders: nothing aligns, so the
    # radius is 0, yet both layers are shared and both count as reconvergent.
    report = compare(*_paths(("parse", "sum"), ("sum", "parse")))
    assert report.radius == 0
    assert set(report.shared) == {"parse", "sum"}
    assert set(report.reconvergent) == {"parse", "sum"}
    assert report.distinct_a == report.distinct_b == ()


# ---------------------------------------------------------------------------
# 3. the report refuses to flatter
# ---------------------------------------------------------------------------


def test_a_report_has_no_truth_value() -> None:
    report = compare(*_paths(("parse", "a"), ("parse", "b")))
    with pytest.raises(TypeError, match="no single truth value"):
        bool(report)


def test_agreement_bounds_names_each_shared_layer_with_its_position() -> None:
    report = compare(
        *_paths(("parse", "backend a", "sum"), ("parse", "backend b", "sum"))
    )
    reasons = agreement_bounds(report)
    assert len(reasons) == 2
    upstream = next(r for r in reasons if "'parse'" in r)
    downstream = next(r for r in reasons if "'sum'" in r)
    assert "upstream of the divergence" in upstream
    assert "downstream of the divergence" in downstream
    assert all("cannot see a fault" in r for r in reasons)


def test_fully_distinct_paths_have_no_bounds_from_sharing() -> None:
    report = compare(*_paths(("parse a", "check a"), ("parse b", "check b")))
    assert agreement_bounds(report) == ()


def test_shared_everything_with_no_duplication_is_called_out() -> None:
    # Same stages, one order shuffled past a common head: nothing distinct.
    report = compare(*_paths(("parse", "sum", "emit"), ("parse", "emit", "sum")))
    reasons = agreement_bounds(report)
    assert any("evidence about nothing" in r for r in reasons)


def test_describe_reads_as_one_line() -> None:
    report = compare(
        *_paths(("parse", "backend a", "sum"), ("parse", "backend b", "sum"))
    )
    text = report.describe()
    assert "radius 1 of 3" in text
    assert "reconvergent: sum" in text
    assert "agreement is evidence about: backend a, backend b" in text


# ---------------------------------------------------------------------------
# 4. the worked subject: the rigor two-backend cross-check
# ---------------------------------------------------------------------------


def test_the_rigor_declaration_reproduces_the_director_run_lesson() -> None:
    from harness.departments.zeta_department import rigor_backend_independence

    report = rigor_backend_independence()
    # docs/25: `_exact`, the grid policy and the contour policy are shared
    # upstream; the S(T)/N(T) interval summation is shared downstream; only
    # the ball-arithmetic layer is implemented twice.
    assert report.radius == 3
    assert len(report.layers_a) == len(report.layers_b) == 5
    assert report.reconvergent == ("S(T)/N(T) interval summation",)
    assert report.distinct_a == ("ball arithmetic: python-flint (Arb)",)
    assert report.distinct_b == ("ball arithmetic: mpmath.iv",)
    reasons = agreement_bounds(report)
    assert len(reasons) == 4  # one per shared layer, nothing else
    assert any("_exact" in r for r in reasons)


def test_the_declared_parsing_anchor_still_exists() -> None:
    from harness.departments.zeta_department import RIGOR_SHARED_LAYERS

    import zeta.rigor as rigor

    assert any("_exact" in layer for layer in RIGOR_SHARED_LAYERS)
    assert hasattr(rigor, "_exact"), (
        "the independence declaration names zeta.rigor._exact, which no "
        "longer exists: update the declaration to the real shared layers"
    )
