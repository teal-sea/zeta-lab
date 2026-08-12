"""The scout's networked half, tested offline via injected fetch.

Pins: OEIS ``FOUND`` requires digit-for-digit content confirmation and a
citable A-number; lexical results in both services stay leads; a query that
never reached the service is ``UNKNOWN`` with ``online=False`` (never a
silent online-unknown, which knownness refuses); and arXiv's source has no
route to ``FOUND`` at all. One slow test hits the real services and skips
where the network does not answer.
"""

from __future__ import annotations

import inspect
import json
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from ontology.knownness import LiteratureStatus, funnel_label  # noqa: E402
from ontology.scout_online import ArxivBackend, OeisBackend  # noqa: E402

_FIB = SimpleNamespace(claim={"sequence": [1, 1, 2, 3, 5, 8, 13, 21]}, label="")
_TEXTUAL = SimpleNamespace(claim={"subject": "pair correlation"}, label="")

_OEIS_HIT = json.dumps(
    {
        "results": [
            {
                "number": 45,
                "name": "Fibonacci numbers: F(n) = F(n-1) + F(n-2).",
                "data": "0,1,1,2,3,5,8,13,21,34,55",
            }
        ]
    }
)
_OEIS_NEAR_MISS = json.dumps(
    {"results": [{"number": 1, "name": "Something else", "data": "1,2,4,8,16"}]}
)
_OEIS_EMPTY = json.dumps({"results": None, "count": 0})

_ARXIV_TWO = (
    "<feed><title>query</title>"
    "<entry><id>http://arxiv.org/abs/1234.5678</id><title>Pair correlation of things</title></entry>"
    "<entry><id>http://arxiv.org/abs/2345.6789</id><title>More correlations</title></entry>"
    "</feed>"
)
_ARXIV_EMPTY = "<feed><title>query</title></feed>"


def _fetch(payload: str):
    def fetch(url: str, timeout: float) -> str:
        return payload

    return fetch


def _broken_fetch(url: str, timeout: float) -> str:
    raise OSError("no route to host")


# ---------------------------------------------------------------------------
# 1. OEIS: FOUND is content-verified or it is nothing
# ---------------------------------------------------------------------------


def test_a_verbatim_sequence_match_is_found_with_a_citable_reference() -> None:
    result = OeisBackend(fetch=_fetch(_OEIS_HIT)).lookup(_FIB)
    assert result.status is LiteratureStatus.FOUND
    assert result.references == ("https://oeis.org/A000045",)
    assert "verbatim" in result.detail
    assert funnel_label(result.label) == result.label


def test_results_without_containment_are_leads_not_findings() -> None:
    result = OeisBackend(fetch=_fetch(_OEIS_NEAR_MISS)).lookup(_FIB)
    assert result.status is LiteratureStatus.NOT_FOUND
    assert result.references == ()
    assert "leads, not findings" in result.detail


def test_a_text_query_can_only_produce_leads() -> None:
    result = OeisBackend(fetch=_fetch(_OEIS_HIT)).lookup(_TEXTUAL)
    assert result.status is LiteratureStatus.NOT_FOUND
    assert "lexical leads only" in result.detail


def test_a_short_sequence_falls_back_to_text_search() -> None:
    short = SimpleNamespace(claim={"sequence": [1, 2, 3]}, label="")
    result = OeisBackend(fetch=_fetch(_OEIS_HIT)).lookup(short)
    # Three terms match half the catalog; no FOUND may come of it.
    assert result.status is not LiteratureStatus.FOUND


def test_an_empty_oeis_answer_is_not_found_with_the_source_named() -> None:
    result = OeisBackend(fetch=_fetch(_OEIS_EMPTY)).lookup(_FIB)
    assert result.status is LiteratureStatus.NOT_FOUND
    assert result.sources_queried == ("OEIS",)
    assert "not absence from the literature" in result.detail


def test_a_failed_query_is_unknown_and_admits_it_was_not_online() -> None:
    result = OeisBackend(fetch=_broken_fetch).lookup(_FIB)
    assert result.status is LiteratureStatus.UNKNOWN
    assert result.online is False
    assert "did not reach oeis" in result.detail.lower()


# ---------------------------------------------------------------------------
# 2. arXiv: a lead generator with no route to FOUND
# ---------------------------------------------------------------------------


def test_arxiv_hits_are_papers_to_read() -> None:
    result = ArxivBackend(fetch=_fetch(_ARXIV_TWO)).lookup(_TEXTUAL)
    assert result.status is LiteratureStatus.NOT_FOUND
    assert "not prior art established" in result.detail
    assert "1234.5678" in result.detail


def test_arxiv_empty_is_bounded() -> None:
    result = ArxivBackend(fetch=_fetch(_ARXIV_EMPTY)).lookup(_TEXTUAL)
    assert result.status is LiteratureStatus.NOT_FOUND
    assert "not absence from the literature" in result.detail


def test_arxiv_failure_is_unknown_offline() -> None:
    result = ArxivBackend(fetch=_broken_fetch).lookup(_TEXTUAL)
    assert result.status is LiteratureStatus.UNKNOWN
    assert result.online is False


def test_the_arxiv_source_has_no_route_to_found() -> None:
    import ast
    import textwrap

    source = textwrap.dedent(inspect.getsource(ArxivBackend))
    found_refs = [
        node
        for node in ast.walk(ast.parse(source))
        if isinstance(node, ast.Attribute) and node.attr == "FOUND"
    ]
    assert found_refs == [], (
        "ArxivBackend accesses LiteratureStatus.FOUND: a title match is "
        "lexical and may never assert prior art"
    )


# ---------------------------------------------------------------------------
# 3. the real services, where the network answers
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_the_real_oeis_confirms_fibonacci_or_the_network_is_absent() -> None:
    result = OeisBackend(timeout=15.0).lookup(_FIB)
    if result.status is LiteratureStatus.UNKNOWN:
        pytest.skip(f"network did not answer: {result.detail}")
    assert result.status is LiteratureStatus.FOUND
    assert "https://oeis.org/A000045" in result.references
