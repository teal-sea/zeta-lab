"""``ontology.scout_online``, the scout's networked half: OEIS and arXiv.

:mod:`ontology.scout` collides candidates with the corpora on disk; this
module asks the two services a laboratory can query without credentials.
Both are :class:`ontology.knownness.LiteratureBackend` implementations, so
they plug into ``check_literature`` unchanged, and both keep the contract
that makes the scout trustworthy:

* **OEIS** (:class:`OeisBackend`) is the one place a machine may say
  ``FOUND`` on its own: an integer-sequence query whose returned entry
  *contains the queried terms digit for digit* is a content-verified match,
  not a lexical hit, and the A-number is a citable reference. A text query,
  or a numeric query whose results do not contain the sequence, produces
  leads only.
* **arXiv** (:class:`ArxivBackend`) never says ``FOUND``. A title or
  abstract matching your words is a paper to read, not prior art
  established; hits ride in ``detail`` as leads for a human, exactly like
  the local corpus backend.
* **zbMATH Open** (:class:`ZbMathBackend`), the reviewing database's free
  public API (api.zbmath.org, no credentials since 2021). Same rule as
  arXiv: reviewed-literature leads with zbMATH identifiers, never
  ``FOUND``: a search hit in a review database is still a lexical hit.

Failure is honest by construction: a query that never reached the service
returns ``UNKNOWN`` with ``online=False`` and the error named,
``knownness`` refuses an *online* backend returning ``UNKNOWN``, and a
backend that could not connect was not online, whatever it hoped. Nothing
here can emit a novelty claim; every label passes ``funnel_label`` at
construction.

Standard library only (``urllib``); the fetch function is injectable so
every path is testable offline.
"""

from __future__ import annotations

import json
import re
import urllib.error
import urllib.parse
import urllib.request
from typing import Callable, Final

from ontology.knownness import (
    NOT_RECOGNISED_OFFLINE,
    LiteratureBackend,
    LiteratureResult,
    LiteratureStatus,
)

__all__ = [
    "ArxivBackend",
    "OeisBackend",
    "ZbMathBackend",
]

#: Courtesy identification for the two public catalogs this module queries.
#: Deliberately names the *instrument* and not its subject: this module sits in
#: the domain-agnostic half of `ontology/`, and `tests/test_discovery_zeta_domain.py`
#: reads the bytes. A caller that wants a subject-specific agent passes its own
#: `fetch`.
_USER_AGENT: Final[str] = "ontology-scout/0.1 (research tool; single queries)"

#: Fewer terms than this and an OEIS numeric query matches half the catalog;
#: the backend falls back to a text query, which can only produce leads.
MIN_SEQUENCE_TERMS: Final[int] = 4

Fetch = Callable[[str, float], str]


def _default_fetch(url: str, timeout: float) -> str:
    request = urllib.request.Request(url, headers={"User-Agent": _USER_AGENT})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read().decode("utf-8", errors="replace")


def _did_not_reach(name: str, exc: Exception) -> LiteratureResult:
    return LiteratureResult(
        status=LiteratureStatus.UNKNOWN,
        label=NOT_RECOGNISED_OFFLINE,
        backend=name,
        online=False,  # it hoped to be online; it was not, and says so
        detail=(
            f"the query did not reach {name}: {exc.__class__.__name__}: {exc}."
            " 'unknown' means the service was not consulted, not that the"
            " observation is absent from it."
        ),
    )


def _terms_from(candidate) -> tuple[str, ...]:
    terms = [
        value
        for value in getattr(candidate, "claim", {}).values()
        if isinstance(value, str) and value.strip()
    ]
    label = getattr(candidate, "label", "")
    if isinstance(label, str) and label.strip():
        terms.append(label)
    return tuple(terms)


def _sequence_from(candidate) -> tuple[int, ...]:
    """The longest integer sequence anywhere in the claim, or ()."""
    best: tuple[int, ...] = ()
    for value in getattr(candidate, "claim", {}).values():
        if (
            isinstance(value, (list, tuple))
            and len(value) > len(best)
            and all(isinstance(x, int) and not isinstance(x, bool) for x in value)
        ):
            best = tuple(value)
    return best


class OeisBackend(LiteratureBackend):
    """OEIS, with ``FOUND`` reserved for content-verified sequence matches."""

    name = "oeis"
    online = True

    def __init__(self, fetch: Fetch = _default_fetch, timeout: float = 20.0) -> None:
        self.fetch = fetch
        self.timeout = timeout

    def lookup(self, candidate) -> LiteratureResult:
        sequence = _sequence_from(candidate)
        if len(sequence) >= MIN_SEQUENCE_TERMS:
            query = ",".join(str(n) for n in sequence)
            verified = True
        else:
            terms = _terms_from(candidate)
            if not terms:
                return LiteratureResult(
                    status=LiteratureStatus.UNKNOWN,
                    label=NOT_RECOGNISED_OFFLINE,
                    backend=self.name,
                    online=False,
                    detail="the candidate carries no sequence and no searchable text; no query ran",
                )
            query = " ".join(terms)
            verified = False

        url = "https://oeis.org/search?" + urllib.parse.urlencode(
            {"q": query, "fmt": "json"}
        )
        try:
            payload = json.loads(self.fetch(url, self.timeout))
        except Exception as exc:  # noqa: BLE001 - every failure maps to honesty
            return _did_not_reach(self.name, exc)

        results = payload if isinstance(payload, list) else payload.get("results") or []
        if not results:
            return LiteratureResult(
                status=LiteratureStatus.NOT_FOUND,
                label=NOT_RECOGNISED_OFFLINE,
                backend=self.name,
                online=True,
                sources_queried=("OEIS",),
                detail=f"OEIS returned no results for {query!r}; absence from OEIS is not absence from the literature",
            )

        leads = []
        for entry in results[:10]:
            number = entry.get("number")
            a_number = f"A{number:06d}" if isinstance(number, int) else "A??????"
            leads.append(f"{a_number}: {str(entry.get('name', ''))[:120]}")

        if verified:
            needle = ",".join(str(n) for n in sequence)
            confirmed = [
                entry
                for entry in results
                if needle in str(entry.get("data", "")).replace(" ", "")
            ]
            if confirmed:
                references = tuple(
                    f"https://oeis.org/A{entry['number']:06d}"
                    for entry in confirmed[:5]
                    if isinstance(entry.get("number"), int)
                )
                if references:
                    return LiteratureResult(
                        status=LiteratureStatus.FOUND,
                        label="matches-oeis-sequence",
                        backend=self.name,
                        online=True,
                        sources_queried=("OEIS",),
                        references=references,
                        detail=(
                            f"the queried terms {needle} appear verbatim in: "
                            + "; ".join(leads[: len(references)])
                        ),
                    )

        return LiteratureResult(
            status=LiteratureStatus.NOT_FOUND,
            label=NOT_RECOGNISED_OFFLINE,
            backend=self.name,
            online=True,
            sources_queried=("OEIS",),
            detail=(
                "OEIS returned entries but none contains the queried terms "
                "verbatim, leads, not findings: " + "; ".join(leads)
                if verified
                else "OEIS text search, lexical leads only, never a match: "
                + "; ".join(leads)
            ),
        )


class ArxivBackend(LiteratureBackend):
    """arXiv as a lead generator. It has no route to ``FOUND`` on purpose."""

    name = "arxiv"
    online = True

    def __init__(
        self,
        fetch: Fetch = _default_fetch,
        timeout: float = 20.0,
        max_results: int = 10,
    ) -> None:
        self.fetch = fetch
        self.timeout = timeout
        self.max_results = max_results

    def lookup(self, candidate) -> LiteratureResult:
        terms = _terms_from(candidate)
        if not terms:
            return LiteratureResult(
                status=LiteratureStatus.UNKNOWN,
                label=NOT_RECOGNISED_OFFLINE,
                backend=self.name,
                online=False,
                detail="the candidate carries no searchable text; no query ran",
            )
        search = " AND ".join(f'all:"{term}"' for term in terms)
        url = "https://export.arxiv.org/api/query?" + urllib.parse.urlencode(
            {"search_query": search, "max_results": str(self.max_results)}
        )
        try:
            atom = self.fetch(url, self.timeout)
        except Exception as exc:  # noqa: BLE001
            return _did_not_reach(self.name, exc)

        entries = re.findall(r"<entry>(.*?)</entry>", atom, re.DOTALL)
        leads = []
        for entry in entries:
            title = re.search(r"<title>(.*?)</title>", entry, re.DOTALL)
            ident = re.search(r"<id>(.*?)</id>", entry, re.DOTALL)
            leads.append(
                " ".join((title.group(1) if title else "(untitled)").split())[:120]
                + (f" <{ident.group(1).strip()}>" if ident else "")
            )
        if leads:
            detail = (
                f"{len(leads)} arXiv candidate(s) for {terms!r}, papers to "
                "read, not prior art established: " + "; ".join(leads)
            )
        else:
            detail = (
                f"arXiv returned no entries for {terms!r}; absence from this "
                "query is not absence from the literature"
            )
        return LiteratureResult(
            status=LiteratureStatus.NOT_FOUND,
            label=NOT_RECOGNISED_OFFLINE,
            backend=self.name,
            online=True,
            sources_queried=("arXiv",),
            detail=detail,
        )


class ZbMathBackend(LiteratureBackend):
    """zbMATH Open as a lead generator. No credentials, and no ``FOUND``."""

    name = "zbmath-open"
    online = True

    def __init__(
        self,
        fetch: Fetch = _default_fetch,
        timeout: float = 20.0,
        max_results: int = 10,
    ) -> None:
        self.fetch = fetch
        self.timeout = timeout
        self.max_results = max_results

    def lookup(self, candidate) -> LiteratureResult:
        terms = _terms_from(candidate)
        if not terms:
            return LiteratureResult(
                status=LiteratureStatus.UNKNOWN,
                label=NOT_RECOGNISED_OFFLINE,
                backend=self.name,
                online=False,
                detail="the candidate carries no searchable text; no query ran",
            )
        url = (
            "https://api.zbmath.org/v1/document/_search?"
            + urllib.parse.urlencode(
                {
                    "search_string": " ".join(terms),
                    "results_per_page": str(self.max_results),
                }
            )
        )
        try:
            payload = json.loads(self.fetch(url, self.timeout))
        except Exception as exc:  # noqa: BLE001
            return _did_not_reach(self.name, exc)

        total = (payload.get("status") or {}).get("nr_total_results")
        entries = payload.get("result") or []
        leads = []
        for entry in entries:
            title_field = entry.get("title")
            if isinstance(title_field, dict):
                title = title_field.get("title") or "(untitled)"
            else:
                title = title_field or "(untitled)"
            ident = entry.get("identifier") or entry.get("zbmath_url") or ""
            leads.append(f"{str(title)[:120]}" + (f" <zbMATH:{ident}>" if ident else ""))
        if leads:
            detail = (
                f"zbMATH Open reports {total} result(s) for {terms!r}; the "
                f"first {len(leads)}, reviewed literature to read, not "
                "prior art established: " + "; ".join(leads)
            )
        else:
            detail = (
                f"zbMATH Open returned no results for {terms!r}; absence "
                "from this query is not absence from the literature"
            )
        return LiteratureResult(
            status=LiteratureStatus.NOT_FOUND,
            label=NOT_RECOGNISED_OFFLINE,
            backend=self.name,
            online=True,
            sources_queried=("zbMATH Open",),
            detail=detail,
        )
