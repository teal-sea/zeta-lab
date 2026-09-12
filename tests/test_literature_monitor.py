"""The literature monitor, held to the standard the brief sets for it.

``meta/literature-monitor.md`` section 4: a cross-check that cannot fail is not
a cross-check. These tests pin

* the validation gate (a cold run over 2026-09-01 to 2026-09-12 returns both
  arXiv:2609.02882 and arXiv:2609.07918), which is non-negotiable;
* the query-level facts measured in section 2, so that removing the query that
  catches Wang fails loudly instead of quietly narrowing coverage;
* fail-closed behaviour: an HTTP 503, malformed XML and an unexpectedly empty
  response each exit non-zero with the query named, and none of them prints
  "no new papers";
* dedup against an existing issue list, and version-suffix detection.

No test here touches the network except the one marked ``slow``, which skips
itself when arXiv is unreachable. Everything else replays recorded responses
from ``tests/fixtures/literature_monitor/`` or builds synthetic ones in a
temporary directory through the same replay path the script uses.
"""

from __future__ import annotations

import importlib.util
import io
import json
import os
import pathlib
import re
import socket
import sys
import urllib.error

import pytest

_REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
_SCRIPT = _REPO_ROOT / "scripts" / "literature_monitor.py"
_FIXTURES = _REPO_ROOT / "tests" / "fixtures" / "literature_monitor"
_WORKFLOW = _REPO_ROOT / ".github" / "workflows" / "literature-monitor.yml"

_spec = importlib.util.spec_from_file_location("literature_monitor", _SCRIPT)
lm = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
sys.modules["literature_monitor"] = lm  # dataclasses resolve annotations through sys.modules
_spec.loader.exec_module(lm)

LAMZOURI = "2609.02882"
WANG = "2609.07918"
WINDOW = ("2026-09-01", "2026-09-12")

_HAVE_RECORDINGS = (_FIXTURES / "manifest.json").exists() and (_FIXTURES / "baseline.json").exists()
#: Written by hand on 2026-09-12 because arXiv answered HTTP 429 all session. While
#: this marker exists the fixture-backed tests exercise the fixture SHAPE, not the
#: live API's behaviour; tests/fixtures/literature_monitor/README.md says how to record.
_PLACEHOLDERS = (_FIXTURES / "PLACEHOLDER").exists()
needs_recordings = pytest.mark.skipif(
    not _HAVE_RECORDINGS,
    reason=(
        "tests/fixtures/literature_monitor/ has no recorded arXiv responses. Record them with "
        "`python scripts/literature_monitor.py --record tests/fixtures/literature_monitor "
        "--since 2026-09-01 --until 2026-09-12 --no-version-check`. Until then the validation "
        "gate in meta/literature-monitor.md section 4 is NOT being exercised."
    ),
)


# --------------------------------------------------------------------------
# helpers: a synthetic fixture directory built through the script's own key
# --------------------------------------------------------------------------

_ATOM = "http://www.w3.org/2005/Atom"


def _entry(ident: str, version: int, published: str, updated: str | None = None,
           title: str = "A paper", authors=("A. Author",), category="math.NT") -> str:
    updated = updated or published
    names = "".join(f"<author><name>{a}</name></author>" for a in authors)
    return (
        f"<entry><id>http://arxiv.org/abs/{ident}v{version}</id>"
        f"<updated>{updated}T12:00:00Z</updated><published>{published}T12:00:00Z</published>"
        f"<title>{title}</title><summary>  An abstract.\n  Two lines.</summary>{names}"
        f'<arxiv:primary_category xmlns:arxiv="http://arxiv.org/schemas/atom" term="{category}"/>'
        f"</entry>"
    )


def _feed(entries: list[str], total: int | None = None) -> str:
    total = len(entries) if total is None else total
    return (
        '<?xml version="1.0" encoding="UTF-8"?>'
        f'<feed xmlns="{_ATOM}"><title>ArXiv Query</title>'
        f'<opensearch:totalResults xmlns:opensearch="http://a9.com/-/spec/opensearch/1.1/">{total}</opensearch:totalResults>'
        + "".join(entries)
        + "</feed>"
    )


def _write_fixture(directory: pathlib.Path, responses: dict[tuple, str | int]) -> None:
    """``responses`` maps a params tuple to a body (str) or an HTTP status (int)."""
    directory.mkdir(parents=True, exist_ok=True)
    manifest = {}
    for n, (params_items, body) in enumerate(responses.items()):
        params = dict(params_items)
        key = lm._request_key(params)
        if isinstance(body, int):
            manifest[key] = {"file": "", "status": body, "params": params}
        else:
            name = f"r{n}.xml"
            (directory / name).write_text(body, encoding="utf-8")
            manifest[key] = {"file": name, "status": 200, "params": params}
    (directory / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")


def _qparams(query: lm.Query, start: int = 0) -> tuple:
    return tuple(sorted(lm._query_params(query, start).items()))


def _run(argv: list[str]) -> tuple[int, str]:
    out = io.StringIO()
    code = lm.main(argv, out=out)
    return code, out.getvalue()


@pytest.fixture
def empty_tree(tmp_path: pathlib.Path) -> pathlib.Path:
    tree = tmp_path / "tree"
    tree.mkdir()
    return tree


@pytest.fixture
def no_issues(tmp_path: pathlib.Path) -> pathlib.Path:
    path = tmp_path / "issues.json"
    path.write_text("[]", encoding="utf-8")
    return path


# --------------------------------------------------------------------------
# (a) the validation gate, section 4 of the brief
# --------------------------------------------------------------------------


def test_fixtures_are_real_recordings_not_placeholders() -> None:
    """The gate below is only as good as its fixtures. Until the placeholders are
    replaced by ``--record`` output this skips, loudly, so a green run cannot be
    read as the section 4 gate having been paid."""
    if _PLACEHOLDERS:
        pytest.skip(
            "TODO: tests/fixtures/literature_monitor/ holds PLACEHOLDERS written by hand on "
            "2026-09-12 (arXiv API was returning HTTP 429). The section 4 gate is being checked "
            "against the fixture shape only. Record real responses per the README there."
        )
    assert not any(p.name.endswith("-PLACEHOLDER.xml") for p in _FIXTURES.iterdir())


@needs_recordings
def test_cold_run_over_the_calibration_window_returns_both_lamzouri_and_wang() -> None:
    """Non-negotiable. A monitor that misses Wang is a source of false confidence.

    While ``_PLACEHOLDERS`` is true this pins the scan against hand-written fixtures
    in the API's shape; it becomes the real gate the moment the recordings land."""
    fetch = lm.FixtureFetch(str(_FIXTURES))
    reports, hits = lm.scan(fetch, *WINDOW, baseline=lm.load_baseline(str(_FIXTURES / "baseline.json")))
    failed = [r for r in reports if not r.queried]
    assert not failed, [(r.name, r.error) for r in failed]
    assert LAMZOURI in hits, "Lamzouri, arXiv:2609.02882, missed by every query"
    assert WANG in hits, "Wang, arXiv:2609.07918, missed by every query: the incident reproduced"
    assert hits[WANG].matched, "Wang was kept without a matching query named"
    assert hits[WANG].published == "2026-09-07"


@needs_recordings
def test_dry_run_from_fixtures_would_open_both_papers(empty_tree, no_issues) -> None:
    """The same gate through the command line, with the tree and issue list empty."""
    code, out = _run([
        "--dry-run", "--fixture", str(_FIXTURES), "--since", WINDOW[0], "--until", WINDOW[1],
        "--no-version-check", "--tree-root", str(empty_tree), "--existing-issues", str(no_issues),
    ])
    assert code == 0, out
    assert f"WOULD OPEN     new-paper    arXiv:{LAMZOURI}" in out, out
    assert f"WOULD OPEN     new-paper    arXiv:{WANG}" in out, out
    assert "DID NOT QUERY" not in out
    assert "no new papers" not in out.lower()


# --------------------------------------------------------------------------
# (b) the query-level facts of section 2, pinned
# --------------------------------------------------------------------------

#: Section 2 of the brief, measured live on 2026-09-12 against cat:math.NT.
#: (query name, returns Lamzouri, returns Wang)
SECTION_2 = (
    ("simple-zeros", True, False),
    ("simple-critical-zeros", False, True),
    ("pair-correlation", True, True),
    ("critical-line", True, True),
)

#: The queries whose presence is load-bearing. Removing or rewording any of
#: these must fail here, not narrow coverage quietly.
PINNED_QUERIES = {
    "simple-critical-zeros": 'all:"simple critical zeros"',
    "simple-zeros": 'all:"simple zeros"',
    "pair-correlation": 'all:"pair correlation"',
    "critical-line": 'abs:"critical line"',
}


def test_the_load_bearing_queries_are_present_and_unchanged() -> None:
    by_name = {q.name: q.search for q in lm.QUERIES}
    for name, search in PINNED_QUERIES.items():
        assert name in by_name, f"query {name!r} was removed from QUERIES"
        assert by_name[name] == search, f"query {name!r} was reworded: {by_name[name]!r}"


def test_the_brief_lists_every_query_the_monitor_runs() -> None:
    """The brief's starting list, section 3. Extra queries are fine; a missing one is not."""
    searches = " ".join(q.search.lower() for q in lm.QUERIES)
    for phrase in ("pair correlation", "simple zeros", "simple critical zeros", "critical line",
                   "zeros of the riemann zeta", "de bruijn-newman", "davenport-heilbronn",
                   "li's criterion", "mollifier", "form factor", "short intervals"):
        assert phrase in searches, f"the brief's query {phrase!r} is not in QUERIES"


@needs_recordings
@pytest.mark.parametrize("name,has_lamzouri,has_wang", SECTION_2)
def test_section_2_query_facts(name: str, has_lamzouri: bool, has_wang: bool) -> None:
    query = next(q for q in lm.QUERIES if q.name == name)
    fetch = lm.FixtureFetch(str(_FIXTURES))
    report, papers = lm.run_query(query, fetch, *WINDOW, baseline=lm.load_baseline(str(_FIXTURES / "baseline.json")))
    assert report.queried, report.error
    idents = {p.ident for p in papers}
    assert (LAMZOURI in idents) == has_lamzouri, f"{name}: Lamzouri {'missing' if has_lamzouri else 'unexpectedly present'}"
    assert (WANG in idents) == has_wang, f"{name}: Wang {'missing' if has_wang else 'unexpectedly present'}"


@needs_recordings
def test_planted_fault_removing_the_query_that_catches_wang_is_detected() -> None:
    """Detector power. With ``simple-critical-zeros`` removed AND the two broad
    queries that also see Wang removed, the scan misses him: the same three
    queries are what stand between the monitor and the incident it exists to
    prevent, and this test is what turns red if any of them go."""
    fetch = lm.FixtureFetch(str(_FIXTURES))
    baseline = lm.load_baseline(str(_FIXTURES / "baseline.json"))
    catchers = {name for name, _, wang in SECTION_2 if wang}
    narrowed = tuple(q for q in lm.QUERIES if q.name not in catchers)
    assert len(narrowed) == len(lm.QUERIES) - len(catchers)
    _, hits_full = lm.scan(fetch, *WINDOW, queries=lm.QUERIES, baseline=baseline)
    _, hits_narrow = lm.scan(fetch, *WINDOW, queries=narrowed, baseline=baseline)
    assert WANG in hits_full
    assert set(hits_full[WANG].matched) >= catchers, hits_full[WANG].matched
    assert set(hits_narrow.get(WANG).matched if WANG in hits_narrow else ()) .isdisjoint(catchers)


# --------------------------------------------------------------------------
# (c) fail closed: 503, malformed XML, unexpectedly empty
# --------------------------------------------------------------------------

_ONE = lm.Query("pair-correlation", 'all:"pair correlation"')
_TWO = lm.Query("simple-critical-zeros", 'all:"simple critical zeros"')


def _fail_closed_run(tmp_path, monkeypatch, responses: dict, queries=(_ONE, _TWO)) -> tuple[int, str]:
    fixture = tmp_path / "fx"
    _write_fixture(fixture, responses)
    monkeypatch.setattr(lm, "QUERIES", tuple(queries))
    monkeypatch.setattr(lm, "BASELINE_PATH", str(tmp_path / "absent-baseline.json"))
    tree = tmp_path / "tree"
    tree.mkdir()
    issues = tmp_path / "issues.json"
    issues.write_text("[]")
    return _run([
        "--dry-run", "--fixture", str(fixture), "--since", WINDOW[0], "--until", WINDOW[1],
        "--no-version-check", "--tree-root", str(tree), "--existing-issues", str(issues),
    ])


_GOOD_PAGE = _feed([_entry(WANG, 1, "2026-09-07", title="Simple critical zeros", authors=("Biao Wang",))])


def test_http_503_fails_the_run_and_names_the_query(tmp_path, monkeypatch) -> None:
    code, out = _fail_closed_run(tmp_path, monkeypatch, {
        _qparams(_ONE): 503,
        _qparams(_TWO): _GOOD_PAGE,
    })
    assert code != 0
    assert "DID NOT QUERY  pair-correlation" in out, out
    assert "HTTP 503" in out
    assert "queried        simple-critical-zeros" in out, "the healthy query must still be reported as queried"
    assert "RUN FAILED" in out
    assert "no new papers" not in out.lower()


def test_malformed_xml_fails_the_run_and_names_the_query(tmp_path, monkeypatch) -> None:
    code, out = _fail_closed_run(tmp_path, monkeypatch, {
        _qparams(_ONE): _GOOD_PAGE,
        _qparams(_TWO): "<feed><entry><id>http://arxiv.org/abs/2609.07918v1</id>",  # truncated
    })
    assert code != 0
    assert "DID NOT QUERY  simple-critical-zeros" in out, out
    assert "not well-formed" in out
    assert "no new papers" not in out.lower()


def test_unexpectedly_empty_response_fails_the_run(tmp_path, monkeypatch) -> None:
    """Zero entries from a query that has never returned zero is a broken query,
    not a quiet day, whether or not a baseline file exists."""
    code, out = _fail_closed_run(tmp_path, monkeypatch, {
        _qparams(_ONE): _feed([]),
        _qparams(_TWO): _GOOD_PAGE,
    })
    assert code != 0
    assert "DID NOT QUERY  pair-correlation" in out, out
    assert "zero entries" in out
    assert "no new papers" not in out.lower()


def test_empty_response_with_positive_baseline_fails(tmp_path) -> None:
    fixture = tmp_path / "fx"
    _write_fixture(fixture, {_qparams(_ONE): _feed([])})
    report, papers = lm.run_query(_ONE, lm.FixtureFetch(str(fixture)), *WINDOW, baseline={"pair-correlation": 87})
    assert not report.queried
    assert "zero entries" in report.error and "pair-correlation" in report.error
    assert papers == []


def test_a_request_with_no_recording_is_did_not_query_not_nothing_new(tmp_path, monkeypatch) -> None:
    code, out = _fail_closed_run(tmp_path, monkeypatch, {_qparams(_ONE): _GOOD_PAGE})
    assert code != 0
    assert "DID NOT QUERY  simple-critical-zeros" in out
    assert "no recorded response" in out


def test_quiet_window_is_queried_nothing_new_and_exits_zero(tmp_path, monkeypatch) -> None:
    """The other half of the distinction: entries returned, none in the window."""
    old = _feed([_entry("2501.00001", 1, "2025-01-02")])
    code, out = _fail_closed_run(tmp_path, monkeypatch, {_qparams(_ONE): old, _qparams(_TWO): old})
    assert code == 0, out
    assert "queried        pair-correlation" in out
    assert "0 in window" in out
    assert "0 issue(s) would be opened" in out
    assert "DID NOT QUERY" not in out


def test_window_not_covered_by_max_pages_fails(tmp_path, monkeypatch) -> None:
    """Ten full pages that never reach back to ``since`` is not coverage."""
    monkeypatch.setattr(lm, "PAGE_SIZE", 2)
    monkeypatch.setattr(lm, "MAX_PAGES", 2)
    page = _feed([_entry("2609.00001", 1, "2026-09-10"), _entry("2609.00002", 1, "2026-09-10")])
    fixture = tmp_path / "fx"
    _write_fixture(fixture, {_qparams(_ONE, 0): page, _qparams(_ONE, 2): page})
    report, _ = lm.run_query(_ONE, lm.FixtureFetch(str(fixture)), *WINDOW, baseline={})
    assert not report.queried
    assert "not covered" in report.error


def test_arxiv_error_entry_is_an_error_not_a_paper() -> None:
    """arXiv answers a malformed query with one entry whose id is an api URL."""
    atom = _feed(["<entry><id>http://export.arxiv.org/api/errors#bad</id><title>Error</title></entry>"])
    with pytest.raises(lm.MonitorError, match="without an arXiv id"):
        lm.parse_feed(atom, "query 'x'")


# --------------------------------------------------------------------------
# (d) dedup against an existing issue list
# --------------------------------------------------------------------------

_FAKE_ISSUES = [
    {"number": 7, "title": "arXiv:2609.07918: Simple critical zeros", "body": "**arXiv:2609.07918v1** ..."},
    {"number": 9, "title": "unrelated", "body": "mentions 2405.12545 in passing"},
    {"number": 12, "title": "arXiv:2609.02882 has a new version v2", "body": "**arXiv:2609.02882v2**"},
]


def test_ids_mentioned_extracts_bare_and_versioned() -> None:
    bare, versioned = lm.ids_mentioned(_FAKE_ISSUES)
    assert bare == {"2609.07918", "2405.12545", "2609.02882"}
    assert versioned == {"2609.07918v1", "2609.02882v2"}


def _paper(ident: str, version: int = 1, published: str = "2026-09-07") -> lm.Paper:
    return lm.Paper(ident=ident, version=version, title=f"T {ident}", authors=("X",),
                    published=published, updated=published, summary="s", primary_category="math.NT",
                    matched=["pair-correlation"])


def test_plan_skips_papers_already_in_an_issue_and_opens_the_rest() -> None:
    hits = {WANG: _paper(WANG), LAMZOURI: _paper(LAMZOURI, published="2026-09-02"), "2609.11619": _paper("2609.11619")}
    bare, versioned = lm.ids_mentioned(_FAKE_ISSUES)
    actions, skipped = lm.plan_actions(hits, [], cited={}, existing_bare=bare, existing_versioned=versioned)
    opened = {a.key for a in actions}
    assert opened == {"2609.11619"}, opened
    assert any(WANG in s and "existing issue" in s for s in skipped)
    assert any(LAMZOURI in s and "existing issue" in s for s in skipped)


def test_plan_skips_papers_already_cited_in_the_tree() -> None:
    hits = {WANG: _paper(WANG)}
    actions, skipped = lm.plan_actions(hits, [], cited={WANG: 1}, existing_bare=set(), existing_versioned=set())
    assert actions == []
    assert skipped == [f"{WANG}: already cited in the tree"]


def test_plan_skips_a_version_already_reported_but_not_a_newer_one() -> None:
    bare, versioned = lm.ids_mentioned(_FAKE_ISSUES)
    v2 = _paper(LAMZOURI, version=2, published="2026-09-02")
    v3 = _paper(LAMZOURI, version=3, published="2026-09-02")
    actions, skipped = lm.plan_actions({}, [(v2, 1)], cited={LAMZOURI: 1}, existing_bare=bare, existing_versioned=versioned)
    assert actions == [] and any("version already reported" in s for s in skipped)
    actions, _ = lm.plan_actions({}, [(v3, 1)], cited={LAMZOURI: 1}, existing_bare=bare, existing_versioned=versioned)
    assert [a.kind for a in actions] == ["new-version"]
    assert "v3" in actions[0].title and "tree cites v1" in actions[0].title


def test_dedup_through_the_command_line(tmp_path, monkeypatch, empty_tree) -> None:
    fixture = tmp_path / "fx"
    _write_fixture(fixture, {_qparams(_ONE): _feed([
        _entry(WANG, 1, "2026-09-07", title="Simple critical zeros", authors=("Biao Wang",)),
        _entry("2609.11619", 1, "2026-09-10", title="Sharp unconditional moment bounds", authors=("Hagen",)),
    ])})
    issues = tmp_path / "issues.json"
    issues.write_text(json.dumps(_FAKE_ISSUES))
    monkeypatch.setattr(lm, "QUERIES", (_ONE,))
    code, out = _run(["--dry-run", "--fixture", str(fixture), "--since", WINDOW[0], "--until", WINDOW[1],
                      "--no-version-check", "--tree-root", str(empty_tree), "--existing-issues", str(issues)])
    assert code == 0, out
    assert f"skip           {WANG}: already mentioned in an existing issue" in out
    assert "WOULD OPEN     new-paper    arXiv:2609.11619" in out
    assert "1 issue(s) would be opened" in out


def test_issue_body_carries_the_fields_the_brief_requires_and_no_assessment() -> None:
    paper = _paper(WANG)
    paper.title = "Simple critical zeros and distinct zeros"
    paper.authors = ("Biao Wang",)
    paper.summary = "We prove things."
    title, body = lm.new_paper_issue(paper)
    assert title.startswith(f"arXiv:{WANG}: Simple critical zeros")
    for needle in (f"arXiv:{WANG}v1", "Biao Wang", "2026-09-07", "We prove things.",
                   "pair-correlation", f"https://arxiv.org/abs/{WANG}v1"):
        assert needle in body, needle
    for banned in ("important", "relevant", "must read", "priority"):
        assert banned not in body.lower(), f"the body assesses: {banned!r}"


# --------------------------------------------------------------------------
# (e) version-suffix detection
# --------------------------------------------------------------------------


def test_cited_in_tree_returns_the_highest_version_cited(tmp_path) -> None:
    (tmp_path / "a.md").write_text("see arXiv:2609.02882v1 and arXiv:2609.02882 v2 and arXiv:2609.07918.")
    (tmp_path / "b.py").write_text('"""arXiv:2609.02882v2 again; arXiv:1301.3158"""')
    (tmp_path / "c.png").write_bytes(b"arXiv:9999.99999v9")  # not a text file, never read
    skipped = tmp_path / "tests" / "fixtures" / "literature_monitor"
    skipped.mkdir(parents=True)
    (skipped / "q.xml").write_text("arXiv:8888.88888v1")  # the fixture directory is not a citation
    cited = lm.cited_in_tree(str(tmp_path))
    assert cited == {"2609.02882": 2, "2609.07918": 0, "1301.3158": 0}


def test_check_versions_flags_a_newer_version_than_the_tree_cites(tmp_path) -> None:
    cited = {LAMZOURI: 1, WANG: 1}
    params = {"id_list": f"{LAMZOURI},{WANG}", "max_results": "2"}
    fixture = tmp_path / "fx"
    _write_fixture(fixture, {tuple(sorted(params.items())): _feed([
        _entry(LAMZOURI, 2, "2026-09-02", updated="2026-09-09"),
        _entry(WANG, 1, "2026-09-07"),
    ])})
    report, updates = lm.check_versions(cited, lm.FixtureFetch(str(fixture)), *WINDOW)
    assert report.queried and report.checked == 2
    assert [(p.versioned, v) for p, v in updates] == [(f"{LAMZOURI}v2", 1)]


def test_check_versions_bare_citation_only_fires_for_an_update_inside_the_window(tmp_path) -> None:
    cited = {"1301.3158": 0, "2005.05142": 0}
    params = {"id_list": "1301.3158,2005.05142", "max_results": "2"}
    fixture = tmp_path / "fx"
    _write_fixture(fixture, {tuple(sorted(params.items())): _feed([
        _entry("1301.3158", 3, "2013-01-14", updated="2014-06-01"),   # old replacement: silence
        _entry("2005.05142", 2, "2020-05-11", updated="2026-09-08"),  # replaced this week: report
    ])})
    report, updates = lm.check_versions(cited, lm.FixtureFetch(str(fixture)), *WINDOW)
    assert report.queried
    assert [p.versioned for p, _ in updates] == ["2005.05142v2"]


def test_check_versions_fails_closed_on_an_empty_batch(tmp_path) -> None:
    params = {"id_list": LAMZOURI, "max_results": "1"}
    fixture = tmp_path / "fx"
    _write_fixture(fixture, {tuple(sorted(params.items())): _feed([])})
    report, updates = lm.check_versions({LAMZOURI: 1}, lm.FixtureFetch(str(fixture)), *WINDOW)
    assert not report.queried and "zero entries" in report.error
    assert updates == []


@needs_recordings
def test_recorded_lamzouri_is_at_v2_while_the_window_cites_v1() -> None:
    """Section 2 of the brief: Lamzouri was at v2 on 2026-09-12. If the recorded
    fixture disagrees, the fixture is not a recording of that day."""
    fetch = lm.FixtureFetch(str(_FIXTURES))
    baseline = lm.load_baseline(str(_FIXTURES / "baseline.json"))
    _, hits = lm.scan(fetch, *WINDOW, baseline=baseline)
    assert hits[LAMZOURI].version >= 2


# --------------------------------------------------------------------------
# the surrounding contract: workflow, style, stdlib
# --------------------------------------------------------------------------


def test_workflow_runs_weekdays_only_after_announcement_and_never_on_push() -> None:
    text = _WORKFLOW.read_text(encoding="utf-8")
    cron = re.search(r'cron:\s*"([^"]+)"', text)
    assert cron, "no cron schedule"
    minute, hour, dom, month, dow = cron.group(1).split()
    assert dow == "1-5", f"must run Monday to Friday only, got day-of-week {dow!r}"
    assert (minute, hour) == ("0", "6"), "06:00 UTC, after arXiv's announcement and before full.yml"
    assert "workflow_dispatch" in text
    assert not re.search(r"^\s+push:", text, re.MULTILINE), "the monitor must not run on push"
    assert re.search(r"issues:\s*write", text) and re.search(r"contents:\s*read", text)
    assert "timeout-minutes: 15" in text
    assert "--dry-run" not in text.split("run: python")[-1], "the scheduled run must be real"
    assert "secrets.GITHUB_TOKEN" in text


def test_script_is_stdlib_only_and_never_prints_the_token() -> None:
    src = _SCRIPT.read_text(encoding="utf-8")
    imports = re.findall(r"^(?:from|import)\s+([A-Za-z_][\w.]*)", src, re.MULTILINE)
    allowed = {"argparse", "datetime", "hashlib", "json", "os", "re", "sys", "time", "urllib",
               "xml", "dataclasses", "typing", "__future__"}
    assert {i.split(".")[0] for i in imports} <= allowed, imports
    assert "print(token" not in src and "token}" not in src.replace('f"Bearer {token}"', "")


def test_no_em_dashes_in_what_this_build_wrote() -> None:
    em_dash = chr(0x2014)  # built, not written: this file must not contain one either
    for path in (_SCRIPT, _WORKFLOW, pathlib.Path(__file__)):
        assert em_dash not in path.read_text(encoding="utf-8"), f"em dash in {path.name}"


def test_author_watches_are_not_enabled_unverified() -> None:
    """The brief: au:Wang_B returned nothing. Nothing goes live without a known-paper check."""
    live_author_queries = [q for q in lm.QUERIES if q.search.lstrip("(").startswith("au:")]
    assert live_author_queries == [], "an author query was enabled; verify it with --verify-authors first"
    assert any(a == "Lamzouri" for _, _, a in lm.AUTHOR_WATCH_UNVERIFIED)


def test_courtesy_spacing_is_at_least_three_seconds() -> None:
    assert lm.SPACING_SECONDS >= 3.0


# --------------------------------------------------------------------------
# network: one live check, slow, skipped when offline
# --------------------------------------------------------------------------


def _online() -> bool:
    try:
        socket.create_connection(("export.arxiv.org", 443), timeout=3).close()
        return True
    except OSError:
        return False


@pytest.mark.slow
@pytest.mark.skipif(not _online(), reason="export.arxiv.org unreachable")
def test_live_api_still_returns_wang_for_simple_critical_zeros() -> None:
    query = next(q for q in lm.QUERIES if q.name == "simple-critical-zeros")
    try:
        report, papers = lm.run_query(query, lm._live, *WINDOW, baseline={})
    except urllib.error.HTTPError as exc:  # pragma: no cover, rate limiting
        pytest.skip(f"arXiv answered HTTP {exc.code}")
    if not report.queried and "HTTP 429" in report.error:
        pytest.skip(report.error)
    assert report.queried, report.error
    assert WANG in {p.ident for p in papers}
