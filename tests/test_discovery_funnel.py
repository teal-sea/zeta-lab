"""Tests for discovery.registry / ledger / funnel / metrics — the pipeline.

What is pinned here, in the order the design's claims are made:

1. **The seam holds.** The four modules import nothing from the laboratory
   package (AST scan), pull nothing into ``sys.modules`` when imported in a
   clean interpreter, keep working when the laboratory package is made
   *unimportable*, and contain no subject-matter vocabulary (lexical scan).
2. **The plug-in interface is a decision procedure**, not a docstring: a screen
   that stops a candidate without an earned terminal verdict is refused, and so
   is a domain that names a check no plug-in performs.
3. **Every candidate that enters leaves.** Count in equals count out, over a
   domain built to exercise all seven dispositions; the guard that enforces it
   is exercised directly in both directions.
4. **Deduplication is against the whole ledger**, not the run — and an
   interrupted run resumes rather than duplicating or stranding.
5. **The metrics arithmetic is verified by hand** on a synthetic ledger whose
   every count and rate is written out in the test, and every empty denominator
   gives ``None`` rather than a fabricated zero.
"""

from __future__ import annotations

import ast
import json
import re
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from discovery import funnel as F  # noqa: E402
from discovery import ledger as L  # noqa: E402
from discovery import metrics as M  # noqa: E402
from discovery import registry as R  # noqa: E402
from discovery import schema as S  # noqa: E402
from discovery.ledger import Ledger, LedgerView  # noqa: E402
from discovery.registry import (  # noqa: E402
    BaseGenerator,
    BaseKnownnessDetector,
    BaseScreen,
    Domain,
    DomainError,
    ScreenResult,
)
from discovery.schema import (  # noqa: E402
    Candidate,
    CandidateKind,
    Precision,
    Provenance,
    Verdict,
    VerdictStatus,
)

_NOW = "2026-07-01T10:00:00+00:00"


# ---------------------------------------------------------------------------
# fixtures: a small, entirely fictitious domain
# ---------------------------------------------------------------------------


def _prov(generator: str = "gen", version: str = "1", dps: int = 20) -> Provenance:
    """A valid provenance built without shelling out to git (tests are hot)."""
    return Provenance(
        generator=generator,
        generator_version=version,
        lab_object="fictitious.object",
        parameters={"n": 3},
        precision=Precision("dps", dps),
        code_revision=None,
        code_dirty=None,
        code_revision_source="unavailable",
        captured_at=_NOW,
        runtime={"python": "3.13"},
        duration_s=0.0,
    )


def _constant(subject: str, value: float = 1.5, generator: str = "gen", dps: int = 20):
    return Candidate(
        kind=CandidateKind.CONSTANT,
        claim={"subject": subject, "value": value},
        evidence={"uncertainty": 1e-12},
        provenance=_prov(generator, dps=dps),
    )


def _verdict(status: VerdictStatus, **evidence) -> Verdict:
    return Verdict(
        status=status,
        decided_by="test",
        decided_by_version="1",
        decided_at=_NOW,
        evidence=evidence,
    )


_KNOWN = dict(references=["ID:1"], match_kind="statement")
_TRIVIAL = dict(derived_from=["fact A"], argument="one line", checked_by="proc")
_REFUTED = dict(
    witness={"n": 7},
    defect=3.0,
    tolerance=1e-3,
    effort=20.0,
    escalated_effort=40.0,
    escalated_defect=3.0,
)


class ListGenerator(BaseGenerator):
    """Yields a fixed list of candidates."""

    def __init__(self, name: str, items, version: str = "1") -> None:
        self.name = name
        self.version = version
        self._items = list(items)

    def generate(self, context):
        yield from self._items


class EmptyGenerator(BaseGenerator):
    """Runs, and finds nothing. The commonest outcome, and it must be logged."""

    name = "empty"
    version = "1"

    def generate(self, context):
        return iter(())


class BrokenGenerator(BaseGenerator):
    """Raises. A broken lead source must not take the run down with it."""

    name = "broken"
    version = "1"

    def generate(self, context):
        raise RuntimeError("the instrument is unplugged")
        yield  # pragma: no cover


class Catalogue(BaseKnownnessDetector):
    """Says 'already known' for the subjects it was handed."""

    version = "1"

    def __init__(self, subjects, name: str = "catalogue") -> None:
        self.name = name
        self._subjects = set(subjects)

    def check(self, candidate):
        if candidate.claim.get("subject") in self._subjects:
            return _verdict(VerdictStatus.KNOWN, **_KNOWN)
        return None


class Killer(BaseScreen):
    """Kills the subjects it was handed, with the status it was given."""

    def __init__(self, name, cost, checks, subjects, status, evidence, effort=None):
        self.name = name
        self.cost = cost
        self.checks = tuple(checks)
        self._subjects = set(subjects)
        self._status = status
        self._evidence = evidence
        self._effort = effort

    def apply(self, candidate):
        if candidate.claim.get("subject") in self._subjects:
            return ScreenResult(
                self.name,
                False,
                _verdict(self._status, **self._evidence),
                detail="killed",
                effort=self._effort,
            )
        return ScreenResult(self.name, True, effort=self._effort)


def _full_domain(items, *, verified_effort: float | None = 40.0) -> Domain:
    """A domain that can send a candidate to every one of the seven exits."""
    return Domain(
        name="fictitious",
        version="1",
        description="a domain about nothing at all",
        generators=(ListGenerator("gen", items), EmptyGenerator()),
        screens=(
            Killer("cheap-triv", "cheap", ("trivial",), {"t"}, VerdictStatus.TRIVIAL, _TRIVIAL),
            Killer(
                "deep-refute",
                "expensive",
                ("refutation",),
                {"r"},
                VerdictStatus.REFUTED,
                _REFUTED,
                effort=verified_effort,
            ),
        ),
        detectors=(Catalogue({"k"}),),
    )


# ---------------------------------------------------------------------------
# 1. the seam: these modules know nothing about the laboratory
# ---------------------------------------------------------------------------

_DOMAIN_AGNOSTIC_FILES = ("registry.py", "ledger.py", "funnel.py", "metrics.py")
_FORBIDDEN_ROOTS = ("zeta", "numpy", "scipy", "mpmath", "sympy", "matplotlib", "flint")
_BLOCKLIST = (
    "zeta",
    "riemann",
    "zeros",
    "primes",
    "l-function",
    "dirichlet",
    "hardy",
    "mertens",
    "jensen",
    "gue",
    "epstein",
    "critical line",
    "hypothesis",
    "mpmath",
)


def _discovery_dir() -> Path:
    return Path(S.__file__).resolve().parent


@pytest.mark.parametrize("filename", _DOMAIN_AGNOSTIC_FILES)
def test_pipeline_modules_import_nothing_from_the_laboratory(filename) -> None:
    tree = ast.parse((_discovery_dir() / filename).read_text(encoding="utf-8"))
    imported: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            imported.append(node.module)
    for name in imported:
        assert name.split(".")[0] not in _FORBIDDEN_ROOTS, f"{filename} imports {name}"


@pytest.mark.parametrize("filename", _DOMAIN_AGNOSTIC_FILES)
def test_pipeline_modules_contain_no_subject_matter_vocabulary(filename) -> None:
    """A leaked seam is usually a leaked *word* first."""
    source = (_discovery_dir() / filename).read_text(encoding="utf-8").lower()
    found = [w for w in _BLOCKLIST if re.search(rf"\b{re.escape(w)}\b", source)]
    assert not found, f"{filename} mentions {found}"


def test_importing_the_pipeline_pulls_in_no_laboratory_module() -> None:
    code = (
        "import sys; sys.path.insert(0, %r);"
        "import discovery.funnel, discovery.metrics, discovery.registry, discovery.ledger;"
        "bad=[m for m in sys.modules if m.split('.')[0] in %r];"
        "print(','.join(sorted(bad)))" % (str(_REPO_ROOT), _FORBIDDEN_ROOTS)
    )
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, timeout=120
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "", f"the pipeline dragged in: {result.stdout.strip()}"


def test_importing_the_package_front_door_pulls_in_no_laboratory_module() -> None:
    """``import discovery`` is what a reader actually types, and it must be as
    clean as importing the four modules by hand."""
    code = (
        "import sys; sys.path.insert(0, %r); import discovery;"
        "bad=[m for m in sys.modules if m.split('.')[0] in %r];"
        "print(','.join(sorted(bad)))" % (str(_REPO_ROOT), _FORBIDDEN_ROOTS)
    )
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, timeout=120
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "", f"discovery dragged in: {result.stdout.strip()}"


def test_the_pipeline_runs_with_the_laboratory_package_unimportable(tmp_path) -> None:
    """Not merely 'does not import it': it must work when it *cannot* be imported.

    A meta-path finder refuses every laboratory module, and a whole funnel run
    plus a metrics report is executed behind it.
    """
    script = textwrap.dedent(
        f"""
        import sys
        sys.path.insert(0, {str(_REPO_ROOT)!r})

        BANNED = {_FORBIDDEN_ROOTS!r}

        class Wall:
            def find_module(self, name, path=None):
                return self.find_spec(name, path)
            def find_spec(self, name, path=None, target=None):
                if name.split('.')[0] in BANNED:
                    raise ImportError("the laboratory package is walled off: " + name)
                return None

        sys.meta_path.insert(0, Wall())
        try:
            import zeta
        except ImportError:
            pass
        else:
            raise AssertionError("the wall does not work")

        sys.path.insert(0, {str(Path(__file__).resolve().parent)!r})
        from test_discovery_funnel import _full_domain, _constant
        from discovery.funnel import run_funnel
        from discovery.ledger import Ledger
        from discovery.metrics import render_text

        led = Ledger({str(tmp_path / "walled.jsonl")!r})
        run = run_funnel(_full_domain([_constant("k"), _constant("t"), _constant("s")]),
                         ledger=led)
        assert run.generated == 3, run.generated
        text = render_text(led)
        assert "FUNNEL" in text
        print("OK", sorted(run.dispositions().items()))
        """
    )
    result = subprocess.run(
        [sys.executable, "-c", script], capture_output=True, text=True, timeout=180
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.startswith("OK"), result.stdout


# ---------------------------------------------------------------------------
# 2. the registry: the plug-in interface is enforced
# ---------------------------------------------------------------------------


def test_a_passing_screen_may_not_carry_a_verdict() -> None:
    result = ScreenResult("s", True, _verdict(VerdictStatus.KNOWN, **_KNOWN))
    assert any("decided nothing" in r for r in result.reasons())


def test_a_stopping_screen_must_supply_a_verdict() -> None:
    assert any("must supply a verdict" in r for r in ScreenResult("s", False).reasons())


def test_a_screen_may_not_stop_a_candidate_with_a_non_terminal_verdict() -> None:
    result = ScreenResult("s", False, Verdict())
    assert any("terminal" in r for r in result.reasons())


def test_a_screen_may_not_stop_a_candidate_with_an_unearned_verdict() -> None:
    """The status must already earn itself under the schema's own rules."""
    bare = Verdict(
        status=VerdictStatus.SURVIVES,
        decided_by="s",
        decided_by_version="1",
        decided_at=_NOW,
        evidence={},
    )
    reasons = ScreenResult("s", False, bare).reasons()
    assert any("checks_run" in r for r in reasons)
    with pytest.raises(DomainError):
        ScreenResult("s", False, bare).validate()


@pytest.mark.parametrize("effort", [0.0, -1.0, float("inf")])
def test_screen_effort_must_be_a_positive_finite_number(effort) -> None:
    assert ScreenResult("s", True, effort=effort).reasons()


def test_a_well_formed_result_has_no_reasons() -> None:
    assert ScreenResult("s", True, effort=30.0).reasons() == ()
    stop = ScreenResult("s", False, _verdict(VerdictStatus.TRIVIAL, **_TRIVIAL))
    assert stop.reasons() == ()
    stop.validate()


def test_a_domain_with_no_generator_produces_nothing_and_is_refused() -> None:
    reasons = R.domain_reasons(Domain(name="d", version="1"))
    assert any("no generator" in r for r in reasons)


def test_a_screen_may_not_claim_a_check_outside_the_schema_vocabulary() -> None:
    bad = Killer("s", "cheap", ("vibes",), set(), VerdictStatus.TRIVIAL, _TRIVIAL)
    domain = Domain(name="d", version="1", generators=(EmptyGenerator(),), screens=(bad,))
    assert any("unknown check" in r for r in R.domain_reasons(domain))


def test_a_screen_must_declare_a_known_cost() -> None:
    bad = Killer("s", "moderate", (), set(), VerdictStatus.TRIVIAL, _TRIVIAL)
    domain = Domain(name="d", version="1", generators=(EmptyGenerator(),), screens=(bad,))
    assert any("cost must be one of" in r for r in R.domain_reasons(domain))


def test_plug_in_names_must_be_unique_because_rates_are_per_name() -> None:
    domain = Domain(
        name="d",
        version="1",
        generators=(ListGenerator("same", []), ListGenerator("same", [])),
    )
    assert any("must be unique" in r for r in R.domain_reasons(domain))


def test_domain_queries_and_missing_checks() -> None:
    domain = _full_domain([])
    assert [s.name for s in domain.cheap_screens()] == ["cheap-triv"]
    assert [s.name for s in domain.expensive_screens()] == ["deep-refute"]
    assert domain.checks_available() == frozenset({"known", "trivial", "refutation"})
    assert domain.missing_checks() == ()
    assert domain.generator("gen").name == "gen"
    with pytest.raises(DomainError):
        domain.generator("absent")
    with pytest.raises(DomainError):
        domain.screens_by_cost("free")
    assert "fictitious" in domain.describe()


def test_a_domain_missing_a_check_says_so_in_its_description() -> None:
    domain = Domain(name="d", version="1", generators=(EmptyGenerator(),))
    assert domain.missing_checks() == S.REQUIRED_SURVIVAL_CHECKS
    assert "cannot produce a survivor" in domain.describe()


def test_the_registry_refuses_to_overwrite_silently() -> None:
    R.clear_registry()
    try:
        domain = _full_domain([])
        R.register_domain(domain)
        assert R.list_domains() == ("fictitious",)
        assert R.get_domain("fictitious") is domain
        with pytest.raises(DomainError, match="already registered"):
            R.register_domain(domain)
        R.register_domain(domain, replace=True)
        with pytest.raises(DomainError, match="no domain"):
            R.get_domain("absent")
        R.unregister_domain("fictitious")
        R.unregister_domain("fictitious")  # idempotent
        assert R.list_domains() == ()
    finally:
        R.clear_registry()


def test_run_funnel_accepts_a_registered_domain_by_name(tmp_path) -> None:
    R.clear_registry()
    try:
        R.register_domain(_full_domain([_constant("k")]))
        run = F.run_funnel("fictitious", ledger=tmp_path / "l.jsonl")
        assert run.domain == "fictitious"
        assert run.dispositions()["known"] == 1
    finally:
        R.clear_registry()


# ---------------------------------------------------------------------------
# 3. the ledger
# ---------------------------------------------------------------------------


def test_the_default_ledger_is_private_and_derived_from_the_module_location() -> None:
    assert L.DEFAULT_LEDGER_PATH.parent.name == "conjectures"
    assert L.DEFAULT_LEDGER_PATH.parent.parent == _REPO_ROOT
    ignore = (_REPO_ROOT / ".gitignore").read_text(encoding="utf-8")
    assert "conjectures/*" in ignore, "the ledger must never be committed"
    readme = (_REPO_ROOT / "discovery" / "README.md").read_text(encoding="utf-8")
    assert "conjectures/" in readme and "gitignore" in readme.lower()


def test_the_default_ledger_path_can_be_overridden_by_environment(monkeypatch, tmp_path) -> None:
    monkeypatch.setenv(L.LEDGER_ENV_VAR, str(tmp_path / "elsewhere.jsonl"))
    assert L.default_ledger_path() == tmp_path / "elsewhere.jsonl"
    assert Ledger().path == tmp_path / "elsewhere.jsonl"


def test_runs_path_sits_beside_the_candidate_log() -> None:
    assert L.runs_path_for("/x/ledger.jsonl").name == "ledger.runs.jsonl"


def test_a_missing_ledger_reads_as_empty_not_as_an_error(tmp_path) -> None:
    led = Ledger(tmp_path / "nothing.jsonl")
    assert led.candidates() == ()
    assert led.runs() == ()
    assert led.latest() == {}
    assert led.size() == 0
    assert led.view().is_empty()


def test_append_read_round_trip_and_last_write_wins(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    candidate = _constant("a")
    led.append(candidate)
    led.append(candidate.with_verdict(_verdict(VerdictStatus.KNOWN, **_KNOWN)))
    assert led.size() == 2
    assert len(led.latest()) == 1
    assert led.latest()[candidate.id].verdict.status is VerdictStatus.KNOWN
    assert led.contains(candidate.id)
    assert led.get("cand-nope") is None
    assert led.ids() == frozenset({candidate.id})


def test_ledger_query_filters_are_conjunctive(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    led.append(_constant("a", generator="g1"))
    led.append(_constant("b", generator="g2").with_verdict(_verdict(VerdictStatus.KNOWN, **_KNOWN)))
    assert len(led.query()) == 2
    assert len(led.query(generator="g1")) == 1
    assert len(led.query(status="known")) == 1
    assert len(led.query(status=["known", "open"])) == 2
    assert len(led.query(kind="constant", generator="g2", status="known")) == 1
    assert led.query(kind="relation") == ()
    assert len(led.query(since="2026-01-01")) == 2
    assert led.query(since="2027-01-01") == ()
    assert led.query(until="2020-01-01") == ()


def test_unresolved_reports_candidates_a_dead_run_left_open(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    open_one = _constant("a")
    led.append(open_one)
    led.append(_constant("b").with_verdict(_verdict(VerdictStatus.KNOWN, **_KNOWN)))
    assert [c.id for c in led.unresolved()] == [open_one.id]


def test_compaction_keeps_only_the_current_state(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    candidate = _constant("a")
    led.append(candidate)
    led.append(candidate.with_verdict(_verdict(VerdictStatus.KNOWN, **_KNOWN)))
    led.append(_constant("b"))
    assert led.size() == 3
    assert led.compact() == 2
    assert led.size() == 2
    assert led.latest()[candidate.id].verdict.status is VerdictStatus.KNOWN


def test_a_corrupted_ledger_line_is_refused_not_silently_skipped(tmp_path) -> None:
    path = tmp_path / "l.jsonl"
    led = Ledger(path)
    led.append(_constant("a"))
    with path.open("a", encoding="utf-8") as handle:
        handle.write("{not json}\n")
    with pytest.raises(L.LedgerError, match="line 2"):
        led.candidates()


def test_a_run_record_needs_a_run_id_and_must_be_json_safe(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    with pytest.raises(L.LedgerError, match="run_id"):
        led.append_run({"domain": "d"})
    with pytest.raises(L.LedgerError, match="JSON-safe"):
        led.append_run({"run_id": "r", "x": float("inf")})
    led.append_run({"run_id": "r", "state": "started"})
    assert led.runs()[0]["record"] == L.RUN_RECORD_TYPE


def test_foreign_lines_in_the_run_stream_are_ignored(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    led.runs_path.parent.mkdir(parents=True, exist_ok=True)
    led.runs_path.write_text(
        json.dumps({"record": "something_else"}) + "\n"
        + json.dumps({"record": "funnel_run", "run_id": "r"}) + "\n",
        encoding="utf-8",
    )
    assert [r["run_id"] for r in led.runs()] == ["r"]


def test_latest_runs_collapses_started_then_finished(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    led.append_run({"run_id": "r", "state": "started"})
    led.append_run({"run_id": "r", "state": "finished"})
    led.append_run({"run_id": "s", "state": "started"})
    latest = led.view().latest_runs()
    assert {r["run_id"]: r["state"] for r in latest} == {"r": "finished", "s": "started"}


def test_concurrent_appends_from_separate_processes_never_tear_a_line(tmp_path) -> None:
    """Four processes, twenty appends each: eighty whole, valid lines."""
    path = tmp_path / "shared.jsonl"
    script = tmp_path / "writer.py"
    script.write_text(
        textwrap.dedent(
            f"""
            import sys
            sys.path.insert(0, {str(_REPO_ROOT)!r})
            sys.path.insert(0, {str(Path(__file__).resolve().parent)!r})
            from test_discovery_funnel import _constant
            from discovery.ledger import Ledger
            led = Ledger(sys.argv[1])
            tag = sys.argv[2]
            for i in range(20):
                led.append(_constant(f"{{tag}}-{{i}}"))
            """
        ),
        encoding="utf-8",
    )
    procs = [
        subprocess.Popen(
            [sys.executable, str(script), str(path), f"w{w}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        for w in range(4)
    ]
    for proc in procs:
        _out, err = proc.communicate(timeout=180)
        assert proc.returncode == 0, err.decode()
    lines = [ln for ln in path.read_text(encoding="utf-8").splitlines() if ln.strip()]
    assert len(lines) == 80
    for line in lines:
        json.loads(line)  # every line is whole and parseable
    assert len(Ledger(path).latest()) == 80


# ---------------------------------------------------------------------------
# 4. the funnel
# ---------------------------------------------------------------------------


def test_every_candidate_that_enters_leaves_with_a_terminal_disposition(tmp_path) -> None:
    """The invariant, over a run that exercises six of the seven exits.

    ``inconclusive`` is the seventh and cannot be reached by a domain that can
    decide everything; it is pinned separately (see the stage-omission, missing
    check and insufficient-effort tests below).
    """
    duplicate_already_there = _constant("d")
    led = Ledger(tmp_path / "l.jsonl")
    led.append(duplicate_already_there.with_verdict(_verdict(VerdictStatus.KNOWN, **_KNOWN)))

    invalid = Candidate(  # value 0.0 is a relation q = 0, not a constant
        kind=CandidateKind.CONSTANT,
        claim={"subject": "bad", "value": 0.0},
        evidence={"uncertainty": 1e-9},
        provenance=_prov(),
    )
    items = [
        _constant("k"),  # known, at the gate
        _constant("t"),  # trivial, cheap screen
        _constant("r"),  # refuted, expensive screen
        _constant("s"),  # survives
        duplicate_already_there,  # duplicate, against the ledger
        _constant("s"),  # duplicate, within the run
        invalid,  # invalid
    ]
    run = F.run_funnel(_full_domain(items), ledger=led)

    assert run.generated == len(items)
    assert len(run.outcomes) == len(items), "count in must equal count out"
    assert sum(run.dispositions().values()) == len(items)
    assert set(o.disposition for o in run.outcomes) <= set(F.DISPOSITIONS)
    assert run.dispositions() == {
        "duplicate": 2,
        "invalid": 1,
        "known": 1,
        "trivial": 1,
        "refuted": 1,
        "survives": 1,
        "inconclusive": 0,
    }
    # and each left at the stage the design says it should
    by_subject = {o.candidate_id: o for o in run.outcomes}
    assert by_subject[_constant("k").id].stage == "knownness"
    assert by_subject[_constant("t").id].stage == "cheap_screens"
    assert by_subject[_constant("r").id].stage == "expensive_screens"
    assert by_subject[_constant("s").id].stage in {"terminal", "deduplicate"}


def test_the_conservation_guard_fires_in_both_directions() -> None:
    good = F.Outcome("cand-1", "g", "1", "constant", "terminal", "survives")
    F._check_conservation(1, [good])
    with pytest.raises(F.FunnelError, match="dropped observations"):
        F._check_conservation(2, [good])
    bogus = F.Outcome("cand-1", "g", "1", "constant", "terminal", "interesting")
    with pytest.raises(F.FunnelError, match="outside the vocabulary"):
        F._check_conservation(1, [bogus])


def test_stage_tallies_conserve_candidates(tmp_path) -> None:
    items = [_constant("k"), _constant("t"), _constant("r"), _constant("s")]
    run = F.run_funnel(_full_domain(items), ledger=tmp_path / "l.jsonl")
    remaining = run.generated
    for tally in run.stage_tallies:
        if tally.entered:
            assert tally.entered == remaining
            remaining = tally.passed
    assert remaining == 0, "everything must have left by the end"


def test_a_broken_generator_is_visible_as_broken_in_the_report(tmp_path) -> None:
    """"Found nothing" and "raised" must not hide inside one another."""
    domain = Domain(
        name="d",
        version="1",
        generators=(BrokenGenerator(), EmptyGenerator()),
        detectors=(Catalogue({"k"}),),
    )
    led = Ledger(tmp_path / "l.jsonl")
    F.run_funnel(domain, ledger=led)
    report = M.funnel_report(led)
    assert report.invocations == 2
    assert report.zero_yield_invocations == 2
    assert report.errored_invocations == 1
    assert "1 raised" in report.render_text()


def test_a_broken_generator_is_recorded_and_does_not_kill_the_run(tmp_path) -> None:
    domain = Domain(
        name="d",
        version="1",
        generators=(BrokenGenerator(), ListGenerator("gen", [_constant("k")])),
        detectors=(Catalogue({"k"}),),
    )
    run = F.run_funnel(domain, ledger=tmp_path / "l.jsonl")
    reports = {g.generator: g for g in run.generators}
    assert reports["broken"].produced == 0
    assert "RuntimeError" in reports["broken"].error
    assert reports["broken"].zero_yield
    assert run.dispositions()["known"] == 1
    assert any("broken" in e for e in run.errors)


def test_a_generator_that_yields_nothing_is_still_an_invocation(tmp_path) -> None:
    run = F.run_funnel(_full_domain([]), ledger=tmp_path / "l.jsonl")
    assert run.generated == 0
    assert [g.produced for g in run.generators] == [0, 0]
    assert all(g.zero_yield for g in run.generators)
    report = M.funnel_report(Ledger(tmp_path / "l.jsonl"))
    assert report.invocations == 2 and report.zero_yield_invocations == 2
    assert report.zero_yield_rate == 1.0
    assert report.candidates_per_invocation == 0.0


def test_a_generator_may_not_decide_its_own_candidate(tmp_path) -> None:
    pre_decided = _constant("x").with_verdict(_verdict(VerdictStatus.SURVIVES, **{
        "checks_run": list(S.REQUIRED_SURVIVAL_CHECKS),
        "effort": 1.0,
        "verified_effort": 2.0,
        "proof_gap": "everything",
    }))
    run = F.run_funnel(_full_domain([pre_decided]), ledger=tmp_path / "l.jsonl")
    assert run.dispositions()["invalid"] == 1
    assert "may not decide its own candidate" in run.outcomes[0].detail


def test_an_invalid_candidate_is_counted_but_never_written(tmp_path) -> None:
    invalid = Candidate(
        kind=CandidateKind.CONSTANT,
        claim={"subject": "bad", "value": 0.0},
        evidence={"uncertainty": 1e-9},
        provenance=_prov(),
    )
    led = Ledger(tmp_path / "l.jsonl")
    run = F.run_funnel(_full_domain([invalid]), ledger=led)
    assert run.dispositions()["invalid"] == 1
    assert led.candidates() == ()
    assert run.outcomes[0].stage == "generate"


def test_deduplication_is_against_the_whole_ledger_not_just_this_run(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    items = [_constant("k"), _constant("t"), _constant("s")]
    first = F.run_funnel(_full_domain(items), ledger=led)
    assert first.dispositions()["duplicate"] == 0
    size_after_first = led.size()

    second = F.run_funnel(_full_domain(items), ledger=led)
    assert second.dispositions()["duplicate"] == 3
    assert second.written == 0
    assert led.size() == size_after_first, "a repeat run must add no candidate record"
    assert len(led.latest()) == 3


def test_two_generators_finding_the_same_claim_collide_within_one_run(tmp_path) -> None:
    """The collision is the measurement: generator B found nothing A had not."""
    shared = _constant("s")
    domain = Domain(
        name="d",
        version="1",
        generators=(ListGenerator("a", [shared]), ListGenerator("b", [_constant("s")])),
        detectors=(Catalogue(set()),),
    )
    run = F.run_funnel(domain, ledger=tmp_path / "l.jsonl")
    assert run.dispositions()["duplicate"] == 1
    dup = [o for o in run.outcomes if o.disposition == "duplicate"][0]
    assert dup.generator == "b" and "already emitted this run by a" in dup.detail


def test_an_interrupted_run_resumes_without_duplicating_ledger_entries(tmp_path) -> None:
    """Crash after the second checkpoint; re-run; nothing lost, nothing doubled."""

    class Bomb(BaseScreen):
        """Passes once, then explodes — a mid-run death."""

        name = "bomb"
        cost = "cheap"
        checks = ("trivial", "refutation")

        def __init__(self) -> None:
            self.calls = 0

        def apply(self, candidate):
            self.calls += 1
            if self.calls > 1:
                raise RuntimeError("the process died here")
            return ScreenResult(self.name, True, effort=40.0)

    items = [_constant("a"), _constant("b"), _constant("c")]
    led = Ledger(tmp_path / "l.jsonl")
    dying = Domain(
        name="d",
        version="1",
        generators=(ListGenerator("gen", items),),
        screens=(Bomb(),),
        detectors=(Catalogue(set()),),
    )
    with pytest.raises(RuntimeError, match="died here"):
        F.run_funnel(dying, ledger=led)

    # one candidate decided, one checkpointed and stranded, one never reached
    assert len(led.unresolved()) == 1
    stranded = led.unresolved()[0].id
    size_after_crash = led.size()

    healthy = Domain(
        name="d",
        version="1",
        generators=(ListGenerator("gen", items),),
        screens=(
            Killer("ok", "cheap", ("trivial", "refutation"), set(), VerdictStatus.TRIVIAL,
                   _TRIVIAL, effort=40.0),
        ),
        detectors=(Catalogue(set()),),
    )
    resumed = F.run_funnel(healthy, ledger=led)
    assert resumed.resumed == 1
    assert [o.resumed for o in resumed.outcomes if o.candidate_id == stranded] == [True]
    assert resumed.dispositions()["duplicate"] == 1  # the one already decided
    assert led.unresolved() == (), "resuming must leave nothing open"
    assert len(led.latest()) == 3

    # and a third run adds no candidate records at all
    before = led.size()
    third = F.run_funnel(healthy, ledger=led)
    assert third.dispositions()["duplicate"] == 3
    assert led.size() == before
    assert size_after_crash < before  # the resume did write the missing verdicts

    # the crashed run is still visible in the denominator
    report = M.funnel_report(led)
    assert report.runs == 3 and report.runs_incomplete == 1


def test_checkpointing_can_be_switched_off(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    F.run_funnel(_full_domain([_constant("k")]), ledger=led, checkpoint=False)
    assert led.size() == 1  # the terminal record only


def test_dry_run_writes_nothing_at_all(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    items = [_constant("k"), _constant("t"), _constant("s")]
    run = F.run_funnel(_full_domain(items), ledger=led, dry_run=True)
    assert run.dry_run
    assert run.generated == 3
    assert run.dispositions()["known"] == 1
    assert run.written == 0
    assert not led.path.exists() and not led.runs_path.exists()
    assert M.funnel_report(led).runs == 0


def test_dry_run_still_deduplicates_against_the_existing_ledger(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    F.run_funnel(_full_domain([_constant("k")]), ledger=led)
    dry = F.run_funnel(_full_domain([_constant("k")]), ledger=led, dry_run=True)
    assert dry.dispositions()["duplicate"] == 1


def test_limit_bounds_generation_and_says_that_it_did(tmp_path) -> None:
    items = [_constant(f"s{i}") for i in range(5)]
    domain = Domain(
        name="d",
        version="1",
        generators=(ListGenerator("first", items), ListGenerator("second", items)),
        detectors=(Catalogue(set()),),
    )
    run = F.run_funnel(domain, limit=2, ledger=tmp_path / "l.jsonl")
    assert run.generated == 2
    assert run.limit_reached
    reports = {g.generator: g for g in run.generators}
    assert reports["first"].produced == 2
    assert reports["second"].skipped and not reports["second"].zero_yield
    with pytest.raises(F.FunnelError, match="limit"):
        F.run_funnel(domain, limit=-1, ledger=tmp_path / "l.jsonl")


def test_omitting_stages_yields_inconclusive_not_a_free_promotion(tmp_path) -> None:
    run = F.run_funnel(
        _full_domain([_constant("s")]),
        stages=("generate", "deduplicate"),
        ledger=tmp_path / "l.jsonl",
    )
    assert run.dispositions()["inconclusive"] == 1
    led = Ledger(tmp_path / "l.jsonl")
    verdict = list(led.latest().values())[0].verdict
    assert verdict.evidence["reason"] == "budget_exhausted"
    assert "stages_skipped" in verdict.evidence["ceiling"]


@pytest.mark.parametrize("stages", [("deduplicate",), ()])
def test_generate_may_not_be_omitted(stages, tmp_path) -> None:
    with pytest.raises(F.FunnelError):
        F.run_funnel(_full_domain([]), stages=stages, ledger=tmp_path / "l.jsonl")


def test_unknown_stage_names_are_refused(tmp_path) -> None:
    with pytest.raises(F.FunnelError, match="unknown stages"):
        F.run_funnel(_full_domain([]), stages=("generate", "magic"), ledger=tmp_path / "l.jsonl")


def test_a_domain_that_cannot_run_a_check_cannot_produce_a_survivor(tmp_path) -> None:
    """The generalisation of 'you may not survive a check that never ran'."""
    domain = Domain(
        name="d",
        version="1",
        generators=(ListGenerator("gen", [_constant("s")]),),
        screens=(Killer("only", "expensive", ("refutation",), set(), VerdictStatus.TRIVIAL,
                        _TRIVIAL, effort=40.0),),
        detectors=(Catalogue(set()),),
    )
    assert domain.missing_checks() == ("trivial",)
    run = F.run_funnel(domain, ledger=tmp_path / "l.jsonl")
    assert run.dispositions()["inconclusive"] == 1
    verdict = list(Ledger(tmp_path / "l.jsonl").latest().values())[0].verdict
    assert verdict.evidence["reason"] == "dependency_unavailable"
    assert tuple(verdict.evidence["ceiling"]["checks_run"]) == ("known", "refutation")


def test_survival_requires_verification_to_have_cost_more_than_generation(tmp_path) -> None:
    # generated at 20 digits, "verified" at 20 digits: not an escalation
    run = F.run_funnel(
        _full_domain([_constant("s", dps=20)], verified_effort=20.0),
        ledger=tmp_path / "l.jsonl",
    )
    assert run.dispositions()["inconclusive"] == 1
    verdict = list(Ledger(tmp_path / "l.jsonl").latest().values())[0].verdict
    assert verdict.evidence["reason"] == "precision_insufficient"


def test_a_screen_reporting_no_effort_at_all_cannot_promote(tmp_path) -> None:
    run = F.run_funnel(
        _full_domain([_constant("s")], verified_effort=None), ledger=tmp_path / "l.jsonl"
    )
    assert run.dispositions()["inconclusive"] == 1


def test_a_survivor_carries_the_three_checks_and_a_proof_gap(tmp_path) -> None:
    F.run_funnel(_full_domain([_constant("s", dps=20)]), ledger=tmp_path / "l.jsonl")
    survivor = list(Ledger(tmp_path / "l.jsonl").latest().values())[0]
    assert survivor.verdict.status is VerdictStatus.SURVIVES
    evidence = survivor.verdict.evidence
    assert set(S.REQUIRED_SURVIVAL_CHECKS) <= set(evidence["checks_run"])
    assert evidence["effort"] == 20.0 and evidence["verified_effort"] == 40.0
    assert "lead" in evidence["proof_gap"] and "not a result" in evidence["proof_gap"]
    S.validate_verdict(survivor.verdict)


def test_an_exact_computation_cannot_be_escalated_and_is_recorded_inconclusive(tmp_path) -> None:
    """Schema friction, recorded rather than papered over.

    ``Precision('exact').effort_digits()`` is infinite, so no verification can
    cost strictly more, and ``survives`` is unreachable for an exact result.
    The funnel says so in the record instead of promoting anyway.
    """
    exact = Candidate(
        kind=CandidateKind.CONSTANT,
        claim={"subject": "s", "value": 1.5},
        evidence={"uncertainty": 1e-12},
        provenance=Provenance(
            generator="gen",
            generator_version="1",
            lab_object="fictitious.object",
            precision=Precision("exact"),
            captured_at=_NOW,
            code_revision_source="unavailable",
        ),
    )
    run = F.run_funnel(_full_domain([exact]), ledger=tmp_path / "l.jsonl")
    assert run.dispositions()["inconclusive"] == 1
    verdict = list(Ledger(tmp_path / "l.jsonl").latest().values())[0].verdict
    assert verdict.evidence["ceiling"]["effort"] == "exact"


def test_a_screen_returning_the_wrong_type_is_a_hard_error(tmp_path) -> None:
    class Wrong(BaseScreen):
        """Returns a bool."""

        name = "wrong"
        cost = "cheap"
        checks = ()

        def apply(self, candidate):
            return True

    domain = Domain(
        name="d", version="1",
        generators=(ListGenerator("gen", [_constant("s")]),),
        screens=(Wrong(),),
    )
    with pytest.raises(F.FunnelError, match="not a ScreenResult"):
        F.run_funnel(domain, ledger=tmp_path / "l.jsonl")


def test_a_detector_returning_a_non_terminal_verdict_is_a_hard_error(tmp_path) -> None:
    class Sloppy(BaseKnownnessDetector):
        """Returns 'open'."""

        name = "sloppy"
        version = "1"

        def check(self, candidate):
            return Verdict()

    domain = Domain(
        name="d", version="1",
        generators=(ListGenerator("gen", [_constant("s")]),),
        detectors=(Sloppy(),),
    )
    with pytest.raises(F.FunnelError, match="non-terminal"):
        F.run_funnel(domain, ledger=tmp_path / "l.jsonl")


def test_a_detector_returning_an_unearned_verdict_is_a_hard_error(tmp_path) -> None:
    class Sloppy(BaseKnownnessDetector):
        """Claims 'known' with no reference."""

        name = "sloppy"
        version = "1"

        def check(self, candidate):
            return _verdict(VerdictStatus.KNOWN)

    domain = Domain(
        name="d", version="1",
        generators=(ListGenerator("gen", [_constant("s")]),),
        detectors=(Sloppy(),),
    )
    with pytest.raises(F.FunnelError, match="unearned"):
        F.run_funnel(domain, ledger=tmp_path / "l.jsonl")


def test_a_generator_yielding_a_non_candidate_is_a_hard_error(tmp_path) -> None:
    domain = Domain(name="d", version="1", generators=(ListGenerator("gen", ["hello"]),))
    with pytest.raises(F.FunnelError, match="not a Candidate"):
        F.run_funnel(domain, ledger=tmp_path / "l.jsonl")


def test_only_reopenable_statuses_may_be_reopened(tmp_path) -> None:
    with pytest.raises(F.FunnelError, match="may be re-opened"):
        F.run_funnel(_full_domain([]), ledger=tmp_path / "l.jsonl", reopen=("known",))


def test_reopening_an_inconclusive_candidate_re_examines_it(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    # first pass: no escalation reported, so it lands inconclusive
    F.run_funnel(_full_domain([_constant("s")], verified_effort=None), ledger=led)
    assert list(led.latest().values())[0].verdict.status is VerdictStatus.INCONCLUSIVE
    # second pass, now with a real escalation and permission to re-open
    again = F.run_funnel(
        _full_domain([_constant("s")], verified_effort=40.0),
        ledger=led,
        reopen=("inconclusive",),
    )
    assert again.dispositions()["survives"] == 1
    assert list(led.latest().values())[0].verdict.status is VerdictStatus.SURVIVES
    # without permission it would simply be a duplicate
    third = F.run_funnel(_full_domain([_constant("s")]), ledger=led)
    assert third.dispositions()["duplicate"] == 1


def test_the_run_record_round_trips_and_renders(tmp_path) -> None:
    items = [_constant("k"), _constant("t"), _constant("r"), _constant("s")]
    run = F.run_funnel(_full_domain(items), ledger=tmp_path / "l.jsonl")
    again = F.FunnelRun.from_dict(json.loads(json.dumps(run.to_dict())))
    assert again.run_id == run.run_id
    assert again.dispositions() == run.dispositions()
    assert [t.to_dict() for t in again.stage_tallies] == [t.to_dict() for t in run.stage_tallies]
    assert [t.to_dict() for t in again.screen_tallies] == [
        t.to_dict() for t in run.screen_tallies
    ]
    text = run.render_text()
    assert run.run_id in text and "dispositions" in text
    assert run.stage_tally("nonexistent").entered == 0


def test_the_funnels_own_tallies_agree_with_the_metrics_derivation(tmp_path) -> None:
    """Two independent computations of the same flow must agree.

    The funnel counts stage entry as it goes; ``metrics`` re-derives it from
    the outcomes alone. If those two ever disagree the reports are fiction.
    """
    items = [_constant("k"), _constant("t"), _constant("r"), _constant("s")]
    led = Ledger(tmp_path / "l.jsonl")
    run = F.run_funnel(_full_domain(items), ledger=led)
    report = M.funnel_report(led)
    for tally in run.stage_tallies:
        stat = report.stage(tally.stage)
        assert (stat.entered, stat.left) == (tally.entered, tally.left), tally.stage


def test_the_ledger_path_recorded_in_a_run_is_never_machine_local(tmp_path) -> None:
    run = F.run_funnel(_full_domain([]), ledger=tmp_path / "l.jsonl")
    assert run.ledger_path == "l.jsonl"
    inside = F.run_funnel(_full_domain([]), ledger=_REPO_ROOT / "conjectures" / "t.jsonl",
                          dry_run=True)
    assert inside.ledger_path == "conjectures/t.jsonl"
    assert not re.search(r"(?:/Users/|/home/|[A-Za-z]:\\Users\\)", str(run.ledger_path))


# ---------------------------------------------------------------------------
# 5. the metrics — arithmetic verified by hand
# ---------------------------------------------------------------------------


def _outcome(cid, gen, stage, disposition, seconds, version="1"):
    return {
        "candidate_id": cid,
        "generator": gen,
        "generator_version": version,
        "kind": "constant",
        "stage": stage,
        "disposition": disposition,
        "seconds": seconds,
    }


def _synthetic_view() -> LedgerView:
    """A hand-built ledger. Every number below is asserted explicitly.

    Run A — 10 candidates from genA, genB ran and found nothing:
        1 invalid (generate), 2 duplicate (deduplicate), 3 known (knownness),
        1 trivial (cheap), 2 refuted (expensive), 1 survives (terminal).
    Run B — genA re-finds 4 (all duplicates), genC finds 2 (1 known, 1 inconclusive).
    Run C — started and never finished: a crashed run, still in the denominator.
    """
    run_a = {
        "record": "funnel_run",
        "run_id": "run-A",
        "state": "finished",
        "domain": "d",
        "domain_version": "1",
        "started_at": "2026-07-01T10:00:00+00:00",
        "seconds": 9.0,
        "stages": list(F.STAGES),
        "generators": [
            {"generator": "genA", "version": "1", "produced": 10, "seconds": 4.0},
            {"generator": "genB", "version": "1", "produced": 0, "seconds": 1.0},
        ],
        "outcomes": [
            _outcome("c0", "genA", "generate", "invalid", 0.5),
            _outcome("c1", "genA", "deduplicate", "duplicate", 0.5),
            _outcome("c2", "genA", "deduplicate", "duplicate", 0.5),
            _outcome("c3", "genA", "knownness", "known", 0.5),
            _outcome("c4", "genA", "knownness", "known", 0.5),
            _outcome("c5", "genA", "knownness", "known", 0.5),
            _outcome("c6", "genA", "cheap_screens", "trivial", 0.5),
            _outcome("c7", "genA", "expensive_screens", "refuted", 0.5),
            _outcome("c8", "genA", "expensive_screens", "refuted", 0.5),
            _outcome("c9", "genA", "terminal", "survives", 0.5),
        ],
        "stage_tallies": [
            {"stage": "generate", "entered": 10, "left": 1, "seconds": 5.0},
            {"stage": "deduplicate", "entered": 9, "left": 2, "seconds": 0.1},
            {"stage": "knownness", "entered": 7, "left": 3, "seconds": 0.7},
            {"stage": "cheap_screens", "entered": 4, "left": 1, "seconds": 0.4},
            {"stage": "expensive_screens", "entered": 3, "left": 2, "seconds": 3.0},
            {"stage": "terminal", "entered": 1, "left": 1, "seconds": 0.2},
        ],
        "screen_tallies": [
            {"screen": "cat", "cost": "detector", "calls": 7, "stopped": 3, "seconds": 0.7},
            {"screen": "triv", "cost": "cheap", "calls": 4, "stopped": 1, "seconds": 0.4},
            {"screen": "verify", "cost": "expensive", "calls": 3, "stopped": 2, "seconds": 3.0},
        ],
    }
    run_b = {
        "record": "funnel_run",
        "run_id": "run-B",
        "state": "finished",
        "domain": "d",
        "domain_version": "1",
        "started_at": "2026-07-01T12:00:00+00:00",
        "seconds": 6.0,
        "stages": list(F.STAGES),
        "generators": [
            {"generator": "genA", "version": "1", "produced": 4, "seconds": 2.0},
            {"generator": "genC", "version": "2", "produced": 2, "seconds": 3.0},
        ],
        "outcomes": [
            _outcome("c1", "genA", "deduplicate", "duplicate", 0.25),
            _outcome("c2", "genA", "deduplicate", "duplicate", 0.25),
            _outcome("c3", "genA", "deduplicate", "duplicate", 0.25),
            _outcome("c4", "genA", "deduplicate", "duplicate", 0.25),
            _outcome("d1", "genC", "knownness", "known", 0.25, version="2"),
            _outcome("d2", "genC", "terminal", "inconclusive", 0.25, version="2"),
        ],
        "stage_tallies": [
            {"stage": "generate", "entered": 6, "left": 0, "seconds": 5.0},
            {"stage": "deduplicate", "entered": 6, "left": 4, "seconds": 0.05},
            {"stage": "knownness", "entered": 2, "left": 1, "seconds": 0.2},
            {"stage": "cheap_screens", "entered": 1, "left": 0, "seconds": 0.1},
            {"stage": "expensive_screens", "entered": 1, "left": 0, "seconds": 1.0},
            {"stage": "terminal", "entered": 1, "left": 1, "seconds": 0.05},
        ],
        "screen_tallies": [
            {"screen": "cat", "cost": "detector", "calls": 2, "stopped": 1, "seconds": 0.2},
            {"screen": "triv", "cost": "cheap", "calls": 1, "stopped": 0, "seconds": 0.1},
            {"screen": "verify", "cost": "expensive", "calls": 1, "stopped": 0, "seconds": 1.0},
        ],
    }
    run_c_started = {
        "record": "funnel_run",
        "run_id": "run-C",
        "state": "started",
        "domain": "d",
        "domain_version": "1",
        "started_at": "2026-07-02T09:00:00+00:00",
        "stages": list(F.STAGES),
    }
    return LedgerView(runs=(run_a, run_b, run_c_started))


def test_funnel_report_arithmetic_is_exactly_what_was_put_in() -> None:
    report = M.funnel_report(_synthetic_view())

    assert (report.runs, report.runs_incomplete, report.dry_runs) == (3, 1, 0)
    assert report.invocations == 4  # genA twice, genB once, genC once
    assert report.zero_yield_invocations == 1  # genB
    assert report.zero_yield_rate == 1 / 4
    assert report.generated == 16  # 10 + 6
    assert report.candidates_per_invocation == 16 / 4

    assert report.dispositions == {
        "duplicate": 6,  # 2 in A, 4 in B
        "invalid": 1,
        "known": 4,  # 3 in A, 1 in B
        "trivial": 1,
        "refuted": 2,
        "survives": 1,
        "inconclusive": 1,
    }
    assert sum(report.dispositions.values()) == report.generated

    rates = report.rates
    assert rates["duplicate"] == 6 / 16 == 0.375
    assert rates["known"] == 4 / 16 == 0.25
    assert rates["refuted"] == 2 / 16 == 0.125
    assert rates["survives"] == 1 / 16 == 0.0625
    assert abs(sum(v for v in rates.values() if v is not None) - 1.0) < 1e-12
    assert report.survivors == 1 and report.survival_rate == 1 / 16
    assert report.seconds_per_survivor == 15.0 / 1

    # the flow, stage by stage: 16 in, 16 out
    expected = {
        "generate": (16, 1),
        "deduplicate": (15, 6),
        "knownness": (9, 4),
        "cheap_screens": (5, 1),
        "expensive_screens": (4, 2),
        "terminal": (2, 2),
    }
    for stage, (entered, left) in expected.items():
        stat = report.stage(stage)
        assert (stat.entered, stat.left) == (entered, left), stage
    assert report.stage("generate").pass_rate == 15 / 16
    assert report.stage("deduplicate").pass_rate == 9 / 15 == 0.6
    assert report.stage("knownness").pass_rate == 5 / 9
    assert report.stage("cheap_screens").pass_rate == 4 / 5 == 0.8
    assert report.stage("expensive_screens").pass_rate == 2 / 4 == 0.5
    assert report.stage("terminal").pass_rate == 0.0
    assert report.stage("terminal").kill_rate == 1.0
    assert sum(s.left for s in report.stages) == report.generated

    assert report.seconds == 15.0  # 9 + 6, the crashed run recorded none
    assert report.generation_seconds == 10.0  # 4 + 1 + 2 + 3
    assert report.screening_seconds == 10 * 0.5 + 6 * 0.25 == 6.5
    assert report.stage("expensive_screens").seconds == 3.0 + 1.0
    assert report.unresolved == 0 and report.inventory == {}


def test_generator_scorecard_arithmetic_is_exactly_what_was_put_in() -> None:
    stats = {s.generator: s for s in M.generator_scorecard(_synthetic_view())}
    assert set(stats) == {"genA", "genB", "genC"}

    a = stats["genA"]
    assert a.invocations == 2 and a.zero_yield == 0 and a.errored == 0
    assert a.produced == 14  # 10 in run A, 4 in run B
    assert (a.duplicate, a.invalid, a.known, a.trivial, a.refuted, a.survives) == (
        6, 1, 3, 1, 2, 1,
    )
    assert a.inconclusive == 0
    assert a.unique == 14 - 6 - 1 == 7
    assert a.generation_seconds == 4.0 + 2.0 == 6.0
    assert a.screening_seconds == 10 * 0.5 + 4 * 0.25 == 6.0
    assert a.seconds == 12.0
    assert a.duplicate_rate == 6 / 14
    assert a.known_rate == 3 / 14
    assert a.trivial_rate == 1 / 14
    assert a.refuted_rate == 2 / 14
    assert a.survival_rate == 1 / 14
    assert a.unsettled_rate == (14 - 6 - 1 - 3 - 1) / 14 == 3 / 14
    assert a.cost_per_survivor == 12.0
    assert a.survivors_per_second == 1 / 12.0
    assert a.seconds_per_candidate == 12.0 / 14
    assert a.versions == ("1",)

    b = stats["genB"]
    assert b.invocations == 1 and b.zero_yield == 1 and b.produced == 0
    assert b.seconds == 1.0
    # every rate over an empty population is undefined, not zero
    for undefined in (
        b.known_rate, b.trivial_rate, b.refuted_rate, b.survival_rate,
        b.unsettled_rate, b.duplicate_rate, b.cost_per_survivor, b.seconds_per_candidate,
    ):
        assert undefined is None
    assert b.survivors_per_second == 0.0  # 0 survivors over 1 second *is* defined

    c = stats["genC"]
    assert c.produced == 2 and c.known == 1 and c.inconclusive == 1
    assert c.known_rate == 0.5 and c.survival_rate == 0.0
    assert c.unsettled_rate == (2 - 0 - 0 - 1 - 0) / 2 == 0.5
    assert c.cost_per_survivor is None
    assert c.seconds == 3.0 + 2 * 0.25 == 3.5
    assert c.versions == ("2",)

    # ranking: survivors per second, then the unsettled share, then name
    ranked = [s.generator for s in M.generator_scorecard(_synthetic_view())]
    assert ranked == ["genA", "genC", "genB"]
    assert [s.rank for s in M.generator_scorecard(_synthetic_view())] == [1, 2, 3]


def test_stage_costs_arithmetic_is_exactly_what_was_put_in() -> None:
    costs = M.stage_costs(_synthetic_view())
    by_stage = {s.stage: s for s in costs.stages}
    assert by_stage["generate"].seconds == 5.0 + 5.0 == 10.0
    assert by_stage["deduplicate"].seconds == pytest.approx(0.15)
    assert by_stage["knownness"].seconds == pytest.approx(0.9)
    assert by_stage["expensive_screens"].seconds == 3.0 + 1.0
    assert abs(costs.total_seconds - (10.0 + 0.15 + 0.9 + 0.5 + 4.0 + 0.25)) < 1e-12
    assert by_stage["knownness"].seconds_per_candidate == pytest.approx(0.9 / 9)

    screens = {s.screen: s for s in costs.screens}
    assert (screens["cat"].calls, screens["cat"].stopped) == (9, 4)
    assert screens["cat"].seconds == pytest.approx(0.9)
    assert screens["cat"].stop_rate == 4 / 9
    assert (screens["verify"].calls, screens["verify"].stopped) == (4, 2)
    assert screens["verify"].seconds == 4.0
    assert screens["verify"].seconds_per_kill == 2.0
    assert screens["triv"].stop_rate == 1 / 5
    # ordered by cost, descending
    assert [s.screen for s in costs.screens] == ["verify", "cat", "triv"]


def test_time_series_arithmetic_is_exactly_what_was_put_in() -> None:
    daily = {b.bucket: b for b in M.time_series(_synthetic_view(), bucket="day")}
    assert set(daily) == {"2026-07-01", "2026-07-02"}
    first = daily["2026-07-01"]
    assert (first.runs, first.invocations, first.generated) == (2, 4, 16)
    assert first.seconds == 15.0
    assert first.survivors == 1 and first.survival_rate == 1 / 16
    assert first.known_rate == 4 / 16
    second = daily["2026-07-02"]  # the crashed run
    assert (second.runs, second.generated) == (1, 0)
    assert second.survival_rate is None

    monthly = M.time_series(_synthetic_view(), bucket="month")
    assert [b.bucket for b in monthly] == ["2026-07"]
    assert monthly[0].runs == 3 and monthly[0].generated == 16
    assert [b.bucket for b in M.time_series(_synthetic_view(), bucket="year")] == ["2026"]
    with pytest.raises(ValueError, match="bucket must be"):
        M.time_series(_synthetic_view(), bucket="fortnight")


def test_a_run_with_an_unusable_timestamp_is_bucketed_not_dropped() -> None:
    view = LedgerView(runs=({"run_id": "r", "state": "finished", "started_at": "soon"},))
    assert [b.bucket for b in M.time_series(view)] == ["unknown"]


def test_rate_refuses_to_invent_a_zero() -> None:
    assert M.rate(1, 4) == 0.25
    assert M.rate(0, 4) == 0.0
    assert M.rate(3, 0) is None
    assert M.rate(0, 0) is None


def test_the_empty_ledger_reports_nothing_without_dividing_by_zero(tmp_path) -> None:
    for source in (LedgerView(), Ledger(tmp_path / "absent.jsonl"), tmp_path / "absent.jsonl"):
        report = M.funnel_report(source)
        assert report.runs == 0 and report.generated == 0 and report.invocations == 0
        assert all(v is None for v in report.rates.values())
        assert report.zero_yield_rate is None
        assert report.candidates_per_invocation is None
        assert report.survival_rate is None
        assert report.seconds_per_survivor is None
        assert all(s.pass_rate is None for s in report.stages)
        assert M.generator_scorecard(source) == ()
        assert M.time_series(source) == ()
        costs = M.stage_costs(source)
        assert costs.screens == () and costs.total_seconds == 0.0
        text = M.render_text(source)
        assert "no run has been recorded" in text
        assert "no generator invocation" in text
        assert "nothing has been screened yet" in text
        assert "no dated run" in text


def test_a_single_entry_ledger_reports_sane_rates() -> None:
    view = LedgerView(
        runs=(
            {
                "record": "funnel_run",
                "run_id": "r",
                "state": "finished",
                "started_at": "2026-07-01T10:00:00+00:00",
                "seconds": 2.0,
                "stages": list(F.STAGES),
                "generators": [
                    {"generator": "g", "version": "1", "produced": 1, "seconds": 2.0}
                ],
                "outcomes": [_outcome("c", "g", "terminal", "survives", 1.0)],
                "stage_tallies": [{"stage": "terminal", "entered": 1, "left": 1, "seconds": 1.0}],
            },
        )
    )
    report = M.funnel_report(view)
    assert report.generated == 1 and report.survival_rate == 1.0
    assert report.rates["known"] == 0.0
    assert report.stage("generate").pass_rate == 1.0
    assert report.stage("terminal").pass_rate == 0.0
    only = M.generator_scorecard(view)[0]
    assert only.survival_rate == 1.0 and only.cost_per_survivor == 3.0
    assert only.rank == 1
    assert "100.0%" in report.render_text()


def test_the_candidate_stream_supplies_the_standing_inventory(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    led.append(_constant("a"))  # still open: a run died before deciding it
    led.append(_constant("b").with_verdict(_verdict(VerdictStatus.KNOWN, **_KNOWN)))
    report = M.funnel_report(led)
    assert report.inventory == {"open": 1, "known": 1}
    assert report.unresolved == 1
    assert "still 'open'" in report.render_text()


def test_render_text_produces_every_table_for_a_real_run(tmp_path) -> None:
    items = [_constant("k"), _constant("t"), _constant("r"), _constant("s")]
    led = Ledger(tmp_path / "l.jsonl")
    F.run_funnel(_full_domain(items), ledger=led)
    text = M.render_text(led)
    for heading in ("FUNNEL", "GENERATOR SCORECARD", "STAGE AND SCREEN COSTS", "OVER TIME"):
        assert heading in text
    for stage in F.STAGES:
        assert stage in text
    assert "lower bound" in text  # deduplication is never reported as exact
    assert "private" in text
    assert M.funnel_report(led).to_dict()["generated"] == 4
    assert M.stage_costs(led).to_dict()["stages"]
    assert M.generator_scorecard(led)[0].to_dict()["produced"] == 4
    assert M.time_series(led)[0].to_dict()["runs"] == 1


def test_metrics_refuse_a_source_that_is_not_a_ledger() -> None:
    with pytest.raises(TypeError, match="not a ledger"):
        M.funnel_report(object())


def test_the_scorecard_says_when_its_ranking_is_only_a_proxy() -> None:
    view = LedgerView(
        runs=(
            {
                "record": "funnel_run",
                "run_id": "r",
                "state": "finished",
                "started_at": "2026-07-01T10:00:00+00:00",
                "seconds": 1.0,
                "stages": list(F.STAGES),
                "generators": [
                    {"generator": "g", "version": "1", "produced": 1, "seconds": 1.0}
                ],
                "outcomes": [_outcome("c", "g", "knownness", "known", 0.1)],
            },
        )
    )
    text = M.render_text(view)
    assert "no source has produced a survivor" in text
    assert "residue" in text


# ---------------------------------------------------------------------------
# 6. adversarial: work that must not disappear from the denominators
# ---------------------------------------------------------------------------


class _Thrower(BaseScreen):
    """Passes the first candidate, then raises: a mid-run plug-in defect."""

    name = "thrower"
    cost = "cheap"
    checks = ("trivial", "refutation")

    def __init__(self) -> None:
        self.calls = 0

    def apply(self, candidate):
        self.calls += 1
        if self.calls > 1:
            raise ZeroDivisionError("the screen is broken")
        return ScreenResult(self.name, True, effort=40.0)


def _throwing_domain(items):
    return Domain(
        name="d",
        version="1",
        generators=(ListGenerator("gen", items),),
        screens=(_Thrower(),),
        detectors=(Catalogue(set()),),
    )


def test_a_crashed_run_still_reports_the_work_it_did(tmp_path) -> None:
    """A plug-in that throws must not take the run's *measurements* with it.

    The exception propagates (a broken screen is a defect, not a verdict), but
    everything decided before it is written up as ``state="crashed"``. Without
    this, a run that screened four hundred observations and died on the four
    hundred and first contributes nothing to any conversion rate — the exact
    failure this package exists to prevent.
    """
    led = Ledger(tmp_path / "l.jsonl")
    items = [_constant("a"), _constant("b"), _constant("c")]
    with pytest.raises(ZeroDivisionError, match="broken"):
        F.run_funnel(_throwing_domain(items), ledger=led)

    states = [(r.get("run_id"), r.get("state")) for r in led.runs()]
    assert [s for _, s in states] == ["started", "crashed"]
    assert len({rid for rid, _ in states}) == 1, "both records are the same run"
    crashed = led.runs()[-1]
    assert "ZeroDivisionError" in crashed["aborted_by"]
    assert crashed["entered"] == 3 and crashed["undecided"] == 2
    assert any("run aborted" in e for e in crashed["errors"])

    report = M.funnel_report(led)
    assert report.runs == 1 and report.runs_incomplete == 1
    assert report.generated == 1, "the candidate that was decided must be counted"
    assert report.dispositions["survives"] == 1
    assert report.unresolved == 1, "the checkpointed one is still open, and says so"
    # the stage flow of a crashed run is reconstructible and conserves
    assert sum(s.left for s in report.stages) == report.generated
    scorecard = {s.generator: s for s in M.generator_scorecard(led)}
    assert scorecard["gen"].produced == 1 and scorecard["gen"].survives == 1


def test_a_crashed_dry_run_writes_nothing_at_all(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    with pytest.raises(ZeroDivisionError):
        F.run_funnel(
            _throwing_domain([_constant("a"), _constant("b")]),
            ledger=led,
            dry_run=True,
        )
    assert not led.path.exists() and not led.runs_path.exists()


def test_the_crashed_record_never_claims_more_than_it_decided(tmp_path) -> None:
    """A crashed run's stage flow must not say a candidate reached a stage it
    never reached: metrics reconstruct the flow from the outcomes, and the run's
    own tallies must agree with that reconstruction."""
    led = Ledger(tmp_path / "l.jsonl")
    with pytest.raises(ZeroDivisionError):
        F.run_funnel(
            _throwing_domain([_constant("a"), _constant("b"), _constant("c")]),
            ledger=led,
        )
    crashed = F.FunnelRun.from_dict(led.runs()[-1])
    assert len(crashed.outcomes) == 1
    for tally in crashed.stage_tallies:
        assert tally.entered <= len(crashed.outcomes)
    report = M.funnel_report(led)
    for stat in report.stages:
        assert stat.entered == crashed.stage_tally(stat.stage).entered


def test_a_stage_or_disposition_outside_the_vocabulary_is_shown_not_dropped() -> None:
    """A hand-edited run record must not be able to lose counts silently.

    The funnel refuses to *write* a disposition outside :data:`DISPOSITIONS`,
    but the ledger is a text file. If a foreign name ever appears, the report
    has to keep its count and show it, so that the rows still add up to the
    total they are shares of.
    """
    view = LedgerView(
        runs=(
            {
                "record": "funnel_run",
                "run_id": "r",
                "state": "finished",
                "started_at": "2026-07-01T10:00:00+00:00",
                "seconds": 1.0,
                "stages": list(F.STAGES),
                "generators": [
                    {"generator": "g", "version": "1", "produced": 2, "seconds": 1.0}
                ],
                "outcomes": [
                    _outcome("c1", "g", "terminal", "survives", 0.1),
                    _outcome("c2", "g", "sorcery", "interesting", 0.1),
                ],
            },
        )
    )
    report = M.funnel_report(view)
    assert report.generated == 2
    assert report.dispositions["interesting"] == 1
    assert sum(s.left for s in report.stages) == report.generated, "no count lost"
    assert any(s.stage == "sorcery" for s in report.stages)
    text = report.render_text()
    assert "interesting" in text and "sorcery" in text


def test_a_reused_run_id_is_refused_rather_than_erasing_a_run(tmp_path) -> None:
    """Run records collapse by ``run_id``; reusing one would silently delete an
    earlier run's outcomes from every denominator."""
    led = Ledger(tmp_path / "l.jsonl")
    F.run_funnel(_full_domain([_constant("k")]), ledger=led, run_id="fixed")
    with pytest.raises(F.FunnelError, match="already in"):
        F.run_funnel(_full_domain([_constant("t")]), ledger=led, run_id="fixed")
    assert M.funnel_report(led).runs == 1
    # a generated id is never refused, however many runs there are
    F.run_funnel(_full_domain([_constant("t")]), ledger=led)
    F.run_funnel(_full_domain([_constant("r")]), ledger=led)
    assert M.funnel_report(led).runs == 3


def test_a_spent_budget_says_the_limit_was_reached(tmp_path) -> None:
    """``limit=0`` generates nothing *because of the limit*, and says so."""
    run = F.run_funnel(_full_domain([_constant("a")]), ledger=tmp_path / "l.jsonl", limit=0)
    assert run.generated == 0
    assert run.limit_reached
    assert all(g.skipped for g in run.generators)
    assert M.funnel_report(Ledger(tmp_path / "l.jsonl")).invocations == 0


def test_no_report_ever_calls_an_unmatched_payload_new(tmp_path) -> None:
    """The integrity rule of the knownness layer, enforced on the *metrics*.

    A catalogue that matched nothing has established nothing about the wider
    literature. The share it leaves over is a residue of the checks that ran,
    and no rendered table may spell it as a discovery.
    """
    led = Ledger(tmp_path / "l.jsonl")
    F.run_funnel(_full_domain([_constant("k"), _constant("s")]), ledger=led)
    text = M.render_text(led).casefold()
    for word in ("novel", "novelty", "new result", "unpublished", "discovery"):
        assert word not in text, f"the report claims {word!r}"
    source = (_discovery_dir() / "metrics.py").read_text(encoding="utf-8")
    assert "novelty_rate" not in source
    stat = M.generator_scorecard(led)[0]
    assert stat.unsettled_rate == (2 - 0 - 0 - 1 - 0) / 2 == 0.5
    assert "unsettled_rate" in stat.to_dict()


def test_the_candidates_a_crash_never_decided_are_reported_not_hidden(tmp_path) -> None:
    """A crash drops observations. The report has to say how many.

    The crash record carries ``undecided``, but the first review of this layer
    found that no report surfaced it: ``funnel_report`` counted only the
    outcomes, so a run that lost two of three observations rendered as a run
    that simply produced one. A denominator quietly shrunk by a crash is the
    accounting error this package exists to prevent, so the count is reported
    beside the rates it is deliberately *not* part of.
    """
    led = Ledger(tmp_path / "l.jsonl")
    with pytest.raises(ZeroDivisionError):
        F.run_funnel(
            _throwing_domain([_constant("a"), _constant("b"), _constant("c")]),
            ledger=led,
        )
    report = M.funnel_report(led)
    assert report.undecided == 2
    assert report.generated == 1, "undecided candidates are NOT in any rate"
    assert report.to_dict()["undecided"] == 2
    text = report.render_text()
    assert "2 candidate(s) entered a run that then crashed" in text
    assert "in no count or rate above" in text


def test_a_clean_ledger_reports_no_undecided_candidates(tmp_path) -> None:
    led = Ledger(tmp_path / "l.jsonl")
    F.run_funnel(_full_domain([_constant("k"), _constant("t")]), ledger=led)
    report = M.funnel_report(led)
    assert report.undecided == 0
    assert "crashed" not in report.render_text()
    assert M.funnel_report(Ledger(tmp_path / "empty.jsonl")).undecided == 0


def test_a_hand_edited_undecided_count_cannot_poison_the_report(tmp_path) -> None:
    """The field is read off a raw record, so it is read defensively."""
    led = Ledger(tmp_path / "l.jsonl")
    for bad in ("not-a-number", None, -5):
        led.append_run({"run_id": f"r-{bad}", "state": "crashed", "undecided": bad})
    assert M.funnel_report(led).undecided == 0
