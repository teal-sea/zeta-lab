"""Does the funnel reproduce history?

A classification system that cannot correctly bin claims whose outcomes are
already settled is not ready to classify anything unsettled. This module
replays four famous claims and one constructed negative control through the
laboratory's own pipeline and asserts that each lands where a century of
subsequent work says it belongs.

The five cases and the answers being demanded
---------------------------------------------
===================  =============================  =========================
case                 what history settled           what the funnel must do
===================  =============================  =========================
Gauss, 1792          true, proved 1896              catalogued as a theorem
Montgomery, 1973     true so far as anyone knows,   catalogued as a conjecture,
                     still open                     and *not* as proved
Mertens, 1897        **false**, disproved 1985      never a survivor
Li, 1997             equivalent to an open problem  catalogued as open
PSLQ coincidence     never true                     refuted by the screens
===================  =============================  =========================

Each case is replayed twice: once with the whole pipeline, and once with the
catalogue emptied — the position the original author was in. The second replay
is the searching one, and it needs a positive control, because "nothing was
promoted" is not a measurement if promotion was unreachable. That control is
:func:`~discovery.domains.zeta_history.build_honest_twin`, which does reach
``survives`` in the same mode.

**No test here is evidence for the Riemann Hypothesis.** The Mertens case is in
the suite precisely because a century of finite computation was not evidence for
*that* conjecture either. The strongest sentence any of these tests supports is
"no violation was found in the range examined".

What this suite found, and did not paper over
---------------------------------------------
Two defects are pinned below as tests rather than hidden:

* every historically correct answer was carried by the already-known catalogue
  alone — with the catalogue emptied, not one of the four claims was decided by
  anything that looked at the mathematics
  (:func:`test_every_correct_historical_answer_was_carried_by_the_catalogue`);
* a correct measurement and a wrong coincidence that share nine significant
  digits are the *same candidate* under the deduplication contract, so logging
  one silently discards the other
  (:func:`test_dedup_merges_a_measurement_with_a_coincidence_sharing_nine_digits`).
"""

from __future__ import annotations

import ast
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

import pytest

from discovery import historical_cases as HC
from discovery.domains import zeta_domain as Z
from discovery.domains import zeta_history as ZH
from discovery.funnel import DISPOSITIONS, run_funnel
from discovery.knownness import FACT_STATUSES, FORBIDDEN_LABEL_WORDS
from discovery.ledger import Ledger
from discovery.registry import Domain, validate_domain
from discovery.schema import (
    CandidateKind,
    VerdictStatus,
    candidate_reasons,
    content_hash,
    same_claim,
    verdict_reasons,
)

DOMAIN = Z.DOMAIN
CASE_KEYS = tuple(case.key for case in ZH.HISTORICAL_CASES)


@pytest.fixture(autouse=True)
def _cases_are_registered():
    """The case table is process-wide and one test below empties it."""
    ZH.register_all()
    yield
    ZH.register_all()


@pytest.fixture(scope="session")
def replays(tmp_path_factory) -> dict[str, HC.CaseResult]:
    """Every case, both modes, run once per worker."""
    root = tmp_path_factory.mktemp("history")
    results = HC.run_history(ZH.HISTORICAL_CASES, DOMAIN, ledger_dir=root)
    return {r.case_key: r for r in results}


def _case(key: str) -> HC.HistoricalCase:
    return next(c for c in ZH.HISTORICAL_CASES if c.key == key)


# ---------------------------------------------------------------------------
# 1. the harness knows nothing about the subject
# ---------------------------------------------------------------------------

_FORBIDDEN_ROOTS = ("zeta", "numpy", "scipy", "mpmath", "sympy", "matplotlib", "flint")
_SUBJECT_WORDS = (
    "zeta",
    "riemann",
    "zeros",
    "primes",
    "dirichlet",
    "hardy",
    "mertens",
    "jensen",
    "gue",
    "epstein",
    "critical line",
    "hypothesis",
)


def _harness_path() -> Path:
    return Path(HC.__file__).resolve()


def test_the_harness_imports_nothing_from_the_laboratory() -> None:
    """The validation machinery must transplant to another subject unchanged."""
    tree = ast.parse(_harness_path().read_text(encoding="utf-8"))
    names: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names.extend(a.name for a in node.names)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            names.append(node.module)
    assert not [n for n in names if n.split(".")[0] in _FORBIDDEN_ROOTS]


def test_the_harness_names_no_subject_matter() -> None:
    """A leaked seam is usually a leaked word first."""
    source = _harness_path().read_text(encoding="utf-8").lower()
    offenders = [w for w in _SUBJECT_WORDS if re.search(rf"\b{re.escape(w)}\b", source)]
    assert not offenders, offenders


def test_importing_the_harness_pulls_in_no_laboratory_module() -> None:
    root = str(_harness_path().parent.parent)
    code = (
        "import sys; sys.path.insert(0, %r);"
        "import discovery.historical_cases;"
        "print(','.join(sorted(m for m in sys.modules if m.split('.')[0]=='zeta')))"
        % root
    )
    out = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, timeout=120
    )
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip() == "", out.stdout


def test_the_subject_matter_half_lives_under_domains() -> None:
    """The file that names the laboratory is inside ``domains/``, as required."""
    assert Path(ZH.__file__).resolve().parent.name == "domains"


# ---------------------------------------------------------------------------
# 2. the harness will not let a case lower its own bar
# ---------------------------------------------------------------------------


def _minimal_case(**overrides) -> HC.HistoricalCase:
    base = dict(
        key="probe",
        title="a probe",
        proposed=1900,
        outcome=HC.HistoricalOutcome.FALSE,
        build=ZH.build_low_precision_coincidence,
        expect_full=frozenset({"known"}),
        expect_uncatalogued=frozenset({"inconclusive"}),
        if_it_fails="the probe would mean nothing",
        settled=1950,
        settled_by="somebody",
    )
    base.update(overrides)
    return HC.HistoricalCase(**base)


@pytest.mark.parametrize("outcome", list(HC.HistoricalOutcome))
def test_a_case_may_not_expect_a_disposition_history_rules_out(outcome) -> None:
    """The one rule a green-seeking author must not be able to relax.

    Without it, any failing case could be repaired by editing its expectation,
    and a suite that can be edited into agreement measures nothing.
    """
    banned = HC.IMPOSSIBLE_DISPOSITIONS[outcome]
    assert banned, outcome
    bad = _minimal_case(
        outcome=outcome,
        settled=1950 if outcome is HC.HistoricalOutcome.TRUE_AND_PROVEN else None,
        settled_by="somebody" if outcome is HC.HistoricalOutcome.TRUE_AND_PROVEN else "",
        expect_full=frozenset({sorted(banned)[0]}),
    )
    reasons = HC.case_reasons(bad)
    assert any("history rules out" in r for r in reasons), reasons
    with pytest.raises(HC.HistoryError):
        HC.register_case(bad, replace=True)


def test_every_outcome_has_at_least_one_impossible_disposition() -> None:
    """A historical outcome that forbids nothing would validate nothing."""
    assert set(HC.IMPOSSIBLE_DISPOSITIONS) == set(HC.HistoricalOutcome)
    for outcome, banned in HC.IMPOSSIBLE_DISPOSITIONS.items():
        assert banned, outcome
        assert banned <= set(DISPOSITIONS), outcome


def test_a_false_or_spurious_claim_may_never_be_recorded_as_a_survivor() -> None:
    """The headline rule, stated once as a rule rather than five times as data."""
    for outcome in (HC.HistoricalOutcome.FALSE, HC.HistoricalOutcome.SPURIOUS):
        assert "survives" in HC.IMPOSSIBLE_DISPOSITIONS[outcome]
    open_problem = HC.HistoricalOutcome.EQUIVALENT_TO_AN_OPEN_PROBLEM
    assert {"survives", "refuted"} <= HC.IMPOSSIBLE_DISPOSITIONS[open_problem]


@pytest.mark.parametrize(
    "overrides,fragment",
    [
        ({"if_it_fails": "  "}, "if_it_fails"),
        ({"key": "not an identifier!"}, "identifier"),
        ({"title": ""}, "title"),
        ({"settled": 1800}, "precedes"),
        ({"settled_by": ""}, "who settled"),
        ({"expect_full": frozenset({"promoted"})}, "outside the vocabulary"),
        ({"expect_full": frozenset()}, "non-empty"),
        ({"build": "not callable"}, "callable"),
        ({"must_cite": ("",)}, "must_cite"),
        (
            {"expect_screens_kill": True, "expect_uncatalogued": frozenset({"inconclusive"})},
            "not a kill",
        ),
    ],
)
def test_case_reasons_names_each_way_a_case_is_malformed(overrides, fragment) -> None:
    reasons = HC.case_reasons(_minimal_case(**overrides))
    assert any(fragment in r for r in reasons), (fragment, reasons)


def test_a_proved_claim_must_record_when_and_by_whom() -> None:
    reasons = HC.case_reasons(
        _minimal_case(
            outcome=HC.HistoricalOutcome.TRUE_AND_PROVEN,
            settled=None,
            settled_by="",
            expect_full=frozenset({"known"}),
        )
    )
    assert any("when, and by whom" in r for r in reasons), reasons


def test_every_registered_case_is_well_formed_and_says_what_a_failure_means() -> None:
    for case in ZH.HISTORICAL_CASES:
        assert not HC.case_reasons(case), case.key
        assert len(case.if_it_fails) > 60, case.key
        assert case.note.strip(), case.key


def test_the_case_table_registers_gets_lists_and_clears() -> None:
    HC.clear_cases()
    assert HC.list_cases() == ()
    ZH.register_all()
    assert set(HC.list_cases()) == set(CASE_KEYS)
    assert HC.get_case("mertens").outcome is HC.HistoricalOutcome.FALSE
    with pytest.raises(HC.HistoryError):
        HC.register_case(_case("mertens"))  # already there, replace not passed
    HC.unregister_case("mertens")
    with pytest.raises(HC.HistoryError):
        HC.get_case("mertens")


def test_a_replay_must_be_told_where_to_write() -> None:
    """No default ledger: a replay must never touch the laboratory's own log."""
    with pytest.raises(TypeError):
        HC.replay(_case("mertens"), DOMAIN)  # type: ignore[call-arg]


def test_run_case_refuses_an_unknown_mode_and_refuses_to_skip_the_full_pass(
    tmp_path,
) -> None:
    with pytest.raises(HC.HistoryError):
        HC.run_case(_case("mertens"), DOMAIN, ledger_dir=tmp_path, modes=("wishful",))
    with pytest.raises(HC.HistoryError):
        HC.run_case(
            _case("mertens"), DOMAIN, ledger_dir=tmp_path, modes=("uncatalogued",)
        )


def test_the_empty_catalogue_is_a_usable_detector_that_recognises_nothing() -> None:
    detector = HC.NullKnownnessDetector()
    probe = Domain(
        name="probe",
        version="1.0",
        generators=(HC.CaseGenerator(_case("mertens")),),
        screens=DOMAIN.screens,
        detectors=(detector,),
    )
    validate_domain(probe)
    assert "known" in probe.checks_available()
    assert detector.check(ZH.build_honest_twin()) is None
    assert detector.describe().strip()


def test_check_case_marks_an_impossible_disposition_as_critical() -> None:
    """The adjudicator's own failure path, exercised rather than assumed."""
    case = _case("mertens")
    fake = HC.CaseReplay(
        case_key=case.key,
        mode="full",
        candidate_id="cand-0",
        kind="structural",
        stage="terminal",
        disposition="survives",
        screen="",
        detail="",
        status="survives",
        references=("Odlyzko and te Riele 1985",),
    )
    result = HC.check_case(case, fake)
    assert not result.passed
    assert result.critical
    assert "impossible" in result.critical[0]
    assert "MISCLASSIFIED" in HC.render_text([result])


def test_render_text_on_nothing_says_nothing_was_validated() -> None:
    assert "nothing was validated" in HC.render_text([])


# ---------------------------------------------------------------------------
# 3. the five cases
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("key", CASE_KEYS)
def test_the_funnel_reproduces_the_settled_outcome(key, replays) -> None:
    """The headline. A failure prints what that failure would have meant."""
    result = replays[key]
    case = _case(key)
    assert result.passed, (
        f"{key}: {result.reasons}\n"
        f"full={result.full.to_dict()}\n"
        f"uncatalogued={None if result.uncatalogued is None else result.uncatalogued.to_dict()}\n"
        f"what this failure would mean: {case.if_it_fails}"
    )


@pytest.mark.parametrize("key", CASE_KEYS)
def test_every_replayed_observation_was_a_well_formed_candidate(key) -> None:
    """``invalid`` would mean the case author failed, not the ontology."""
    candidate = _case(key).build()
    assert not candidate_reasons(candidate), key
    assert candidate.verdict.status is VerdictStatus.OPEN


# -- 3.1 Gauss, 1792 --------------------------------------------------------


def test_gauss_prime_counts_are_catalogued_as_a_theorem(replays) -> None:
    rep = replays["gauss_prime_counts"].full
    assert rep.disposition == "known"
    assert rep.stage == "knownness"
    assert rep.verdict_evidence["literature_status"] == "theorem"
    blob = rep.record_text()
    assert "hadamard" in blob and "de la vallee poussin" in blob
    assert "gauss" in blob


def test_the_gauss_fit_is_the_one_gauss_could_have_made(replays) -> None:
    """Two windows over 10^3..10^6, and a tolerance that can actually fail."""
    candidate = ZH.build_gauss_prime_counting()
    assert candidate.kind is CandidateKind.ASYMPTOTIC
    windows = candidate.evidence["windows"]
    assert len(windows) == 2
    span = max(w["index_max"] for w in windows) / min(w["index_min"] for w in windows)
    assert span >= 1000
    tolerance = float(candidate.evidence["tolerance"])
    drift = max(abs(float(w["exponent"]) - 1.0) for w in windows)
    assert drift <= tolerance
    # Not vacuous: the same fit against x rather than Li(x) misses by more than
    # the tolerance, so the statistic distinguishes the two classical forms.
    import numpy as np

    from zeta.explicit import pi_true

    for block in ZH.GAUSS_WINDOWS:
        counts = [pi_true(x) for x in block]
        against_x = ZH._loglog_exponent([float(x) for x in block], counts)
        assert abs(against_x - 1.0) > tolerance, (block, against_x)


def test_the_recorded_prime_counts_are_the_real_ones(replays) -> None:
    """Every number in the record is pinned, per the house rule."""
    from zeta.explicit import pi_true

    windows = ZH.build_gauss_prime_counting().evidence["windows"]
    pinned = {1_000: 168, 10_000: 1229, 100_000: 9592, 1_000_000: 78498}
    seen = {}
    for window in windows:
        for x, count in zip(window["x"], window["pi_x"]):
            seen[int(x)] = int(count)
            assert int(count) == pi_true(int(x))
    for x, expected in pinned.items():
        assert seen[x] == expected


# -- 3.2 Montgomery, 1973 ---------------------------------------------------


def test_montgomery_is_catalogued_as_a_conjecture_and_never_as_proved(
    replays,
) -> None:
    """The distinction the verdict vocabulary cannot make on its own.

    ``known`` covers "already established" and "already conjectured" alike, so
    the catalogue's ``status`` is what separates them, and the record's prose is
    held to it: no word in it may claim a proof.
    """
    rep = replays["montgomery_pair"].full
    assert rep.disposition == "known"
    assert rep.verdict_evidence["literature_status"] == "conjecture"
    assert rep.status != VerdictStatus.SURVIVES.value
    blob = rep.record_text()
    for word in ("proved", "proven", "is a theorem"):
        assert word not in blob, word
    assert "montgomery 1973" in blob and "odlyzko 1987" in blob


def test_the_pair_correlation_beats_the_uncorrelated_null_by_the_stated_margin() -> None:
    candidate = ZH.build_montgomery_pair_correlation()
    evidence = candidate.evidence
    ratio = float(evidence["defect"])
    assert ratio == pytest.approx(
        float(evidence["rms_vs_predicted"]) / float(evidence["rms_vs_uncorrelated"])
    )
    assert 0.0 < ratio < float(evidence["tolerance"])
    # The tolerance is refutable: a flat empirical curve would score 1.0 and be
    # refused by the schema outright.
    assert float(evidence["tolerance"]) < 1.0
    assert float(evidence["rms_vs_predicted"]) < float(evidence["rms_vs_uncorrelated"])
    assert float(evidence["max_abs_deviation"]) < 0.25


def test_the_montgomery_form_is_the_one_in_the_1973_paper() -> None:
    """1 - (sin(pi r)/(pi r))^2, checked at the points the record carries."""
    import math

    candidate = ZH.build_montgomery_pair_correlation()
    for r, predicted in zip(
        candidate.evidence["r"], candidate.evidence["predicted"]
    ):
        r = float(r)
        expected = 1.0 if r == 0 else 1.0 - (math.sin(math.pi * r) / (math.pi * r)) ** 2
        assert float(predicted) == pytest.approx(expected, abs=1e-4)


# -- 3.3 Mertens, 1897 — the case that matters ------------------------------


def test_the_funnel_would_not_have_endorsed_the_mertens_conjecture(replays) -> None:
    """The whole suite exists for this assertion.

    Every computation feasible for a century supported ``|M(x)| < sqrt(x)``, and
    it is false. A ``survives`` disposition here — in either mode — would mean
    the pipeline endorses a false conjecture on exactly the evidence that
    convinced its contemporaries, and nothing else it produces could be trusted.
    """
    result = replays["mertens"]
    for rep in (result.full, result.uncatalogued):
        assert rep is not None
        assert rep.disposition != "survives", rep.to_dict()
        assert rep.status != VerdictStatus.SURVIVES.value


def test_mertens_is_catalogued_with_the_disproof(replays) -> None:
    rep = replays["mertens"].full
    assert rep.disposition == "known"
    assert rep.verdict_evidence["literature_status"] == "disproved"
    blob = rep.record_text()
    assert "odlyzko" in blob and "te riele" in blob
    assert "1985" in blob


def test_the_mertens_record_says_only_that_no_violation_was_found_in_range() -> None:
    candidate = ZH.build_mertens_conjecture()
    evidence = candidate.evidence
    assert evidence["n_violations_in_range"] == 0
    assert evidence["first_violation"] is None
    assert evidence["n_scanned"] == ZH.MERTENS_LIMIT - 1
    assert float(evidence["max_ratio"]) < 1.0
    note = str(evidence["note"]).lower()
    assert "range examined" in note
    assert "10^14" in note
    # The claim recorded is the bounded one, not the conjecture.
    assert str(ZH.MERTENS_LIMIT) in candidate.claim["family"]
    assert str(ZH.MERTENS_LIMIT) in candidate.claim["scope"]


def test_every_mertens_control_fails_the_predicate() -> None:
    """The control is why nobody should have believed it.

    A sum on the same square-root scale with independent signs exceeds sqrt(x)
    somewhere inside a million terms every time. The schema demands at least one
    failing control; all three fail, so the predicate is not one that everything
    on this scale satisfies.
    """
    controls = ZH.build_mertens_conjecture().evidence["controls"]
    assert len(controls) == ZH.MERTENS_CONTROLS >= 3
    for control in controls:
        assert control["satisfied"] is False, control
        assert float(control["max_ratio"]) > 1.0
        assert control["n_exceeding"] > 0
        assert control["first_x_exceeding"] is not None


def test_mertens_is_not_promoted_even_with_the_battery_removed(tmp_path) -> None:
    """What actually stops it, once every other obstacle is taken away.

    In the ``uncatalogued`` replay the counterexample battery stops it first, so
    that replay does not show what the terminal stage would have said. Removing
    the battery as well answers it: the observation was generated by exact
    integer arithmetic, and nothing can verify an exact result more expensively
    than it was produced, so the funnel records ``precision_insufficient`` with a
    ceiling of ``exact`` (``discovery/README.md`` section 8.2). The conjecture is
    still not endorsed — but by a rule of bookkeeping, not by mathematics, and
    that is worth knowing about one's own instrument.
    """
    case = _case("mertens")
    screens = tuple(s for s in DOMAIN.screens if s.name != "counterexample_battery")
    probe = Domain(
        name="mertens-without-the-battery",
        version="1.0",
        generators=(HC.CaseGenerator(case),),
        screens=screens,
        detectors=(HC.NullKnownnessDetector(),),
    )
    path = tmp_path / "mertens.jsonl"
    run = run_funnel(probe, ledger=path)
    outcome = run.outcomes[0]
    assert outcome.disposition == "inconclusive"
    verdict = Ledger(path).latest()[outcome.candidate_id].verdict
    assert verdict.evidence["reason"] == "precision_insufficient"
    assert verdict.evidence["ceiling"]["effort"] == "exact"


def test_the_mertens_case_would_actually_fail_if_the_funnel_endorsed_it(tmp_path) -> None:
    """The teeth, exercised end to end rather than argued for.

    The three tests above show only that the pipeline *does not* promote this
    conjecture — and two of the three reasons it does not are bookkeeping
    (``Precision('exact')``, and a battery with no analogue of the predicate),
    not mathematics. So "Mertens was not endorsed" is, on its own, compatible
    with a validation suite that could never fail. This test removes that doubt
    from the other end: it builds a pipeline that **does** endorse the Mertens
    observation — every screen a rubber stamp reporting a colossal verification
    effort, and the candidate's precision made finite so that the effort
    comparison can be satisfied — and asserts that the adjudicator then reports
    a CRITICAL misclassification.

    Together with :func:`test_a_case_may_not_expect_a_disposition_history_rules_out`
    (the expectation cannot be edited to agree) this is what makes the suite a
    measurement rather than a decoration.
    """
    import dataclasses

    from discovery.registry import BaseKnownnessDetector, BaseScreen, ScreenResult
    from discovery.schema import Precision

    case = _case("mertens")

    class RubberStamp(BaseScreen):
        """Passes everything and claims to have verified it expensively."""

        name = "rubber_stamp"
        cost = "expensive"
        checks = ("trivial", "refutation")

        def apply(self, candidate):
            return ScreenResult(self.name, True, effort=1e6)

    class NoCatalogue(BaseKnownnessDetector):
        name = "no-catalogue"
        version = "1.0"

        def check(self, candidate):
            return None

    def build_finite():
        candidate = case.build()
        provenance = dataclasses.replace(
            candidate.provenance, precision=Precision(kind="dps", value=30)
        )
        return dataclasses.replace(candidate, provenance=provenance)

    endorsing = Domain(
        name="mertens-endorsing-pipeline",
        version="1.0",
        generators=(HC.CaseGenerator(dataclasses.replace(case, build=build_finite)),),
        screens=(RubberStamp(),),
        detectors=(NoCatalogue(),),
    )
    run = run_funnel(endorsing, ledger=tmp_path / "endorsed.jsonl")
    assert run.outcomes[0].disposition == "survives", (
        "the probe did not manage to make the pipeline endorse it, so this test "
        "proves nothing about the adjudicator"
    )

    replay = HC.CaseReplay(
        case_key=case.key,
        mode="uncatalogued",
        candidate_id=run.outcomes[0].candidate_id,
        kind=run.outcomes[0].kind,
        stage=run.outcomes[0].stage,
        disposition="survives",
        screen=RubberStamp.name,
        detail="",
        status=VerdictStatus.SURVIVES.value,
        references=(),
    )
    result = HC.check_case(case, replay, replay)
    assert not result.passed
    assert result.critical, result.reasons
    assert all("impossible" in reason for reason in result.critical)
    assert "MISCLASSIFIED" in HC.render_text([result])
    # And the failure message prints what the case said it would mean.
    assert "endorsed the Mertens conjecture" in case.if_it_fails


# -- 3.4 Li, 1997 -----------------------------------------------------------


def test_li_criterion_is_catalogued_as_equivalent_to_an_open_problem(replays) -> None:
    rep = replays["li_criterion"].full
    assert rep.disposition == "known"
    assert rep.verdict_evidence["literature_status"] == "equivalent_to_open_problem"
    blob = rep.record_text()
    assert "li 1997" in blob and "bombieri" in blob


def test_the_li_criterion_is_never_a_discovery_and_never_a_refutation(
    replays,
) -> None:
    """Neither terminal verdict is available for an equivalent-to-open claim.

    A finite positivity check cannot be a lead towards an open question, and it
    cannot settle one either; if this pipeline ever recorded ``refuted`` here,
    the correct inference would be a bug in the laboratory.
    """
    result = replays["li_criterion"]
    for rep in (result.full, result.uncatalogued):
        assert rep is not None
        assert rep.disposition not in ("survives", "refuted"), rep.to_dict()


def test_the_li_control_fails_as_soon_as_a_zero_leaves_the_line() -> None:
    """The predicate discriminates, which is what makes the claim have content."""
    controls = ZH.build_li_criterion().evidence["controls"]
    off_line, on_line = controls[0], controls[1]
    assert off_line["satisfied"] is False
    assert 1 <= int(off_line["first_negative_n"]) <= ZH.LI_N_MAX
    assert float(off_line["min_value"]) < 0
    assert on_line["satisfied"] is True
    assert float(on_line["min_value"]) >= 0


def test_the_recorded_li_coefficients_match_the_laboratory() -> None:
    from mpmath import mp

    from zeta.li import li_closed_form_lambda1

    evidence = ZH.build_li_criterion().evidence
    witnesses = evidence["witnesses"]
    assert len(witnesses) == ZH.LI_N_MAX == evidence["n_checked"]
    assert evidence["n_satisfied"] == evidence["n_checked"]
    assert all(w["satisfied"] for w in witnesses)
    with mp.workdps(40):
        first = mp.mpf(str(witnesses[0]["lambda_n"]))
        assert abs(first - li_closed_form_lambda1(dps=35)) < mp.mpf("1e-11")
    assert float(evidence["min_lambda"]) > 0


# -- 3.5 the negative control -----------------------------------------------


def test_the_low_precision_coincidence_is_refuted_in_both_modes(replays) -> None:
    """The only case the screens must kill on the arithmetic alone."""
    result = replays["pslq_coincidence"]
    for rep in (result.full, result.uncatalogued):
        assert rep is not None
        assert rep.disposition == "refuted", rep.to_dict()
        assert rep.screen == "precision_stability"
    assert not HC.gate_dependence(result)


def test_the_refutation_survived_a_precision_increase(replays) -> None:
    """A failure that vanishes at higher precision is arithmetic, not a result."""
    rep = replays["pslq_coincidence"].full
    evidence = rep.verdict_evidence
    assert float(evidence["escalated_effort"]) > float(evidence["effort"])
    assert float(evidence["escalated_defect"]) > float(evidence["tolerance"])
    assert float(evidence["defect"]) > float(evidence["tolerance"])


def test_the_coincidence_is_genuinely_compelling_before_it_dissolves() -> None:
    """A negative control nobody would have believed tests nothing."""
    evidence = ZH.build_low_precision_coincidence().evidence
    assert float(evidence["digits_of_agreement"]) >= 11.0
    assert len(evidence["integer_relation"]) == len(ZH.COINCIDENCE_BASIS) + 1
    assert evidence["search_digits"] == ZH.COINCIDENCE_DIGITS == 10
    assert evidence["closed_form"].strip()


def test_the_integer_relation_really_holds_at_ten_digits_and_fails_at_twenty() -> None:
    """The construction, re-derived rather than trusted."""
    from mpmath import mp

    from zeta.core import Xi

    found = ZH.pslq_coincidence()
    with mp.workdps(60):
        true = mp.mpf(Xi(mp.mpf(1), dps=50))
        spurious = mp.mpf(found["spurious_value"])
        gap = abs(spurious - true)
        assert gap < mp.mpf("1e-11")   # compelling at the precision it was found
        assert gap > mp.mpf("1e-20")   # and wrong at the precision claimed


def test_the_honest_twin_of_the_negative_control_survives(tmp_path) -> None:
    """The positive control, without which "it was killed" proves nothing.

    Same subject, same route, same claimed error bar; the only difference is
    that the number is measured rather than guessed. It reaches ``survives`` in
    both modes, so the ``uncatalogued`` replay is a real counterfactual and not
    a pipeline that cannot promote anything.

    Reaching ``survives`` is not a discovery. It means only that nothing in this
    system killed it, and the record's own ``proof_gap`` says so.
    """
    twin = ZH.build_honest_twin()

    class _Probe:
        name = "honest-twin"
        version = "1.0"

        def describe(self) -> str:
            return "the positive control"

        def generate(self, context):
            yield twin

    for mode, detectors in (
        ("full", DOMAIN.detectors),
        ("uncatalogued", (HC.NullKnownnessDetector(),)),
    ):
        path = tmp_path / f"twin-{mode}.jsonl"
        run = run_funnel(
            Domain(
                name=f"twin-{mode}",
                version="1.0",
                generators=(_Probe(),),
                screens=DOMAIN.screens,
                detectors=detectors,
            ),
            ledger=path,
        )
        outcome = run.outcomes[0]
        assert outcome.disposition == "survives", (mode, outcome.detail)
        verdict = Ledger(path).latest()[outcome.candidate_id].verdict
        assert not verdict_reasons(verdict)
        assert float(verdict.evidence["verified_effort"]) > float(
            verdict.evidence["effort"]
        )
        assert "lead" in verdict.evidence["proof_gap"].lower()


# ---------------------------------------------------------------------------
# 4. what the measurement showed — including the unflattering part
# ---------------------------------------------------------------------------


def test_every_correct_historical_answer_was_carried_by_the_catalogue(
    replays,
) -> None:
    """The measurement this suite exists to make, and it is not flattering.

    All four historical claims are settled by the already-known gate. With the
    catalogue emptied, not one of them is decided by anything that examined the
    mathematics: each is recorded ``inconclusive`` for a different missing
    dependency. That is the correct behaviour — the pipeline refuses to promote
    what it could not verify — but it means the screens contributed nothing to
    four of the five right answers, and a laboratory that had not measured this
    would be crediting its screens for the catalogue's work.
    """
    historical = [k for k in CASE_KEYS if k != "pslq_coincidence"]
    dependent = [k for k in CASE_KEYS if HC.gate_dependence(replays[k])]
    assert sorted(dependent) == sorted(historical), dependent
    for key in historical:
        rep = replays[key].uncatalogued
        assert rep is not None
        assert rep.disposition == "inconclusive"
        assert rep.verdict_evidence["reason"] in (
            "dependency_unavailable",
            "precision_insufficient",
        )


def test_each_case_was_stopped_for_a_distinct_and_named_reason(replays) -> None:
    """Pinning what actually happened, so a change to it is visible in a diff."""
    stops = {
        key: (
            replays[key].uncatalogued.stage,
            replays[key].uncatalogued.screen,
            replays[key].uncatalogued.verdict_evidence.get("reason"),
        )
        for key in CASE_KEYS
    }
    assert stops == {
        "gauss_prime_counts": ("terminal", "", "precision_insufficient"),
        "montgomery_pair": (
            "cheap_screens",
            "precision_stability",
            "dependency_unavailable",
        ),
        "mertens": (
            "expensive_screens",
            "counterexample_battery",
            "dependency_unavailable",
        ),
        "li_criterion": (
            "expensive_screens",
            "counterexample_battery",
            "dependency_unavailable",
        ),
        "pslq_coincidence": ("cheap_screens", "precision_stability", None),
    }, stops


def test_the_full_pipeline_settles_four_of_five_by_catalogue_lookup(replays) -> None:
    """The package's own premise, measured on cases with known answers."""
    counts = Counter(r.full.disposition for r in replays.values())
    assert counts["known"] == 4
    assert counts["refuted"] == 1
    assert counts["survives"] == 0


def test_the_catalogue_distinguishes_the_kinds_of_being_known(replays) -> None:
    """Four ``known`` verdicts, four different things being said."""
    statuses = {
        key: replays[key].full.verdict_evidence.get("literature_status")
        for key in CASE_KEYS
        if replays[key].full.disposition == "known"
    }
    assert statuses == {
        "gauss_prime_counts": "theorem",
        "montgomery_pair": "conjecture",
        "mertens": "disproved",
        "li_criterion": "equivalent_to_open_problem",
    }
    assert set(statuses.values()) <= set(FACT_STATUSES)


# ---------------------------------------------------------------------------
# 5. two limits of the ontology, pinned rather than hidden
# ---------------------------------------------------------------------------


def test_dedup_merges_a_measurement_with_a_coincidence_sharing_nine_digits(
    tmp_path,
) -> None:
    """A defect, recorded as a test because it is real and not yet fixed.

    The honest measurement of the quantity and the wrong closed form agree to
    twelve significant digits. Identity is the canonical claim rounded to
    ``DEFAULT_DEDUP_DIGITS = 9``, so the two are **the same candidate**: same
    id, ``same_claim`` true. In one pass the second one emitted is recorded
    ``duplicate`` and never screened — so whichever is logged first silently
    determines the fate of the other, and a refuted coincidence can shadow a
    correct measurement of the same quantity.

    They collide at every resolution up to and including twelve digits and
    separate at thirteen, so the resolution is the whole cause. The fix is a
    schema change (identity for a ``constant`` would have to include its error
    bound, which changes every id and needs a major version), and it is reported
    rather than made here.
    """
    honest = ZH.build_honest_twin()
    spurious = ZH.build_low_precision_coincidence()
    assert honest.claim["value"] != spurious.claim["value"]
    assert honest.id == spurious.id
    assert same_claim(honest, spurious)
    # The exact threshold, not a comfortable value above it: a tolerance that
    # cannot fail is not a test.
    for digits in range(1, 13):
        assert content_hash(honest.kind, honest.claim, digits) == content_hash(
            spurious.kind, spurious.claim, digits
        ), digits
    for digits in (13, 15, 20):
        assert content_hash(honest.kind, honest.claim, digits) != content_hash(
            spurious.kind, spurious.claim, digits
        ), digits

    class _Both:
        name = "both-twins"
        version = "1.0"

        def describe(self) -> str:
            return "the coincidence, then the measurement"

        def generate(self, context):
            yield spurious
            yield honest

    path = tmp_path / "collision.jsonl"
    run = run_funnel(
        Domain(
            name="collision",
            version="1.0",
            generators=(_Both(),),
            screens=DOMAIN.screens,
            detectors=DOMAIN.detectors,
        ),
        ledger=path,
    )
    dispositions = [o.disposition for o in run.outcomes]
    assert dispositions == ["refuted", "duplicate"], dispositions


def test_a_structural_claim_cannot_record_an_exhaustive_scan(replays) -> None:
    """A second limit: ``n_checked`` counts witnesses, not members checked.

    The Mertens scan covers 999 999 integers and the record says ``n_checked =
    12``, because the schema requires ``n_checked == len(witnesses)`` and a
    million witnesses is a data set rather than a record. The true count lives
    in a free-form evidence key that nothing validates, so the one number a
    reader would trust is the smaller and less impressive one.
    """
    evidence = ZH.build_mertens_conjecture().evidence
    assert evidence["n_checked"] == len(evidence["witnesses"]) == len(
        ZH.MERTENS_CHECKPOINTS
    )
    assert evidence["n_scanned"] > 1000 * evidence["n_checked"]


# ---------------------------------------------------------------------------
# 6. honest scope
# ---------------------------------------------------------------------------

_OVERCLAIM_RE = re.compile(
    r"(evidence for (?:the )?(?:rh|riemann)"
    r"|proves? (?:the )?(?:rh|riemann hypothesis)"
    r"|supports? (?:the )?riemann hypothesis"
    r"|confirms? (?:the )?riemann hypothesis"
    r"|establishes (?:the )?riemann hypothesis)"
)
_HEDGES = ("not ", "nothing ", "never ", "cannot ", "no ")


@pytest.mark.parametrize(
    "path",
    [Path(ZH.__file__), Path(HC.__file__), Path(__file__)],
    ids=["zeta_history", "historical_cases", "this_test_module"],
)
def test_no_occurrence_of_an_rh_claim_is_left_unhedged(path: Path) -> None:
    source = path.read_text(encoding="utf-8").lower()
    for match in _OVERCLAIM_RE.finditer(source):
        window = source[max(0, match.start() - 60) : match.start()]
        assert any(hedge in window for hedge in _HEDGES), source[
            max(0, match.start() - 90) : match.end() + 30
        ]


def test_no_label_or_record_text_claims_novelty(replays) -> None:
    """Offline, nothing here may be rendered as a find."""
    novelty = tuple(w for w in FORBIDDEN_LABEL_WORDS if w not in ("first", "original"))
    for key, result in replays.items():
        for rep in (result.full, result.uncatalogued):
            if rep is None:
                continue
            blob = rep.record_text()
            for word in novelty:
                assert not re.search(rf"\b{re.escape(word)}\b", blob), (key, word)


def test_every_case_note_and_record_stays_inside_what_was_measured() -> None:
    """No historical case may describe a finite check as settling anything."""
    banned = ("we have shown", "this establishes", "this proves")
    for case in ZH.HISTORICAL_CASES:
        blob = " ".join((case.title, case.note, case.if_it_fails)).lower()
        for phrase in banned:
            assert phrase not in blob, (case.key, phrase)
