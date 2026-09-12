"""The intervention ledger, held to the same standard as the instruments.

``meta/ledger.py`` is the second laboratory's instrument, so it gets the
treatment any instrument here gets: a schema with enforced invariants, planted
faults proving the invariants have detector power, and the seam tests that keep
it domain-agnostic (same pattern as ``ontology/schema.py`` and
``dossier/status.py``).

The invariant worth stating plainly, because it is the one that keeps the ledger
from flattering the laboratory: **claiming that something has been automated
costs a named artefact.** "We automated that" is the cheapest sentence in this
whole project to assert, and a ledger that accepts it for free would turn into a
progress report.
"""

from __future__ import annotations

import pathlib
import re
import sys

import pytest

_REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from meta.ledger import (  # noqa: E402
    Automatability,
    CaughtBy,
    Category,
    Intervention,
    Judgment,
    Ledger,
    MetaObservation,
    OperatorFunction,
    Party,
    Resolution,
    load,
    validate,
)


def _judgment(**over) -> Judgment:
    base = dict(
        session="s",
        date="2026-01-01",
        assessed="how bad a thing was",
        system_assessment="very bad",
        operator_assessment="not bad",
        function=OperatorFunction.SEVERITY,
        resolution=Resolution.OPERATOR_RIGHT,
        resolved_by=Party.OPERATOR,
        evidence="what happened next",
    )
    base.update(over)
    return Judgment(**base)


def _ok(**over) -> Intervention:
    base = dict(
        session="s",
        date="2026-01-01",
        what_required_intervention="a human had to do something",
        why_the_system_stopped="the system had no way to do it",
        missing_capability="the thing it lacked",
        category=Category.AUTOMATABLE,
        automatability=Automatability.SPECULATIVE,
        caught_by=CaughtBy.HUMAN,
        evidence_that_would_demonstrate="a test that fires",
    )
    base.update(over)
    return Intervention(**base)


# --------------------------------------------------------------------------
# 1. the shipped ledger is admissible and non-trivial
# --------------------------------------------------------------------------


def test_the_committed_ledger_validates() -> None:
    led = load()
    validate(led)
    assert led.interventions, "the ledger is empty: the baseline was never recorded"


def test_the_committed_ledger_records_both_classes_of_evidence() -> None:
    """Every interesting run yields research evidence and meta-research evidence."""
    led = load()
    assert led.observations, "no meta-observations: only half the evidence is being kept"


def test_the_baseline_records_interventions_the_architecture_did_not_catch() -> None:
    """A ledger listing only what the tests already catch measures nothing.

    This is the honest-baseline check: at least one entry must be attributed to a
    human or an outsider, because that is the class the automation thesis has to
    move.
    """
    led = load()
    caught = led.by_caught_by()
    assert caught.get(CaughtBy.HUMAN.value, 0) + caught.get(CaughtBy.OUTSIDER.value, 0) > 0


# --------------------------------------------------------------------------
# 2. planted faults, the invariants have detector power
# --------------------------------------------------------------------------


def test_claiming_automation_without_an_artifact_is_refused() -> None:
    bad = _ok(automatability=Automatability.AUTOMATED, automation_evidence="")
    reasons = bad.reasons_invalid()
    assert any("named artifact" in r for r in reasons), reasons
    with pytest.raises(ValueError):
        validate(Ledger(interventions=[bad]))


def test_claiming_automation_with_an_artifact_is_admitted() -> None:
    good = _ok(
        automatability=Automatability.AUTOMATED,
        automation_evidence="tests/test_meta_ledger.py",
    )
    assert good.reasons_invalid() == []


def test_an_automatable_gap_must_be_named() -> None:
    """You cannot automate a capability gap you cannot state."""
    bad = _ok(missing_capability="   ")
    assert any("cannot state" in r for r in bad.reasons_invalid())


def test_an_automatable_claim_must_say_what_would_demonstrate_it() -> None:
    bad = _ok(evidence_that_would_demonstrate="")
    assert any("would demonstrate" in r for r in bad.reasons_invalid())


def test_an_irreducible_intervention_needs_no_automation_evidence() -> None:
    """``NO`` means the intervention should not be automated, so it owes nothing."""
    ok = _ok(
        category=Category.OWNER_AUTHORITY,
        automatability=Automatability.NO,
        missing_capability="",
        evidence_that_would_demonstrate="",
    )
    assert ok.reasons_invalid() == []


def test_a_meta_observation_must_arise_from_actual_work() -> None:
    bad = MetaObservation(
        session="s", date="d", observation="agents are interesting", arose_from="",
        supports="something",
    )
    assert any("opinion" in r for r in bad.reasons_invalid())


def test_a_meta_observation_must_cut_one_way_or_the_other() -> None:
    bad = MetaObservation(
        session="s", date="d", observation="noted", arose_from="a real run",
    )
    assert any("neither supports nor undercuts" in r for r in bad.reasons_invalid())


# --------------------------------------------------------------------------
# 3. the ledger refuses to collapse into a score
# --------------------------------------------------------------------------


def test_the_ledger_has_no_truth_value() -> None:
    """``if ledger:`` would be asking 'are we autonomous yet' as one question."""
    with pytest.raises(TypeError):
        bool(load())


def test_a_ratio_must_name_its_numerator() -> None:
    led = Ledger(interventions=[_ok(category=Category.DOMAIN_JUDGMENT)])
    with pytest.raises(ValueError):
        led.ratio("", 3)
    assert "per 1 scarce-judgment" in led.ratio("kernel-checked theorems", 3)


def test_the_denominator_is_judgment_and_authority_only() -> None:
    led = Ledger(
        interventions=[
            _ok(category=Category.AUTOMATABLE),
            _ok(category=Category.ASSISTABLE),
            _ok(category=Category.DOMAIN_JUDGMENT),
            _ok(category=Category.OWNER_AUTHORITY, automatability=Automatability.NO,
                missing_capability="", evidence_that_would_demonstrate=""),
        ]
    )
    assert led.scarce_judgment_count() == 2


# --------------------------------------------------------------------------
# 4. the anti-self-validation check has detector power
# --------------------------------------------------------------------------


def test_a_flattering_ledger_is_flagged_as_suspicious() -> None:
    """The failure mode is a ledger that only records what already works."""
    flattering = Ledger(
        interventions=[
            _ok(caught_by=CaughtBy.TEST, automatability=Automatability.AUTOMATED,
                automation_evidence="a test"),
            _ok(caught_by=CaughtBy.TEST, automatability=Automatability.AUTOMATED,
                automation_evidence="a test"),
        ]
    )
    s = flattering.suspicions()
    assert any("owner-authority" in x for x in s), s
    assert any("only records what the architecture already catches" in x for x in s), s
    assert any("meta-observations" in x for x in s), s


def test_an_empty_ledger_is_not_autonomy() -> None:
    assert any("not autonomy" in x for x in Ledger().suspicions())


def test_render_names_every_category_and_offers_no_total() -> None:
    text = load().render()
    for c in Category:
        assert c.value in text
    for c in CaughtBy:
        assert c.value in text
    assert "autonomy" not in text.lower() or "not autonomy" in text.lower()


# --------------------------------------------------------------------------
# 5. seam: the instrument must not learn its subject
# --------------------------------------------------------------------------

_SUBJECT_VOCABULARY = (
    "zeta",
    "riemann",
    "hardy",
    "gamma",
    "prime",
    "critical line",
    "euler",
    "modular",
)

_FORBIDDEN_ROOTS = ("zeta", "numpy", "scipy", "mpmath", "sympy", "matplotlib", "flint")


# --------------------------------------------------------------------------
# 4b. calibration: the system may not mark its own homework
# --------------------------------------------------------------------------


def test_the_system_may_not_resolve_a_disagreement_it_is_party_to() -> None:
    """The guard without which this whole record is worthless.

    The system always holds one of the two positions in a ``Judgment``, so
    letting it adjudicate is the co-designed-verification failure applied to
    calibration, the exact failure this laboratory has measured in its own audit.
    """
    bad = _judgment(resolved_by=Party.SYSTEM, resolution=Resolution.SYSTEM_RIGHT)
    assert any("may not adjudicate" in r for r in bad.reasons_invalid())
    with pytest.raises(ValueError):
        validate(Ledger(judgments=[bad]))


def test_a_resolution_costs_evidence_but_an_open_disagreement_does_not() -> None:
    assert any("costs named evidence" in r for r in _judgment(evidence="").reasons_invalid())
    open_case = _judgment(
        resolution=Resolution.UNRESOLVED, resolved_by=Party.OUTCOME, evidence=""
    )
    assert open_case.reasons_invalid() == []
    assert not open_case.scorable()


def test_calibration_is_reported_per_function_and_never_averaged() -> None:
    led = Ledger(
        judgments=[
            _judgment(function=OperatorFunction.SEVERITY),
            _judgment(function=OperatorFunction.SCOPE, resolution=Resolution.SYSTEM_RIGHT,
                      resolved_by=Party.OUTCOME),
        ]
    )
    cal = led.calibration_by_function()
    assert set(cal) == {
        OperatorFunction.SEVERITY.value,
        OperatorFunction.SCOPE.value,
    }
    assert cal[OperatorFunction.SEVERITY.value][Resolution.OPERATOR_RIGHT.value] == 1
    assert cal[OperatorFunction.SCOPE.value][Resolution.SYSTEM_RIGHT.value] == 1
    assert not hasattr(led, "calibration_score"), (
        "an aggregate calibration score would hide which function transferred"
    )


def test_an_early_lead_for_the_system_is_flagged_not_celebrated() -> None:
    """The shape a self-serving calibration record takes early on."""
    led = Ledger(
        interventions=[_ok(category=Category.OWNER_AUTHORITY,
                           automatability=Automatability.NO,
                           missing_capability="", evidence_that_would_demonstrate="")],
        observations=[MetaObservation(session="s", date="d", observation="o",
                                      arose_from="w", supports="x")],
        judgments=[
            _judgment(resolution=Resolution.SYSTEM_RIGHT, resolved_by=Party.OUTCOME),
            _judgment(resolution=Resolution.SYSTEM_RIGHT, resolved_by=Party.OUTCOME),
        ],
    )
    assert any("too few to read as transfer" in x for x in led.suspicions())


def test_a_ledger_with_no_recorded_disagreements_is_suspicious() -> None:
    led = Ledger(
        interventions=[_ok(category=Category.OWNER_AUTHORITY,
                           automatability=Automatability.NO,
                           missing_capability="", evidence_that_would_demonstrate="")],
        observations=[MetaObservation(session="s", date="d", observation="o",
                                      arose_from="w", supports="x")],
    )
    assert any("not being written down" in x for x in led.suspicions())


def test_the_committed_ledger_records_disagreements_resolved_against_the_system() -> None:
    """The baseline is 0 for 3. If this ever passes trivially, check why."""
    led = load()
    scored = [j for j in led.judgments if j.scorable()]
    assert scored, "no scored calibration cases: the essence is not being measured"
    assert any(j.resolution is Resolution.OPERATOR_RIGHT for j in scored)


def test_the_ledger_module_contains_no_subject_matter_vocabulary() -> None:
    """A ledger of interventions in any laboratory should need no edits here."""
    source = (_REPO_ROOT / "meta" / "ledger.py").read_text(encoding="utf-8").lower()
    for word in _SUBJECT_VOCABULARY:
        assert not re.search(rf"\b{re.escape(word)}\b", source), (
            f"meta/ledger.py names {word!r}: the instrument has learned its subject"
        )


def test_the_ledger_module_imports_nothing_from_the_laboratory() -> None:
    import ast

    tree = ast.parse((_REPO_ROOT / "meta" / "ledger.py").read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        names = []
        if isinstance(node, ast.Import):
            names = [a.name for a in node.names]
        elif isinstance(node, ast.ImportFrom) and node.module:
            names = [node.module]
        for name in names:
            assert name.split(".")[0] not in _FORBIDDEN_ROOTS, f"ledger.py imports {name}"
