"""Tests for discovery.schema — the ontology of the discovery funnel.

What is pinned here, in the order the design's claims are made:

1. **Every category is a function.** Each of the five kinds accepts a concrete
   payload and refuses a concrete near-miss; the refusals are the interesting
   half. A vague observation is accepted by no kind, and the five kinds are
   proved pairwise exclusive on their key sets, not merely on examples.
2. **Failure is recordable.** Each of the six verdict states is entered with
   evidence that earns it and refused without it — including the anti-noise
   guard on ``refuted`` (the failure must survive a precision increase) and the
   three-check requirement on ``survives``.
3. **Identity is the claim.** The content hash ignores key order, provenance,
   verdict, label and evidence; it is sensitive at the 9th significant digit
   and insensitive at the 15th; 20 000 near-identical claims give 20 000
   distinct ids.
4. **Records round-trip and malformed ones are refused** — a stored id that
   disagrees with its claim, a non-finite float, a machine-local path, a
   foreign claim key, an unknown schema major.
5. **The seam holds.** The module imports nothing from the laboratory package
   (AST scan), pulls nothing into ``sys.modules`` when imported in a clean
   interpreter, and contains no subject-matter vocabulary (lexical scan).
"""

from __future__ import annotations

import ast
import itertools
import json
import math
import re
import subprocess
import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from discovery import schema as S  # noqa: E402
from discovery.schema import (  # noqa: E402
    Candidate,
    CandidateKind,
    CandidateLink,
    CandidateRelation,
    InconclusiveReason,
    KnownEntry,
    Precision,
    Provenance,
    ValidationError,
    Verdict,
    VerdictStatus,
)

_NOW = "2026-08-02T12:00:00+00:00"


# ---------------------------------------------------------------------------
# fixtures: one well-formed payload per kind, plus a provenance record
# ---------------------------------------------------------------------------


def _provenance(**overrides) -> Provenance:
    base = dict(
        generator="unit_generator",
        generator_version="0.1.0",
        lab_object="package.module.quantity",
        parameters={"n_max": 2000},
        precision=Precision(kind="dps", value=30),
        seed=None,
        stochastic=False,
        code_revision="0123456789abcdef0123456789abcdef01234567",
        code_dirty=False,
        code_revision_source="git",
        captured_at=_NOW,
        runtime={"python": "3.14.0"},
        duration_s=1.5,
    )
    base.update(overrides)
    return Provenance(**base)


GOOD_PAYLOADS: dict[CandidateKind, tuple[dict, dict]] = {
    CandidateKind.CONSTANT: (
        {"subject": "series.coefficient_1", "value": 0.023095708966121034},
        {"uncertainty": 1e-18},
    ),
    CandidateKind.ASYMPTOTIC: (
        {
            "subject": "series.coefficient_n",
            "index": "n",
            "limit": "+inf",
            "scale": "n*log(n)/2",
            "exponent": 1.0,
        },
        {
            "tolerance": 0.05,
            "windows": [
                {"index_min": 100, "index_max": 500, "exponent": 0.99, "n_points": 40},
                {"index_min": 500, "index_max": 2000, "exponent": 1.01, "n_points": 60},
            ],
        },
    ),
    CandidateKind.RELATION: (
        {"lhs": "route.integral", "rhs": "route.closed_form", "relation": "eq"},
        {
            "defect": 1e-25,
            "tolerance": 1e-20,
            "defect_definition": "abs(lhs - rhs)",
        },
    ),
    CandidateKind.EXTREMAL: (
        {
            "subject": "ratio.partial_sum",
            "direction": "max",
            "space": "index <= 10^6",
            "n_searched": 1000000,
            "argopt": "7725038629",
            "value": 0.5709,
        },
        {"runner_up": 0.5705},
    ),
    CandidateKind.STRUCTURAL: (
        {
            "family": "family.polynomials",
            "predicate": "all_roots_real",
            "scope": "d<=12,n<=10",
        },
        {
            "witnesses": ["m1", "m2", "m3"],
            "n_checked": 3,
            "n_satisfied": 3,
            "controls": [{"id": "control.shifted", "satisfied": False}],
        },
    ),
}


def _candidate(kind: CandidateKind, **overrides) -> Candidate:
    claim, evidence = GOOD_PAYLOADS[kind]
    base = dict(
        kind=kind,
        claim=dict(claim),
        evidence=dict(evidence),
        provenance=_provenance(),
    )
    base.update(overrides)
    return Candidate(**base)


# ---------------------------------------------------------------------------
# 1. the categories are decision procedures
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("kind", list(CandidateKind))
def test_each_kind_accepts_its_own_payload(kind: CandidateKind) -> None:
    claim, evidence = GOOD_PAYLOADS[kind]
    assert S.kind_reasons(kind, claim, evidence) == ()
    assert S.accepts(kind, claim, evidence)
    assert S.classify(claim, evidence) is kind


REJECTIONS: list[tuple[str, str, dict, dict]] = [
    (
        "constant/vanishing",
        "constant",
        {"subject": "q", "value": 0.0},
        {"uncertainty": 1e-9},
    ),
    (
        "constant/no-digit-determined",
        "constant",
        {"subject": "q", "value": 1e-9},
        {"uncertainty": 1e-8},
    ),
    (
        "constant/no-error-bound",
        "constant",
        {"subject": "q", "value": 1.5},
        {},
    ),
    (
        "constant/exact-count-is-not-a-measurement",
        "constant",
        {"subject": "q", "value": 29},
        {"uncertainty": 0.5},
    ),
    (
        "asymptotic/narrow-span",
        "asymptotic",
        {
            "subject": "s",
            "index": "n",
            "limit": "+inf",
            "scale": "n",
            "exponent": 1.0,
        },
        {
            "tolerance": 0.05,
            "windows": [
                {"index_min": 100, "index_max": 110, "exponent": 1.0, "n_points": 5},
                {"index_min": 110, "index_max": 120, "exponent": 1.0, "n_points": 5},
            ],
        },
    ),
    (
        "asymptotic/single-window",
        "asymptotic",
        {
            "subject": "s",
            "index": "n",
            "limit": "+inf",
            "scale": "n",
            "exponent": 1.0,
        },
        {
            "tolerance": 0.05,
            "windows": [
                {"index_min": 10, "index_max": 10000, "exponent": 1.0, "n_points": 50}
            ],
        },
    ),
    (
        "asymptotic/unstable-fit",
        "asymptotic",
        {
            "subject": "s",
            "index": "n",
            "limit": "+inf",
            "scale": "n",
            "exponent": 1.0,
        },
        {
            "tolerance": 0.05,
            "windows": [
                {"index_min": 10, "index_max": 100, "exponent": 0.9, "n_points": 20},
                {"index_min": 100, "index_max": 1000, "exponent": 1.4, "n_points": 20},
            ],
        },
    ),
    (
        "relation/tautology",
        "relation",
        {"lhs": "a", "rhs": "a", "relation": "eq"},
        {"defect": 0.0, "tolerance": 1e-9, "defect_definition": "abs(lhs-rhs)"},
    ),
    (
        "relation/defect-exceeds-tolerance",
        "relation",
        {"lhs": "a", "rhs": "b", "relation": "eq"},
        {"defect": 3.0, "tolerance": 1e-3, "defect_definition": "abs(lhs-rhs)"},
    ),
    (
        "relation/undefined-defect",
        "relation",
        {"lhs": "a", "rhs": "b", "relation": "eq"},
        {"defect": 1e-9, "tolerance": 1e-3},
    ),
    (
        "relation/unknown-operator",
        "relation",
        {"lhs": "a", "rhs": "b", "relation": "resembles"},
        {"defect": 1e-9, "tolerance": 1e-3, "defect_definition": "d"},
    ),
    (
        "extremal/empty-search",
        "extremal",
        {
            "subject": "s",
            "direction": "max",
            "space": "sp",
            "n_searched": 1,
            "argopt": "x",
            "value": 1.0,
        },
        {"runner_up": 0.5},
    ),
    (
        "extremal/tie",
        "extremal",
        {
            "subject": "s",
            "direction": "max",
            "space": "sp",
            "n_searched": 10,
            "argopt": "x",
            "value": 1.0,
        },
        {"runner_up": 1.0},
    ),
    (
        "extremal/no-runner-up",
        "extremal",
        {
            "subject": "s",
            "direction": "max",
            "space": "sp",
            "n_searched": 10,
            "argopt": "x",
            "value": 1.0,
        },
        {},
    ),
    (
        "structural/no-failing-control",
        "structural",
        {"family": "f", "predicate": "p", "scope": "s"},
        {
            "witnesses": ["a", "b", "c"],
            "n_checked": 3,
            "n_satisfied": 3,
            "controls": [{"id": "c1", "satisfied": True}],
        },
    ),
    (
        "structural/no-controls",
        "structural",
        {"family": "f", "predicate": "p", "scope": "s"},
        {"witnesses": ["a", "b", "c"], "n_checked": 3, "n_satisfied": 3, "controls": []},
    ),
    (
        "structural/known-exception",
        "structural",
        {"family": "f", "predicate": "p", "scope": "s"},
        {
            "witnesses": ["a", "b", "c"],
            "n_checked": 3,
            "n_satisfied": 2,
            "controls": [{"id": "c1", "satisfied": False}],
        },
    ),
    (
        "structural/too-few-witnesses",
        "structural",
        {"family": "f", "predicate": "p", "scope": "s"},
        {
            "witnesses": ["a"],
            "n_checked": 1,
            "n_satisfied": 1,
            "controls": [{"id": "c1", "satisfied": False}],
        },
    ),
]


@pytest.mark.parametrize(
    "name,kind,claim,evidence",
    REJECTIONS,
    ids=[case[0] for case in REJECTIONS],
)
def test_near_misses_are_refused_with_a_reason(
    name: str, kind: str, claim: dict, evidence: dict
) -> None:
    reasons = S.kind_reasons(kind, claim, evidence)
    assert reasons, f"{name}: the category accepted a payload it must refuse"
    assert all(isinstance(r, str) and r for r in reasons)
    # ... and no *other* kind quietly picks it up either.
    assert S.classify(claim, evidence) is None


@pytest.mark.parametrize(
    "payload",
    [
        {},
        {"note": "the numbers look interesting"},
        {"subject": "q"},
        {"value": 1.0},
        {"subject": "q", "value": 1.0, "commentary": "suggestive"},
    ],
)
def test_vague_observations_are_not_candidates(payload: dict) -> None:
    assert S.classify(payload, {}) is None
    for kind in CandidateKind:
        assert not S.accepts(kind, payload, {})


def test_kinds_are_pairwise_exclusive_by_construction() -> None:
    """Proved on the key sets, so it holds for payloads nobody has written yet."""
    for a, b in itertools.combinations(CandidateKind, 2):
        required = S.required_claim_keys(a) | S.required_claim_keys(b)
        shared = S.allowed_claim_keys(a) & S.allowed_claim_keys(b)
        assert not required <= shared, f"{a} and {b} could both accept one claim"


def test_each_good_payload_is_refused_by_the_other_four_kinds() -> None:
    for kind, (claim, evidence) in GOOD_PAYLOADS.items():
        for other in CandidateKind:
            if other is kind:
                continue
            assert not S.accepts(other, claim, evidence)


def test_foreign_and_unknown_claim_keys_are_refused() -> None:
    claim, evidence = GOOD_PAYLOADS[CandidateKind.CONSTANT]
    polluted = dict(claim) | {"direction": "max"}
    assert S.kind_reasons("constant", polluted, evidence)
    stray = dict(claim) | {"comment": "looks nice"}
    assert S.kind_reasons("constant", stray, evidence)


def test_there_are_exactly_five_kinds_and_six_statuses() -> None:
    assert len(list(CandidateKind)) == 5
    assert len(list(VerdictStatus)) == 6
    assert set(S.KIND_RULES) == set(CandidateKind)


# ---------------------------------------------------------------------------
# 2. verdict states and their entry criteria
# ---------------------------------------------------------------------------


GOOD_VERDICT_EVIDENCE: dict[VerdictStatus, dict] = {
    VerdictStatus.KNOWN: {
        "references": ["doi:10.0000/example"],
        "match_kind": "value",
        "defect": 1e-14,
        "tolerance": 1e-12,
    },
    VerdictStatus.TRIVIAL: {
        "derived_from": ["lab.fact.functional_identity"],
        "argument": "substitute the defining series and cancel the common factor",
        "checked_by": "tests/test_x.py::test_reduction",
    },
    VerdictStatus.REFUTED: {
        "witness": {"index": 17},
        "defect": 1e-3,
        "tolerance": 1e-9,
        "effort": 30,
        "escalated_effort": 60,
        "escalated_defect": 1e-3,
    },
    VerdictStatus.SURVIVES: {
        "checks_run": ["known", "trivial", "refutation"],
        "effort": 30,
        "verified_effort": 80,
        "proof_gap": "nothing here bounds the truncation tail uniformly in the index",
    },
    VerdictStatus.INCONCLUSIVE: {
        "reason": "budget_exhausted",
        "detail": "abandoned after 900 s of quadrature",
        "ceiling": {"seconds": 900},
    },
}


def _verdict(status: VerdictStatus, evidence: dict) -> Verdict:
    return Verdict(
        status=status,
        decided_by="unit_screen",
        decided_by_version="0.1.0",
        decided_at=_NOW,
        evidence=evidence,
    )


@pytest.mark.parametrize("status", list(GOOD_VERDICT_EVIDENCE))
def test_verdict_states_accept_evidence_that_earns_them(status: VerdictStatus) -> None:
    verdict = _verdict(status, GOOD_VERDICT_EVIDENCE[status])
    assert S.verdict_reasons(verdict) == ()
    S.validate_verdict(verdict)
    assert verdict.is_terminal


def test_open_is_the_only_non_terminal_state_and_carries_no_evidence() -> None:
    assert S.verdict_reasons(Verdict()) == ()
    assert not Verdict().is_terminal
    assert set(VerdictStatus) - S.TERMINAL_STATUSES == {VerdictStatus.OPEN}
    assert S.verdict_reasons(Verdict(evidence={"smuggled": True}))


BAD_VERDICTS: list[tuple[str, VerdictStatus, dict]] = [
    ("known/no-reference", VerdictStatus.KNOWN, {"references": [], "match_kind": "value"}),
    (
        "known/opinion-not-identifier",
        VerdictStatus.KNOWN,
        {"references": ["  "], "match_kind": "statement"},
    ),
    (
        "known/match-outside-its-own-tolerance",
        VerdictStatus.KNOWN,
        {
            "references": ["r"],
            "match_kind": "value",
            "defect": 1e-3,
            "tolerance": 1e-9,
        },
    ),
    (
        "trivial/argument-is-not-one-line",
        VerdictStatus.TRIVIAL,
        {"derived_from": ["a"], "argument": "x" * 300, "checked_by": "t"},
    ),
    (
        "trivial/nothing-to-derive-from",
        VerdictStatus.TRIVIAL,
        {"derived_from": [], "argument": "obvious", "checked_by": "t"},
    ),
    (
        "trivial/unchecked",
        VerdictStatus.TRIVIAL,
        {"derived_from": ["a"], "argument": "obvious"},
    ),
    (
        "refuted/no-escalation",
        VerdictStatus.REFUTED,
        {
            "witness": {"index": 1},
            "defect": 1e-3,
            "tolerance": 1e-9,
            "effort": 30,
            "escalated_effort": 30,
            "escalated_defect": 1e-3,
        },
    ),
    (
        "refuted/failure-vanished-at-higher-effort",
        VerdictStatus.REFUTED,
        {
            "witness": {"index": 1},
            "defect": 1e-3,
            "tolerance": 1e-9,
            "effort": 30,
            "escalated_effort": 90,
            "escalated_defect": 1e-30,
        },
    ),
    (
        "refuted/inside-tolerance",
        VerdictStatus.REFUTED,
        {
            "witness": {"index": 1},
            "defect": 1e-30,
            "tolerance": 1e-9,
            "effort": 30,
            "escalated_effort": 90,
            "escalated_defect": 1e-30,
        },
    ),
    (
        "refuted/no-witness",
        VerdictStatus.REFUTED,
        {
            "defect": 1e-3,
            "tolerance": 1e-9,
            "effort": 30,
            "escalated_effort": 90,
            "escalated_defect": 1e-3,
        },
    ),
    (
        "survives/a-check-never-ran",
        VerdictStatus.SURVIVES,
        {
            "checks_run": ["known", "trivial"],
            "effort": 30,
            "verified_effort": 80,
            "proof_gap": "the tail",
        },
    ),
    (
        "survives/verification-was-not-more-expensive",
        VerdictStatus.SURVIVES,
        {
            "checks_run": list(S.REQUIRED_SURVIVAL_CHECKS),
            "effort": 80,
            "verified_effort": 80,
            "proof_gap": "the tail",
        },
    ),
    (
        "survives/no-proof-gap",
        VerdictStatus.SURVIVES,
        {
            "checks_run": list(S.REQUIRED_SURVIVAL_CHECKS),
            "effort": 30,
            "verified_effort": 80,
        },
    ),
    (
        "inconclusive/reason-off-vocabulary",
        VerdictStatus.INCONCLUSIVE,
        {"reason": "we got bored", "detail": "d", "ceiling": {"seconds": 10}},
    ),
    (
        "inconclusive/no-ceiling",
        VerdictStatus.INCONCLUSIVE,
        {"reason": "budget_exhausted", "detail": "d"},
    ),
]


@pytest.mark.parametrize(
    "name,status,evidence", BAD_VERDICTS, ids=[case[0] for case in BAD_VERDICTS]
)
def test_verdict_states_refuse_evidence_that_does_not_earn_them(
    name: str, status: VerdictStatus, evidence: dict
) -> None:
    verdict = _verdict(status, evidence)
    assert S.verdict_reasons(verdict), f"{name}: status granted without earning it"
    with pytest.raises(ValidationError):
        S.validate_verdict(verdict)


@pytest.mark.parametrize("status", list(GOOD_VERDICT_EVIDENCE))
def test_a_decided_verdict_must_say_who_decided_it(status: VerdictStatus) -> None:
    anonymous = Verdict(status=status, evidence=GOOD_VERDICT_EVIDENCE[status])
    reasons = S.verdict_reasons(anonymous)
    assert any("decided_by" in r for r in reasons)


def test_inconclusive_can_record_a_line_of_work_that_produced_nothing() -> None:
    """The unflattering case must be expressible, including irreproducibility."""
    for reason in InconclusiveReason:
        verdict = _verdict(
            VerdictStatus.INCONCLUSIVE,
            {
                "reason": reason.value,
                "detail": "recorded so the conversion rate absorbs it",
                "ceiling": {"seconds": 60},
            },
        )
        assert S.verdict_reasons(verdict) == ()


def test_a_verdict_does_not_change_a_candidate_identity() -> None:
    candidate = _candidate(CandidateKind.CONSTANT)
    decided = candidate.with_verdict(
        _verdict(VerdictStatus.KNOWN, GOOD_VERDICT_EVIDENCE[VerdictStatus.KNOWN])
    )
    assert decided.id == candidate.id
    assert decided.verdict.status is VerdictStatus.KNOWN
    assert candidate.verdict.status is VerdictStatus.OPEN
    assert S.latest_by_id([candidate, decided]) == {candidate.id: decided}


def test_candidate_links_are_typed_graph_annotations_not_deductions() -> None:
    target = _candidate(CandidateKind.RELATION)
    source = _candidate(
        CandidateKind.CONSTANT,
        related_to=(
            CandidateLink(target.id, CandidateRelation.IMPLIES),
            {
                "candidate_id": "cand-" + "f" * 32,
                "relation": "equivalent_to",
            },
        ),
    )
    S.validate_candidate(source)
    assert source.related_to[0].relation is CandidateRelation.IMPLIES
    assert source.related_to[1].relation is CandidateRelation.EQUIVALENT_TO
    # A dangling target and a one-way equivalence are both allowed: links do
    # not query a ledger, demand reciprocal edges, or propagate a verdict.
    assert source.verdict.status is VerdictStatus.OPEN


def test_candidate_links_do_not_change_identity_and_round_trip() -> None:
    target = _candidate(CandidateKind.RELATION)
    plain = _candidate(CandidateKind.CONSTANT)
    linked = _candidate(
        CandidateKind.CONSTANT,
        related_to=(CandidateLink(target.id, "implies"),),
    )
    assert linked.id == plain.id
    restored = S.from_json(S.to_json(linked))
    assert restored == linked
    assert restored.related_to == linked.related_to


@pytest.mark.parametrize(
    "link,pattern",
    [
        ({"candidate_id": "not-an-id", "relation": "implies"}, "candidate_id"),
        ({"candidate_id": "cand-" + "0" * 32, "relation": "resembles"}, "relation"),
        ({"candidate_id": "cand-" + "0" * 32}, "requires"),
        (
            {
                "candidate_id": "cand-" + "0" * 32,
                "relation": "implies",
                "confidence": 0.9,
            },
            "unknown",
        ),
    ],
)
def test_candidate_links_refuse_malformed_edge_shapes(link, pattern) -> None:
    with pytest.raises(ValidationError, match=pattern):
        _candidate(CandidateKind.CONSTANT, related_to=(link,))


# ---------------------------------------------------------------------------
# 3. identity: the content hash and the deduplication contract
# ---------------------------------------------------------------------------


def test_hash_ignores_key_order_and_numeric_spelling() -> None:
    a = S.content_hash("constant", {"subject": "q", "value": 1.2345678901234567})
    b = S.content_hash("constant", {"value": 1.2345678901234567, "subject": "q"})
    c = S.content_hash("constant", {"subject": "q", "value": "1.23456789012345670001"})
    assert a == b == c


def test_hash_is_sensitive_at_nine_digits_and_insensitive_beyond() -> None:
    #                                     123456789 <- the significant digits kept
    base = S.content_hash("constant", {"subject": "q", "value": 1.2345678901234567})
    ninth = S.content_hash("constant", {"subject": "q", "value": 1.2345679001234567})
    tenth = S.content_hash("constant", {"subject": "q", "value": 1.2345678911234567})
    fifteenth = S.content_hash("constant", {"subject": "q", "value": 1.2345678901234599})
    assert base != ninth, "a change in the 9th significant digit must split"
    assert base == tenth == fifteenth, "digits beyond the 9th must not split"


def test_exactness_is_part_of_the_claim() -> None:
    """An exact count and a measured value of equal magnitude differ, on purpose."""
    exact = S.content_hash("extremal", {"n_searched": 1000000})
    measured = S.content_hash("extremal", {"n_searched": 1000000.0})
    assert exact != measured


def test_hash_depends_on_the_kind_and_on_the_schema_major() -> None:
    claim = {"subject": "q", "value": 1.0}
    assert S.content_hash("constant", claim) != S.content_hash("extremal", claim)
    assert f'"v":{S.SCHEMA_MAJOR}' in S.canonical_claim("constant", claim)


def test_hash_ignores_provenance_verdict_label_and_evidence() -> None:
    baseline = _candidate(CandidateKind.CONSTANT)
    claim, evidence = GOOD_PAYLOADS[CandidateKind.CONSTANT]
    other = Candidate(
        kind=CandidateKind.CONSTANT,
        claim=dict(claim),
        evidence=dict(evidence) | {"uncertainty": 1e-25, "extra_support": [1, 2, 3]},
        provenance=_provenance(
            generator="a_different_generator",
            generator_version="9.9.9",
            precision=Precision(kind="bits", value=512),
            captured_at="2027-01-01T00:00:00+00:00",
            code_revision="f" * 40,
        ),
        verdict=_verdict(
            VerdictStatus.SURVIVES, GOOD_VERDICT_EVIDENCE[VerdictStatus.SURVIVES]
        ),
        label="found again, months later",
    )
    assert other.id == baseline.id
    assert S.same_claim(other, baseline)


def test_id_format_and_purity() -> None:
    candidate = _candidate(CandidateKind.RELATION)
    assert candidate.id.startswith("cand-")
    assert re.fullmatch(r"cand-[0-9a-f]{32}", candidate.id)
    assert candidate.id == _candidate(CandidateKind.RELATION).id


def test_twenty_thousand_near_identical_claims_do_not_collide() -> None:
    ids = {
        S.content_hash("constant", {"subject": f"q{i}", "value": 1.0 + i * 1e-7})
        for i in range(20000)
    }
    assert len(ids) == 20000


def test_resolution_is_part_of_identity_and_same_claim_bridges_it() -> None:
    claim = {"subject": "q", "value": 0.123456789123}
    assert S.content_hash("constant", claim, 9) != S.content_hash("constant", claim, 6)
    coarse = {"kind": "constant", "claim": {"subject": "q", "value": 0.12345679}, "dedup_digits": 8}
    fine = {"kind": "constant", "claim": {"subject": "q", "value": 0.1234567891}, "dedup_digits": 9}
    assert S.same_claim(fine, coarse)
    assert not S.same_claim(fine, {**coarse, "claim": {"subject": "q", "value": 0.9}})


def test_dedup_digits_may_not_exceed_the_digits_the_error_bound_determines() -> None:
    claim = {"subject": "q", "value": 1.234567}
    evidence = {"uncertainty": 1e-4}  # four digits determined, no more
    honest = Candidate(
        kind=CandidateKind.CONSTANT,
        claim=claim,
        evidence=evidence,
        provenance=_provenance(),
        dedup_digits=4,
    )
    S.validate_candidate(honest)
    overclaimed = Candidate(
        kind=CandidateKind.CONSTANT,
        claim=claim,
        evidence=evidence,
        provenance=_provenance(),
        dedup_digits=9,
    )
    with pytest.raises(ValidationError, match="determines"):
        S.validate_candidate(overclaimed)


@pytest.mark.parametrize("digits", [0, -1, 31, 1.5, True])
def test_dedup_digits_is_validated(digits) -> None:
    claim, evidence = GOOD_PAYLOADS[CandidateKind.CONSTANT]
    with pytest.raises(ValidationError):
        Candidate(
            kind=CandidateKind.CONSTANT,
            claim=dict(claim),
            evidence=dict(evidence),
            provenance=_provenance(),
            dedup_digits=digits,
        )


def test_list_order_is_meaning_inside_a_claim() -> None:
    forward = S.content_hash("structural", {"family": "f", "predicate": "p", "scope": "1,2"})
    reverse = S.content_hash("structural", {"family": "f", "predicate": "p", "scope": "2,1"})
    assert forward != reverse
    assert S.content_hash("constant", {"a": [1, 2]}) != S.content_hash(
        "constant", {"a": [2, 1]}
    )


# ---------------------------------------------------------------------------
# 4. serialisation and malformed-record rejection
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("kind", list(CandidateKind))
def test_json_round_trip_is_exact(kind: CandidateKind) -> None:
    candidate = _candidate(kind).with_verdict(
        _verdict(VerdictStatus.KNOWN, GOOD_VERDICT_EVIDENCE[VerdictStatus.KNOWN])
    )
    text = S.to_json(candidate)
    json.loads(text)  # it is valid JSON, on one line
    assert "\n" not in text
    restored = S.from_json(text)
    assert restored == candidate
    assert restored.id == candidate.id
    assert restored.kind is kind
    assert restored.verdict.status is VerdictStatus.KNOWN
    assert restored.provenance == candidate.provenance
    assert S.to_json(restored) == text


def test_jsonl_round_trip_and_append(tmp_path: Path) -> None:
    path = tmp_path / "log" / "candidates.jsonl"
    first = [_candidate(k) for k in (CandidateKind.CONSTANT, CandidateKind.RELATION)]
    assert S.write_jsonl(path, first) == 2
    S.append_jsonl(path, _candidate(CandidateKind.EXTREMAL))
    back = S.read_jsonl(path)
    assert [c.id for c in back] == [c.id for c in first] + [
        _candidate(CandidateKind.EXTREMAL).id
    ]
    assert [c.id for c in S.iter_jsonl(path)] == [c.id for c in back]
    assert S.loads_jsonl(S.dumps_jsonl(back)) == back
    assert S.read_jsonl(tmp_path / "absent.jsonl") == []


def test_append_only_log_collapses_to_the_latest_verdict(tmp_path: Path) -> None:
    path = tmp_path / "candidates.jsonl"
    candidate = _candidate(CandidateKind.ASYMPTOTIC)
    S.append_jsonl(path, candidate)
    S.append_jsonl(
        path,
        candidate.with_verdict(
            _verdict(VerdictStatus.TRIVIAL, GOOD_VERDICT_EVIDENCE[VerdictStatus.TRIVIAL])
        ),
    )
    log = S.read_jsonl(path)
    assert len(log) == 2
    collapsed = S.latest_by_id(log)
    assert len(collapsed) == 1
    assert collapsed[candidate.id].verdict.status is VerdictStatus.TRIVIAL


def test_a_corrupt_line_is_refused_and_located(tmp_path: Path) -> None:
    path = tmp_path / "candidates.jsonl"
    S.append_jsonl(path, _candidate(CandidateKind.CONSTANT))
    with path.open("a", encoding="utf-8") as handle:
        handle.write("\n")  # blank lines are skipped, not fatal
        handle.write("{not json}\n")
    with pytest.raises(ValidationError, match="line 3"):
        S.read_jsonl(path)


def test_equal_ids_imply_the_same_claim() -> None:
    """The direction the metrics layer relies on when it counts by id."""
    left = _candidate(CandidateKind.CONSTANT)
    right = _candidate(CandidateKind.CONSTANT, label="found again", evidence={"uncertainty": 1e-20})
    assert left.id == right.id
    assert S.same_claim(left, right)


def test_a_stored_id_that_disagrees_with_its_claim_is_refused() -> None:
    record = _candidate(CandidateKind.CONSTANT).to_dict()
    record["claim"]["value"] = 0.5
    with pytest.raises(ValidationError, match="does not match"):
        S.from_dict(record)
    record.pop("id")
    assert S.from_dict(record).claim["value"] == 0.5


def test_unknown_top_level_keys_are_tolerated_but_unknown_claim_keys_are_not() -> None:
    record = _candidate(CandidateKind.CONSTANT).to_dict()
    record["a_field_from_a_later_minor_version"] = {"x": 1}
    assert S.from_dict(record).id == _candidate(CandidateKind.CONSTANT).id
    record2 = _candidate(CandidateKind.CONSTANT).to_dict()
    record2["claim"]["stray"] = 1
    record2.pop("id")
    with pytest.raises(ValidationError):
        S.from_dict(record2)


def test_version_1_0_record_defaults_to_no_graph_edges_without_moving_its_id() -> None:
    record = _candidate(CandidateKind.CONSTANT).to_dict()
    original_id = record["id"]
    record["schema_version"] = "1.0"
    record.pop("related_to")
    restored = S.from_dict(record)
    assert restored.schema_version == "1.0"
    assert restored.related_to == ()
    assert restored.id == original_id


MALFORMED_RECORDS: list[tuple[str, dict]] = [
    ("missing-kind", {"kind": None}),
    ("unknown-kind", {"kind": "vibe"}),
    ("claim-not-a-mapping", {"claim": ["subject", "q"]}),
    ("future-major", {"schema_version": "2.0"}),
    ("unreadable-version", {"schema_version": "one point nought"}),
]


@pytest.mark.parametrize(
    "name,patch", MALFORMED_RECORDS, ids=[case[0] for case in MALFORMED_RECORDS]
)
def test_malformed_records_are_refused(name: str, patch: dict) -> None:
    record = _candidate(CandidateKind.CONSTANT).to_dict()
    record.pop("id")
    record.update(patch)
    if record.get("kind") is None:
        record.pop("kind")
    with pytest.raises(ValidationError):
        S.from_dict(record)


def test_missing_provenance_is_refused() -> None:
    record = _candidate(CandidateKind.CONSTANT).to_dict()
    record.pop("id")
    record.pop("provenance")
    with pytest.raises(ValidationError, match="provenance"):
        S.from_dict(record)
    record["provenance"] = {"generator": "g"}
    with pytest.raises(ValidationError, match="missing"):
        S.from_dict(record)


def test_non_finite_numbers_cannot_enter_a_record() -> None:
    claim, evidence = GOOD_PAYLOADS[CandidateKind.CONSTANT]
    bad = Candidate(
        kind=CandidateKind.CONSTANT,
        claim=dict(claim),
        evidence=dict(evidence) | {"residual": math.inf},
        provenance=_provenance(),
    )
    with pytest.raises(ValidationError, match="non-finite"):
        S.validate_candidate(bad)
    # a non-finite number in the *claim* cannot even be hashed, so the
    # candidate never comes into existence
    with pytest.raises(ValidationError, match="finite"):
        Candidate(
            kind=CandidateKind.CONSTANT,
            claim={"subject": "q", "value": math.nan},
            evidence=dict(evidence),
            provenance=_provenance(),
        )


def test_machine_local_paths_may_never_be_recorded() -> None:
    claim, evidence = GOOD_PAYLOADS[CandidateKind.CONSTANT]
    candidate = Candidate(
        kind=CandidateKind.CONSTANT,
        claim=dict(claim),
        evidence=dict(evidence) | {"source_file": "/Users/someone/lab/data.json"},
        provenance=_provenance(),
    )
    with pytest.raises(ValidationError, match="machine-local"):
        S.validate_candidate(candidate)
    with pytest.raises(ValidationError, match="machine-local"):
        S.validate_provenance(_provenance(parameters={"path": "/home/someone/x"}))


def test_claim_keys_must_be_identifiers() -> None:
    candidate = Candidate(
        kind=CandidateKind.CONSTANT,
        claim={"subject": "q", "value": 1.0, "not an identifier": 1},
        evidence={"uncertainty": 1e-6},
        provenance=_provenance(),
    )
    assert any("identifier" in r or "not part of this kind" in r for r in candidate.reasons())


def test_migrate_record_refuses_an_unknown_major() -> None:
    with pytest.raises(ValidationError, match="not supported"):
        S.migrate_record({"schema_version": "2.0"})
    assert S.migrate_record({"schema_version": S.SCHEMA_VERSION})


def test_schema_history_matches_the_declared_version() -> None:
    assert S.SCHEMA_VERSION == f"{S.SCHEMA_MAJOR}.{S.SCHEMA_MINOR}"
    assert S.SCHEMA_HISTORY[-1]["version"] == S.SCHEMA_VERSION
    assert len({entry["version"] for entry in S.SCHEMA_HISTORY}) == len(S.SCHEMA_HISTORY)


def test_public_surface_is_declared_and_complete() -> None:
    for name in S.__all__:
        assert hasattr(S, name), f"__all__ names {name}, which does not exist"
    assert len(set(S.__all__)) == len(S.__all__)


# ---------------------------------------------------------------------------
# 5. provenance
# ---------------------------------------------------------------------------


def test_capture_provenance_records_a_revision_inside_this_checkout() -> None:
    provenance = S.capture_provenance(
        generator="unit",
        generator_version="0.1.0",
        lab_object="package.module.quantity",
        precision=Precision(kind="dps", value=25),
    )
    S.validate_provenance(provenance)
    assert provenance.code_revision_source in ("git", "unavailable")
    if provenance.code_revision_source == "git":
        assert re.fullmatch(r"[0-9a-f]{7,64}", provenance.code_revision)
        assert isinstance(provenance.code_dirty, bool)
    else:  # pragma: no cover - only outside a checkout
        assert provenance.code_revision is None
    assert provenance.runtime["python"]
    assert provenance.captured_at.endswith("+00:00")


def test_git_revision_degrades_gracefully_without_git(monkeypatch) -> None:
    def explode(*args, **kwargs):
        raise FileNotFoundError("git")

    monkeypatch.setattr(S.subprocess, "run", explode)
    assert S.git_revision() == (None, None, "unavailable")


def test_git_revision_degrades_gracefully_outside_a_repository(tmp_path: Path) -> None:
    revision, dirty, source = S.git_revision(tmp_path)
    if source == "git":  # pragma: no cover - only if the temp dir sits in a checkout
        pytest.skip("temporary directory is itself inside a repository")
    assert (revision, dirty, source) == (None, None, "unavailable")


def test_reproducibility_is_a_query_not_a_decoration() -> None:
    assert _provenance().is_reproducible()
    assert not _provenance(code_dirty=True).is_reproducible()
    assert not _provenance(
        code_revision=None, code_revision_source="unavailable"
    ).is_reproducible()
    assert not _provenance(stochastic=True, seed=7, code_dirty=None).is_reproducible()
    assert _provenance(stochastic=True, seed=7).is_reproducible()


def test_a_stochastic_generator_must_record_its_seed() -> None:
    with pytest.raises(ValidationError, match="seed"):
        S.validate_provenance(_provenance(stochastic=True, seed=None))
    S.validate_provenance(_provenance(stochastic=True, seed=20260802))


@pytest.mark.parametrize(
    "overrides,pattern",
    [
        ({"generator": "  "}, "generator must be named"),
        ({"generator_version": ""}, "generator_version"),
        ({"lab_object": "not a path"}, "lab_object"),
        ({"lab_object": "9bad.start"}, "lab_object"),
        ({"parameters": {"not an identifier": 1}}, "identifier"),
        ({"captured_at": ""}, "captured_at"),
        ({"captured_at": "yesterday"}, "captured_at"),
        ({"code_revision_source": "vibes"}, "code_revision_source"),
        ({"code_revision": "zzz", "code_revision_source": "git"}, "hexadecimal"),
        ({"runtime": {"python": 3.14}}, "runtime"),
        ({"duration_s": -1.0}, "duration_s"),
    ],
)
def test_provenance_validation_rejects_unreplayable_records(overrides, pattern) -> None:
    with pytest.raises(ValidationError, match=pattern):
        S.validate_provenance(_provenance(**overrides))


@pytest.mark.parametrize(
    "kwargs",
    [
        {"kind": "invented"},
        {"kind": "dps", "value": 0},
        {"kind": "dps", "value": None},
        {"kind": "float64", "value": 53},
    ],
)
def test_precision_is_a_closed_vocabulary(kwargs) -> None:
    with pytest.raises(ValidationError):
        Precision(**kwargs)


def test_precision_efforts_are_comparable_across_kinds() -> None:
    assert Precision("bits", 256).effort_digits() > Precision("dps", 30).effort_digits()
    assert Precision("dps", 30).effort_digits() > Precision("float64").effort_digits()
    assert Precision("exact").effort_digits() == math.inf
    assert Precision("dps", 30).to_dict()["value"] == 30
    assert Precision.from_dict(Precision("bits", 128).to_dict()) == Precision("bits", 128)


# ---------------------------------------------------------------------------
# 6. the already-known detector
# ---------------------------------------------------------------------------


def test_match_known_recognises_a_value_already_in_the_catalogue() -> None:
    candidate = _candidate(CandidateKind.CONSTANT)
    catalogue = [
        KnownEntry(
            id="entry.1",
            reference="Reference Work, p. 12",
            value="0.0230957089661210338",
            tolerance="1e-20",
        )
    ]
    verdict = S.match_known(candidate, catalogue)
    assert verdict is not None and verdict.status is VerdictStatus.KNOWN
    assert verdict.evidence["match_kind"] == "value"
    S.validate_verdict(verdict)


def test_match_known_recognises_a_statement_already_recorded() -> None:
    candidate = _candidate(CandidateKind.RELATION)
    catalogue = [
        KnownEntry(
            id="entry.2",
            reference="docs/07#identity",
            keys=("route.integral", "route.closed_form"),
        )
    ]
    verdict = S.match_known(candidate, catalogue)
    assert verdict is not None and verdict.evidence["match_kind"] == "statement"
    S.validate_verdict(verdict)


def test_match_known_returns_nothing_rather_than_a_weaker_status() -> None:
    candidate = _candidate(CandidateKind.CONSTANT)
    assert S.match_known(candidate, []) is None
    assert (
        S.match_known(
            candidate, [KnownEntry(id="e", reference="r", keys=("something.else",))]
        )
        is None
    )
    # a value that disagrees beyond the candidate's own error bound is not a match
    assert (
        S.match_known(
            candidate,
            [KnownEntry(id="e", reference="r", value="0.5", tolerance="1e-30")],
        )
        is None
    )


# ---------------------------------------------------------------------------
# 7. the seam: this module knows nothing about the laboratory
# ---------------------------------------------------------------------------

_DOMAIN_AGNOSTIC_FILES = ("schema.py", "__init__.py")
_FORBIDDEN_ROOTS = ("zeta", "numpy", "scipy", "mpmath", "sympy", "matplotlib", "flint")


def _discovery_dir() -> Path:
    return Path(S.__file__).resolve().parent


@pytest.mark.parametrize("filename", _DOMAIN_AGNOSTIC_FILES)
def test_domain_agnostic_modules_import_nothing_from_the_laboratory(filename) -> None:
    source = (_discovery_dir() / filename).read_text(encoding="utf-8")
    tree = ast.parse(source)
    imported: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            if node.level == 0 and node.module:
                imported.append(node.module)
    for name in imported:
        root = name.split(".")[0]
        assert root not in _FORBIDDEN_ROOTS, f"{filename} imports {name}"


def test_importing_the_schema_pulls_in_no_laboratory_module() -> None:
    root = _discovery_dir().parent
    code = (
        "import sys; sys.path.insert(0, %r);"
        "import discovery.schema;"
        "bad=[m for m in sys.modules if m.split('.')[0] in %r];"
        "print(','.join(sorted(bad)))" % (str(root), _FORBIDDEN_ROOTS)
    )
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, timeout=120
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "", f"schema dragged in: {result.stdout.strip()}"


@pytest.mark.parametrize("filename", _DOMAIN_AGNOSTIC_FILES)
def test_domain_agnostic_modules_contain_no_subject_matter_vocabulary(filename) -> None:
    """A leaked seam is usually a leaked *word* first."""
    source = (_discovery_dir() / filename).read_text(encoding="utf-8").lower()
    blocklist = (
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
    found = [word for word in blocklist if re.search(rf"\b{re.escape(word)}\b", source)]
    assert not found, f"{filename} mentions {found}"


# ---------------------------------------------------------------------------
# 6. adversarial review: the verdict's evidence is part of the record
# ---------------------------------------------------------------------------
#
# Section 3 of the design document promises two rules "on every record": no
# non-finite float anywhere, and no machine-local absolute path in any string.
# The first review of this module found that ``verdict.evidence`` was exempt
# from both, so a machine-local path reached the log silently and a NaN escaped
# as a ``ValueError`` out of ``json.dumps`` instead of a refusal naming the
# field. These pin the promise the document makes.


def _known_verdict(**evidence) -> Verdict:
    payload = {"references": ["a source"], "match_kind": "statement"}
    payload.update(evidence)
    return Verdict(
        status=VerdictStatus.KNOWN,
        decided_by="reviewer",
        decided_by_version="1",
        decided_at=_NOW,
        evidence=payload,
    )


def test_a_machine_local_path_in_the_verdict_evidence_is_refused() -> None:
    candidate = _candidate(CandidateKind.CONSTANT).with_verdict(
        _known_verdict(source_file="/Users/someone/private/notes.txt")
    )
    reasons = S.candidate_reasons(candidate)
    assert any("machine-local" in r for r in reasons), reasons
    assert any(r.startswith("verdict.evidence") for r in reasons), reasons
    with pytest.raises(ValidationError):
        S.validate_candidate(candidate)


@pytest.mark.parametrize("bad", [float("nan"), float("inf"), -float("inf")])
def test_a_non_finite_float_in_the_verdict_evidence_is_refused(bad) -> None:
    candidate = _candidate(CandidateKind.CONSTANT).with_verdict(_known_verdict(score=bad))
    reasons = S.candidate_reasons(candidate)
    assert any("non-finite" in r for r in reasons), reasons
    with pytest.raises(ValidationError):
        S.validate_candidate(candidate)


def test_a_nested_path_in_the_verdict_evidence_is_refused() -> None:
    candidate = _candidate(CandidateKind.CONSTANT).with_verdict(
        _known_verdict(detail={"files": ["/home/someone/run.log"]})
    )
    assert any("machine-local" in r for r in S.candidate_reasons(candidate))


def test_an_honest_verdict_evidence_still_validates() -> None:
    candidate = _candidate(CandidateKind.CONSTANT).with_verdict(
        _known_verdict(
            entry_id="euler-mascheroni-constant",
            defect=1e-30,
            tolerance=1e-18,
            match_kind="value",
            detail={"nested": [1, 2.5, "conjectures/ledger.jsonl", None, True]},
        )
    )
    assert S.candidate_reasons(candidate) == ()
    assert json.loads(S.to_json(candidate))["verdict"]["evidence"]["entry_id"]


def test_the_open_verdict_carries_no_evidence_so_nothing_to_check() -> None:
    candidate = _candidate(CandidateKind.CONSTANT)
    assert candidate.verdict.status is VerdictStatus.OPEN
    assert S.candidate_reasons(candidate) == ()
