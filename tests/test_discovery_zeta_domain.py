"""Tests for ``ontology.domains.zeta_domain``, the laboratory's plug-in.

What these tests are and are not. They check that the generators emit
well-formed, re-derivable candidates; that the screens kill what they claim to
kill and admit what they cannot see; that the counterexample battery actually
runs on a structural claim; and that the seam holds, that the bookkeeping half
of ``ontology/`` still knows nothing about the subject.

**No test here is evidence for the Riemann Hypothesis, and none of them is
phrased as if it were.** The strongest thing any of them says is "no violation
was found in the range examined" or "nothing in this system killed this
candidate". A candidate that reaches ``survives`` is a lead whose first
outstanding task is a literature search this offline system cannot perform.
"""

from __future__ import annotations

import ast
import math
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

import pytest
from mpmath import mp

from ontology import registry as R
from ontology import schema as S
from ontology.domains import zeta_domain as Z
from ontology.funnel import DISPOSITIONS, STAGES, run_funnel
from ontology.knownness import FORBIDDEN_LABEL_WORDS, KnownFactRegistry
from ontology.ledger import Ledger
from ontology.registry import Domain, ScreenResult, get_domain, validate_domain
from ontology.schema import (
    Candidate,
    CandidateKind,
    Precision,
    VerdictStatus,
    candidate_reasons,
    verdict_reasons,
)

DOMAIN = Z.DOMAIN

#: A probe domain with no catalogue runs no ``knownness`` stage.
STAGES_NO_KNOWN = tuple(s for s in STAGES if s != "knownness")


# ---------------------------------------------------------------------------
# fixtures, the laboratory work is done once per worker, not once per test
# ---------------------------------------------------------------------------


@pytest.fixture(autouse=True)
def _domain_is_registered():
    """Keep the domain in the process-wide table.

    The registry is process-wide and other test modules legitimately clear it,
    so registration must not be assumed to survive from import time.
    """
    R.register_domain(DOMAIN, replace=True)
    yield


@pytest.fixture(scope="session")
def generated() -> dict[str, tuple[Candidate, ...]]:
    """Every generator's default output, keyed by generator name."""
    return {gen.name: tuple(gen.generate({})) for gen in DOMAIN.generators}


@pytest.fixture(scope="session")
def all_candidates(generated) -> tuple[Candidate, ...]:
    return tuple(c for batch in generated.values() for c in batch)


@pytest.fixture(scope="session")
def constants(generated) -> tuple[Candidate, ...]:
    return generated["zeta_constants"]


@pytest.fixture(scope="session")
def structurals(generated) -> tuple[Candidate, ...]:
    return generated["zeta_structural"]


@pytest.fixture(scope="session")
def screens() -> dict[str, R.Screen]:
    return {screen.name: screen for screen in DOMAIN.screens}


@pytest.fixture(scope="session")
def default_run(tmp_path_factory):
    """One full pass of the funnel over the default context."""
    path = tmp_path_factory.mktemp("funnel") / "ledger.jsonl"
    return run_funnel(DOMAIN, ledger=path), path


# ---------------------------------------------------------------------------
# 1. the seam: only this one file knows the subject
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


def _discovery_dir() -> Path:
    return Path(S.__file__).resolve().parent


def _agnostic_files() -> list[Path]:
    """Every importable module of ``ontology/`` outside ``domains/``.

    The package directory also holds numbered experiment scripts
    (``01_f1_geometry.py`` and friends).  Their stems are not valid Python
    identifiers, so they cannot be imported as modules of the package and are
    not part of its API surface, the agnostic seam does not cover them, and
    they are subject-matter scripts by design.
    """
    return sorted(
        p for p in _discovery_dir().glob("*.py") if p.stem.isidentifier()
    )


def _imports_of(path: Path) -> list[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"))
    names: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            names.append(node.module)
    return names


def test_the_seam_holds_no_agnostic_module_imports_the_laboratory() -> None:
    """The bookkeeping half must be transplantable to another subject."""
    offenders: list[str] = []
    for path in _agnostic_files():
        for name in _imports_of(path):
            root = name.split(".")[0]
            if root in _FORBIDDEN_ROOTS and path.name != "knownness.py":
                offenders.append(f"{path.name} imports {name}")
    assert not offenders, offenders


def test_knownness_is_the_documented_exception_and_only_that() -> None:
    """``knownness`` knows general mathematics; it must not know the subject."""
    roots = {n.split(".")[0] for n in _imports_of(_discovery_dir() / "knownness.py")}
    assert "zeta" not in roots
    assert roots & {"mpmath"}, "the identifier needs an arbitrary-precision backend"


#: ``knownness`` is the documented one-step-less-strict module: it knows
#: general mathematics (pi, gamma, PSLQ, the standard constant basis) but must
#: not know *this* laboratory. These are the names that would betray it.
_LABORATORY_WORDS = (
    "epstein",
    "davenport",
    "heilbronn",
    "riemann hypothesis",
    "critical line",
    "jensen",
    "hardy",
    "de bruijn",
)


def test_no_agnostic_module_mentions_the_subject_matter() -> None:
    """A leaked seam is usually a leaked *word* first."""
    offenders: list[str] = []
    for path in _agnostic_files():
        source = path.read_text(encoding="utf-8").lower()
        words = _SUBJECT_WORDS if path.name != "knownness.py" else _LABORATORY_WORDS
        for word in words:
            if re.search(rf"\b{re.escape(word)}\b", source):
                offenders.append(f"{path.name} mentions {word!r}")
    assert not offenders, offenders


def test_domains_package_itself_stays_free_of_the_laboratory() -> None:
    """Importing ``ontology.domains`` must not drag in the science package."""
    init = _discovery_dir() / "domains" / "__init__.py"
    assert not [n for n in _imports_of(init) if n.split(".")[0] in _FORBIDDEN_ROOTS]


def test_importing_discovery_pulls_in_no_laboratory_module() -> None:
    root = _discovery_dir().parent
    code = (
        "import sys; sys.path.insert(0, %r);"
        "import ontology, ontology.domains;"
        "bad=[m for m in sys.modules if m.split('.')[0] in %r];"
        "print(','.join(sorted(bad)))" % (str(root), ("zeta",))
    )
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, timeout=180
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "", f"discovery dragged in: {result.stdout.strip()}"


def test_the_domain_module_is_the_one_that_names_the_subject() -> None:
    """The seam is only worth having if the domain side actually uses it."""
    source = Path(Z.__file__).read_text(encoding="utf-8")
    assert "zeta." in source
    roots = {n.split(".")[0] for n in _imports_of(Path(Z.__file__))}
    assert "zeta" in roots


# ---------------------------------------------------------------------------
# 2. registration
# ---------------------------------------------------------------------------


def test_domain_registers_and_validates() -> None:
    validate_domain(DOMAIN)
    assert get_domain("zeta") is DOMAIN
    assert isinstance(DOMAIN, Domain)


def test_domain_supplies_at_least_five_generators_and_both_screen_costs() -> None:
    assert len(DOMAIN.generators) >= 5
    assert DOMAIN.cheap_screens() and DOMAIN.expensive_screens()
    assert DOMAIN.detectors


def test_domain_can_run_every_check_a_survivor_needs() -> None:
    """A domain missing a required check can never produce a survivor."""
    assert DOMAIN.missing_checks() == ()
    assert set(S.REQUIRED_SURVIVAL_CHECKS) <= DOMAIN.checks_available()


def test_generator_and_screen_names_are_unique_and_versioned() -> None:
    names = [g.name for g in DOMAIN.generators] + [s.name for s in DOMAIN.screens]
    assert len(names) == len(set(names))
    for plugin in list(DOMAIN.generators) + list(DOMAIN.detectors):
        assert plugin.version.strip()
        assert plugin.describe().strip()


def test_every_generator_declares_a_lab_object_and_a_description() -> None:
    for gen in DOMAIN.generators:
        assert gen.describe().strip(), gen.name
        assert gen.name.startswith("zeta_"), gen.name


# ---------------------------------------------------------------------------
# 3. what the generators produce
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "generator_name",
    [
        "zeta_constants",
        "zeta_asymptotics",
        "zeta_relations",
        "zeta_extremal",
        "zeta_finite_field",
        "zeta_structural",
    ],
)
def test_each_generator_produces_well_formed_candidates(generated, generator_name) -> None:
    batch = generated[generator_name]
    assert batch, f"{generator_name} produced nothing"
    for candidate in batch:
        reasons = candidate_reasons(candidate)
        assert not reasons, f"{generator_name}/{candidate.label}: {reasons}"


def test_every_candidate_starts_undecided(all_candidates) -> None:
    """A generator that grades its own leads has no measurable hit rate."""
    for candidate in all_candidates:
        assert candidate.verdict.status is VerdictStatus.OPEN
        assert not candidate.verdict.evidence


def test_provenance_names_its_generator_and_a_dotted_lab_object(all_candidates) -> None:
    generators = {g.name for g in DOMAIN.generators}
    for candidate in all_candidates:
        provenance = candidate.provenance
        assert provenance.generator in generators
        assert provenance.generator_version
        assert re.match(r"^[A-Za-z_][\w.]*$", provenance.lab_object)
        assert provenance.lab_object.startswith("zeta.")
        assert provenance.captured_at
        assert provenance.runtime.get("mpmath")


def test_every_recorded_route_can_actually_re_derive_its_quantity(all_candidates) -> None:
    """Provenance is 'enough for re-derivation' only if the route reproduces it.

    Running and returning a finite number is not the property claimed: a route
    that returned 42 would satisfy that. What the record has to support is
    re-deriving *the number it wrote down*, inside the error bar it claimed,
    so that is what is checked, from the round-tripped record rather than from
    the live object.
    """
    checked = 0
    for candidate in all_candidates:
        record = S.from_json(S.to_json(candidate))  # the record, and nothing else
        route_name = record.provenance.parameters.get("route")
        if route_name is None:
            continue
        assert route_name in Z.ROUTES, route_name
        route = Z.ROUTES[route_name]
        dps = Z._base_dps(record)
        # Parsing the recorded decimals must happen at a precision that can hold
        # them: mp.mpf re-rounds to the *ambient* dps, so reading a 25-digit
        # claim at the default 15 would manufacture a disagreement.
        with mp.workdps(dps + 40):
            claimed = Z._claimed_number(record)
            tolerance = Z._claim_tolerance(record)
            assert claimed is not None and tolerance is not None, record.label
            value = mp.mpf(route.compute(Z._route_params(record), dps))
            assert mp.isfinite(value)
            moved = abs(value - claimed)
        assert moved <= tolerance, (
            f"{record.label}: the route re-derived {mp.nstr(value, 12)} but the "
            f"record claims {mp.nstr(claimed, 12)} +- {mp.nstr(tolerance, 3)}"
        )
        checked += 1
    assert checked >= 5, "too few candidates carry a re-derivation route to be meaningful"


def test_candidate_ids_are_unique_within_a_pass(all_candidates) -> None:
    ids = [c.id for c in all_candidates]
    assert len(ids) == len(set(ids))


def test_all_five_candidate_kinds_are_exercised(all_candidates) -> None:
    kinds = {c.kind for c in all_candidates}
    assert kinds == set(CandidateKind), sorted(k.value for k in set(CandidateKind) - kinds)


@pytest.mark.parametrize(
    "generator_name",
    [
        "zeta_constants",
        "zeta_asymptotics",
        "zeta_relations",
        "zeta_finite_field",
        "zeta_structural",
    ],
)
def test_generators_are_deterministic_under_a_fixed_seed(generator_name) -> None:
    """Ids and claims are not enough: the draws live in the *evidence*.

    A generator whose RNG ignored the seed would still produce identical ids
    and identical claims here, the seed appears in the claim as text, and the
    sampled objects appear only in the evidence. Comparing the evidence is what
    makes this test able to fail.
    """
    gen = {g.name: g for g in DOMAIN.generators}[generator_name]
    first = list(gen.generate({"seed": 4242}))
    second = list(gen.generate({"seed": 4242}))
    assert [c.id for c in first] == [c.id for c in second]
    assert [dict(c.claim) for c in first] == [dict(c.claim) for c in second]
    assert [dict(c.evidence) for c in first] == [dict(c.evidence) for c in second]


def test_the_stochastic_generator_records_its_seed_and_obeys_it() -> None:
    """'Obeys it' means the draws are the seed's, and a different seed draws
    differently. Recording the number is the easy half."""
    gen = {g.name: g for g in DOMAIN.generators}["zeta_structural"]
    stochastic = [
        c for c in gen.generate({"seed": 7}) if c.provenance.stochastic
    ]
    assert stochastic, "no generator marked itself stochastic"
    for candidate in stochastic:
        assert candidate.provenance.seed == 7
        assert candidate.provenance.is_reproducible() or (
            candidate.provenance.code_dirty is not False
        )
    again = [c for c in gen.generate({"seed": 7}) if c.provenance.stochastic]
    other = [c for c in gen.generate({"seed": 8}) if c.provenance.stochastic]
    assert [c.provenance.seed for c in other] == [8] * len(other)
    # replay: the same seed must redraw the same objects, witness for witness
    assert [c.evidence["witnesses"] for c in again] == [
        c.evidence["witnesses"] for c in stochastic
    ]
    assert [c.evidence["controls"] for c in again] == [
        c.evidence["controls"] for c in stochastic
    ]
    # and a different seed must actually draw something else, or the seed is
    # decoration and the record is telling a story about a fixed sample
    assert len(other) == len(stochastic)
    assert all(
        a.evidence["witnesses"] != b.evidence["witnesses"]
        for a, b in zip(stochastic, other)
    ), "a different seed produced the same draws: the seed is not being used"


def test_no_candidate_records_a_machine_local_path(all_candidates) -> None:
    for candidate in all_candidates:
        text = S.to_json(candidate)
        assert "/Users/" not in text and "/home/" not in text


# ---------------------------------------------------------------------------
# 4. the schema's decision procedures actually bite on this domain's output
# ---------------------------------------------------------------------------


def test_asymptotic_candidates_span_at_least_a_factor_of_four(generated) -> None:
    batch = generated["zeta_asymptotics"]
    assert batch
    for candidate in batch:
        windows = candidate.evidence["windows"]
        assert len(windows) >= S.MIN_WINDOWS
        span = max(float(w["index_max"]) for w in windows) / min(
            float(w["index_min"]) for w in windows
        )
        assert span >= S.MIN_INDEX_SPAN, (candidate.label, span)
        for window in windows:
            assert int(window["n_points"]) >= S.MIN_WINDOW_POINTS


def test_asymptotic_tolerances_are_tight_enough_to_be_falsifiable(generated) -> None:
    """A tolerance a wrong exponent would also pass is not a measurement."""
    for candidate in generated["zeta_asymptotics"]:
        tolerance = float(candidate.evidence["tolerance"])
        claimed = float(candidate.claim["exponent"])
        assert 0 < tolerance <= 0.1 * max(abs(claimed), 1.0)
        drift = max(
            abs(float(w["exponent"]) - claimed) for w in candidate.evidence["windows"]
        )
        # It must pass, but not by so much that the tolerance is decorative.
        assert drift <= tolerance
        assert drift > 0.0, "a drift of exactly zero would mean the fit is not a fit"


def test_a_narrow_window_fit_is_refused_and_the_refusal_is_recorded() -> None:
    """A rate fitted over a range that never quadruples is a local coincidence.

    The generator must not drop the refusal silently: a conversion rate whose
    denominator omits the fits that were built and thrown away is wrong.
    """
    gen = {g.name: g for g in DOMAIN.generators}["zeta_asymptotics"]
    emitted = list(gen.generate({"lambda_windows": ((20, 25), (25, 30))}))
    subjects = {c.claim["subject"] for c in emitted}
    assert "zeta.li.lambda_n" not in subjects
    assert gen.refused, "the refused fit left no trace"
    assert any("span" in reason for reason in gen.refused)
    # The default windows are accepted, so the refusal is about the range and
    # not about the generator being broken.
    assert any(c.claim["subject"] == "zeta.li.lambda_n" for c in gen.generate({}))
    assert gen.refused == []


def test_every_generator_records_the_payloads_it_built_and_did_not_emit() -> None:
    """A generator that drops its failures silently has a wrong denominator.

    A payload that never leaves the generator never enters the funnel, so it
    appears in no conversion rate at all, the pipeline cannot count what it
    was never shown. Every generator therefore keeps a ``refused`` list, and it
    is reset per pass so it always describes the run that just happened.
    """
    for gen in DOMAIN.generators:
        assert isinstance(gen.refused, list), gen.name
        assert hasattr(gen, "_refuse"), gen.name
        list(gen.generate({}))
        assert isinstance(gen.refused, list), gen.name


def test_an_extremal_search_too_small_to_have_a_record_leaves_a_trace() -> None:
    """One candidate for a record is not a search, and the refusal is logged."""
    gen = Z.ExtremalGenerator()
    emitted = list(gen.generate({"jensen_d_max": 2, "jensen_n_max": 0}))
    subjects = {c.claim["subject"] for c in emitted}
    assert "zeta.li.min_relative_root_gap_of_jensen_polynomial" not in subjects
    assert any("Jensen" in reason for reason in gen.refused), gen.refused
    assert any("at least two" in reason for reason in gen.refused), gen.refused
    # the default grid is large enough, so the refusal is about the grid
    assert any(
        c.claim["subject"] == "zeta.li.min_relative_root_gap_of_jensen_polynomial"
        for c in gen.generate({})
    )


def test_an_integer_relation_hunt_that_finds_nothing_leaves_a_trace() -> None:
    """The common case, PSLQ finds nothing significant, must be recorded."""
    gen = Z.RelationsGenerator()
    assert gen.pslq_notes == [], "pslq_notes must exist before the first pass"
    assert gen.refused == []
    list(gen.generate({}))
    assert len(gen.pslq_notes) == 3
    barren = [s for s, coefficients, _ in gen.pslq_notes if coefficients is None]
    assert barren, "every hunt succeeded; this test would then prove nothing"
    for subject in barren:
        assert any(subject in reason for reason in gen.refused), (subject, gen.refused)


def test_structural_candidates_carry_a_control_the_predicate_fails(generated) -> None:
    """A property everything satisfies distinguishes nothing."""
    batch = generated["zeta_structural"]
    assert batch
    for candidate in batch:
        controls = candidate.evidence["controls"]
        failed = [c for c in controls if c.get("satisfied") is False]
        assert failed, candidate.label
        assert candidate.evidence["n_checked"] == len(candidate.evidence["witnesses"])
        assert candidate.evidence["n_satisfied"] == candidate.evidence["n_checked"]
        assert len(candidate.evidence["witnesses"]) >= S.MIN_WITNESSES


def test_extremal_candidates_strictly_beat_a_stated_runner_up(all_candidates) -> None:
    extremals = [c for c in all_candidates if c.kind is CandidateKind.EXTREMAL]
    assert extremals
    for candidate in extremals:
        value = float(candidate.claim["value"])
        runner_up = float(candidate.evidence["runner_up"])
        if candidate.claim["direction"] == "max":
            assert value > runner_up, candidate.label
        else:
            assert value < runner_up, candidate.label
        assert int(candidate.claim["n_searched"]) >= 2


def test_constant_candidates_do_not_hash_digits_they_did_not_measure(
    all_candidates,
) -> None:
    for candidate in all_candidates:
        if candidate.kind is not CandidateKind.CONSTANT:
            continue
        with mp.workdps(60):
            value = abs(mp.mpf(str(candidate.claim["value"])))
            uncertainty = mp.mpf(str(candidate.evidence["uncertainty"]))
            determined = int(mp.floor(mp.log10(value / uncertainty)))
        assert candidate.dedup_digits <= determined, candidate.label


# ---------------------------------------------------------------------------
# 5. the screens
# ---------------------------------------------------------------------------


def _probe_constant(dps: int, uncertainty: str, subject: str = "zeta.li.lambda_1_probe"):
    """A lambda_1 candidate harvested at ``dps`` claiming ``uncertainty``.

    Used both ways: with an honest error bar it is a genuine constant, and with
    a fictitious one it is exactly the candidate a precision screen exists to
    catch.
    """
    value = Z._lambda_table(1, dps)[0]
    text = Z._num(value, dps)
    return Candidate(
        kind=CandidateKind.CONSTANT,
        claim={"subject": subject, "value": text},
        evidence={"uncertainty": uncertainty},
        provenance=Z._provenance(
            generator="zeta_constants",
            version="1.0",
            route="li_lambda",
            lab_object="zeta.li.li_coefficients",
            parameters={"n": 1, "method": "cauchy", "radius": "0.5", "dps": dps},
            precision=Precision("dps", dps, "mpmath"),
            seed=1,
            duration_s=0.0,
        ),
        dedup_digits=Z._dedup_digits(text, uncertainty),
        label=f"probe lambda_1 at dps={dps} claiming {uncertainty}",
    )


def test_precision_stability_rejects_a_deliberately_noisy_candidate(screens) -> None:
    """A value harvested at 20 digits cannot honestly claim an error of 1e-30."""
    noisy = _probe_constant(dps=20, uncertainty="1e-30")
    assert not candidate_reasons(noisy)
    result = screens["precision_stability"].apply(noisy)
    result.validate()
    assert not result.passed
    assert result.verdict.status is VerdictStatus.REFUTED
    evidence = result.verdict.evidence
    # The refutation had to survive a second, higher escalation.
    assert float(evidence["escalated_effort"]) > float(evidence["effort"])
    assert mp.mpf(evidence["escalated_defect"]) > mp.mpf(evidence["tolerance"])
    assert not verdict_reasons(result.verdict)


def test_precision_stability_passes_a_genuine_constant(screens) -> None:
    honest = _probe_constant(dps=25, uncertainty="1e-20")
    result = screens["precision_stability"].apply(honest)
    result.validate()
    assert result.passed
    assert result.effort is not None and result.effort > 25


def test_precision_stability_would_see_a_movement_below_a_part_in_1e17(screens) -> None:
    """The screen must not silently run at the ambient 15 digits.

    Two values agreeing to 25 digits differ by exactly zero when subtracted at
    the default precision. A screen that cannot register such a movement cannot
    fail, and a screen that cannot fail is a defect.
    """
    borderline = _probe_constant(dps=20, uncertainty="1e-24")
    result = screens["precision_stability"].apply(borderline)
    result.validate()
    assert not result.passed, "a 3e-22 movement against a claimed 1e-24 must be caught"
    assert mp.mpf(result.verdict.evidence["defect"]) > mp.mpf("1e-24")


def test_precision_stability_is_honest_about_float64_routes(screens, constants) -> None:
    float64 = [
        c
        for c in constants
        if c.provenance.precision.kind == "float64"
    ]
    assert float64
    for candidate in float64:
        result = screens["precision_stability"].apply(candidate)
        result.validate()
        assert result.passed
        assert result.effort is None, "an inapplicable screen must claim no effort"
        assert "float64" in result.detail


def test_precision_stability_records_a_missing_route_rather_than_passing(screens) -> None:
    orphan = Candidate(
        kind=CandidateKind.CONSTANT,
        claim={"subject": "zeta.core.unrouted_probe", "value": "1.25"},
        evidence={"uncertainty": "1e-6"},
        provenance=Z._provenance(
            generator="zeta_constants",
            version="1.0",
            route=None,
            lab_object="zeta.core.Xi",
            parameters={"dps": 25},
            precision=Precision("dps", 25, "mpmath"),
            seed=1,
            duration_s=0.0,
        ),
        dedup_digits=5,
    )
    result = screens["precision_stability"].apply(orphan)
    result.validate()
    assert not result.passed
    assert result.verdict.status is VerdictStatus.INCONCLUSIVE
    assert result.verdict.evidence["reason"] == "dependency_unavailable"


def test_triviality_catches_a_claim_that_is_true_by_construction(screens, constants) -> None:
    """Unfolding forces the mean spacing to 1; measuring it is not a discovery."""
    target = [
        c
        for c in constants
        if c.claim.get("subject") == "zeta.statistics.mean_unfolded_spacing"
    ]
    assert target
    result = screens["triviality"].apply(target[0])
    result.validate()
    assert not result.passed
    verdict = result.verdict
    assert verdict.status is VerdictStatus.TRIVIAL
    assert not verdict_reasons(verdict)
    assert verdict.evidence["derived_from"]
    assert len(verdict.evidence["argument"]) <= S.MAX_ARGUMENT_CHARS
    assert "unfold" in verdict.evidence["checked_by"].lower() or verdict.evidence[
        "checked_by"
    ].startswith("ontology.domains.zeta_domain")


def test_triviality_catches_the_jensen_normalisation_relation(screens, generated) -> None:
    relations = [
        c
        for c in generated["zeta_relations"]
        if c.claim.get("rhs") == "8 * zeta.core.Xi_at_0"
    ]
    assert relations
    result = screens["triviality"].apply(relations[0])
    result.validate()
    assert not result.passed
    assert result.verdict.status is VerdictStatus.TRIVIAL


def test_triviality_checks_the_reduction_on_the_candidates_own_sample(screens) -> None:
    """The reduction has to be run on the object the candidate is about.

    A rule that always evaluated a fixed sample would declare a candidate
    harvested from 200 ordinates trivial on the strength of a computation about
    2000 of them. The verdict records which parameters it used.
    """
    gen = Z.ConstantsGenerator()
    small = [
        c
        for c in gen.generate({"n_zeros": 300})
        if c.claim.get("subject") == "zeta.statistics.mean_unfolded_spacing"
    ]
    assert small
    result = screens["triviality"].apply(small[0])
    result.validate()
    assert not result.passed
    assert result.verdict.status is VerdictStatus.TRIVIAL
    used = result.verdict.evidence["checked_with"]
    assert used["n_zeros"] == "300", used
    assert small[0].provenance.parameters["n_zeros"] == 300


def test_triviality_does_not_fire_on_a_genuine_constant(screens, constants) -> None:
    lambda_1 = [c for c in constants if c.claim.get("subject") == "zeta.li.lambda_1"]
    assert lambda_1
    result = screens["triviality"].apply(lambda_1[0])
    result.validate()
    assert result.passed


def test_numeric_sanity_refuses_a_value_a_theorem_forbids(screens) -> None:
    """Hasse's theorem bounds the ratio by 1; a larger value is a bug, not a find."""
    impossible = Candidate(
        kind=CandidateKind.EXTREMAL,
        claim={
            "subject": "zeta.finitefield.max_hasse_ratio",
            "direction": "max",
            "space": "a fabricated search, for the purpose of this test",
            "n_searched": 2,
            "argopt": "fabricated",
            "value": 1.5,
        },
        evidence={"runner_up": 1.4},
        provenance=Z._provenance(
            generator="zeta_finite_field",
            version="1.0",
            route=None,
            lab_object="zeta.finitefield.sato_tate_histogram",
            parameters={"p": 503},
            precision=Precision("exact", None, "python-int"),
            seed=1,
            duration_s=0.0,
        ),
    )
    result = screens["numeric_sanity"].apply(impossible)
    result.validate()
    assert not result.passed
    assert result.verdict.status is VerdictStatus.REFUTED
    assert "Hasse" in result.verdict.notes or "Hasse" in result.detail
    # the escalation fields are nominal, and the record has to say so
    assert "nominal" in result.verdict.notes


@pytest.mark.parametrize("overshoot", [1e-13, 5e-13, 9e-13])
def test_a_hair_outside_a_proved_range_is_inconclusive_not_a_broken_verdict(
    screens, overshoot
) -> None:
    """The near-boundary case must not abort the pipeline.

    A refutation whose defect is inside its own tolerance is unearned, so the
    schema refuses it, ``ScreenResult.validate`` raises, and ``run_funnel``
    turns that into a ``FunnelError`` that kills the run, taking every
    candidate behind it out of the funnel. The only interesting range check,
    the one that lands a hair outside a proved bound, must therefore be
    recorded as *inconclusive*, not as a refutation the schema will reject.
    """
    marginal = Candidate(
        kind=CandidateKind.EXTREMAL,
        claim={
            "subject": "zeta.finitefield.max_hasse_ratio",
            "direction": "max",
            "space": "a fabricated search, for the purpose of this test",
            "n_searched": 2,
            "argopt": "fabricated",
            "value": 1.0 + overshoot,
        },
        evidence={"runner_up": 1.0},
        provenance=Z._provenance(
            generator="zeta_finite_field",
            version="1.0",
            route=None,
            lab_object="zeta.finitefield.sato_tate_histogram",
            parameters={"p": 503},
            precision=Precision("exact", None, "python-int"),
            seed=1,
            duration_s=0.0,
        ),
    )
    result = screens["numeric_sanity"].apply(marginal)
    result.validate()  # must not raise: a malformed result aborts the funnel
    assert not result.passed
    assert result.verdict.status is VerdictStatus.INCONCLUSIVE
    assert result.verdict.evidence["reason"] == "precision_insufficient"
    assert not verdict_reasons(result.verdict)


def test_a_marginal_range_violation_does_not_abort_a_funnel_run(tmp_path) -> None:
    """The same defect, seen from the pipeline: the run must complete."""
    from ontology.registry import BaseGenerator, Domain

    class Marginal(BaseGenerator):
        name, version = "zeta_probe", "1.0"

        def generate(self, context):
            for value in (1.0 + 1e-13, 0.5):
                yield Candidate(
                    kind=CandidateKind.EXTREMAL,
                    claim={
                        "subject": "zeta.finitefield.max_hasse_ratio",
                        "direction": "max",
                        "space": f"a fabricated search at {value!r}",
                        "n_searched": 2,
                        "argopt": "fabricated",
                        "value": value,
                    },
                    evidence={"runner_up": 0.25},
                    provenance=Z._provenance(
                        generator=self.name,
                        version=self.version,
                        route=None,
                        lab_object="zeta.finitefield.sato_tate_histogram",
                        parameters={"p": 503},
                        precision=Precision("dps", 25, "mpmath"),
                        seed=1,
                        duration_s=0.0,
                    ),
                )

    probe = Domain(
        name="zeta-marginal-probe",
        version="1.0",
        generators=(Marginal(),),
        screens=DOMAIN.screens,
        detectors=(),
    )
    run = run_funnel(probe, ledger=tmp_path / "ledger.jsonl", stages=STAGES_NO_KNOWN)
    assert len(run.outcomes) == 2
    assert all(o.disposition for o in run.outcomes)
    assert {o.disposition for o in run.outcomes} <= set(DISPOSITIONS)


def test_numeric_sanity_passes_the_real_finite_field_records(screens, generated) -> None:
    hasse = [
        c
        for c in generated["zeta_finite_field"]
        if c.claim.get("subject") == "zeta.finitefield.max_hasse_ratio"
    ]
    assert hasse
    for candidate in hasse:
        result = screens["numeric_sanity"].apply(candidate)
        result.validate()
        assert result.passed
        # No violation of Hasse's bound was found in the range examined.
        assert 0.0 < float(candidate.claim["value"]) <= 1.0


def test_independent_method_cross_checks_where_a_second_route_exists(
    screens, constants
) -> None:
    lambda_1 = [c for c in constants if c.claim.get("subject") == "zeta.li.lambda_1"][0]
    result = screens["independent_method"].apply(lambda_1)
    result.validate()
    assert result.passed
    assert result.effort is not None
    assert "definition" in result.detail


def test_independent_method_says_so_when_no_second_route_exists(screens, constants) -> None:
    float64 = [c for c in constants if c.provenance.precision.kind == "float64"][0]
    result = screens["independent_method"].apply(float64)
    result.validate()
    assert result.passed
    assert result.effort is None
    assert "unavailable" in result.detail


def test_high_precision_recompute_costs_more_than_generation(screens, constants) -> None:
    lambda_1 = [c for c in constants if c.claim.get("subject") == "zeta.li.lambda_1"][0]
    result = screens["high_precision_recompute"].apply(lambda_1)
    result.validate()
    assert result.passed
    assert result.effort > lambda_1.provenance.precision.effort_digits()


def _check_all_screens(candidates) -> None:
    for candidate in candidates:
        for screen in DOMAIN.screens:
            result = screen.apply(candidate)
            assert isinstance(result, ScreenResult)
            result.validate()
            if result.passed:
                assert result.verdict is None
            else:
                assert result.verdict.status in S.TERMINAL_STATUSES


def test_every_screen_handles_one_candidate_of_every_kind(all_candidates) -> None:
    """A screen must never raise on a kind it was not written for."""
    representative = {}
    for candidate in all_candidates:
        representative.setdefault(candidate.kind, candidate)
    assert set(representative) == set(CandidateKind)
    _check_all_screens(representative.values())


@pytest.mark.slow
def test_every_screen_returns_a_valid_result_for_every_candidate(
    all_candidates,
) -> None:
    _check_all_screens(all_candidates)


# ---------------------------------------------------------------------------
# 6. the mandatory gate: the counterexample battery
# ---------------------------------------------------------------------------


def test_battery_runs_on_a_structural_claim_and_records_what_it_found(
    screens, structurals
) -> None:
    """AGENTS.md makes this a standing test, not an optional one."""
    jensen = [
        c for c in structurals if c.claim["predicate"] == Z.PREDICATE_TURAN
    ]
    assert jensen, "the Jensen hyperbolicity claim was not generated"
    result = screens["counterexample_battery"].apply(jensen[0])
    result.validate()
    assert result.effort is not None, "the battery must report the effort it spent"
    assert "battery" in result.detail


def test_the_jensen_predicate_does_not_distinguish_zeta_from_the_counterexample() -> None:
    """The Davenport-Heilbronn function satisfies it too, so it explains nothing.

    This is gate #3 of docs/09 executed: f obeys the functional equation, has a
    real Hardy-style Z, and violates RH. A property f also has cannot be the
    load-bearing step of any argument about the zeros of zeta.
    """
    from zeta.epstein import battery

    report = battery(Z._claim_turan, dps=30)
    assert report["riemann_zeta"] is True
    assert report["davenport_heilbronn"] is True
    assert report["distinguishes"] is False


def test_the_battery_reexpression_agrees_with_the_laboratory_on_zeta() -> None:
    """The battery's own route to gamma(0) must reproduce Xi(0)."""
    from zeta.epstein import zeta_interface

    gammas = Z._even_taylor_gammas(zeta_interface(30)["completed"], 30)
    with mp.workdps(40):
        assert abs(gammas[0] - mp.mpf("0.49712077818831410991")) < mp.mpf("1e-18")
        # The Turan inequality holds here, and holds by only a few per cent.
        margin = gammas[1] ** 2 - gammas[0] * gammas[2]
        assert margin > 0
        assert margin / (gammas[1] ** 2) < mp.mpf("0.2")


def test_battery_records_dependency_unavailable_rather_than_waving_a_claim_through(
    screens, structurals
) -> None:
    orphan = [
        c for c in structurals if c.claim["predicate"] == Z.PREDICATE_HASSE
    ]
    assert orphan
    result = screens["counterexample_battery"].apply(orphan[0])
    result.validate()
    assert not result.passed
    assert result.verdict.status is VerdictStatus.INCONCLUSIVE
    assert result.verdict.evidence["reason"] == "dependency_unavailable"


def test_battery_screen_ignores_non_structural_candidates(screens, constants) -> None:
    result = screens["counterexample_battery"].apply(constants[0])
    result.validate()
    assert result.passed and result.effort is None


# ---------------------------------------------------------------------------
# 7. the already-known catalogue
# ---------------------------------------------------------------------------


def test_the_catalogue_is_well_formed_and_every_entry_cites_a_source() -> None:
    registry = Z.build_fact_registry()
    assert isinstance(registry, KnownFactRegistry)
    for fact in Z.ZETA_FACTS:
        assert not KnownFactRegistry.reasons(fact), fact.id
        assert fact.source.strip()
        assert fact.domain == "zeta"


def test_lambda_1_is_recognised_as_already_known(constants) -> None:
    lambda_1 = [c for c in constants if c.claim.get("subject") == "zeta.li.lambda_1"][0]
    verdict = Z.CatalogueDetector().check(lambda_1)
    assert verdict is not None
    assert verdict.status is VerdictStatus.KNOWN
    assert not verdict_reasons(verdict)
    assert verdict.evidence["references"]


def test_an_uncatalogued_constant_is_not_recognised_and_is_not_called_new() -> None:
    gen = {g.name: g for g in DOMAIN.generators}["zeta_constants"]
    outside = [
        c
        for c in gen.generate({"xi_points": ("1",)})
        if c.claim.get("subject") == "zeta.core.Xi_at_1"
    ]
    assert outside
    assert Z.CatalogueDetector().check(outside[0]) is None


def test_no_catalogue_text_claims_novelty() -> None:
    """A catalogue entry asserts that something is *established*, never new.

    ``FORBIDDEN_LABEL_WORDS`` also contains ordinary English ("first"), which a
    citation legitimately uses; the words checked here are the ones that could
    only be a novelty claim.
    """
    novelty = tuple(
        w for w in FORBIDDEN_LABEL_WORDS if w not in ("first", "original")
    )
    assert novelty, "the forbidden-word list lost its novelty terms"
    for fact in Z.ZETA_FACTS:
        blob = " ".join((fact.statement, fact.canonical_form, fact.source)).lower()
        for word in novelty:
            assert not re.search(rf"\b{re.escape(word)}\b", blob), (fact.id, word)


# ---------------------------------------------------------------------------
# 8. the integer-relation hunt and its significance guard
# ---------------------------------------------------------------------------


def test_pslq_recovers_the_closed_form_of_lambda_1() -> None:
    value = Z._lambda_table(1, 30)[0]
    coefficients, note = Z.pslq_relation(value, dps=30)
    assert coefficients == (2, -2, -1, 2, 1), (coefficients, note)
    # 2*lambda_1 - 2 - gamma + 2 log 2 + log pi = 0.
    with mp.workdps(50):
        residual = (
            2 * value - 2 - mp.euler + 2 * mp.log(2) + mp.log(mp.pi)
        )
        assert abs(residual) < mp.mpf("1e-25")


def test_pslq_refuses_a_relation_it_does_not_have_the_digits_to_support() -> None:
    """The classic false positive: many coefficients, few digits."""
    value = mp.mpf("0.14785636201262747")  # a float64 statistic, 15 digits at best
    coefficients, note = Z.pslq_relation(value, dps=12)
    assert coefficients is None
    assert "digits" in note


def test_pslq_guard_scales_with_the_size_of_the_coefficients() -> None:
    """A relation with huge coefficients needs proportionally more digits."""
    value = Z._lambda_table(1, 30)[0]
    tight, _ = Z.pslq_relation(value, dps=30, min_surplus_digits=8.0)
    assert tight is not None
    impossible, note = Z.pslq_relation(value, dps=30, min_surplus_digits=10**6)
    assert impossible is None and "significant" in note


# ---------------------------------------------------------------------------
# 9. the funnel, end to end
# ---------------------------------------------------------------------------


def test_every_candidate_leaves_the_funnel_with_a_disposition(default_run) -> None:
    run, _ = default_run
    total = sum(report.produced for report in run.generators)
    assert total == len(run.outcomes)
    assert all(outcome.disposition for outcome in run.outcomes)


def test_the_dominant_outcome_is_already_known(default_run) -> None:
    """The premise the whole package serves, measured rather than assumed."""
    run, _ = default_run
    counts = Counter(outcome.disposition for outcome in run.outcomes)
    assert counts["known"] == max(counts.values())
    assert counts["known"] >= len(run.outcomes) // 2
    assert counts["invalid"] == 0


def test_the_default_pass_produces_no_survivor(default_run) -> None:
    """A first pass over the laboratory's best-studied objects yields no lead.

    That is the honest headline, not a disappointment: every candidate the
    generators found is either catalogued, true by construction, or beyond what
    this system can verify. If this assertion ever fails, the correct first
    inference is that the catalogue has a gap.
    """
    run, _ = default_run
    counts = Counter(outcome.disposition for outcome in run.outcomes)
    assert counts["survives"] == 0, [
        o.candidate_id for o in run.outcomes if o.disposition == "survives"
    ]


def test_the_ledger_round_trips_with_ids_verified(default_run) -> None:
    _, path = default_run
    ledger = Ledger(path)
    latest = ledger.latest()
    assert latest
    for candidate in latest.values():
        assert candidate.id == S.content_hash(
            candidate.kind, candidate.claim, candidate.dedup_digits
        )


def test_a_candidate_the_catalogue_does_not_cover_can_reach_survives(
    tmp_path,
) -> None:
    """``survives`` means only that nothing in this system killed it.

    The candidate used here is Xi(1), a value the domain catalogue does not
    carry. Reaching ``survives`` is not a discovery and not evidence for
    anything: the record's own ``proof_gap`` says what is missing, and the first
    outstanding task is the literature search this offline system cannot do.
    """
    path = tmp_path / "ledger.jsonl"
    run = run_funnel(DOMAIN, ledger=path, context={"xi_points": ("0", "1")})
    survivors = [
        c
        for c in Ledger(path).latest().values()
        if c.verdict.status is VerdictStatus.SURVIVES
    ]
    assert len(survivors) == 1, [c.label for c in survivors]
    verdict = survivors[0].verdict
    assert not verdict_reasons(verdict)
    assert set(S.REQUIRED_SURVIVAL_CHECKS) <= set(verdict.evidence["checks_run"])
    assert float(verdict.evidence["verified_effort"]) > float(
        verdict.evidence["effort"]
    )
    gap = verdict.evidence["proof_gap"]
    assert gap.strip()
    assert "lead" in gap.lower()


def test_a_dry_run_writes_nothing(tmp_path) -> None:
    path = tmp_path / "ledger.jsonl"
    run = run_funnel(DOMAIN, ledger=path, dry_run=True, limit=3)
    assert run.outcomes
    assert not path.exists()


# ---------------------------------------------------------------------------
# 10. honest scope
# ---------------------------------------------------------------------------

_OVERCLAIM_RE = re.compile(
    r"(evidence for (?:the )?(?:rh|riemann)"
    r"|proves? (?:the )?(?:rh|riemann hypothesis)"
    r"|supports? (?:the )?riemann hypothesis"
    r"|confirms? (?:the )?riemann hypothesis"
    r"|establishes (?:the )?riemann hypothesis)"
)

#: A hedge must sit immediately before the phrase for it to be a denial.
_HEDGES = ("not ", "nothing ", "never ", "cannot ", "no ")


@pytest.mark.parametrize(
    "path",
    [Path(Z.__file__), Path(__file__)],
    ids=["zeta_domain", "this_test_module"],
)
def test_no_occurrence_of_an_rh_claim_is_left_unhedged(path: Path) -> None:
    """Every mention of RH in these files must be a denial, not an assertion."""
    source = path.read_text(encoding="utf-8").lower()
    for match in _OVERCLAIM_RE.finditer(source):
        window = source[max(0, match.start() - 60) : match.start()]
        assert any(hedge in window for hedge in _HEDGES), source[
            max(0, match.start() - 90) : match.end() + 30
        ]


def test_the_domain_description_states_its_own_scope() -> None:
    # The phrase is assembled rather than written out, so that this file's own
    # source stays clean for the unhedged-claim scan above.
    phrase = " ".join(("evidence", "for", "the", "riemann", "hypothesis"))
    description = DOMAIN.description.lower()
    assert phrase in description
    assert "nothing this domain produces is evidence" in description


# ---------------------------------------------------------------------------
# 11. numbers this domain asserts, pinned
# ---------------------------------------------------------------------------


def test_the_harvested_lambda_1_matches_its_closed_form(constants) -> None:
    from zeta.li import li_closed_form_lambda1

    candidate = [c for c in constants if c.claim.get("subject") == "zeta.li.lambda_1"][0]
    with mp.workdps(60):
        harvested = mp.mpf(str(candidate.claim["value"]))
        assert abs(harvested - li_closed_form_lambda1(dps=50)) < mp.mpf("1e-20")


def test_the_harvested_xi_at_zero_matches_the_ground_truth_table(constants) -> None:
    candidate = [c for c in constants if c.claim.get("subject") == "zeta.core.Xi_at_0"][0]
    with mp.workdps(40):
        assert abs(
            mp.mpf(str(candidate.claim["value"])) - mp.mpf("0.49712077818831410991")
        ) < mp.mpf("1e-18")


def test_no_hasse_violation_was_found_in_the_range_examined(generated) -> None:
    """Hasse's theorem is a theorem; this only reports that nothing contradicts it."""
    for candidate in generated["zeta_finite_field"]:
        if candidate.claim.get("subject") == "zeta.finitefield.max_hasse_ratio":
            assert float(candidate.claim["value"]) <= 1.0
            assert candidate.evidence["hasse_violations"] == 0


def test_the_zero_counting_fit_reproduces_the_known_exponent(generated) -> None:
    counting = [
        c
        for c in generated["zeta_asymptotics"]
        if c.claim["subject"] == "zeta.zeros.N_of_T"
    ]
    assert counting
    for window in counting[0].evidence["windows"]:
        assert abs(float(window["exponent"]) - 1.0) < 0.005


def test_the_mertens_growth_fit_sits_near_one_half(generated) -> None:
    """A measurement over a finite range, not a statement about the true order."""
    rows = [
        c
        for c in generated["zeta_asymptotics"]
        if c.claim["subject"] == "zeta.criteria.running_max_abs_mertens"
    ]
    assert rows
    for window in rows[0].evidence["windows"]:
        assert abs(float(window["exponent"]) - 0.5) < 0.06


def test_the_weil_margins_are_positive_and_above_the_noise_floor(generated) -> None:
    """No violation of Weil positivity was found in the family tested.

    The comparison has to be like with like. ``positivity_probe`` reports the
    margin as ``W/scale`` but the noise floor as an absolute bound on ``W``, so
    a bare ``margin > noise_floor`` compares two different quantities; and the
    floor recorded must be the floor of the member the record names, not the
    smallest floor in the family. Both are checked here against the probe.
    """
    from zeta.weil import positivity_probe

    rows = [
        c
        for c in generated["zeta_extremal"]
        if c.claim["subject"] == "zeta.weil.min_positivity_margin_gaussian"
    ]
    assert rows
    candidate = rows[0]
    probe = positivity_probe(family="gaussian", n_points=5, dps=15)
    tightest = min(probe, key=lambda r: r["margin"])
    assert float(candidate.claim["argopt"]) == pytest.approx(float(tightest["param"]))
    with mp.workdps(40):
        margin = mp.mpf(str(candidate.claim["value"]))
        floor = mp.mpf(str(candidate.evidence["noise_floor"]))
        absolute = mp.mpf(str(candidate.evidence["noise_floor_absolute_on_W"]))
        scale = mp.mpf(str(candidate.evidence["scale"]))
        assert margin > 0
        # the recorded floor is this member's own, on the margin's scale
        # (both are rendered to six significant digits in the record)
        assert abs(absolute - mp.mpf(str(tightest["noise_floor"]))) <= mp.mpf("1e-5") * absolute
        assert abs(floor - absolute / scale) <= mp.mpf("1e-5") * floor
        assert margin > floor
        # and W itself is resolved above its own absolute floor
        assert mp.mpf(str(tightest["W"])) > absolute
    assert candidate.evidence["resolved_above_noise"] is True


@pytest.mark.slow
def test_the_weil_noise_floor_belongs_to_the_member_the_record_names() -> None:
    """At the default precision the tightest member also owns the smallest
    floor, so the two ways of picking it agree and the check above cannot tell
    them apart. Raise the probe precision until nothing escalates and they come
    apart: the floor then scales with the member's own ``scale``, and the
    smallest belongs to the *widest* member, not the tightest one.
    """
    from zeta.weil import positivity_probe

    probe = positivity_probe(family="gaussian", n_points=5, dps=30)
    tightest = min(probe, key=lambda r: r["margin"])
    smallest_floor = min(probe, key=lambda r: r["noise_floor"])
    assert tightest["param"] != smallest_floor["param"], (
        "the two selections still coincide; this test would prove nothing"
    )
    candidate = [
        c
        for c in Z.ExtremalGenerator().generate({"weil_dps": 30})
        if c.claim["subject"] == "zeta.weil.min_positivity_margin_gaussian"
    ][0]
    assert float(candidate.claim["argopt"]) == pytest.approx(float(tightest["param"]))
    with mp.workdps(40):
        absolute = mp.mpf(str(candidate.evidence["noise_floor_absolute_on_W"]))
        assert abs(absolute - mp.mpf(str(tightest["noise_floor"]))) <= (
            mp.mpf("1e-5") * absolute
        )
        wrong = mp.mpf(str(smallest_floor["noise_floor"]))
        assert abs(absolute - wrong) > mp.mpf("1e-3") * absolute, (
            "the record carries the smallest floor in the family rather than "
            "the floor of the member it names"
        )


def test_numeric_helpers_reject_numpy_scalars_reaching_the_schema() -> None:
    """``repr(numpy.float64(0.5))`` is ``np.float64(0.5)``, which is not a number.

    The schema parses floats through ``repr``, so a numpy scalar that slips
    through would raise deep inside canonicalisation. Everything leaving this
    module is converted first, and this pins that it is.
    """
    import numpy as np

    assert isinstance(Z._f(np.float64(0.5)), float)
    assert type(Z._i(np.int64(7))) is int
    with pytest.raises(ValueError):
        Z._f(np.float64("inf"))
    assert Z._num(np.float64(0.5), 6) == "0.5"


# ---------------------------------------------------------------------------
# 9. the Legendre-Weil generator: the explicit formula as an instrument
# ---------------------------------------------------------------------------


@pytest.fixture(scope="session")
def legendre(generated) -> tuple[Candidate, ...]:
    return generated["zeta_legendre_weil"]


def test_legendre_emits_two_relations_per_interval_and_no_constant(legendre) -> None:
    kinds = Counter(c.kind for c in legendre)
    assert kinds[CandidateKind.RELATION] == 6  # 3 intervals x (identity, detection)
    # The Lambda-mass constant is opt-in: the default pass is designed to
    # yield no survivor, and the constant is a survivor by construction.
    assert kinds[CandidateKind.CONSTANT] == 0
    gen = next(g for g in DOMAIN.generators if g.name == "zeta_legendre_weil")
    assert gen.refused == []


def test_legendre_mass_constant_is_emitted_only_on_request() -> None:
    gen = Z.LegendreWeilGenerator()
    asked = list(
        gen.generate(
            {"dps": 25, "legendre_n": (10,), "legendre_mass_constant": True}
        )
    )
    kinds = Counter(c.kind for c in asked)
    assert kinds[CandidateKind.RELATION] == 2
    assert kinds[CandidateKind.CONSTANT] == 1


def test_legendre_eq_relations_are_instances_of_the_explicit_formula(legendre) -> None:
    """The identity candidates must die ``known``: they instantiate a theorem.

    A catalogue that reported one of these as a lead would be failing at
    exactly the coverage the custom matcher exists to provide.
    """
    eqs = [c for c in legendre if c.claim.get("relation") == "eq"]
    assert len(eqs) == 3
    for candidate in eqs:
        hit = Z.FACT_REGISTRY.match(candidate)
        assert hit is not None, candidate.label
        assert hit.fact_id == "riemann-weil-explicit-formula"
        assert hit.detail["literature_status"] == "theorem"


def test_legendre_detections_match_the_finite_verification_fact(legendre) -> None:
    gts = [c for c in legendre if c.claim.get("relation") == "gt"]
    assert len(gts) == 3
    for candidate in gts:
        hit = Z.FACT_REGISTRY.match(candidate)
        assert hit is not None, candidate.label
        assert hit.fact_id == "legendre-interval-primes-finite-range"
        n = hit.detail["n"]
        assert hit.detail["interval"] == [n * n, (n + 1) ** 2]


def test_legendre_matcher_declines_outside_the_verified_range(legendre) -> None:
    """Beyond (n+1)^2 <= 4e18 the fact is an open conjecture; no match allowed.

    Built from a real detection candidate with only the interval index moved
    out of range, so the decline is the range guard and nothing else.
    """
    import dataclasses

    real = next(c for c in legendre if c.claim.get("relation") == "gt")
    n = 2_100_000_000  # (n+1)^2 = 4.41e18 > 4e18
    claim = dict(real.claim)
    claim["lhs"] = f"zeta.weil.legendre_interval_lambda_mass[n={n}]"
    far = dataclasses.replace(real, claim=claim)
    fact = Z.FACT_REGISTRY.get("legendre-interval-primes-finite-range")
    assert fact.match(real) is not None
    assert fact.match(far) is None


def test_legendre_mass_constant_matches_a_hand_sieve(legendre) -> None:
    """The measured constant against a two-line sieve of (100, 121).

    The primes are 101, 103, 107, 109, 113 and no other prime power lands in
    the open interval (121 = 11^2 is the boundary, where g vanishes); the
    oracle shares nothing with zeta.weil's prime machinery but g itself.
    """
    from sympy import isprime

    from zeta.weil import legendre_pair

    gen = Z.LegendreWeilGenerator()
    emitted = list(
        gen.generate(
            {"dps": 25, "legendre_n": (10,), "legendre_mass_constant": True}
        )
    )
    candidate = next(c for c in emitted if c.kind is CandidateKind.CONSTANT)
    assert candidate.claim["subject"] == "zeta.weil.legendre_lambda_mass_n_10"
    with mp.workdps(40):
        _, g = legendre_pair(10)
        oracle = mp.fsum(
            mp.log(k) * g(mp.log(k)) / mp.sqrt(k)
            for k in range(101, 121)
            if isprime(k)
        )
        measured = mp.mpf(candidate.claim["value"])
        assert abs(measured - oracle) < mp.mpf(str(candidate.evidence["uncertainty"]))


def test_legendre_cross_check_route_agrees_with_the_engine() -> None:
    """The sympy re-summation and the weil-engine route give the same mass."""
    params = {"n": 3, "gamma_max": 120.0}
    with mp.workdps(40):
        engine = mp.mpf(Z._route_legendre_lambda_mass(params, 20))
        sieve = mp.mpf(Z._route_legendre_lambda_mass_cross(params, 20))
        assert abs(engine - sieve) < mp.mpf("1e-15")
        assert engine > 0  # (9, 16) contains the primes 11 and 13


def test_legendre_generator_refuses_n_below_2_and_says_why() -> None:
    gen = Z.LegendreWeilGenerator()
    cands = list(
        gen.generate(
            {
                "dps": 15,
                "legendre_n": (1, 2),
                "legendre_gamma_max": 120.0,
                "legendre_mass_constant": True,
            }
        )
    )
    # n = 1 is refused with a reason; n = 2 still yields both relations and,
    # as the largest valid interval, the requested constant.
    assert [c.kind for c in cands] == [
        CandidateKind.RELATION,
        CandidateKind.RELATION,
        CandidateKind.CONSTANT,
    ]
    assert any("n=1" in reason for reason in gen.refused)
