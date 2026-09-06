"""Department #3, pinned, the compiler department's wiring, backends and limits.

Every number this department reports is measured here rather than trusted from
a declaration, in the repository's usual habit. History worth knowing when
reading this file: the department spent its first day as an unregistered
candidate (git 2041d86; ``compiler/FINDINGS.md``), blocked on a detector blind
to the poison class and on three zeta-shaped assumptions in the shared
conformance suite. Admission cleared both: ``compiler.semantics`` gained a
second, poison-aware backend, and the conformance suite gained the ``probe``
convention of FINDINGS §7. Three groups of tests below carry that history:

* ``test_the_concrete_detector_remains_blind_to_the_poison_lesion`` still
  asserts rung 1's blindness, the arrival of a detector that sees the lesion
  does not un-measure the one that cannot, and the model tests beside it
  assert the new backend sees exactly what was invisible.
* The two-backend cross-checks pin the model against compiled output at every
  defined point of every fixture, and pin the model's rival disagreement
  counts against rung 1's. Where the two backends can both speak they must
  agree; where only the model can speak, that asymmetry is the measurement.
* ``test_the_department_is_registered`` replaced the probe-discipline test
  that asserted the opposite; the identity-lesion test now demonstrates that
  the strengthened conformance rule catches what the old rule passed.
"""

from __future__ import annotations

import os
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from compiler import catalog, semantics  # noqa: E402
from harness.departments import compiler_department as dept  # noqa: E402
from harness.protocol import (  # noqa: E402
    Battery,
    department_reasons,
    list_departments,
    run_ablation,
    run_battery,
    run_nulls,
    run_power,
)

#: Disagreements each known-invalid rewrite shows over the 65536-point domain.
#: Measured, then pinned; a change here means the fixtures or the backend moved.
RIVAL_DISAGREEMENTS = {
    "sdiv2_to_ashr": 16384,
    "udiv4_to_ashr": 32768,
    "slt_to_sign_of_difference": 16384,
}


# ---------------------------------------------------------------------------
# The backend, and the impossibility of a misleading green run
# ---------------------------------------------------------------------------


def test_a_semantic_backend_is_actually_available() -> None:
    """Fails loudly rather than skipping. A missing detector is not a pass.

    If this fails, nothing else in this file measured anything, and that must be
    visible in the headline rather than hidden in a skip count.
    """
    assert semantics.BACKEND == "clang.exhaustive_i8", (
        "no semantic backend: " + semantics.backend_status()["clang.exhaustive_i8"]
    )


def test_backend_status_names_the_absent_backends_too() -> None:
    status = semantics.backend_status()
    assert "alive2.refinement" in status
    assert status["alive2.refinement"].startswith(("available:", "ABSENT:"))
    assert status["pymodel.refinement_i8"].startswith("available:")


def test_without_clang_the_concrete_claim_raises_and_the_model_still_answers() -> None:
    """Self-attack: strip the PATH and confirm each backend fails honestly.

    The clang-based claim must raise rather than answer, a missing detector is
    not a pass. The model is pure Python and cannot be switched off by the
    environment, so it must keep answering; an environment-proof backend is
    exactly what the dormant-cross-check lesson in ROADMAP.md asks for.
    """
    code = textwrap.dedent(
        f"""
        import sys; sys.path.insert(0, {str(_REPO_ROOT)!r})
        from compiler import catalog, semantics
        assert semantics.available_backends() == ["pymodel.refinement_i8"], (
            semantics.available_backends()
        )
        try:
            catalog.claim_exhaustive_agreement(catalog.TARGET)
        except semantics.SemanticsUnavailable:
            print("RAISED")
        else:
            print("ANSWERED")
        print("MODEL", catalog.claim_model_refinement(catalog.TARGET))
        """
    )
    proc = subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True,
        text=True,
        env={"PATH": "/nonexistent", "HOME": os.environ.get("HOME", "/tmp")},
        timeout=120,
    )
    assert proc.stdout.split() == ["RAISED", "MODEL", "True"], proc.stdout + proc.stderr


def test_malformed_ir_is_rejected_and_never_read_as_agreement() -> None:
    broken = catalog.TARGET.with_target(
        "define i8 @f(i8 %x, i8 %y) {\n  %r = frobnicate i8 %x\n  ret i8 %r\n}\n"
    )
    with pytest.raises(semantics.IRRejected):
        catalog.claim_exhaustive_agreement(broken)


# ---------------------------------------------------------------------------
# The target and the rivals
# ---------------------------------------------------------------------------


def test_the_target_agrees_with_its_source_everywhere() -> None:
    report = semantics.agreement(catalog.TARGET.source, catalog.TARGET.target)
    assert report.agrees
    assert report.disagreements == 0
    assert report.domain_size == semantics.DOMAIN_SIZE == 65536
    assert report.level_disagreement == ()


@pytest.mark.parametrize("rival", catalog.RIVALS, ids=lambda r: r.name)
def test_every_rival_disagrees_by_the_pinned_amount(rival) -> None:
    report = semantics.agreement(rival.source, rival.target)
    assert not report.agrees
    assert report.disagreements == RIVAL_DISAGREEMENTS[rival.name]
    assert report.first_witness is not None


def test_every_rival_matches_the_target_on_instruction_count() -> None:
    """The reason the negative reference claim is worth stating."""
    for rival in catalog.RIVALS:
        assert rival.instructions_removed() == catalog.TARGET.instructions_removed() == 0


# ---------------------------------------------------------------------------
# The two reference claims, re-derived
# ---------------------------------------------------------------------------


def test_the_weak_claim_is_killed_by_every_rival() -> None:
    verdict = run_battery(dept.BATTERY, catalog.claim_no_more_instructions, name="no_more_instructions")
    assert verdict.target is True
    assert verdict.distinguishes is False
    assert verdict.shared_with == tuple(sorted(r.name for r in catalog.RIVALS))


def test_the_substantive_claim_distinguishes_the_target() -> None:
    verdict = run_battery(
        dept.BATTERY, catalog.claim_exhaustive_agreement, name="exhaustive_agreement_i8"
    )
    assert verdict.target is True
    assert verdict.shared_with == ()
    assert verdict.distinguishes is True
    assert verdict.errors == {}


def test_every_reference_claim_earns_its_declared_verdict() -> None:
    for reference in dept.REFERENCE_CLAIMS:
        verdict = run_battery(dept.BATTERY, reference.claim, name=reference.name)
        assert verdict.distinguishes == reference.distinguishes, reference.name


def test_feeding_a_rival_in_as_the_target_does_not_distinguish() -> None:
    """Self-attack: swap the roles and confirm the battery refuses to bless it."""
    swapped = Battery(
        name="swapped",
        target=dept.RIVALS[0],
        rivals=(dept.TARGET, *dept.RIVALS[1:]),
        decoys=dept.DECOYS,
        surrogates=dept.SURROGATES,
        lesions=dept.LESIONS,
    )
    verdict = run_battery(swapped, catalog.claim_exhaustive_agreement, name="exhaustive_agreement_i8")
    assert verdict.target is False
    assert verdict.distinguishes is False


# ---------------------------------------------------------------------------
# Ablation, the instrument that turns "our tests pass" into a measurement
# ---------------------------------------------------------------------------


def test_a_narrow_input_set_makes_an_invalid_rewrite_look_perfect() -> None:
    """The department's sharpest result, and the reason the decoys act on inputs.

    Over the whole i8 range the ``sdiv``-to-``ashr`` rewrite is wrong a quarter
    of the time. Over a same-sized test set that only reaches [0, 7] it is wrong
    never. Nothing about the rewrite changed.
    """
    rival = catalog.RIVALS[0]
    verdict = run_ablation(
        dept.BATTERY,
        dept.agreement_over(rival),
        tolerance=0.01,
        payload=list(dept.FULL_DOMAIN),
        name=f"agreement_of_{rival.name}",
    )
    assert verdict.baseline == pytest.approx(0.75)
    assert verdict.decoys["narrow_input_window"] == pytest.approx(1.0)
    assert verdict.decoys["constant_input_set"] == pytest.approx(1.0)
    assert verdict.survives is True
    assert verdict.unmoved_by == ()


def test_every_decoy_preserves_the_number_of_tests_it_destroys_the_reach_of() -> None:
    probe = list(range(2, 60))
    for decoy in dept.DECOYS:
        substituted = decoy.substitute(probe)
        assert len(substituted) == len(probe)
        assert substituted != probe


# ---------------------------------------------------------------------------
# Nulls
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_no_unguided_mutant_reproduces_the_targets_agreement() -> None:
    verdict = run_nulls(
        dept.BATTERY, dept.unguided_agreement, tolerance=0.01, name="exhaustive_agreement_fraction"
    )
    assert verdict.observed == pytest.approx(1.0)
    assert verdict.reproduced_by == ()
    assert verdict.survives is True
    for name, value in verdict.surrogates.items():
        assert value < 0.5, f"surrogate {name} agreed on {value:.3f} of the domain"


# ---------------------------------------------------------------------------
# Detector power, including the blind spot, pinned as a number
# ---------------------------------------------------------------------------


def test_the_lesion_magnitudes_span_four_orders() -> None:
    magnitudes = sorted({lesion.magnitude for lesion in dept.LESIONS})
    assert magnitudes == [1.0 / 65536.0, 1.0 / 256.0, 0.5]


@pytest.mark.parametrize(
    "spec", [s for s in catalog.LESIONS if s.visible_concretely], ids=lambda s: s.name
)
def test_a_visible_lesion_disagrees_by_exactly_its_declared_magnitude(spec) -> None:
    lesioned = spec.apply(catalog.LESION_HOST)
    report = semantics.agreement(lesioned.source, lesioned.target)
    assert 1.0 - report.fraction == pytest.approx(spec.magnitude)


def test_the_concrete_detector_remains_blind_to_the_poison_lesion() -> None:
    """Rung 1's blind spot is still a fact, still pinned.

    The predecessor of this test carried the instruction to delete it when a
    refinement backend arrived. The backend arrived; the *blindness of the
    concrete run* did not go anywhere, a compiled binary still returns the
    wrapped value, so its tables still agree, and un-pinning it would let
    someone read rung 1 verdicts as covering the poison class again.
    """
    spec = next(s for s in catalog.LESIONS if s.name == "nsw_flag_on_a_wrapping_shift")
    assert spec.visible_concretely is False
    lesioned = spec.apply(catalog.LESION_HOST)
    report = semantics.agreement(lesioned.source, lesioned.target)
    assert report.agrees is True
    assert report.disagreements == 0
    assert spec.magnitude == 0.5


def test_the_model_sees_the_poison_lesion_the_binary_cannot() -> None:
    """The admission blocker, cleared and measured.

    Same lesioned program as the blindness test above: the concrete tables
    agree exactly, and the model reports refinement failure on precisely half
    the domain, all of it in the poison class: 32768 poison violations, zero
    value violations. The two backends are not disagreeing; they are answering
    different questions, and only one of them can ask this one.
    """
    spec = next(s for s in catalog.LESIONS if s.name == "nsw_flag_on_a_wrapping_shift")
    lesioned = spec.apply(catalog.LESION_HOST)
    report = semantics.refinement(lesioned.source, lesioned.target)
    assert report.refines is False
    assert report.poison_violations == 32768
    assert report.value_violations == 0
    assert report.ub_violations == 0
    assert 1.0 - report.fraction == pytest.approx(spec.magnitude)
    assert "with respect to" in report.evidence


@pytest.mark.parametrize("op", ("udiv", "sdiv"))
def test_exact_division_marks_nonmultiples_poison(op: str) -> None:
    """LLVM ``exact`` division is poison whenever the remainder is nonzero."""
    ir = textwrap.dedent(
        f"""
        define i8 @f(i8 %x, i8 %y) {{
        entry:
          %r = {op} exact i8 %x, 2
          ret i8 %r
        }}
        """
    )
    table = semantics.model_output_table(ir)
    assert sum(value is semantics.POISON for value in table) == 32768
    defined = sum(
        value is not semantics.POISON and value is not semantics.UB for value in table
    )
    assert defined == 32768


def test_concrete_detector_power_is_reported_as_blindness_not_as_a_pass() -> None:
    verdict = run_power(
        dept.BATTERY, dept.concrete_detector, payload=catalog.LESION_HOST, name="exhaustive_i8_run"
    )
    assert verdict.has_power is False
    assert verdict.blind_to == ("nsw_flag_on_a_wrapping_shift",)
    assert verdict.smallest_detected == pytest.approx(1.0 / 65536.0)


def test_the_model_detector_has_full_power() -> None:
    """What rung 2 added, as the power difference between the two detectors."""
    verdict = run_power(
        dept.BATTERY, dept.model_detector, payload=catalog.LESION_HOST, name="model_refinement_i8"
    )
    assert verdict.has_power is True
    assert verdict.blind_to == ()
    assert verdict.smallest_detected == pytest.approx(1.0 / 65536.0)


@pytest.mark.parametrize("spec", catalog.LESIONS, ids=lambda s: s.name)
def test_every_lesion_violates_refinement_by_exactly_its_declared_magnitude(spec) -> None:
    """The model closes the two-units gap FINDINGS §3 recorded.

    ``magnitude`` was defined as the share of the domain on which the candidate
    stops being a valid stand-in, a property of the violation, chosen so the
    poison lesion's size stayed reportable while no detector could see it. The
    model measures exactly that quantity, for all four lesions, including the
    one whose concrete disagreement is zero.
    """
    lesioned = spec.apply(catalog.LESION_HOST)
    report = semantics.refinement(lesioned.source, lesioned.target)
    assert report.refines is False
    assert 1.0 - report.fraction == pytest.approx(spec.magnitude)


def test_a_lesion_that_would_plant_nothing_refuses_instead() -> None:
    """Self-attack: a lesion whose pattern is absent must not report as applied."""
    ghost = catalog.LesionSpec(
        name="ghost", magnitude=0.1, find="icmp ne i8 %q, %q", replace="x", visible_concretely=True
    )
    with pytest.raises(ValueError, match="would have planted nothing"):
        ghost.apply(catalog.LESION_HOST)


def test_the_two_optimisation_levels_are_not_an_independent_second_check() -> None:
    """Measured, not assumed: on these rivals -O2 caught nothing -O0 missed."""
    for rival in catalog.RIVALS:
        at_o0 = semantics.output_table(rival.source, "-O0") != semantics.output_table(rival.target, "-O0")
        at_o2 = semantics.output_table(rival.source, "-O2") != semantics.output_table(rival.target, "-O2")
        assert at_o0 == at_o2, f"{rival.name}: the levels disagreed, which would be new information"


# ---------------------------------------------------------------------------
# Admission record, and the strengthened conformance rule
# ---------------------------------------------------------------------------


def test_the_department_validates() -> None:
    assert department_reasons(dept.DEPARTMENT) == ()


def test_the_department_is_registered() -> None:
    """The graduation step, recorded. The predecessor of this test asserted the
    opposite while the candidate was a probe; both directions were deliberate.
    """
    from harness import departments as D

    assert D.KNOWN_DEPARTMENTS["compiler"] == "harness.departments.compiler_department"
    assert "compiler" in list_departments()


def test_the_lesions_and_surrogates_fit_the_generalised_audit_natively() -> None:
    """What the three ``conformance_leak`` tests this replaces documented.

    The shared audit used to call ``lesion.apply(())`` and ``len(sample)``,
    zeta's payload shapes. It now asks the instrument for a ``probe`` and
    checks ``apply(probe) != probe``. The shapes that could not fit the old
    audit are pinned here so the generalisation cannot be quietly reverted:
    these lesions still cannot take ``()``, and these samples still have no
    length.
    """
    with pytest.raises(AttributeError):
        dept.LESIONS[0].apply(())
    sample = dept.SURROGATES[0].sample()
    assert isinstance(sample, catalog.Transformation)
    with pytest.raises(TypeError):
        len(sample)  # type: ignore[arg-type]
    assert dept.LESIONS[0].probe == catalog.LESION_HOST
    assert dept.LESIONS[0].apply(dept.LESIONS[0].probe) != dept.LESIONS[0].probe


def test_the_strengthened_lesion_rule_catches_an_identity_lesion() -> None:
    """The reason the §7 change is a strengthening and not an accommodation.

    ``len(apply(())) > 0``, the old rule, is satisfied by a lesion that
    returns its input untouched; ``apply(probe) != probe``, the rule the
    conformance suite now applies, is not.
    """

    class IdentityLesion:
        name = "identity"
        magnitude = 0.5
        probe = catalog.LESION_HOST

        def describe(self) -> str:
            return "returns its input unchanged"

        def apply(self, payload):
            return payload

    lesion = IdentityLesion()
    assert len(tuple(lesion.apply(("planted",)))) > 0  # the old rule: passes
    assert lesion.apply(lesion.probe) == lesion.probe  # the new rule: caught


# ---------------------------------------------------------------------------
# The two backends check each other, the rigor.py habit, imported whole
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "fixture",
    sorted(p.stem for p in catalog.FIXTURES.glob("*.ll")),
)
def test_the_model_matches_the_compiled_output_on_every_fixture(fixture) -> None:
    """At every input where the model claims a defined value, the compiled
    program must produce that byte at every optimisation level. All ten
    fixtures are poison-free and UB-free, so all 65536 points constrain the
    check for each. A failure here means one backend is wrong about the
    program, and nothing built on either may be quoted until it is known which.
    """
    check = semantics.model_matches_clang(catalog.load_ir(fixture))
    assert check["comparable"] == semantics.DOMAIN_SIZE
    assert check["agrees"] is True, check["first_mismatch"]


@pytest.mark.parametrize("rival", catalog.RIVALS, ids=lambda r: r.name)
def test_the_model_reproduces_the_pinned_rival_disagreements(rival) -> None:
    """The two backends agree about how wrong each rival is, independently.

    The rivals are poison-free, so every refinement violation is a value
    violation and the model's count must equal the concrete backend's pinned
    disagreement count exactly.
    """
    report = semantics.refinement(rival.source, rival.target)
    assert report.refines is False
    assert report.violations == RIVAL_DISAGREEMENTS[rival.name]
    assert report.violations == report.value_violations


def test_the_model_refuses_ir_it_does_not_implement() -> None:
    """The model must not guess: an unknown opcode raises, and the exception is
    an :class:`IRRejected`, so callers treating 'the backend refused' uniformly
    stay correct."""
    with pytest.raises(semantics.ModelUnsupported):
        semantics.model_output_table(
            "define i8 @f(i8 %x, i8 %y) {\nentry:\n  %r = fadd i8 %x, %y\n  ret i8 %r\n}\n"
        )
    assert issubclass(semantics.ModelUnsupported, semantics.IRRejected)


# ---------------------------------------------------------------------------
# Vocabulary
# ---------------------------------------------------------------------------


def test_the_candidate_never_claims_a_reserved_or_overstated_word() -> None:
    """``certified`` belongs to ``zeta/rigor.py``; the rest are upgrades of evidence.

    Docstrings are exempt because this package's docstrings *discuss* the words
    in order to disclaim them, ``compiler/semantics.py`` says in prose that it
    may not borrow ``certified``, and a scan that failed on that sentence would
    be punishing the disclaimer. What is scanned is everything a caller could
    read back as a verdict: identifiers, and every string literal that is not a
    docstring.
    """
    import ast

    # Affirmative phrasings only. ``EVIDENCE_EXHAUSTIVE_I8`` says "not
    # equivalence, not refinement" and must keep saying it, so a bare
    # "equivalence" cannot be the thing that is banned.
    banned = (
        "certified",
        "formally verified",
        "proves equivalence",
        "is equivalent",
        "proven equivalent",
        "verified optimization",
        "verified optimisation",
        "guaranteed correct",
    )
    for path in sorted((_REPO_ROOT / "compiler").rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        docstrings = {
            id(node.body[0].value)
            for node in ast.walk(tree)
            if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
            and node.body
            and isinstance(node.body[0], ast.Expr)
            and isinstance(node.body[0].value, ast.Constant)
            and isinstance(node.body[0].value.value, str)
        }
        spoken: list[str] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                if id(node) not in docstrings:
                    spoken.append(node.value)
            elif isinstance(node, ast.Name):
                spoken.append(node.id)
            elif isinstance(node, (ast.FunctionDef, ast.ClassDef, ast.AsyncFunctionDef)):
                spoken.append(node.name)
            elif isinstance(node, ast.Attribute):
                spoken.append(node.attr)
        haystack = " ".join(spoken).lower()
        for word in banned:
            assert word not in haystack, (
                f"{path.name} could report the reserved or overstated word {word!r} to a caller"
            )
