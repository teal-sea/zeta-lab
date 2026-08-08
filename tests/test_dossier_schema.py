"""Tests for ``dossier.schema`` and ``dossier.status`` — the domain-neutral half.

What is pinned here:

1. **The four axes cannot be collapsed.** ``Support`` has no truth value, no
   aggregate and no ordering; asking for one raises. This is the experiment's
   central claim expressed as a test, because the failure mode it guards
   against is a caller writing ``if support:``.
2. **An assertion needs an artifact.** Any axis claiming positive support with
   no detail or no artifact is refused.
3. **Intent and discrimination are required.** A dossier with no intent, or
   with obligations that no plausible wrong definition would fail, is refused —
   those are the two things that make the record worth keeping.
4. **Identity is the object, not its progress.** The id is stable as evidence
   accumulates and changes when the definition changes.
5. **The seam holds.** The generic modules import nothing from any laboratory
   (AST scan), pull nothing into ``sys.modules`` (clean-interpreter check), and
   contain no subject-matter vocabulary (lexical scan).
"""

from __future__ import annotations

import ast
import re
import subprocess
import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from dossier import schema as S  # noqa: E402
from dossier.schema import (  # noqa: E402
    Definition,
    Dossier,
    DossierError,
    Intent,
    OpenQuestion,
    RejectedAlternative,
    SemanticObligation,
    dossier_id,
    dossier_reasons,
    validate_dossier,
)
from dossier.status import (  # noqa: E402
    AXES,
    AxisRecord,
    CertifiedStatus,
    FormalStatus,
    LiteratureStatus,
    NumericStatus,
    Support,
    support_reasons,
)


def _support(**overrides) -> Support:
    return Support(**overrides)


def _dossier(**overrides) -> Dossier:
    kwargs = dict(
        name="example",
        intent=Intent(purpose="a purpose"),
        definition=Definition(statement="f(x) = x"),
        obligations=(
            SemanticObligation(
                name="discriminates",
                statement="something a wrong definition fails",
                discriminating=True,
            ),
        ),
    )
    kwargs.update(overrides)
    return Dossier(**kwargs)


# ---------------------------------------------------------------------------
# 1. The four axes cannot be collapsed
# ---------------------------------------------------------------------------


def test_there_are_exactly_four_axes() -> None:
    assert AXES == ("numeric", "certified", "literature", "formal")


def test_support_has_no_truth_value() -> None:
    """The central test. A dossier is not verified or unverified."""
    with pytest.raises(TypeError, match="no truth value"):
        bool(_support())


def test_support_cannot_be_used_in_a_conditional() -> None:
    with pytest.raises(TypeError):
        if _support():  # pragma: no cover - the raise is the assertion
            pass


def test_support_exposes_no_aggregate() -> None:
    support = _support()
    for forbidden in ("is_verified", "verified", "score", "level", "percent", "complete"):
        assert not hasattr(support, forbidden), f"Support grew an aggregate: {forbidden}"


def test_every_axis_is_reachable_by_name() -> None:
    support = _support()
    for axis in AXES:
        assert isinstance(support.record(axis), AxisRecord)


def test_an_unknown_axis_is_refused() -> None:
    with pytest.raises(KeyError):
        _support().record("vibes")


def test_the_render_always_shows_all_four_axes() -> None:
    text = _support().render()
    for axis in AXES:
        assert axis in text


def test_the_defaults_assert_nothing() -> None:
    support = _support()
    assert support.numeric.status == NumericStatus.NOT_ATTEMPTED
    assert support.certified.status == CertifiedStatus.NOT_ATTEMPTED
    assert support.literature.status == LiteratureStatus.UNLOCATED
    assert support.formal.status == FormalStatus.NOT_ATTEMPTED


def test_certified_has_a_not_decided_value() -> None:
    """The safe failure mode, mirroring zeta.rigor.proven_sign returning 0."""
    assert CertifiedStatus.NOT_DECIDED in set(CertifiedStatus)


def test_formal_tracks_sorry_separately_from_proved() -> None:
    assert FormalStatus.STATED_WITH_SORRY != FormalStatus.PROVED


# ---------------------------------------------------------------------------
# 2. An assertion needs an artifact
# ---------------------------------------------------------------------------


def test_a_bare_positive_assertion_is_refused() -> None:
    reasons = support_reasons(
        _support(numeric=AxisRecord(status=NumericStatus.AGREES_TO_TOLERANCE))
    )
    assert any("no detail" in r for r in reasons), reasons
    assert any("no artifact" in r for r in reasons), reasons


def test_a_supported_assertion_with_evidence_passes() -> None:
    assert (
        support_reasons(
            _support(
                numeric=AxisRecord(
                    status=NumericStatus.AGREES_TO_TOLERANCE,
                    detail="agrees to 1e-30",
                    artifact="tests/test_x.py::test_y",
                )
            )
        )
        == ()
    )


def test_a_negative_status_needs_no_artifact() -> None:
    """Only assertions of support carry the burden; 'not attempted' does not."""
    assert support_reasons(_support(numeric=AxisRecord(status=NumericStatus.DISAGREES))) == ()


def test_an_invalid_status_string_is_refused() -> None:
    reasons = support_reasons(_support(formal=AxisRecord(status="mostly-proved")))
    assert any("not one of" in r for r in reasons), reasons


def test_unlocated_literature_is_not_novelty() -> None:
    """'Not found' is the absence of a lookup — it asserts nothing."""
    assert not AxisRecord(status=LiteratureStatus.UNLOCATED).asserts_support("literature")


# ---------------------------------------------------------------------------
# 3. Intent and discrimination are required
# ---------------------------------------------------------------------------


def test_a_complete_dossier_validates() -> None:
    assert dossier_reasons(_dossier()) == ()
    validate_dossier(_dossier())


def test_a_dossier_without_intent_is_refused() -> None:
    reasons = dossier_reasons(_dossier(intent=None))
    assert any("no intent" in r for r in reasons), reasons


def test_a_dossier_without_a_definition_is_refused() -> None:
    reasons = dossier_reasons(_dossier(definition=None))
    assert any("no definition" in r for r in reasons), reasons


def test_a_dossier_with_no_obligations_is_refused() -> None:
    reasons = dossier_reasons(_dossier(obligations=()))
    assert any("no semantic obligation" in r for r in reasons), reasons


def test_obligations_that_discriminate_nothing_are_refused() -> None:
    """A check no plausible wrong definition fails is a tautology in disguise."""
    reasons = dossier_reasons(
        _dossier(
            obligations=(
                SemanticObligation(name="trivial", statement="f is a function", discriminating=False),
            )
        )
    )
    assert any("discriminating" in r for r in reasons), reasons


def test_a_rejected_alternative_must_say_why() -> None:
    reasons = dossier_reasons(
        _dossier(rejected=(RejectedAlternative(statement="g(x) = x + 1", why_rejected=""),))
    )
    assert any("why_rejected" in r for r in reasons), reasons


def test_an_open_question_must_say_what_would_settle_it() -> None:
    reasons = dossier_reasons(
        _dossier(open_questions=(OpenQuestion(question="is it?", what_would_settle_it=""),))
    )
    assert any("what_would_settle_it" in r for r in reasons), reasons


def test_an_open_question_defaults_to_unresolved() -> None:
    """No resolution means still open; that must not, by itself, be a reason."""
    q = OpenQuestion(question="is it?", what_would_settle_it="a proof")
    assert q.resolution == ""
    assert dossier_reasons(_dossier(open_questions=(q,))) == ()


def test_a_blank_resolution_is_refused() -> None:
    """Whitespace-only resolution reads as resolved but answers nothing.

    Distinct from leaving ``resolution=""``: that means open. A resolution
    field that is *set* but empty of content is the schema's other failure
    mode — decoration, exactly what ``dossier_reasons`` exists to catch.
    """
    reasons = dossier_reasons(
        _dossier(
            open_questions=(
                OpenQuestion(question="is it?", what_would_settle_it="a proof", resolution="   "),
            )
        )
    )
    assert any("resolution" in r for r in reasons), reasons


def test_a_real_resolution_is_accepted() -> None:
    q = OpenQuestion(
        question="is it?", what_would_settle_it="a proof", resolution="yes, see test_x"
    )
    assert dossier_reasons(_dossier(open_questions=(q,))) == ()


def test_duplicate_obligation_names_are_refused() -> None:
    obligation = SemanticObligation(name="dup", statement="s", discriminating=True)
    reasons = dossier_reasons(_dossier(obligations=(obligation, obligation)))
    assert any("more than one obligation" in r for r in reasons), reasons


def test_an_unknown_schema_version_is_refused() -> None:
    reasons = dossier_reasons(_dossier(schema_version="99.0"))
    assert any("schema version" in r for r in reasons), reasons


def test_validate_raises_with_every_reason() -> None:
    with pytest.raises(DossierError) as excinfo:
        validate_dossier(_dossier(intent=None, obligations=()))
    message = str(excinfo.value)
    assert "no intent" in message and "no semantic obligation" in message


def test_obligation_lookup_by_name() -> None:
    assert _dossier().obligation("discriminates").discriminating is True
    with pytest.raises(KeyError):
        _dossier().obligation("absent")


# ---------------------------------------------------------------------------
# 4. Identity is the object, not its progress
# ---------------------------------------------------------------------------


def test_the_id_is_stable_as_evidence_accumulates() -> None:
    before = dossier_id(_dossier())
    after = dossier_id(
        _dossier(
            support=_support(
                numeric=AxisRecord(
                    status=NumericStatus.AGREES_TO_TOLERANCE, detail="d", artifact="a"
                )
            ),
            open_questions=(OpenQuestion(question="q", what_would_settle_it="w"),),
        )
    )
    assert before == after


def test_the_id_changes_when_the_definition_changes() -> None:
    assert dossier_id(_dossier()) != dossier_id(
        _dossier(definition=Definition(statement="f(x) = x + 1"))
    )


def test_the_id_changes_when_the_intent_changes() -> None:
    assert dossier_id(_dossier()) != dossier_id(_dossier(intent=Intent(purpose="something else")))


# ---------------------------------------------------------------------------
# 5. The seam
# ---------------------------------------------------------------------------

_FORBIDDEN_ROOTS = ("zeta", "numpy", "scipy", "mpmath", "sympy", "matplotlib", "flint")

_DOMAIN_AGNOSTIC_FILES = ("__init__.py", "schema.py", "status.py", "report.py")


def _dossier_dir() -> Path:
    return Path(S.__file__).resolve().parent


@pytest.mark.parametrize("filename", _DOMAIN_AGNOSTIC_FILES)
def test_the_generic_modules_import_nothing_from_the_laboratory(filename) -> None:
    tree = ast.parse((_dossier_dir() / filename).read_text(encoding="utf-8"))
    imported: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            imported.append(node.module)
    for name in imported:
        assert name.split(".")[0] not in _FORBIDDEN_ROOTS, f"{filename} imports {name}"


def test_importing_the_schema_pulls_in_no_laboratory_module() -> None:
    code = (
        "import sys; sys.path.insert(0, %r);"
        "import dossier;"
        "bad=[m for m in sys.modules if m.split('.')[0] in %r];"
        "print(','.join(sorted(bad)))" % (str(_REPO_ROOT), _FORBIDDEN_ROOTS)
    )
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, timeout=120
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "", f"laboratory modules imported: {result.stdout.strip()}"


#: Words that would mean the generic half had learned its subject.
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


@pytest.mark.parametrize("filename", _DOMAIN_AGNOSTIC_FILES)
def test_the_generic_modules_contain_no_subject_matter_vocabulary(filename) -> None:
    source = (_dossier_dir() / filename).read_text(encoding="utf-8").lower()
    for word in _SUBJECT_VOCABULARY:
        assert not re.search(rf"\b{re.escape(word)}\b", source), (
            f"{filename} names {word!r}: the schema has learned its subject"
        )


def test_the_subject_package_does_not_import_its_subjects_on_import() -> None:
    """A subject module drags in the laboratory; the package must not."""
    code = (
        "import sys; sys.path.insert(0, %r);"
        "import dossier.subjects;"
        "bad=[m for m in sys.modules if m.split('.')[0] in %r];"
        "print(','.join(sorted(bad)))" % (str(_REPO_ROOT), _FORBIDDEN_ROOTS)
    )
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, timeout=120
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == ""


def test_no_second_ledger_or_verdict_vocabulary_was_invented() -> None:
    """Reuse, not reinvention: ontology owns verdicts and ledgers."""
    for filename in _DOMAIN_AGNOSTIC_FILES:
        source = (_dossier_dir() / filename).read_text(encoding="utf-8")
        tree = ast.parse(source)
        defined = {
            node.name
            for node in ast.walk(tree)
            if isinstance(node, (ast.ClassDef, ast.FunctionDef))
        }
        for banned in ("Verdict", "VerdictStatus", "Ledger", "Candidate", "Provenance"):
            assert banned not in defined, (
                f"{filename} defines {banned}, which ontology already owns"
            )
