"""The asymmetry runner must be able to fail before it is allowed to measure.

`meta/evals/asymmetry.py` scores a checker against planted faults.  A scorer
like that has a characteristic way of going wrong: it reports plausible numbers
while measuring nothing, which is the same hollowness the experiment it serves
exists to study.  These tests are the negative controls.

Three of them pin defects that were actually present while the module was being
written, rather than hazards imagined afterwards:

* the artifacts rendered byte-identical to the clean control, because the
  renderer cut off above the depth the corruptions live at;
* Inspect coerces a string ``Score`` value to a float before metrics see it, so
  a metric comparing ``score.value == "unsound"`` reads zero for everything;
* a rate over an empty denominator reported as ``0.0`` would let an empty arm
  read as a perfect one.

Nothing here calls a real model.
"""

from __future__ import annotations

import math

import pytest

pytest.importorskip("inspect_ai", reason="needs inspect_ai (the eval runner)")

from inspect_ai import eval as inspect_eval  # noqa: E402
from inspect_ai.model import ModelOutput, get_model  # noqa: E402

from meta.evals.asymmetry import (  # noqa: E402
    SOUND,
    UNDECIDED,
    UNSOUND,
    _verdict_from,
    asymmetry_dataset,
    asymmetry_e0,
    build_artifacts,
)


# ---------------------------------------------------------------------------
# the artifacts
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def artifacts():
    return build_artifacts()


@pytest.fixture(scope="module")
def log_dir(tmp_path_factory):
    """Inspect writes an eval log per run; keep them out of the repo.

    ``log_dir=None`` does not suppress the write, it falls back to ``./logs``,
    so running the suite from the repo root once left ten ``.eval`` files in a
    directory nobody had gitignored.
    """
    return str(tmp_path_factory.mktemp("inspect-logs"))


def test_every_artifact_is_textually_distinct(artifacts):
    """The defect that was actually there: corruptions invisible in the text.

    Six of nine planted faults once hashed identical to the clean control
    because the renderer truncated above the depth the payloads live at.  A
    checker shown an unchanged battery and asked to find a planted fault is
    being measured on nothing.
    """
    digests = {}
    for artifact in artifacts:
        clash = digests.get(artifact.digest)
        assert clash is None, (
            f"{artifact.name!r} renders identically to {clash!r}: "
            "the planted fault is invisible in what the checker is shown"
        )
        digests[artifact.digest] = artifact.name


def test_there_is_a_clean_control(artifacts):
    """Without one, specificity is undefined and 'always hollow' scores perfectly."""
    clean = [a for a in artifacts if not a.planted]
    assert len(clean) == 1, "exactly one clean control is expected"
    assert clean[0].audit_catches is None


def test_ground_truth_is_derived_from_the_catalog_not_restated(artifacts):
    """``audit_catches`` must agree with ``SHAM_MODES``, its only source."""
    from harness.integrity import SHAM_MODES

    catalog = {mode.name: mode.caught_by is not None for mode in SHAM_MODES}
    for artifact in artifacts:
        if artifact.sham_mode is None:
            continue
        assert artifact.sham_mode in catalog, f"{artifact.sham_mode} left the catalog"
        assert artifact.audit_catches == catalog[artifact.sham_mode]


def test_the_dataset_covers_both_sides_of_the_audits_reach(artifacts):
    """E0 is only informative if some artifacts are audit blind spots."""
    planted = [a for a in artifacts if a.planted]
    assert any(a.audit_catches for a in planted), "no mechanically caught modes"
    assert any(a.audit_catches is False for a in planted), (
        "no audit blind spots in the dataset: E0 would measure nothing"
    )


def test_sample_metadata_carries_the_ground_truth(artifacts):
    dataset = asymmetry_dataset(artifacts)
    assert len(dataset) == len(artifacts)
    for sample in dataset:
        assert set(sample.metadata) >= {"planted", "sham_mode", "audit_catches", "digest"}


# ---------------------------------------------------------------------------
# verdict parsing
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "completion,expected",
    [
        ("SOUND\nthe rivals are structure matched", SOUND),
        ("UNSOUND\nevery detector is constant", UNSOUND),
        ("UNDECIDED", UNDECIDED),
        ("**UNSOUND**\nbecause...", UNSOUND),
        ("hollow\nthe lesions plant nothing", UNSOUND),
        ("", UNDECIDED),
        ("I would rather not say.", UNDECIDED),
    ],
)
def test_verdict_parsing(completion, expected):
    assert _verdict_from(completion) == expected


def test_an_unparseable_answer_is_undecided_not_a_detection():
    """Miscounting silence as a detection is the error that flatters the checker."""
    assert _verdict_from("...\n???") == UNDECIDED


# ---------------------------------------------------------------------------
# the measurements, driven by mock checkers
# ---------------------------------------------------------------------------


def _run(reply: str, artifacts, log_dir: str) -> dict[str, float]:
    """Run the task with a checker that always answers ``reply``."""
    dataset = asymmetry_dataset(artifacts)
    model = get_model(
        "mockllm/model",
        custom_outputs=[
            ModelOutput.from_content("mockllm/model", reply) for _ in range(len(dataset))
        ],
    )
    log = inspect_eval(
        asymmetry_e0(artifacts), model=model, display="none", log_dir=log_dir, score=True
    )[0]
    assert log.status == "success", log.error
    return {name: m.value for name, m in log.results.scores[0].metrics.items()}


def test_a_checker_that_calls_everything_hollow_is_caught_by_specificity(artifacts, log_dir):
    """Detection 1.0 and false confidence 0.0, and still useless.

    This is the repo's own admission rule turned on the checker: a test that
    everything fails has distinguished nothing.
    """
    m = _run("UNSOUND\neverything is hollow", artifacts, log_dir)
    assert m["detection_rate"] == pytest.approx(1.0)
    assert m["false_confidence_rate"] == pytest.approx(0.0)
    assert m["specificity"] == pytest.approx(0.0), (
        "specificity is the only measure that punishes refusing everything"
    )
    assert m["blind_spot_detection"] == pytest.approx(1.0)


def test_a_checker_that_approves_everything_shows_maximal_false_confidence(artifacts, log_dir):
    m = _run("SOUND\nlooks fine", artifacts, log_dir)
    assert m["detection_rate"] == pytest.approx(0.0)
    assert m["false_confidence_rate"] == pytest.approx(1.0)
    assert m["specificity"] == pytest.approx(1.0)
    assert m["blind_spot_detection"] == pytest.approx(0.0)


def test_false_confidence_is_not_one_minus_detection(artifacts, log_dir):
    """The distinction the preregistration insists on, made concrete.

    A checker that declines every artifact detects nothing and is falsely
    confident about nothing.  Folding ``undecided`` into either bucket would
    make these two numbers sum to 1 and erase the difference.
    """
    m = _run("UNDECIDED\nI cannot tell", artifacts, log_dir)
    assert m["detection_rate"] == pytest.approx(0.0)
    assert m["false_confidence_rate"] == pytest.approx(0.0)
    assert m["undecided_rate"] == pytest.approx(1.0)
    assert m["detection_rate"] + m["false_confidence_rate"] != pytest.approx(1.0)


def test_metrics_read_metadata_because_inspect_coerces_score_values(artifacts, log_dir):
    """The trap, pinned.

    Inspect converts a string ``Score`` value to a float before metrics run, so
    ``"unsound"`` and ``"sound"`` both arrive as ``0.0``.  A metric comparing
    ``score.value`` to a verdict string reads zero for every sample and reports
    a plausible number.  If these two runs ever produce the same detection
    rate, the metrics have started reading the coerced value again.
    """
    hollow = _run("UNSOUND", artifacts, log_dir)
    fine = _run("SOUND", artifacts, log_dir)
    assert hollow["detection_rate"] != fine["detection_rate"], (
        "metrics appear to be reading the coerced Score value, not metadata"
    )
    assert hollow["detection_rate"] == pytest.approx(1.0)


def test_the_audit_baseline_is_reported_alongside(artifacts, log_dir):
    """The co-designed comparator, so the checker's number is never read alone."""
    m = _run("UNSOUND", artifacts, log_dir)
    planted = [a for a in artifacts if a.planted]
    expected = sum(1 for a in planted if a.audit_catches) / len(planted)
    assert m["audit_baseline"] == pytest.approx(expected)
    assert m["audit_baseline"] < 1.0, "the audit must have blind spots or E0 is moot"


def test_no_aggregate_score_is_offered(artifacts, log_dir):
    """Five measurements, never averaged into one.

    A single number would erase exactly the distinction the experiment exists
    to draw, in the same way ``dossier.status`` refuses to collapse its four
    kinds of support.
    """
    m = _run("UNSOUND", artifacts, log_dir)
    for forbidden in ("accuracy", "mean", "score", "total", "overall"):
        assert forbidden not in m, f"an aggregate {forbidden!r} crept in"


def test_a_rate_over_no_samples_is_undefined_not_zero(artifacts):
    """An empty arm must not read as a perfect one."""
    from meta.evals.asymmetry import _rate

    assert math.isnan(_rate(0, 0))
    assert _rate(1, 2) == pytest.approx(0.5)
