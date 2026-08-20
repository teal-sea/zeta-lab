"""E0: does an *independent* checker catch what a co-designed audit cannot?

The question, and why it is worth one afternoon
-----------------------------------------------
`harness/integrity.py` audits a department's battery for hollowness.  It
catalogs fifteen ways a battery can measure nothing, and it is candid about its
own reach: six of those modes carry ``caught_by=None``, meaning no mechanical
check in the audit can see them.  Read the ``countermeasure`` field on those six
and the same phrase appears in every one of them, in different words:
*independent authorship*.  "a party that has not seen the payloads."  "a claim
author who never saw the detectors."

So this repository has concluded, six separate times, that independence is the
countermeasure to the thing its own audit cannot detect.  It has never measured
whether that is true.  `meta/asymmetry-experiment.md` says so plainly, and names
its own cheapest first step:

    Have an **independent** party, a model that has seen neither the audit nor
    the batteries' authors' reasoning, attempt to identify which batteries
    measure nothing.  Compare its detection rate against the audit's.

That is E0, and this module is its runner.  One number, and it discriminates
prediction P1 immediately: if the independent party also misses the blind
spots, independence is not the variable and the full factorial is premature.

What this module does and does not claim
----------------------------------------
It **runs** nothing on import and nothing in the test suite beyond a mock
model.  As of this writing **E0 has not been executed against a real model**,
and no result may be quoted from this file until it has.  The preregistration
is a scientific commitment: running it is a deliberate act with a chosen model
and a recorded digest, not a side effect of importing a module.

It covers measurements 1, 2, 3 and 4 of the five the preregistration names
(detection, false confidence, specificity, cost).  Measurement 5, conditional
detection lift, compares *two* checkers and is therefore out of scope for a
single-arm run; it needs two arms and is left for E1.

Three design points that are not decoration
--------------------------------------------
**The measures are never averaged.**  There is no aggregate score and no
``__bool__``, for the same reason `dossier/status.py` keeps its four kinds of
support apart and `meta/ledger.py` refuses to divide until the caller names a
numerator.  The preregistration is explicit that false confidence is *not* one
minus detection and that specificity is what stops a checker that refuses
everything from scoring perfectly.  A single number would erase exactly the
distinction the experiment exists to draw.

**The verdict is ternary**, ``sound`` / ``unsound`` / ``undecided``, following
``zeta.rigor.proven_sign`` returning 0 for "not decided".  A checker that
declines is not thereby wrong, and folding "undecided" into either bucket is
the failure mode the preregistration warns about.

**Ground truth is read from sample metadata, never from the score value.**
Inspect coerces a string ``Score`` value to a float before metrics see it
(``"unsound"`` and ``"sound"`` both arrive as ``0.0``), so a metric written the
obvious way reads zero for everything and reports a plausible-looking number.
``tests/test_meta_evals.py`` pins that trap.
"""

from __future__ import annotations

import dataclasses
import hashlib
import inspect as pyinspect
from collections.abc import Callable, Sequence
from typing import Any, Final

from inspect_ai import Task, task
from inspect_ai.dataset import MemoryDataset, Sample
from inspect_ai.scorer import SampleScore, Score, Value, metric, scorer
from inspect_ai.solver import generate, system_message

__all__ = [
    "SOUND",
    "UNSOUND",
    "UNDECIDED",
    "Artifact",
    "build_artifacts",
    "render_department",
    "asymmetry_dataset",
    "checker_verdict",
    "detection_rate",
    "false_confidence_rate",
    "specificity",
    "undecided_rate",
    "blind_spot_detection",
    "audit_baseline",
    "asymmetry_e0",
]

SOUND: Final = "sound"
UNSOUND: Final = "unsound"
UNDECIDED: Final = "undecided"

_VERDICTS: Final = (SOUND, UNSOUND, UNDECIDED)


# ---------------------------------------------------------------------------
# artifacts: real corrupted batteries, not toy fixtures
# ---------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class Artifact:
    """One battery shown to the checker, with the ground truth kept beside it.

    ``audit_catches`` is the co-designed comparator: whether
    ``harness/integrity.py`` detects this corruption mechanically.  It is
    ``False`` exactly for the modes the catalog declares as blind spots, and
    those are the samples E0 turns on.

    ``digest`` is the SHA-256 of the rendered text.  The preregistration
    requires blinding to be *derived from artifacts* rather than asserted, so a
    run records these and a reader can confirm the checker saw this bundle and
    not a later one.
    """

    name: str
    sham_mode: str | None
    planted: bool
    audit_catches: bool | None
    text: str

    @property
    def digest(self) -> str:
        return hashlib.sha256(self.text.encode("utf-8")).hexdigest()


_MAX_DEPTH: Final = 24


def _render_value(value: Any, depth: int = 0) -> str:
    """A battery as a human auditor would read it, callables included.

    Detectors are functions, so a structural dump alone would hide the thing
    most worth judging.  Their source is inlined where it can be recovered.

    The depth limit is generous on purpose.  An earlier version cut off at 4,
    which was shallower than the payloads the corruptions live in, and six of
    the nine planted faults rendered byte-identical to the clean control -- an
    eval that measures nothing, which is the exact failure mode this experiment
    studies.  ``tests/test_meta_evals.py`` pins every artifact's digest as
    distinct so that regression cannot come back quietly.
    """
    pad = "  " * depth
    if depth > _MAX_DEPTH:
        return f"{pad}<...>"
    if callable(value) and not isinstance(value, type):
        name = getattr(value, "__name__", repr(value))
        try:
            src = pyinspect.getsource(value)
        except (OSError, TypeError):
            return f"{pad}<callable {name}>"
        body = "\n".join(f"{pad}  {line}" for line in src.strip().splitlines())
        return f"{pad}<callable {name}>\n{body}"
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        lines = [f"{pad}{type(value).__name__}:"]
        for field in dataclasses.fields(value):
            lines.append(f"{pad}  {field.name}:")
            lines.append(_render_value(getattr(value, field.name), depth + 2))
        return "\n".join(lines)
    if isinstance(value, (list, tuple)) and not isinstance(value, str):
        if not value:
            return f"{pad}(none)"
        return "\n".join(_render_value(item, depth + 1) for item in value)
    if isinstance(value, dict):
        return "\n".join(
            f"{pad}{k}: {v!r}" for k, v in sorted(value.items(), key=lambda kv: str(kv[0]))
        )
    return f"{pad}{value!r}"


def render_department(department: Any) -> str:
    """The text a checker is shown for one department."""
    return _render_value(department)


def _mutators() -> list[tuple[str, str, Callable[[Any], Any]]]:
    """``(sham_mode, mutator_name, mutator)`` for every planted corruption.

    Only the modes `harness/shams.py` can actually plant are usable, which is a
    subset of the fifteen the catalog names.  The subset still spans both sides
    of the line that matters: modes the audit catches, and modes it declares
    itself blind to.
    """
    from harness import shams

    pairs = [
        ("constant-true-detector", "with_constant_detector"),
        ("target-as-rival", "with_target_as_rival"),
        ("inert-lesion", "with_inert_lesions"),
        ("dropped-hardest-lesion", "without_hardest_lesion"),
        ("key-asymmetry-label-leak", "with_leaked_label"),
        ("co-designed-calibration", "with_vacuous_calibration"),
        ("distant-rivals", "with_distant_rivals"),
        ("detector-is-the-claim", "with_detector_as_claim"),
        ("agreeable-absent-field-oracle", "with_agreeable_absent_fields"),
    ]
    out = []
    for mode, fn_name in pairs:
        fn = getattr(shams, fn_name, None)
        if fn is not None:
            out.append((mode, fn_name, fn))
    return out


def _audit_catches(mode: str) -> bool:
    """True when `harness/integrity.py` detects this mode mechanically.

    Derived from the catalog rather than restated here: a mode with
    ``caught_by=None`` is one of the audit's declared blind spots.
    """
    from harness.integrity import SHAM_MODES

    for entry in SHAM_MODES:
        if entry.name == mode:
            return entry.caught_by is not None
    raise KeyError(f"{mode!r} is not in SHAM_MODES")


def build_artifacts(department: Any | None = None) -> list[Artifact]:
    """One clean control plus one corrupted copy per plantable sham mode.

    The clean control is not optional.  Without it *specificity* cannot be
    measured, and a checker that calls everything hollow scores perfectly on
    detection and false confidence while being useless -- which is the repo's
    own admission rule (``zeta.epstein.battery``) applied to the checker.
    """
    if department is None:
        from harness.departments.zeta_department import DEPARTMENT as department

    artifacts = [
        Artifact(
            name="clean",
            sham_mode=None,
            planted=False,
            audit_catches=None,
            text=render_department(department),
        )
    ]
    for mode, _fn_name, mutate in _mutators():
        corrupted = mutate(department)
        artifacts.append(
            Artifact(
                name=mode,
                sham_mode=mode,
                planted=True,
                audit_catches=_audit_catches(mode),
                text=render_department(corrupted),
            )
        )
    return artifacts


# ---------------------------------------------------------------------------
# the prompt: what an independent checker is told, and what it is not
# ---------------------------------------------------------------------------

CHECKER_SYSTEM_MESSAGE: Final = """\
You are auditing a scientific test battery.

A battery exists to make a claim falsifiable: it names a target, a set of
rivals that share the target's structure but lack the property being claimed,
lesions that damage the target in known ways, and detectors that are supposed
to separate them. A battery is SOUND when it could actually fail -- when a
false claim would be caught by it. A battery is HOLLOW when every check in it
passes by construction, so it measures nothing while looking rigorous.

You will be shown one battery. Decide whether it is sound or hollow.

Answer on the first line with exactly one word: SOUND, UNSOUND, or UNDECIDED.
UNSOUND means you believe the battery is hollow. UNDECIDED is a legitimate
answer and is scored separately from both -- do not guess to avoid it.
Then, on following lines, state briefly what led you there.\
"""


def _verdict_from(completion: str) -> str:
    """First recognisable verdict word, else ``undecided``.

    Deliberately conservative: an unparseable answer counts as undecided rather
    than being forced into a bucket, because miscounting silence as a detection
    is the one error that would flatter the checker.
    """
    for line in completion.strip().splitlines():
        word = line.strip().strip("*#:.- ").split()[:1]
        if not word:
            continue
        token = word[0].lower().strip("*#:.,")
        if token in _VERDICTS:
            return token
        if token in ("hollow", "sham"):
            return UNSOUND
    lowered = completion.lower()
    for candidate in (UNSOUND, SOUND):
        if candidate in lowered:
            return candidate
    return UNDECIDED


# ---------------------------------------------------------------------------
# the five measurements, kept apart on purpose
# ---------------------------------------------------------------------------


def _truth(sample: SampleScore) -> dict[str, Any]:
    return sample.sample_metadata or {}


def _said(sample: SampleScore) -> str:
    return (sample.score.metadata or {}).get("verdict", UNDECIDED)


def _rate(numerator: int, denominator: int) -> float:
    """Undefined rather than zero when the denominator is empty.

    A rate over no samples is not 0.0, and reporting it as 0.0 would let an
    empty arm read as a perfect one.
    """
    if denominator == 0:
        return float("nan")
    return numerator / denominator


@metric
def detection_rate() -> Any:
    """Planted faults called hollow, over planted faults shown."""

    def compute(scores: list[SampleScore]) -> Value:
        planted = [s for s in scores if _truth(s).get("planted")]
        return _rate(sum(1 for s in planted if _said(s) == UNSOUND), len(planted))

    return compute


@metric
def false_confidence_rate() -> Any:
    """Planted faults graded *sound*, over planted faults shown.

    Not one minus :func:`detection_rate`: a checker that answers ``undecided``
    contributes to neither.  This is the quantity that matters for deployment.
    """

    def compute(scores: list[SampleScore]) -> Value:
        planted = [s for s in scores if _truth(s).get("planted")]
        return _rate(sum(1 for s in planted if _said(s) == SOUND), len(planted))

    return compute


@metric
def specificity() -> Any:
    """Clean artifacts correctly graded sound, over clean artifacts shown.

    Without this a checker that answers ``unsound`` to everything scores
    perfectly on detection and false confidence.
    """

    def compute(scores: list[SampleScore]) -> Value:
        clean = [s for s in scores if not _truth(s).get("planted")]
        return _rate(sum(1 for s in clean if _said(s) == SOUND), len(clean))

    return compute


@metric
def undecided_rate() -> Any:
    """How often the checker declined, over everything shown."""

    def compute(scores: list[SampleScore]) -> Value:
        return _rate(sum(1 for s in scores if _said(s) == UNDECIDED), len(scores))

    return compute


@metric
def blind_spot_detection() -> Any:
    """**The number E0 exists to produce.**

    Detection restricted to the modes ``harness/integrity.py`` declares itself
    unable to catch.  The co-designed audit scores 0 here by construction, so
    anything above 0 from an independent checker is the asymmetry the
    preregistration predicts, and 0 is the result that says independence is not
    the variable.
    """

    def compute(scores: list[SampleScore]) -> Value:
        blind = [s for s in scores if _truth(s).get("audit_catches") is False]
        return _rate(sum(1 for s in blind if _said(s) == UNSOUND), len(blind))

    return compute


@metric
def audit_baseline() -> Any:
    """The co-designed comparator, computed from the same dataset.

    Reported alongside so the two arms are read together rather than the
    checker's number being quoted alone.  This is what
    ``harness/integrity.py`` scores on exactly these artifacts.
    """

    def compute(scores: list[SampleScore]) -> Value:
        planted = [s for s in scores if _truth(s).get("planted")]
        return _rate(sum(1 for s in planted if _truth(s).get("audit_catches")), len(planted))

    return compute


@scorer(
    metrics=[
        detection_rate(),
        false_confidence_rate(),
        specificity(),
        undecided_rate(),
        blind_spot_detection(),
        audit_baseline(),
    ]
)
def checker_verdict() -> Any:
    """Record the checker's verdict; the metrics above do the measuring.

    The ``Score`` value is kept as a plain string for the log viewer, but every
    metric reads ``metadata``: Inspect coerces string values to floats before
    metrics run, so a metric that compared ``score.value`` to ``"unsound"``
    would silently measure nothing.
    """

    async def score(state: Any, target: Any) -> Score:
        completion = state.output.completion or ""
        verdict = _verdict_from(completion)
        return Score(
            value=verdict,
            answer=verdict,
            explanation=completion.strip()[:2000],
            metadata={"verdict": verdict},
        )

    return score


# ---------------------------------------------------------------------------
# the task
# ---------------------------------------------------------------------------


def asymmetry_dataset(artifacts: Sequence[Artifact] | None = None) -> MemoryDataset:
    """The artifacts as Inspect samples, ground truth carried in metadata."""
    artifacts = list(artifacts) if artifacts is not None else build_artifacts()
    return MemoryDataset(
        [
            Sample(
                id=a.name,
                input=a.text,
                target=UNSOUND if a.planted else SOUND,
                metadata={
                    "planted": a.planted,
                    "sham_mode": a.sham_mode,
                    "audit_catches": a.audit_catches,
                    "digest": a.digest,
                },
            )
            for a in artifacts
        ],
        name="asymmetry-e0",
    )


@task
def asymmetry_e0(artifacts: Sequence[Artifact] | None = None) -> Task:
    """E0 of `meta/asymmetry-experiment.md`, as an Inspect task.

    Run it with, for example::

        inspect eval meta/evals/asymmetry.py --model anthropic/claude-opus-5

    Cost per artifact (measurement 4) is recorded by Inspect itself in the log,
    so it is not recomputed here.

    **No result from this task exists yet.**  Quoting a number from it requires
    running it, recording the sample digests, and writing the disposition up
    with a ``docs/`` number, per the preregistration -- including if the answer
    is that the asymmetry does not exist.
    """
    return Task(
        dataset=asymmetry_dataset(artifacts),
        solver=[system_message(CHECKER_SYSTEM_MESSAGE), generate()],
        scorer=checker_verdict(),
    )
