"""Department #6: statistical model evaluation, claims about distributions.

The claim under referee here is the commonest one in applied machine
learning: **"model B genuinely improves on the baseline."** Every earlier
department judges deterministic subjects with deterministic instruments,
one run settles a claim. This subject is different in kind: the measurement
is a draw from a distribution, the oracle is weak (there is no calendar
arithmetic for "genuine skill"), and the canonical failure modes are not
wrong code but wrong *protocols*, test contamination, selection on the
evaluation set, a crippled baseline. That difference is why this department
exists: it attacks the single-run assumption the other five never test.

The subject and its rivals
--------------------------
A subject is a *comparison*: a candidate pipeline, a baseline, and the
pair's own evaluation protocol. The task is a fixed synthetic regression
(eight features, two informative, seeded noise), so every number below is
reproducible and no external dataset is involved. Payloads expose behavior
only, three callables, never a score a claim could read as a label:

* ``reported_improvement()``: the pair's own protocol's verdict;
* ``candidate_fresh_mse(seed)``: the candidate, rebuilt per its own recipe
  on a *freshly drawn* training set, evaluated on fresh test data;
* ``baseline_fresh_mse(seed)``: same for its baseline.

The rivals all *report* an improvement and have none:

* **memorizer-leak**: the candidate memorizes rows; its protocol evaluates
  on rows it was shown (test contamination). Reported: near-perfect.
  Fresh: baseline-level.
* **seed-hacked**: best of 40 random linear predictors, selected on the
  evaluation set itself. Reported: positive by selection. Fresh: nothing.
* **crippled-baseline**: a junk candidate beating a deliberately broken
  baseline (constant far from the data). Reported: enormous. Fresh: junk.

The distinguishing reference claim measures against the department's own
honest oracle, the mean predictor's fresh mse, computed by department code
that never calls any subject, on three fresh draws. The killed claim is
"reports an improvement on its own benchmark", true of everything in the
room: **a green number on a self-chosen benchmark distinguishes nothing.**

What this department forced out of the shared layer
---------------------------------------------------
``run_nulls`` compares an observation against **one draw per surrogate**
with a distance tolerance. For deterministic surrogates that is exact; for
a distributional null it is the REDTEAM.md W3/W4 failure, a gate whose
pass probability under the null nobody measured. This subject's null (the
multiple-comparison distribution: apparent improvement of best-of-N junk
selected on the evaluation set, on data with **no signal at all**) is
irreducibly a distribution, so the protocol gained
:func:`harness.protocol.run_null_band` / ``NullBandVerdict``: many draws
per surrogate, an exceedance count instead of a distance, and a verdict
that states its own draw count. That is the recorded architectural
pressure of department #6, in the FINDINGS §7 tradition: a strengthening,
reviewed on its merits, usable by every department.

Instrument honesty rules observed (the sham-battery lessons):

* payloads expose behavior only;
* the honest oracle never calls a subject;
* lesion magnitudes are the planted contamination *fraction*, a property
  of the violation, not of any detector (compiler FINDINGS §3(b));
* the generalization-gap detector's blindness at small contamination is
  measured and pinned, not hidden, the direct row-overlap scan sits next
  to it exactly as the compiler's model backend sits next to its concrete
  one, and the power difference is the measurement.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable

import numpy as np

from harness.protocol import (
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
    register_department,
)
from harness.provenance import Provenance

DEPARTMENT_NAME = "stateval"
DEPARTMENT_VERSION = "1.0"

#: The fixed task: y = X @ W_TRUE + noise. Two informative features of eight.
N_FEATURES = 8
W_TRUE = np.array([2.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0])
NOISE_SCALE = 1.0
N_ROWS = 64
RIDGE_LAMBDA = 1e-3

#: Seeds for the distinguishing claim's fresh draws, fixed, so the claim is
#: deterministic, and disjoint from every subject's own-protocol seed.
FRESH_SEEDS: tuple[int, ...] = (101, 211, 307)

#: The fresh-improvement margin: the candidate must beat the honest mean
#: predictor by at least this factor on every fresh draw. Placed against the
#: measured gap: the genuine candidate's fresh mse is ~0.04x the mean
#: predictor's, the sham rivals' are 0.95x-1.1x. Anything in (0.1, 0.9)
#: separates them by an order of magnitude on each side.
FRESH_MARGIN = 0.9

#: Planted contamination fractions (share of evaluation rows leaked into
#: training). 0.03125 is 2 rows of 64, deliberately below what the
#: generalization-gap detector can see, so its blindness is measured.
LESION_FRACTIONS: tuple[float, ...] = (0.03125, 0.25, 0.75)

_SEED_TASK = 20260809

__all__ = [
    "DEPARTMENT_NAME",
    "DEPARTMENT_VERSION",
    "BATTERY",
    "DEPARTMENT",
    "REFERENCE_CLAIMS",
    "FRESH_SEEDS",
    "FRESH_MARGIN",
    "LESION_FRACTIONS",
    "draw_dataset",
    "ridge_fit",
    "mean_predictor_mse",
    "oracle_fresh_mean_mse",
    "claim_reports_improvement",
    "claim_improves_when_fresh",
    "gap_detector",
    "overlap_scan",
]


# ---------------------------------------------------------------------------
# The task, and the honest oracle (never calls any subject)
# ---------------------------------------------------------------------------


def draw_dataset(seed: int, *, rows: int = N_ROWS, signal: bool = True):
    """One draw of the task: features, targets. ``signal=False`` removes the
    relationship entirely, the null world for the selection surrogate."""
    rng = np.random.default_rng(seed)
    X = rng.normal(size=(rows, N_FEATURES))
    noise = rng.normal(scale=NOISE_SCALE, size=rows)
    y = (X @ W_TRUE if signal else np.zeros(rows)) + noise
    return X, y


def ridge_fit(X: np.ndarray, y: np.ndarray) -> np.ndarray:
    """Closed-form ridge weights, the genuine candidate's recipe."""
    n = X.shape[1]
    return np.linalg.solve(X.T @ X + RIDGE_LAMBDA * np.eye(n), X.T @ y)


def _mse(pred: np.ndarray, y: np.ndarray) -> float:
    return float(np.mean((pred - y) ** 2))


def mean_predictor_mse(y_train: np.ndarray, y_eval: np.ndarray) -> float:
    """The honest reference baseline: predict the training mean."""
    return _mse(np.full_like(y_eval, float(np.mean(y_train))), y_eval)


def oracle_fresh_mean_mse(seed: int) -> float:
    """The department's oracle: the mean predictor's mse on a fresh draw.

    Department code, not payload, the analogue of the calendar oracle in
    department #4. It never calls, imports, or executes any subject.
    """
    X_train, y_train = draw_dataset(seed)
    X_eval, y_eval = draw_dataset(seed + 5000)
    del X_train, X_eval
    return mean_predictor_mse(y_train, y_eval)


# ---------------------------------------------------------------------------
# Subjects: comparisons, candidate, baseline, and their own protocol
# ---------------------------------------------------------------------------


class _Comparison:
    """A candidate/baseline pair with its own evaluation protocol.

    ``payload()`` returns three callables and nothing else. Each subject's
    own protocol runs on its own fixed seed; the fresh callables accept any
    seed, which is how the distinguishing claim gets draws the subject's
    author never chose.
    """

    def __init__(self, name: str, blurb: str, own_protocol: Callable[[], float],
                 fresh_candidate: Callable[[int], float],
                 fresh_baseline: Callable[[int], float]) -> None:
        self.name = name
        self._blurb = blurb
        self._own = own_protocol
        self._fresh_candidate = fresh_candidate
        self._fresh_baseline = fresh_baseline

    def describe(self) -> str:
        return self._blurb

    def payload(self) -> dict:
        return {
            "reported_improvement": self._own,
            "candidate_fresh_mse": self._fresh_candidate,
            "baseline_fresh_mse": self._fresh_baseline,
        }


def _improvement(baseline_mse: float, candidate_mse: float) -> float:
    return 1.0 - candidate_mse / baseline_mse if baseline_mse > 0 else 0.0


# -- the genuine article ----------------------------------------------------

_OWN_SEED = 42


def _genuine_own() -> float:
    X_train, y_train = draw_dataset(_OWN_SEED)
    X_test, y_test = draw_dataset(_OWN_SEED + 1)
    w = ridge_fit(X_train, y_train)
    return _improvement(mean_predictor_mse(y_train, y_test), _mse(X_test @ w, y_test))


def _genuine_fresh_candidate(seed: int) -> float:
    X_train, y_train = draw_dataset(seed)
    X_test, y_test = draw_dataset(seed + 5000)
    w = ridge_fit(X_train, y_train)
    return _mse(X_test @ w, y_test)


def _genuine_fresh_baseline(seed: int) -> float:
    return oracle_fresh_mean_mse(seed)


TARGET = _Comparison(
    "genuine-improvement",
    "ridge on the informative features against the mean predictor, honest "
    "train/test split: skill that survives any fresh draw",
    _genuine_own,
    _genuine_fresh_candidate,
    _genuine_fresh_baseline,
)


# -- rival: memorizer with a leaky protocol ---------------------------------


def _memorizer_predict(X_seen: np.ndarray, y_seen: np.ndarray, X_query: np.ndarray) -> np.ndarray:
    """Exact-row lookup; the training mean for anything unseen."""
    fallback = float(np.mean(y_seen))
    out = np.full(X_query.shape[0], fallback)
    for i, row in enumerate(X_query):
        matches = np.where(np.all(np.isclose(X_seen, row, atol=1e-12), axis=1))[0]
        if matches.size:
            out[i] = y_seen[matches[0]]
    return out


def _memorizer_own() -> float:
    X_train, y_train = draw_dataset(_OWN_SEED)
    X_test, y_test = draw_dataset(_OWN_SEED + 1)
    # The leak: the memorizer is shown the evaluation rows and their labels.
    X_seen = np.vstack([X_train, X_test])
    y_seen = np.concatenate([y_train, y_test])
    candidate = _mse(_memorizer_predict(X_seen, y_seen, X_test), y_test)
    return _improvement(mean_predictor_mse(y_train, y_test), candidate)


def _memorizer_fresh_candidate(seed: int) -> float:
    X_train, y_train = draw_dataset(seed)
    X_test, y_test = draw_dataset(seed + 5000)
    # Same recipe, honestly applied to fresh data: it has never seen these rows.
    return _mse(_memorizer_predict(X_train, y_train, X_test), y_test)


# -- rival: selection on the evaluation set ---------------------------------

_N_CANDIDATES = 40
_JUNK_SCALE = 0.3

#: The selection slice the hack scores itself on.
_SELECTION_ROWS = 6


def _junk_weights(seed: int) -> np.ndarray:
    """Candidates with no access to the signal, by construction.

    Two earlier drafts of this rival were caught by the calibration
    re-derivation before shipping, and both mistakes are the department's
    own subject matter, so they are preserved here:

    1. selecting best-of-40 *unconstrained* random predictors on the full
       evaluation set gave the "sham" genuine skill (measured fresh mse
       ratios 0.47-0.67, inside the margin), selection on signal-bearing
       data is weak training;
    2. shrinking the selection slice to 6 rows changed nothing, because in
       this task ~36% of small random weight vectors genuinely beat the
       mean predictor (E|w_j − w_true|² < |w_true|² is common in 8
       dimensions), so the pool itself carried skill before any selection.

    A rival must lack the property the way finitefield's counterfeits lack
    theirs: by construction. These candidates read only the uninformative
    features, so no selection procedure can extract transferable skill from
    them, whatever improvement they report is protocol, which is the point.
    """
    rng = np.random.default_rng(seed)
    weights = rng.normal(scale=_JUNK_SCALE, size=(_N_CANDIDATES, N_FEATURES))
    weights[:, W_TRUE != 0.0] = 0.0
    return weights


def _select_on(X_eval: np.ndarray, y_eval: np.ndarray, weights: np.ndarray) -> np.ndarray:
    scores = [_mse(X_eval @ w, y_eval) for w in weights]
    return weights[int(np.argmin(scores))]


def _seedhack_own() -> float:
    X_train, y_train = draw_dataset(_OWN_SEED)
    X_test, y_test = draw_dataset(_OWN_SEED + 1)
    del X_train
    # The hack: the winner is chosen on the very rows it is then scored on.
    X_slice, y_slice = X_test[:_SELECTION_ROWS], y_test[:_SELECTION_ROWS]
    w = _select_on(X_slice, y_slice, _junk_weights(_OWN_SEED))
    return _improvement(mean_predictor_mse(y_train, y_slice), _mse(X_slice @ w, y_slice))


def _seedhack_fresh_candidate(seed: int) -> float:
    X_test, y_test = draw_dataset(seed + 5000)
    # Same recipe: select on whatever slice is handed to it, but a fresh
    # protocol scores the winner on rows it never saw.
    X_sel, y_sel = draw_dataset(seed)
    w = _select_on(X_sel[:_SELECTION_ROWS], y_sel[:_SELECTION_ROWS], _junk_weights(_OWN_SEED))
    return _mse(X_test @ w, y_test)


# -- rival: the crippled baseline -------------------------------------------

_CRIPPLED_CONSTANT = 1000.0


def _crippled_own() -> float:
    X_train, y_train = draw_dataset(_OWN_SEED)
    X_test, y_test = draw_dataset(_OWN_SEED + 1)
    del X_train
    junk = _junk_weights(_OWN_SEED)[0]
    baseline = _mse(np.full_like(y_test, _CRIPPLED_CONSTANT), y_test)
    return _improvement(baseline, _mse(X_test @ junk, y_test))


def _crippled_fresh_candidate(seed: int) -> float:
    X_test, y_test = draw_dataset(seed + 5000)
    return _mse(X_test @ _junk_weights(_OWN_SEED)[0], y_test)


def _crippled_fresh_baseline(seed: int) -> float:
    _, y_test = draw_dataset(seed + 5000)
    return _mse(np.full_like(y_test, _CRIPPLED_CONSTANT), y_test)


RIVALS: tuple[_Comparison, ...] = (
    _Comparison(
        "memorizer-leak",
        "a lookup table shown the evaluation rows and their labels: test "
        "contamination as a subject, near-perfect reported, nothing fresh",
        _memorizer_own,
        _memorizer_fresh_candidate,
        _genuine_fresh_baseline,
    ),
    _Comparison(
        "seed-hacked",
        "best of 40 junk linear predictors, selected on the evaluation set "
        "itself: the multiple-comparison sham",
        _seedhack_own,
        _seedhack_fresh_candidate,
        _genuine_fresh_baseline,
    ),
    _Comparison(
        "crippled-baseline",
        "a junk candidate beating a baseline nailed to a constant far from "
        "the data: an enormous improvement over nothing",
        _crippled_own,
        _crippled_fresh_candidate,
        _crippled_fresh_baseline,
    ),
)


# ---------------------------------------------------------------------------
# Claims
# ---------------------------------------------------------------------------


def claim_reports_improvement(payload: dict) -> bool:
    """Fires when the pair's own protocol reports any improvement at all.

    True of the target and of every rival, the calibration claim the
    battery must kill: a green number on a self-chosen benchmark
    distinguishes nothing.
    """
    return payload["reported_improvement"]() > 0.0


def claim_improves_when_fresh(payload: dict) -> bool:
    """Fires when the candidate beats the honest oracle on every fresh draw.

    The oracle is the department's own (the mean predictor on data the
    subject's author never chose); the margin is :data:`FRESH_MARGIN`. This
    is the property the rivals lack: skill that survives leaving the rows
    the protocol was tuned on.
    """
    return all(
        payload["candidate_fresh_mse"](seed) < FRESH_MARGIN * oracle_fresh_mean_mse(seed)
        for seed in FRESH_SEEDS
    )


# ---------------------------------------------------------------------------
# Decoys: destroy the feature-label relationship, keep every marginal
# ---------------------------------------------------------------------------


def _decoy_probe() -> tuple:
    X, y = draw_dataset(_SEED_TASK)
    return (X, y)


@dataclass(frozen=True)
class _LabelShuffleDecoy:
    name: str = "label-shuffle"
    seed: int = _SEED_TASK
    probe: Any = field(default_factory=_decoy_probe)

    def describe(self) -> str:
        return (
            "permutes the labels against the features, every marginal moment "
            "survives, the relationship does not"
        )

    def substitute(self, dataset) -> tuple:
        X, y = dataset
        rng = np.random.default_rng(self.seed)
        return (X, y[rng.permutation(len(y))])


@dataclass(frozen=True)
class _NoiseLabelDecoy:
    name: str = "noise-labels"
    seed: int = _SEED_TASK + 1
    probe: Any = field(default_factory=_decoy_probe)

    def describe(self) -> str:
        return "replaces the labels with noise of the same mean and variance"

    def substitute(self, dataset) -> tuple:
        X, y = dataset
        rng = np.random.default_rng(self.seed)
        return (X, rng.normal(float(np.mean(y)), float(np.std(y)), size=len(y)))


def ridge_improvement_on(dataset) -> float:
    """The ablation measure: in-sample ridge improvement over the mean.

    Under either decoy this must collapse toward zero, a pipeline whose
    measured improvement does not move when the labels are shuffled was
    never reading the relationship.
    """
    X, y = dataset
    w = ridge_fit(X, y)
    return _improvement(_mse(np.full_like(y, float(np.mean(y))), y), _mse(X @ w, y))


# ---------------------------------------------------------------------------
# Surrogates: the multiple-comparison null, as a distribution
# ---------------------------------------------------------------------------


class _SelectionNullSurrogate:
    """Apparent improvement of best-of-N junk on signal-free data.

    Each ``sample()`` call advances a seeded stream and returns one draw of
    the *apparent improvement* a selection-on-eval protocol reports in a
    world with no signal whatsoever. The distribution of these draws is the
    luck floor for any reported improvement, and it is irreducibly a
    distribution, which is what forced ``run_null_band`` into the protocol.
    """

    def __init__(self, name: str, seed: int) -> None:
        self.name = name
        self._rng = np.random.default_rng(seed)

    def describe(self) -> str:
        return (
            "one draw of best-of-40 junk selected on its own evaluation set, on "
            "data with no signal, the multiple-comparison luck distribution"
        )

    def sample(self) -> dict:
        seed = int(self._rng.integers(0, 2**31))
        X_eval, y_eval = draw_dataset(seed, signal=False)
        weights = _junk_weights(seed + 1)
        w = _select_on(X_eval, y_eval, weights)
        value = _improvement(
            mean_predictor_mse(y_eval, y_eval), _mse(X_eval @ w, y_eval)
        )
        # The draw wears the payload shape, so the same statistic reads the
        # target and every null draw alike (the run_nulls convention).
        return {"reported_improvement": lambda value=value: value}


SURROGATES = (
    _SelectionNullSurrogate("selection-null-a", seed=7),
    _SelectionNullSurrogate("selection-null-b", seed=19),
)


def observed_reported_improvement() -> float:
    """The statistic the null band is compared against: the target's own
    reported improvement."""
    return _genuine_own()


# ---------------------------------------------------------------------------
# Lesions: planted contamination of an evaluation protocol
# ---------------------------------------------------------------------------

#: The clean protocol spec the lesions corrupt and the detectors read. Not a
#: subject payload: lesions and detectors act on protocol *configurations*,
#: the way department #4's act on source text.
CLEAN_PROTOCOL: dict = {"leak_fraction": 0.0}


@dataclass(frozen=True)
class _ContaminationLesion:
    name: str
    magnitude: float  # the leaked fraction of evaluation rows, the violation's own size
    probe: Any = field(default_factory=lambda: dict(CLEAN_PROTOCOL))

    def describe(self) -> str:
        share = self.magnitude
        return (
            f"leaks {share:.0%} of the evaluation rows into training "
            f"({int(share * N_ROWS)} of {N_ROWS} rows)"
        )

    def apply(self, protocol: dict) -> dict:
        corrupted = dict(protocol)
        corrupted["leak_fraction"] = self.magnitude
        return corrupted


LESIONS = tuple(
    _ContaminationLesion(name=f"leak-{fraction:g}".replace(".", "_"), magnitude=fraction)
    for fraction in LESION_FRACTIONS
)


def _run_protocol(protocol: dict, seed: int = _SEED_TASK) -> tuple[float, float]:
    """Execute an evaluation protocol spec: returns (reported, fresh) improvement."""
    X_train, y_train = draw_dataset(seed)
    X_test, y_test = draw_dataset(seed + 1)
    leak = float(protocol.get("leak_fraction", 0.0))
    n_leak = int(round(leak * len(y_test)))
    if n_leak:
        X_fit = np.vstack([X_train, X_test[:n_leak]])
        y_fit = np.concatenate([y_train, y_test[:n_leak]])
    else:
        X_fit, y_fit = X_train, y_train
    # A memorizing candidate makes contamination visible in the scores; a
    # heavily regularised one would launder it. The protocol under audit is
    # the evaluation, so the candidate is fixed across clean and corrupted.
    X_seen, y_seen = X_fit, y_fit
    reported = _improvement(
        mean_predictor_mse(y_fit, y_test), _mse(_memorizer_predict(X_seen, y_seen, X_test), y_test)
    )
    X_fresh, y_fresh = draw_dataset(seed + 2)
    fresh = _improvement(
        mean_predictor_mse(y_fit, y_fresh), _mse(_memorizer_predict(X_seen, y_seen, X_fresh), y_fresh)
    )
    return reported, fresh


#: The gap detector's threshold, placed against the measured response:
#: leaking 75% of evaluation rows produces a reported-minus-fresh gap of
#: ~0.75, 25% gives ~0.25, and 2 rows (3.125%) gives ~0.03, comfortably
#: below. 0.1 therefore fires on the two large leaks and is measurably
#: blind to the smallest, which is the point: a contamination detector's
#: floor should be a number, not a hope.
GAP_THRESHOLD = 0.1


def gap_detector(protocol: dict) -> bool:
    """Fires when reported improvement exceeds fresh improvement by more
    than :data:`GAP_THRESHOLD`, the generalization-gap signature of a
    contaminated protocol. Behavioral, and measurably blind below its floor."""
    reported, fresh = _run_protocol(protocol)
    return (reported - fresh) > GAP_THRESHOLD


def overlap_scan(protocol: dict) -> bool:
    """Fires when any evaluation row is literally present in the training
    set the protocol assembles. Direct and exact, the analogue of the zeta
    department's off-line scan: it reads the violation itself, so its full
    power is the baseline the behavioral detector is measured against."""
    seed = _SEED_TASK
    X_train, y_train = draw_dataset(seed)
    X_test, _ = draw_dataset(seed + 1)
    leak = float(protocol.get("leak_fraction", 0.0))
    n_leak = int(round(leak * X_test.shape[0]))
    X_fit = np.vstack([X_train, X_test[:n_leak]]) if n_leak else X_train
    del y_train
    for row in X_test:
        if np.any(np.all(np.isclose(X_fit, row, atol=1e-12), axis=1)):
            return True
    return False


DETECTORS = (
    NamedDetector(
        name="overlap_scan",
        fires=overlap_scan,
        probe=dict(CLEAN_PROTOCOL),
        note=(
            "exact train/eval row-duplication scan, full power down to one "
            "leaked row, and blind in principle to any contamination that is "
            "not literal duplication"
        ),
    ),
    NamedDetector(
        name="generalization_gap",
        fires=gap_detector,
        probe=dict(CLEAN_PROTOCOL),
        note=(
            f"reported-minus-fresh improvement above {GAP_THRESHOLD}: behavioral, "
            "catches contamination however it entered, and measurably blind "
            "below its floor (2 leaked rows of 64 do not move the gap)"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The battery, and the department
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="stateval",
    target=TARGET,
    rivals=RIVALS,
    decoys=(_LabelShuffleDecoy(), _NoiseLabelDecoy()),
    surrogates=SURROGATES,
    lesions=LESIONS,
    notes=(
        "every rival reports an improvement and has none: contamination, "
        "selection-on-eval, and a crippled baseline. The null is a "
        "distribution, not a value, see run_null_band, which this "
        "department forced into the protocol."
    ),
)

REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="reports_improvement",
        claim=claim_reports_improvement,
        distinguishes=False,
        note=(
            "true of the target and of all three rivals: a green number on a "
            "self-chosen benchmark distinguishes nothing, the battery must "
            "kill this"
        ),
    ),
    ReferenceClaim(
        name="improves_when_fresh",
        claim=claim_improves_when_fresh,
        distinguishes=True,
        note=(
            "beats the department's honest oracle on three fresh draws the "
            "subject's author never chose; fires for the genuine comparison only"
        ),
    ),
)

DEPARTMENT = Department(
    name=DEPARTMENT_NAME,
    summary=(
        "statistical model evaluation: whether a reported improvement is skill "
        "or protocol, the first department whose measurements are draws from "
        "a distribution"
    ),
    battery=BATTERY,
    door="docs/doors/stateval.md",
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "a surviving claim distinguishes genuine improvement from the three "
        "named protocol shams on this synthetic task at n = 64; it is not a "
        "statement about any real dataset, any other model class, or effect "
        "sizes the null band cannot resolve"
    ),
    provenance=Provenance(
        authored_by="the laboratory's own process",
        authored_on="2026-08-09",
        independent_of_subject_author=False,
        results_visible_when_authored=False,
        frozen_before_execution=True,
        oracle_calls_subject=False,
        notes=(
            "margins and thresholds were placed against measured response "
            "curves before the reference verdicts were pinned; the oracle is "
            "the mean predictor on draws no subject's author chose"
        ),
    ),
    modules=("harness.departments.stateval_department",),
)

register_department(DEPARTMENT, replace=True)
