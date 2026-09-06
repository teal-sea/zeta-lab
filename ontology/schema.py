"""ontology.schema, the ontology of the discovery funnel.

This module is **domain-agnostic on purpose**. It contains no knowledge of the
laboratory it serves: no subject-matter vocabulary, no imports from the science
package, no special cases for any particular quantity. It would work unchanged
for a chemistry lab or a compiler-optimisation search. Everything the funnel
needs to *say* about an observation is expressed here; everything the funnel
knows about the *subject* lives behind the registry, in a domain module.

The design in one paragraph
---------------------------
An observation enters the funnel as a :class:`Candidate`: a ``kind`` (one of
five, each defined by a *decision procedure* rather than by a word), a
``claim`` (the identity-bearing content, what is being asserted), an
``evidence`` mapping (the support: windows, tolerances, controls, counts), a
:class:`Provenance` record that must make the observation re-derivable months
later, optional typed ``related_to`` graph links, and a :class:`Verdict` whose
status defaults to ``open``. The candidate's
``id`` is a content hash of ``(schema major, kind, canonicalised claim)`` and of
nothing else, so the same observation found twice by two different generators
at two different precisions is recognised as one candidate, which is exactly
what makes per-generator conversion rates measurable.

Three rules the rest of the package depends on
----------------------------------------------
1. **A category is a function.** ``accepts(kind, claim, evidence)`` is total and
   discriminating; ``kind_reasons`` says *why* a payload was refused. A payload
   that no kind accepts is not a candidate, it is a note.
2. **Failure is first-class.** ``already-known`` is a terminal status with its
   own detector, and so are ``refuted``, ``trivial`` and ``inconclusive``. Each
   has entry criteria enforced by :func:`validate_verdict`; a status cannot be
   asserted without the evidence that earns it.
3. **Identity is the claim, not the run.** Provenance, verdict, label,
   ``related_to`` and timestamps are excluded from the hash. See ``README.md``
   for the full deduplication contract and its failure modes.

Serialisation is JSON (one record per line for JSONL). ``from_dict`` recomputes
the content hash and refuses a record whose stored ``id`` disagrees with its
claim, so a hand-edited or corrupted line is rejected rather than silently
counted.
"""

from __future__ import annotations

import datetime as _dt
import hashlib
import json
import math
import platform
import re
import subprocess
from collections.abc import Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field, replace
from decimal import Context as _DecimalContext
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from enum import StrEnum
from pathlib import Path
from types import MappingProxyType
from typing import Any, Final

__all__ = [
    # version and policy constants
    "SCHEMA_VERSION",
    "SCHEMA_MAJOR",
    "SCHEMA_MINOR",
    "SCHEMA_HISTORY",
    "DEFAULT_DEDUP_DIGITS",
    "MIN_INDEX_SPAN",
    "MIN_WINDOWS",
    "MIN_WINDOW_POINTS",
    "MIN_WITNESSES",
    "MAX_ARGUMENT_CHARS",
    # errors
    "SchemaError",
    "ValidationError",
    # vocabularies
    "CandidateKind",
    "CandidateRelation",
    "VerdictStatus",
    "InconclusiveReason",
    "RELATION_OPS",
    "LIMIT_POINTS",
    "DIRECTIONS",
    "PRECISION_KINDS",
    "REQUIRED_SURVIVAL_CHECKS",
    "TERMINAL_STATUSES",
    "REOPENABLE_STATUSES",
    # decision procedures
    "KIND_RULES",
    "kind_reasons",
    "accepts",
    "classify",
    "claim_keys",
    "allowed_claim_keys",
    "required_claim_keys",
    # identity
    "canonical_claim",
    "content_hash",
    "same_claim",
    "latest_by_id",
    # records
    "Precision",
    "Provenance",
    "Verdict",
    "Candidate",
    "CandidateLink",
    "KnownEntry",
    # validation
    "validate_claim",
    "validate_provenance",
    "validate_verdict",
    "validate_candidate",
    "candidate_reasons",
    "verdict_reasons",
    # provenance capture
    "git_revision",
    "capture_provenance",
    # the shape of the already-known detector
    "match_known",
    # serialisation
    "to_dict",
    "from_dict",
    "to_json",
    "from_json",
    "dumps_jsonl",
    "loads_jsonl",
    "append_jsonl",
    "read_jsonl",
    "write_jsonl",
    "iter_jsonl",
    "migrate_record",
]

# ---------------------------------------------------------------------------
# Schema version and migration policy
# ---------------------------------------------------------------------------

SCHEMA_MAJOR: Final[int] = 1
SCHEMA_MINOR: Final[int] = 1
SCHEMA_VERSION: Final[str] = f"{SCHEMA_MAJOR}.{SCHEMA_MINOR}"

#: Append-only log of schema revisions. A *minor* bump may add optional fields
#: and must not change canonicalisation (ids stay stable). A *major* bump may
#: change canonicalisation, therefore changes every id, and must ship a
#: migration that records the old id in ``supersedes``.
SCHEMA_HISTORY: Final[tuple[Mapping[str, str], ...]] = (
    MappingProxyType(
        {
            "version": "1.0",
            "date": "2026-08-02",
            "note": (
                "Initial ontology: five candidate kinds, six verdict statuses, "
                "one provenance record, content hash over "
                "(major, kind, canonical claim)."
            ),
        }
    ),
    MappingProxyType(
        {
            "version": "1.1",
            "date": "2026-08-04",
            "note": (
                "Added optional related_to graph edges. Links are excluded from "
                "candidate identity and do not propagate or constrain verdicts."
            ),
        }
    ),
)

#: Significant decimal digits kept when a measured number enters the content
#: hash. See README, 'the deduplication contract', for why 9.
DEFAULT_DEDUP_DIGITS: Final[int] = 9

#: Screening thresholds used by the decision procedures.
MIN_INDEX_SPAN: Final[float] = 4.0
MIN_WINDOWS: Final[int] = 2
MIN_WINDOW_POINTS: Final[int] = 3
MIN_WITNESSES: Final[int] = 3
MAX_ARGUMENT_CHARS: Final[int] = 240

_ID_PREFIX: Final[str] = "cand-"
_HASH_HEX: Final[int] = 32  # 128 bits of the SHA-256 digest
_CANDIDATE_ID_RE: Final[re.Pattern[str]] = re.compile(
    rf"^{re.escape(_ID_PREFIX)}[0-9a-f]{{{_HASH_HEX}}}$"
)

_NUMERIC_RE: Final[re.Pattern[str]] = re.compile(
    r"^[+-]?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?$"
)
_DOTTED_RE: Final[re.Pattern[str]] = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$"
)
_REVISION_RE: Final[re.Pattern[str]] = re.compile(r"^[0-9a-f]{7,64}$")
#: Machine-local absolute paths must never reach a committed record.
_LOCAL_PATH_RE: Final[re.Pattern[str]] = re.compile(
    r"(?:/Users/|/home/|[A-Za-z]:\\Users\\)"
)


class SchemaError(Exception):
    """Base class for every error raised by this module."""


class ValidationError(SchemaError):
    """A record is malformed: it violates the ontology's own rules."""


# ---------------------------------------------------------------------------
# Canonicalisation and the content hash
# ---------------------------------------------------------------------------


def _is_numeric_str(value: Any) -> bool:
    return isinstance(value, str) and bool(_NUMERIC_RE.match(value.strip()))


def _as_decimal(value: Any) -> Decimal | None:
    """``value`` as an exact :class:`Decimal`, or ``None`` if it is not a number.

    ``bool`` is deliberately excluded: a flag is not a measurement.
    """
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return Decimal(value)
    if isinstance(value, float):
        if not math.isfinite(value):
            return None
        return Decimal(repr(value))
    if isinstance(value, Decimal):
        return value if value.is_finite() else None
    if _is_numeric_str(value):
        try:
            return Decimal(value.strip())
        except InvalidOperation:  # pragma: no cover - regex already filtered
            return None
    return None


def _canon_number(value: Any, digits: int) -> str:
    """A measured number as a canonical fixed-width scientific string.

    ``1.0``, ``"1"``-as-a-float and ``1.0000000001`` all map to the same token
    at nine digits; ``1.00000001`` does not.
    """
    dec = _as_decimal(value)
    if dec is None or not dec.is_finite():
        raise ValidationError(f"not a finite number: {value!r}")
    if dec == 0:
        return "0E+0"
    ctx = _DecimalContext(prec=digits, rounding=ROUND_HALF_EVEN)
    return format(ctx.create_decimal(dec), f".{digits - 1}E")


def _canon(value: Any, digits: int) -> str:
    """Canonical token for any JSON-shaped value.

    Ordering rules, all load-bearing for the hash:

    * mappings are emitted with keys sorted (insertion order is not meaning);
    * sequences keep their order (order *is* meaning in a claim);
    * ``int`` is exact, ``float``/``Decimal``/decimal-looking ``str`` are
      rounded to ``digits`` significant digits, so "exactly one million" and
      "one million, measured" are different claims, on purpose;
    * ``bool`` and ``None`` are their JSON spellings.
    """
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, (float, Decimal)) or _is_numeric_str(value):
        return _canon_number(value, digits)
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=True, sort_keys=True)
    if isinstance(value, Mapping):
        items = sorted(value.items(), key=lambda kv: str(kv[0]))
        inner = ",".join(
            f"{json.dumps(str(k), ensure_ascii=True)}:{_canon(v, digits)}"
            for k, v in items
        )
        return "{" + inner + "}"
    if isinstance(value, Sequence):
        return "[" + ",".join(_canon(v, digits) for v in value) + "]"
    raise ValidationError(f"value is not JSON-shaped: {value!r}")


def canonical_claim(
    kind: "CandidateKind | str",
    claim: Mapping[str, Any],
    digits: int = DEFAULT_DEDUP_DIGITS,
) -> str:
    """The exact byte string that is hashed to give a candidate its identity."""
    kind_token = CandidateKind(kind).value
    return (
        '{"v":'
        + str(SCHEMA_MAJOR)
        + ',"kind":'
        + json.dumps(kind_token)
        + ',"claim":'
        + _canon(claim, digits)
        + "}"
    )


def content_hash(
    kind: "CandidateKind | str",
    claim: Mapping[str, Any],
    digits: int = DEFAULT_DEDUP_DIGITS,
) -> str:
    """Stable content id: ``cand-`` + 128 bits of SHA-256 over the claim.

    Deliberately independent of generator, precision, seed, revision, time,
    label, evidence and verdict, two runs that assert the same thing collide,
    and that collision is the point.
    """
    payload = canonical_claim(kind, claim, digits).encode("utf-8")
    return _ID_PREFIX + hashlib.sha256(payload).hexdigest()[:_HASH_HEX]


def same_claim(
    left: "Candidate | Mapping[str, Any]",
    right: "Candidate | Mapping[str, Any]",
    digits: int | None = None,
) -> bool:
    """Do two candidates assert the same thing?

    ``digits=None`` compares at the coarser of the two records' own
    ``dedup_digits``: the honest resolution, since neither record can be
    sharpened after the fact. Hash equality implies ``same_claim``; the
    converse fails only when the two were recorded at different resolutions,
    which is why the metrics layer should use this function and not ``==`` on
    ids when it needs to be careful.
    """
    lk, lc, ld = _claim_triple(left)
    rk, rc, rd = _claim_triple(right)
    if lk != rk:
        return False
    use = min(ld, rd) if digits is None else digits
    return canonical_claim(lk, lc, use) == canonical_claim(rk, rc, use)


def _claim_triple(
    obj: "Candidate | Mapping[str, Any]",
) -> tuple["CandidateKind", Mapping[str, Any], int]:
    if isinstance(obj, Candidate):
        return obj.kind, obj.claim, obj.dedup_digits
    if isinstance(obj, Mapping):
        return (
            CandidateKind(obj["kind"]),
            obj["claim"],
            int(obj.get("dedup_digits", DEFAULT_DEDUP_DIGITS)),
        )
    raise TypeError(f"not a candidate or record: {obj!r}")


# ---------------------------------------------------------------------------
# Candidate kinds, each one a decision procedure
# ---------------------------------------------------------------------------


class CandidateKind(StrEnum):
    """The five shapes an observation may take. Five, and no more."""

    #: A measured number that might have a closed form.
    CONSTANT = "constant"
    #: A growth-rate claim about a limit.
    ASYMPTOTIC = "asymptotic"
    #: A stated relation between two computed quantities.
    RELATION = "relation"
    #: A record or extreme over an explicitly bounded search.
    EXTREMAL = "extremal"
    #: A universal qualitative claim about an enumerated family.
    STRUCTURAL = "structural"


class CandidateRelation(StrEnum):
    """The two graph relations a candidate may assert about another."""

    #: The candidate carrying the link implies the target candidate.
    IMPLIES = "implies"
    #: The candidate and target express equivalent claims.
    EQUIVALENT_TO = "equivalent_to"


RELATION_OPS: Final[tuple[str, ...]] = (
    "eq",
    "le",
    "lt",
    "ge",
    "gt",
    "proportional",
    "dist_match",
)
LIMIT_POINTS: Final[tuple[str, ...]] = ("+inf", "-inf", "0+", "0-")
DIRECTIONS: Final[tuple[str, ...]] = ("max", "min")
PRECISION_KINDS: Final[tuple[str, ...]] = ("dps", "bits", "float64", "exact")


# --- tiny type-token language used by the field specs ----------------------


def _type_reason(token: str, key: str, value: Any) -> str | None:
    """``None`` if ``value`` satisfies ``token``, else a one-line reason."""
    if token == "text":
        if not isinstance(value, str) or not value.strip():
            return f"{key}: expected non-empty text, got {value!r}"
        return None
    if token == "count":
        if isinstance(value, bool) or not isinstance(value, int):
            return f"{key}: expected an exact integer count, got {value!r}"
        return None
    if token == "measure":
        if isinstance(value, bool) or isinstance(value, int):
            return f"{key}: expected a measured value (float or decimal text), got {value!r}"
        if _as_decimal(value) is None:
            return f"{key}: expected a finite measured value, got {value!r}"
        return None
    if token == "number":
        if _as_decimal(value) is None:
            return f"{key}: expected a finite number, got {value!r}"
        return None
    if token == "atom":
        if isinstance(value, str) and value.strip():
            return None
        if _as_decimal(value) is not None:
            return None
        return f"{key}: expected text or a finite number, got {value!r}"
    if token == "list":
        if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
            return f"{key}: expected a list, got {value!r}"
        return None
    if token.startswith("choice:"):
        options = tuple(token.split(":", 1)[1].split("|"))
        if value not in options:
            return f"{key}: expected one of {options}, got {value!r}"
        return None
    raise SchemaError(f"unknown type token {token!r}")  # pragma: no cover


@dataclass(frozen=True, slots=True)
class _KindRule:
    """The decision procedure for one candidate kind, as data plus a check."""

    claim_required: Mapping[str, str]
    claim_optional: Mapping[str, str]
    evidence_required: Mapping[str, str]
    identity_fields: tuple[str, ...]
    check: Any  # Callable[[Mapping, Mapping], list[str]]
    holds: str
    rejects: str

    def allowed(self) -> frozenset[str]:
        return frozenset(self.claim_required) | frozenset(self.claim_optional)


def _positive(value: Any) -> bool:
    dec = _as_decimal(value)
    return dec is not None and dec > 0


def _nonnegative(value: Any) -> bool:
    dec = _as_decimal(value)
    return dec is not None and dec >= 0


def _determined_digits(value: Any, uncertainty: Any) -> float:
    """How many significant digits the error bound actually pins down.

    Computed in :class:`Decimal` so that quantities far outside the range of a
    double do not raise on the way in.
    """
    val = _as_decimal(value)
    unc = _as_decimal(uncertainty)
    if val is None or unc is None or unc <= 0 or val == 0:
        return 0.0
    return math.floor((abs(val) / unc).log10())


def _check_constant(claim: Mapping[str, Any], evidence: Mapping[str, Any]) -> list[str]:
    bad: list[str] = []
    value = claim.get("value")
    unc = evidence.get("uncertainty")
    if not _positive(unc):
        bad.append("evidence.uncertainty must be a positive error bound")
        return bad
    dec_value = _as_decimal(value)
    if dec_value is None:
        return ["claim.value must be a finite measured number"]
    if dec_value == 0:
        bad.append(
            "a vanishing measured quantity is a relation (q = 0), not a constant"
        )
        return bad
    if abs(dec_value) <= _as_decimal(unc):
        bad.append(
            "|claim.value| must exceed evidence.uncertainty: "
            "no significant digit is determined"
        )
    elif _determined_digits(value, unc) < 1:
        bad.append("fewer than one significant digit is determined")
    return bad


def _check_asymptotic(
    claim: Mapping[str, Any], evidence: Mapping[str, Any]
) -> list[str]:
    bad: list[str] = []
    tol = evidence.get("tolerance")
    if not _positive(tol):
        bad.append("evidence.tolerance must be positive")
    windows = evidence.get("windows")
    if not isinstance(windows, Sequence) or isinstance(windows, (str, bytes)):
        return bad + ["evidence.windows must be a list of fitted windows"]
    if len(windows) < MIN_WINDOWS:
        bad.append(f"at least {MIN_WINDOWS} disjoint fitting windows are required")
    lows: list[float] = []
    highs: list[float] = []
    fitted: list[float] = []
    for i, win in enumerate(windows):
        if not isinstance(win, Mapping):
            bad.append(f"windows[{i}] is not a mapping")
            continue
        lo, hi = _as_decimal(win.get("index_min")), _as_decimal(win.get("index_max"))
        exp = _as_decimal(win.get("exponent"))
        pts = win.get("n_points")
        if lo is None or hi is None or lo <= 0 or hi <= lo:
            bad.append(f"windows[{i}] needs 0 < index_min < index_max")
            continue
        if exp is None:
            bad.append(f"windows[{i}].exponent must be a finite number")
            continue
        if isinstance(pts, bool) or not isinstance(pts, int) or pts < MIN_WINDOW_POINTS:
            bad.append(f"windows[{i}].n_points must be an integer >= {MIN_WINDOW_POINTS}")
            continue
        lows.append(float(lo))
        highs.append(float(hi))
        fitted.append(float(exp))
    if len(fitted) < MIN_WINDOWS:
        return bad
    span = max(highs) / min(lows)
    if span < MIN_INDEX_SPAN:
        bad.append(
            f"index span {span:.3g} is below {MIN_INDEX_SPAN}: "
            "a local fit is not an asymptotic claim"
        )
    claimed = _as_decimal(claim.get("exponent"))
    if claimed is None:
        bad.append("claim.exponent must be a finite number")
    elif _positive(tol):
        drift = max(abs(f - float(claimed)) for f in fitted)
        if drift > float(_as_decimal(tol)):
            bad.append(
                f"per-window exponents drift by {drift:.3g} > tolerance: "
                "the fit is not stable across the range"
            )
    return bad


def _check_relation(claim: Mapping[str, Any], evidence: Mapping[str, Any]) -> list[str]:
    bad: list[str] = []
    lhs, rhs = claim.get("lhs"), claim.get("rhs")
    if isinstance(lhs, str) and isinstance(rhs, str) and lhs.strip() == rhs.strip():
        bad.append("lhs and rhs are the same quantity: a tautology, not a relation")
    defect, tol = evidence.get("defect"), evidence.get("tolerance")
    if not _nonnegative(defect):
        bad.append("evidence.defect must be a finite, non-negative measurement")
    if not _positive(tol):
        bad.append("evidence.tolerance must be positive")
    if _nonnegative(defect) and _positive(tol):
        if _as_decimal(defect) > _as_decimal(tol):
            bad.append(
                "defect exceeds tolerance: this is a refutation of a relation, "
                "not a candidate relation"
            )
    return bad


def _check_extremal(claim: Mapping[str, Any], evidence: Mapping[str, Any]) -> list[str]:
    bad: list[str] = []
    n_searched = claim.get("n_searched")
    if isinstance(n_searched, bool) or not isinstance(n_searched, int) or n_searched < 2:
        bad.append("claim.n_searched must be an integer >= 2: a record needs a field")
    value = _as_decimal(claim.get("value"))
    runner = _as_decimal(evidence.get("runner_up"))
    if value is None:
        bad.append("claim.value must be a finite number")
    if runner is None:
        bad.append("evidence.runner_up must be a finite number (the second best)")
    if value is not None and runner is not None:
        direction = claim.get("direction")
        if direction == "max" and not value > runner:
            bad.append("claimed maximum does not strictly beat the runner-up")
        if direction == "min" and not value < runner:
            bad.append("claimed minimum does not strictly beat the runner-up")
    return bad


def _check_structural(
    claim: Mapping[str, Any], evidence: Mapping[str, Any]
) -> list[str]:
    bad: list[str] = []
    witnesses = evidence.get("witnesses")
    if not isinstance(witnesses, Sequence) or isinstance(witnesses, (str, bytes)):
        bad.append("evidence.witnesses must be a list of checked members")
        witnesses = ()
    if len(witnesses) < MIN_WITNESSES:
        bad.append(f"at least {MIN_WITNESSES} checked members are required")
    n_checked = evidence.get("n_checked")
    n_satisfied = evidence.get("n_satisfied")
    for key, val in (("n_checked", n_checked), ("n_satisfied", n_satisfied)):
        if isinstance(val, bool) or not isinstance(val, int) or val < 0:
            bad.append(f"evidence.{key} must be a non-negative integer")
    if isinstance(n_checked, int) and not isinstance(n_checked, bool):
        if n_checked != len(witnesses):
            bad.append("evidence.n_checked must equal len(evidence.witnesses)")
        if isinstance(n_satisfied, int) and not isinstance(n_satisfied, bool):
            if n_satisfied != n_checked:
                bad.append(
                    "a member already fails the predicate: that is a refutation "
                    "of the claim, not a candidate"
                )
    controls = evidence.get("controls")
    if not isinstance(controls, Sequence) or isinstance(controls, (str, bytes)):
        return bad + [
            "evidence.controls must be a list of {id, satisfied} probes on which "
            "the predicate could have failed"
        ]
    failed = [
        c
        for c in controls
        if isinstance(c, Mapping) and c.get("satisfied") is False and c.get("id")
    ]
    if not failed:
        bad.append(
            "no control failed the predicate: the property discriminates nothing, "
            "so the claim has no content"
        )
    return bad


KIND_RULES: Final[Mapping[CandidateKind, _KindRule]] = MappingProxyType(
    {
        CandidateKind.CONSTANT: _KindRule(
            claim_required=MappingProxyType({"subject": "text", "value": "measure"}),
            claim_optional=MappingProxyType({}),
            evidence_required=MappingProxyType({"uncertainty": "measure"}),
            identity_fields=("subject",),
            check=_check_constant,
            holds="a measured number with an honest error bar that pins >= 1 digit",
            rejects="a value indistinguishable from nought, or one with no error bar",
        ),
        CandidateKind.ASYMPTOTIC: _KindRule(
            claim_required=MappingProxyType(
                {
                    "subject": "text",
                    "index": "text",
                    "limit": "choice:" + "|".join(LIMIT_POINTS),
                    "scale": "text",
                    "exponent": "number",
                }
            ),
            claim_optional=MappingProxyType({}),
            evidence_required=MappingProxyType(
                {"windows": "list", "tolerance": "measure"}
            ),
            identity_fields=("subject", "scale", "limit"),
            check=_check_asymptotic,
            holds="a rate fitted in >= 2 windows spanning >= 4x, agreeing within tolerance",
            rejects="a one-window fit, a narrow span, or windows that disagree",
        ),
        CandidateKind.RELATION: _KindRule(
            claim_required=MappingProxyType(
                {
                    "lhs": "text",
                    "rhs": "text",
                    "relation": "choice:" + "|".join(RELATION_OPS),
                }
            ),
            claim_optional=MappingProxyType({"constant": "number"}),
            evidence_required=MappingProxyType(
                {
                    "defect": "number",
                    "tolerance": "measure",
                    "defect_definition": "text",
                }
            ),
            identity_fields=("lhs", "rhs", "relation"),
            check=_check_relation,
            holds="two distinct quantities, a named relation, a measured defect within tolerance",
            rejects="a quantity related to itself, or a defect that exceeds its tolerance",
        ),
        CandidateKind.EXTREMAL: _KindRule(
            claim_required=MappingProxyType(
                {
                    "subject": "text",
                    "direction": "choice:" + "|".join(DIRECTIONS),
                    "space": "text",
                    "n_searched": "count",
                    "argopt": "atom",
                    "value": "number",
                }
            ),
            claim_optional=MappingProxyType({}),
            evidence_required=MappingProxyType({"runner_up": "number"}),
            identity_fields=("subject", "space", "n_searched"),
            check=_check_extremal,
            holds="a record over a stated, finite search, strictly beating a stated runner-up",
            rejects="a record with no runner-up, a tie, or a search of fewer than two elements",
        ),
        CandidateKind.STRUCTURAL: _KindRule(
            claim_required=MappingProxyType(
                {"family": "text", "predicate": "text", "scope": "text"}
            ),
            claim_optional=MappingProxyType({}),
            evidence_required=MappingProxyType(
                {
                    "witnesses": "list",
                    "n_checked": "count",
                    "n_satisfied": "count",
                    "controls": "list",
                }
            ),
            identity_fields=("family", "predicate", "scope"),
            check=_check_structural,
            holds="every member of an enumerated family satisfies a predicate that a control fails",
            rejects="a predicate no control fails, or a family with a known exception",
        ),
    }
)


def required_claim_keys(kind: CandidateKind | str) -> frozenset[str]:
    """The claim keys a candidate of this kind must carry."""
    return frozenset(KIND_RULES[CandidateKind(kind)].claim_required)


def allowed_claim_keys(kind: CandidateKind | str) -> frozenset[str]:
    """Required plus optional claim keys. Anything else is refused."""
    return KIND_RULES[CandidateKind(kind)].allowed()


def kind_reasons(
    kind: CandidateKind | str,
    claim: Mapping[str, Any],
    evidence: Mapping[str, Any] | None = None,
) -> tuple[str, ...]:
    """Why ``kind`` refuses this payload. Empty tuple means it accepts.

    This *is* the category: there is no other definition of what a
    ``constant`` or a ``structural`` candidate is.
    """
    rule = KIND_RULES[CandidateKind(kind)]
    evidence = {} if evidence is None else evidence
    if not isinstance(claim, Mapping):
        return ("claim must be a mapping",)
    if not isinstance(evidence, Mapping):
        return ("evidence must be a mapping",)
    bad: list[str] = []
    keys = set(claim)
    missing = set(rule.claim_required) - keys
    if missing:
        bad.append(f"missing claim fields: {sorted(missing)}")
    foreign = keys - rule.allowed()
    if foreign:
        bad.append(f"claim fields not part of this kind: {sorted(foreign)}")
    for key, token in rule.claim_required.items():
        if key in claim:
            reason = _type_reason(token, f"claim.{key}", claim[key])
            if reason:
                bad.append(reason)
    for key, token in rule.claim_optional.items():
        if key in claim:
            reason = _type_reason(token, f"claim.{key}", claim[key])
            if reason:
                bad.append(reason)
    for key, token in rule.evidence_required.items():
        if key not in evidence:
            bad.append(f"missing evidence field: {key}")
        else:
            reason = _type_reason(token, f"evidence.{key}", evidence[key])
            if reason:
                bad.append(reason)
    if bad:
        return tuple(bad)
    return tuple(rule.check(claim, evidence))


def accepts(
    kind: CandidateKind | str,
    claim: Mapping[str, Any],
    evidence: Mapping[str, Any] | None = None,
) -> bool:
    """Does ``kind`` accept this payload? The decision procedure, as a bool."""
    return not kind_reasons(kind, claim, evidence)


def classify(
    claim: Mapping[str, Any], evidence: Mapping[str, Any] | None = None
) -> CandidateKind | None:
    """The unique kind that accepts this payload, or ``None`` if there is none.

    The five kinds are pairwise exclusive by construction: their required key
    sets are never both contained in the intersection of their allowed key
    sets, and claim keys are checked strictly. ``None`` is the common and
    correct answer for a vague observation, it means "this is not a
    candidate", not "this is a new kind".
    """
    hits = [k for k in CandidateKind if accepts(k, claim, evidence)]
    if not hits:
        return None
    if len(hits) > 1:  # pragma: no cover - prevented by disjoint key sets
        raise SchemaError(f"ambiguous payload, accepted by {hits}")
    return hits[0]


def claim_keys(
    kind: CandidateKind | str, claim: Mapping[str, Any]
) -> tuple[str, ...]:
    """The identity strings of a claim, used by the already-known matcher."""
    rule = KIND_RULES[CandidateKind(kind)]
    out: list[str] = []
    for field_name in rule.identity_fields:
        value = claim.get(field_name)
        if isinstance(value, str) and value.strip():
            out.append(value.strip())
        elif value is not None:
            out.append(str(value))
    return tuple(out)


# ---------------------------------------------------------------------------
# Verdicts, including, and especially, the unflattering ones
# ---------------------------------------------------------------------------


class VerdictStatus(StrEnum):
    """Six states. Four of them are ways of saying "nothing here"."""

    #: Generated, no screen has spoken yet. The only non-terminal state.
    OPEN = "open"
    #: Already in the literature or already in the laboratory. The expected
    #: outcome, with its own detector, never quietly filed as a near miss.
    KNOWN = "known"
    #: True, but it follows from something already recorded by a one-line
    #: argument that was written down and machine-checked.
    TRIVIAL = "trivial"
    #: Numerically refuted, with a witness that survived a precision increase.
    REFUTED = "refuted"
    #: Survived every screen this system can apply, and this system cannot
    #: prove it. A lead, not a result.
    SURVIVES = "survives"
    #: The work ran and decided nothing: budget, precision, a missing
    #: dependency, irreproducibility. This is how an empty month is recorded.
    INCONCLUSIVE = "inconclusive"


class InconclusiveReason(StrEnum):
    """Closed vocabulary: why the work decided nothing."""

    BUDGET_EXHAUSTED = "budget_exhausted"
    PRECISION_INSUFFICIENT = "precision_insufficient"
    DEPENDENCY_UNAVAILABLE = "dependency_unavailable"
    NONDETERMINISTIC = "nondeterministic"
    NOT_REPRODUCIBLE = "not_reproducible"


TERMINAL_STATUSES: Final[frozenset[VerdictStatus]] = frozenset(
    {
        VerdictStatus.KNOWN,
        VerdictStatus.TRIVIAL,
        VerdictStatus.REFUTED,
        VerdictStatus.SURVIVES,
        VerdictStatus.INCONCLUSIVE,
    }
)

#: Terminal for this budget, but a later run may legitimately re-open them.
REOPENABLE_STATUSES: Final[frozenset[VerdictStatus]] = frozenset(
    {VerdictStatus.INCONCLUSIVE, VerdictStatus.SURVIVES}
)

#: A candidate may not be called a survivor unless all three killers ran.
REQUIRED_SURVIVAL_CHECKS: Final[tuple[str, ...]] = ("known", "trivial", "refutation")


def _utc_now() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


@dataclass(frozen=True, slots=True)
class Verdict:
    """What the funnel concluded, and the evidence that earns the conclusion."""

    status: VerdictStatus = VerdictStatus.OPEN
    decided_by: str = ""
    decided_by_version: str = ""
    decided_at: str = ""
    evidence: Mapping[str, Any] = field(default_factory=dict)
    notes: str = ""

    def __post_init__(self) -> None:
        object.__setattr__(self, "status", VerdictStatus(self.status))
        object.__setattr__(self, "evidence", _freeze(self.evidence))

    @classmethod
    def open(cls) -> "Verdict":
        return cls()

    @property
    def is_terminal(self) -> bool:
        return self.status in TERMINAL_STATUSES

    def to_dict(self) -> dict[str, Any]:
        return {
            "status": self.status.value,
            "decided_by": self.decided_by,
            "decided_by_version": self.decided_by_version,
            "decided_at": self.decided_at,
            "evidence": _thaw(self.evidence),
            "notes": self.notes,
        }

    @classmethod
    def from_dict(cls, record: Mapping[str, Any]) -> "Verdict":
        try:
            status = VerdictStatus(record["status"])
        except (KeyError, ValueError) as exc:
            raise ValidationError(f"bad verdict status: {exc}") from exc
        return cls(
            status=status,
            decided_by=str(record.get("decided_by", "")),
            decided_by_version=str(record.get("decided_by_version", "")),
            decided_at=str(record.get("decided_at", "")),
            evidence=record.get("evidence", {}) or {},
            notes=str(record.get("notes", "")),
        )


def verdict_reasons(verdict: Verdict) -> tuple[str, ...]:
    """Entry criteria for each status. Empty tuple means the status is earned."""
    ev = verdict.evidence
    bad: list[str] = []
    if not isinstance(ev, Mapping):
        return ("verdict.evidence must be a mapping",)
    status = verdict.status
    if status is not VerdictStatus.OPEN:
        if not verdict.decided_by.strip():
            bad.append("a decided verdict must name decided_by")
        if not verdict.decided_by_version.strip():
            bad.append("a decided verdict must name decided_by_version")
        if not verdict.decided_at.strip():
            bad.append("a decided verdict must carry decided_at")

    if status is VerdictStatus.OPEN:
        if ev:
            bad.append("an open verdict carries no evidence")

    elif status is VerdictStatus.KNOWN:
        refs = ev.get("references")
        if (
            not isinstance(refs, Sequence)
            or isinstance(refs, (str, bytes))
            or not refs
            or not all(isinstance(r, str) and r.strip() for r in refs)
        ):
            bad.append("known: needs a non-empty list of references (ids, not opinion)")
        match_kind = ev.get("match_kind")
        if match_kind not in ("value", "statement", "identity"):
            bad.append("known: match_kind must be one of value|statement|identity")
        if match_kind == "value":
            defect, tol = ev.get("defect"), ev.get("tolerance")
            if not _nonnegative(defect) or not _positive(tol):
                bad.append("known(value): needs a defect >= 0 and a positive tolerance")
            elif _as_decimal(defect) > _as_decimal(tol):
                bad.append("known(value): the match is outside its own tolerance")

    elif status is VerdictStatus.TRIVIAL:
        derived = ev.get("derived_from")
        if (
            not isinstance(derived, Sequence)
            or isinstance(derived, (str, bytes))
            or not derived
        ):
            bad.append("trivial: needs derived_from, the facts it follows from")
        argument = ev.get("argument")
        if not isinstance(argument, str) or not argument.strip():
            bad.append("trivial: needs the one-line argument, written out")
        elif len(argument) > MAX_ARGUMENT_CHARS:
            bad.append(
                f"trivial: the argument exceeds {MAX_ARGUMENT_CHARS} characters, "
                "so it is not a one-line argument"
            )
        if not isinstance(ev.get("checked_by"), str) or not str(
            ev.get("checked_by")
        ).strip():
            bad.append("trivial: needs checked_by, the procedure that verified it")

    elif status is VerdictStatus.REFUTED:
        witness = ev.get("witness")
        if not isinstance(witness, Mapping) or not witness:
            bad.append("refuted: needs a witness (the parameters at which it fails)")
        defect, tol = ev.get("defect"), ev.get("tolerance")
        if not _nonnegative(defect) or not _positive(tol):
            bad.append("refuted: needs a defect >= 0 and a positive tolerance")
        elif _as_decimal(defect) <= _as_decimal(tol):
            bad.append("refuted: the defect is inside tolerance, so nothing is refuted")
        base = ev.get("effort")
        escalated = ev.get("escalated_effort")
        esc_defect = ev.get("escalated_defect")
        if not _positive(base) or not _positive(escalated):
            bad.append("refuted: needs effort and escalated_effort (positive)")
        elif _as_decimal(escalated) <= _as_decimal(base):
            bad.append(
                "refuted: the failure must persist at strictly higher effort, "
                "otherwise it may be numerical noise"
            )
        if not _nonnegative(esc_defect):
            bad.append("refuted: needs escalated_defect, the defect after escalation")
        elif _positive(tol) and _as_decimal(esc_defect) <= _as_decimal(tol):
            bad.append("refuted: the failure disappeared at higher effort")

    elif status is VerdictStatus.SURVIVES:
        checks = ev.get("checks_run")
        if (
            not isinstance(checks, Sequence)
            or isinstance(checks, (str, bytes))
            or not set(REQUIRED_SURVIVAL_CHECKS) <= set(map(str, checks))
        ):
            bad.append(
                "survives: checks_run must include all of "
                f"{list(REQUIRED_SURVIVAL_CHECKS)}, you may not survive a check "
                "that never ran"
            )
        base, verified = ev.get("effort"), ev.get("verified_effort")
        if not _positive(base) or not _positive(verified):
            bad.append("survives: needs effort and verified_effort (positive)")
        elif _as_decimal(verified) <= _as_decimal(base):
            bad.append(
                "survives: verification must cost strictly more than generation"
            )
        gap = ev.get("proof_gap")
        if not isinstance(gap, str) or not gap.strip():
            bad.append(
                "survives: needs proof_gap, what is missing before this could be "
                "a theorem. A survivor is a lead, not a result"
            )

    elif status is VerdictStatus.INCONCLUSIVE:
        try:
            InconclusiveReason(ev.get("reason"))
        except ValueError:
            bad.append(
                "inconclusive: reason must be one of "
                f"{[r.value for r in InconclusiveReason]}"
            )
        if not isinstance(ev.get("detail"), str) or not str(ev.get("detail")).strip():
            bad.append("inconclusive: needs detail")
        ceiling = ev.get("ceiling")
        if not isinstance(ceiling, Mapping) or not ceiling:
            bad.append("inconclusive: needs ceiling, the resource limit that was hit")

    return tuple(bad)


def validate_verdict(verdict: Verdict) -> None:
    """Raise :class:`ValidationError` unless the verdict earns its status."""
    reasons = verdict_reasons(verdict)
    if reasons:
        raise ValidationError(
            f"verdict '{verdict.status}' is not earned: " + "; ".join(reasons)
        )


# ---------------------------------------------------------------------------
# Provenance
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Precision:
    """How much arithmetic was bought. ``effort_digits`` makes kinds comparable."""

    kind: str = "float64"
    value: int | None = None
    backend: str | None = None

    def __post_init__(self) -> None:
        if self.kind not in PRECISION_KINDS:
            raise ValidationError(
                f"precision.kind must be one of {PRECISION_KINDS}, got {self.kind!r}"
            )
        if self.kind in ("dps", "bits"):
            if (
                isinstance(self.value, bool)
                or not isinstance(self.value, int)
                or self.value < 1
            ):
                raise ValidationError(
                    f"precision.kind={self.kind!r} needs a positive integer value"
                )
        elif self.value is not None:
            raise ValidationError(
                f"precision.kind={self.kind!r} takes no value, got {self.value!r}"
            )

    def effort_digits(self) -> float:
        """Decimal-digit equivalent, so that two precisions can be compared."""
        if self.kind == "dps":
            return float(self.value or 0)
        if self.kind == "bits":
            return float(self.value or 0) * math.log10(2.0)
        if self.kind == "float64":
            return 15.95
        return math.inf  # exact

    def to_dict(self) -> dict[str, Any]:
        return {"kind": self.kind, "value": self.value, "backend": self.backend}

    @classmethod
    def from_dict(cls, record: Mapping[str, Any]) -> "Precision":
        if not isinstance(record, Mapping):
            raise ValidationError(f"precision must be a mapping, got {record!r}")
        return cls(
            kind=str(record.get("kind", "float64")),
            value=record.get("value"),
            backend=record.get("backend"),
        )


def git_revision(
    start: str | Path | None = None, timeout: float = 5.0
) -> tuple[str | None, bool | None, str]:
    """``(revision, dirty, source)`` for the checkout containing ``start``.

    Degrades gracefully and says so: outside a repository, or with no ``git``
    on the path, returns ``(None, None, "unavailable")``. ``dirty`` reports
    modifications to *tracked* files only.
    """
    where = Path(start) if start is not None else Path(__file__).resolve().parent
    if not where.is_dir():
        where = where.parent
    common = {
        "cwd": str(where),
        "capture_output": True,
        "text": True,
        "timeout": timeout,
        "check": True,
    }
    try:
        rev = subprocess.run(["git", "rev-parse", "HEAD"], **common).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return (None, None, "unavailable")
    if not _REVISION_RE.match(rev):
        return (None, None, "unavailable")
    try:
        status = subprocess.run(
            ["git", "status", "--porcelain", "--untracked-files=no"], **common
        ).stdout
        dirty: bool | None = bool(status.strip())
    except (OSError, subprocess.SubprocessError):  # pragma: no cover - rare
        dirty = None
    return (rev, dirty, "git")


@dataclass(frozen=True, slots=True)
class Provenance:
    """Everything needed to re-derive the observation months later.

    Not decoration: :meth:`is_reproducible` is a query the metrics layer is
    expected to use, and a candidate that cannot answer it affirmatively is a
    defect in the generator that made it, not a stylistic lapse.
    """

    generator: str
    generator_version: str
    lab_object: str
    parameters: Mapping[str, Any] = field(default_factory=dict)
    precision: Precision = field(default_factory=Precision)
    seed: int | None = None
    stochastic: bool = False
    code_revision: str | None = None
    code_dirty: bool | None = None
    code_revision_source: str = "unavailable"
    captured_at: str = ""
    runtime: Mapping[str, str] = field(default_factory=dict)
    duration_s: float | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "parameters", _freeze(self.parameters))
        object.__setattr__(self, "runtime", _freeze(self.runtime))

    def is_reproducible(self) -> bool:
        """A clean, identified revision plus a seed wherever randomness enters."""
        if self.code_revision is None or self.code_dirty is not False:
            return False
        return (not self.stochastic) or isinstance(self.seed, int)

    def to_dict(self) -> dict[str, Any]:
        return {
            "generator": self.generator,
            "generator_version": self.generator_version,
            "lab_object": self.lab_object,
            "parameters": _thaw(self.parameters),
            "precision": self.precision.to_dict(),
            "seed": self.seed,
            "stochastic": self.stochastic,
            "code_revision": self.code_revision,
            "code_dirty": self.code_dirty,
            "code_revision_source": self.code_revision_source,
            "captured_at": self.captured_at,
            "runtime": _thaw(self.runtime),
            "duration_s": self.duration_s,
        }

    @classmethod
    def from_dict(cls, record: Mapping[str, Any]) -> "Provenance":
        if not isinstance(record, Mapping):
            raise ValidationError(f"provenance must be a mapping, got {record!r}")
        missing = {"generator", "generator_version", "lab_object"} - set(record)
        if missing:
            raise ValidationError(f"provenance is missing {sorted(missing)}")
        return cls(
            generator=str(record["generator"]),
            generator_version=str(record["generator_version"]),
            lab_object=str(record["lab_object"]),
            parameters=record.get("parameters", {}) or {},
            precision=Precision.from_dict(record.get("precision", {}) or {}),
            seed=record.get("seed"),
            stochastic=bool(record.get("stochastic", False)),
            code_revision=record.get("code_revision"),
            code_dirty=record.get("code_dirty"),
            code_revision_source=str(record.get("code_revision_source", "unavailable")),
            captured_at=str(record.get("captured_at", "")),
            runtime=record.get("runtime", {}) or {},
            duration_s=record.get("duration_s"),
        )


def validate_provenance(provenance: Provenance) -> None:
    """Raise unless the record could actually be replayed by a stranger."""
    bad: list[str] = []
    if not provenance.generator.strip():
        bad.append("generator must be named")
    if not provenance.generator_version.strip():
        bad.append("generator_version must be given (bump it when behaviour changes)")
    if not _DOTTED_RE.match(provenance.lab_object or ""):
        bad.append(
            "lab_object must be a dotted symbol path of the computed object, "
            f"got {provenance.lab_object!r}"
        )
    if not isinstance(provenance.parameters, Mapping):
        bad.append("parameters must be a mapping")
    else:
        for key in provenance.parameters:
            if not isinstance(key, str) or not key.isidentifier():
                bad.append(f"parameter name is not an identifier: {key!r}")
        bad.extend(_json_safety_reasons(provenance.parameters, "parameters"))
    if provenance.stochastic and not isinstance(provenance.seed, int):
        bad.append("a stochastic generator must record its seed")
    if isinstance(provenance.seed, bool):
        bad.append("seed must be an integer, not a flag")
    if provenance.code_revision_source not in ("git", "unavailable"):
        bad.append("code_revision_source must be 'git' or 'unavailable'")
    if provenance.code_revision_source == "git":
        if not isinstance(provenance.code_revision, str) or not _REVISION_RE.match(
            provenance.code_revision
        ):
            bad.append("code_revision_source='git' needs a hexadecimal revision")
    if provenance.captured_at:
        try:
            _dt.datetime.fromisoformat(provenance.captured_at)
        except ValueError:
            bad.append("captured_at must be an ISO-8601 timestamp")
    else:
        bad.append("captured_at must be recorded")
    if not isinstance(provenance.runtime, Mapping) or not all(
        isinstance(k, str) and isinstance(v, str) for k, v in provenance.runtime.items()
    ):
        bad.append("runtime must map names to version strings")
    if provenance.duration_s is not None:
        if not _nonnegative(provenance.duration_s):
            bad.append("duration_s must be a non-negative number")
    if bad:
        raise ValidationError("bad provenance: " + "; ".join(bad))


def capture_provenance(
    *,
    generator: str,
    generator_version: str,
    lab_object: str,
    parameters: Mapping[str, Any] | None = None,
    precision: Precision | None = None,
    seed: int | None = None,
    stochastic: bool = False,
    duration_s: float | None = None,
    runtime: Mapping[str, str] | None = None,
    repo_path: str | Path | None = None,
) -> Provenance:
    """Build a :class:`Provenance`, filling in revision, time and interpreter.

    ``repo_path`` defaults to the directory of this file, so nothing derived
    from a machine-specific working directory is baked in.
    """
    rev, dirty, source = git_revision(repo_path)
    env = {"python": platform.python_version()}
    env.update({str(k): str(v) for k, v in (runtime or {}).items()})
    provenance = Provenance(
        generator=generator,
        generator_version=generator_version,
        lab_object=lab_object,
        parameters=dict(parameters or {}),
        precision=precision or Precision(),
        seed=seed,
        stochastic=stochastic,
        code_revision=rev,
        code_dirty=dirty,
        code_revision_source=source,
        captured_at=_utc_now(),
        runtime=env,
        duration_s=duration_s,
    )
    validate_provenance(provenance)
    return provenance


# ---------------------------------------------------------------------------
# Immutability helpers and JSON-safety checks
# ---------------------------------------------------------------------------


def _freeze(value: Any) -> Any:
    if isinstance(value, Mapping):
        return MappingProxyType({str(k): _freeze(v) for k, v in value.items()})
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        return tuple(_freeze(v) for v in value)
    return value


def _thaw(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {str(k): _thaw(v) for k, v in value.items()}
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        return [_thaw(v) for v in value]
    if isinstance(value, Decimal):
        return str(value)
    return value


def _json_safety_reasons(value: Any, where: str) -> list[str]:
    """Non-finite floats, unserialisable types and machine-local paths."""
    bad: list[str] = []
    if isinstance(value, bool) or value is None:
        return bad
    if isinstance(value, float):
        if not math.isfinite(value):
            bad.append(f"{where}: non-finite float {value!r} cannot be valid JSON")
        return bad
    if isinstance(value, int):
        return bad
    if isinstance(value, str):
        if _LOCAL_PATH_RE.search(value):
            bad.append(f"{where}: machine-local absolute path must not be recorded")
        return bad
    if isinstance(value, Mapping):
        for key, item in value.items():
            if not isinstance(key, str):
                bad.append(f"{where}: key {key!r} is not a string")
            bad.extend(_json_safety_reasons(item, f"{where}.{key}"))
        return bad
    if isinstance(value, Sequence):
        for i, item in enumerate(value):
            bad.extend(_json_safety_reasons(item, f"{where}[{i}]"))
        return bad
    bad.append(f"{where}: {type(value).__name__} is not JSON-shaped")
    return bad


# ---------------------------------------------------------------------------
# The candidate
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class CandidateLink:
    """One non-identity graph edge from a candidate to another candidate.

    Links are annotations, not deductions.  The schema validates their shape
    but does not require the target to exist, add reciprocal equivalence links,
    or propagate verdicts along implications.
    """

    candidate_id: str
    relation: CandidateRelation

    def __post_init__(self) -> None:
        if not isinstance(self.candidate_id, str) or not _CANDIDATE_ID_RE.fullmatch(
            self.candidate_id
        ):
            raise ValidationError(
                "related candidate_id must have the form 'cand-' plus 32 lowercase "
                "hexadecimal digits"
            )
        try:
            relation = CandidateRelation(self.relation)
        except (TypeError, ValueError) as exc:
            raise ValidationError(
                f"unknown candidate relation: {self.relation!r}"
            ) from exc
        object.__setattr__(self, "relation", relation)

    def to_dict(self) -> dict[str, str]:
        return {"candidate_id": self.candidate_id, "relation": self.relation.value}

    @classmethod
    def from_dict(cls, record: Mapping[str, Any]) -> "CandidateLink":
        if not isinstance(record, Mapping):
            raise ValidationError("each related_to entry must be a mapping")
        unknown = set(record) - {"candidate_id", "relation"}
        if unknown:
            raise ValidationError(
                "unknown related_to fields: " + ", ".join(sorted(map(str, unknown)))
            )
        if "candidate_id" not in record or "relation" not in record:
            raise ValidationError(
                "each related_to entry requires candidate_id and relation"
            )
        return cls(candidate_id=record["candidate_id"], relation=record["relation"])


@dataclass(frozen=True, slots=True)
class Candidate:
    """One observation, with its identity, its support and its fate.

    ``id`` is derived, never supplied: it is the content hash of the claim.
    Two candidates with the same id are the same observation by definition,
    and the metrics layer counts them once.
    """

    kind: CandidateKind
    claim: Mapping[str, Any]
    evidence: Mapping[str, Any]
    provenance: Provenance
    verdict: Verdict = field(default_factory=Verdict)
    dedup_digits: int = DEFAULT_DEDUP_DIGITS
    label: str = ""
    related_to: tuple[CandidateLink, ...] = ()
    schema_version: str = SCHEMA_VERSION
    id: str = field(init=False, default="")

    def __post_init__(self) -> None:
        object.__setattr__(self, "kind", CandidateKind(self.kind))
        object.__setattr__(self, "claim", _freeze(self.claim))
        object.__setattr__(self, "evidence", _freeze(self.evidence))
        if not isinstance(self.related_to, Sequence) or isinstance(
            self.related_to, (str, bytes)
        ):
            raise ValidationError("related_to must be a sequence of candidate links")
        links = tuple(
            link if isinstance(link, CandidateLink) else CandidateLink.from_dict(link)
            for link in self.related_to
        )
        object.__setattr__(self, "related_to", links)
        if isinstance(self.dedup_digits, bool) or not isinstance(
            self.dedup_digits, int
        ):
            raise ValidationError("dedup_digits must be an integer")
        if not 1 <= self.dedup_digits <= 30:
            raise ValidationError("dedup_digits must lie in 1..30")
        object.__setattr__(
            self, "id", content_hash(self.kind, self.claim, self.dedup_digits)
        )

    # -- convenience ------------------------------------------------------
    def with_verdict(self, verdict: Verdict) -> "Candidate":
        """The same candidate, same id, with a new verdict appended later."""
        return replace(self, verdict=verdict)

    def reasons(self) -> tuple[str, ...]:
        """Why this candidate is malformed. Empty tuple means it is well formed."""
        return candidate_reasons(self)

    def to_dict(self) -> dict[str, Any]:
        return to_dict(self)

    @classmethod
    def from_dict(cls, record: Mapping[str, Any], *, verify_id: bool = True) -> "Candidate":
        return from_dict(record, verify_id=verify_id)


def candidate_reasons(candidate: Candidate) -> tuple[str, ...]:
    """Every way in which ``candidate`` violates the ontology."""
    bad: list[str] = []
    bad.extend(kind_reasons(candidate.kind, candidate.claim, candidate.evidence))
    bad.extend(_json_safety_reasons(_thaw(candidate.claim), "claim"))
    bad.extend(_json_safety_reasons(_thaw(candidate.evidence), "evidence"))
    # The verdict's evidence is part of the record and is written to the same
    # log, so it is held to the same two rules. Checking only claim/evidence
    # would let a screen record a machine-local path or a non-finite float,
    # which is how a validator acquires a reputation it has not earned: the
    # path reached the log silently, and the float surfaced as a TypeError from
    # json.dumps rather than as a refusal that names the field.
    bad.extend(
        _json_safety_reasons(_thaw(candidate.verdict.evidence), "verdict.evidence")
    )
    for key in candidate.claim:
        if not isinstance(key, str) or not key.isidentifier():
            bad.append(f"claim key is not an identifier: {key!r}")
    try:
        validate_provenance(candidate.provenance)
    except ValidationError as exc:
        bad.append(str(exc))
    bad.extend(verdict_reasons(candidate.verdict))
    # The resolution used for identity may not exceed the resolution the
    # evidence actually establishes: hashing digits you did not measure
    # splits a candidate from its own re-discovery.
    if candidate.kind is CandidateKind.CONSTANT:
        determined = _determined_digits(
            candidate.claim.get("value"), candidate.evidence.get("uncertainty")
        )
        if determined and candidate.dedup_digits > determined:
            bad.append(
                f"dedup_digits={candidate.dedup_digits} exceeds the "
                f"{determined:.0f} digits the error bound determines"
            )
    try:
        major = int(str(candidate.schema_version).split(".")[0])
    except ValueError:
        bad.append(f"schema_version is malformed: {candidate.schema_version!r}")
    else:
        if major != SCHEMA_MAJOR:
            bad.append(
                f"schema major {major} != {SCHEMA_MAJOR}: migrate the record first"
            )
    return tuple(bad)


def validate_claim(
    kind: CandidateKind | str,
    claim: Mapping[str, Any],
    evidence: Mapping[str, Any] | None = None,
) -> None:
    """Raise unless ``kind`` accepts this payload."""
    reasons = kind_reasons(kind, claim, evidence)
    if reasons:
        raise ValidationError(
            f"payload is not a '{CandidateKind(kind).value}' candidate: "
            + "; ".join(reasons)
        )


def validate_candidate(candidate: Candidate) -> None:
    """Raise :class:`ValidationError` listing every violation, or return."""
    reasons = candidate_reasons(candidate)
    if reasons:
        raise ValidationError("malformed candidate: " + "; ".join(reasons))


def latest_by_id(candidates: Iterable[Candidate]) -> dict[str, Candidate]:
    """Collapse an append-only log: the last record for an id wins.

    This is the reduction the metrics layer must apply before counting
    anything, and the reason the log can be appended to without rewriting.
    """
    out: dict[str, Candidate] = {}
    for candidate in candidates:
        out[candidate.id] = candidate
    return out


# ---------------------------------------------------------------------------
# The shape of the already-known detector
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class KnownEntry:
    """One entry of a domain-supplied catalogue of things already established.

    The catalogue is domain data; the matching rule is not. ``keys`` are
    identity strings (compared against :func:`claim_keys`); ``value`` and
    ``tolerance``, when present, allow a numeric match.
    """

    id: str
    reference: str
    keys: tuple[str, ...] = ()
    value: float | str | None = None
    tolerance: float | str | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "reference": self.reference,
            "keys": list(self.keys),
            "value": self.value,
            "tolerance": self.tolerance,
        }


def match_known(
    candidate: Candidate,
    catalogue: Iterable[KnownEntry],
    *,
    decided_by: str = "match_known",
    decided_by_version: str = "1.0",
) -> Verdict | None:
    """A ``known`` verdict if the catalogue already contains this observation.

    Two match modes, both evidenced:

    * **statement**: every key of an entry appears among the candidate's own
      identity strings (see :func:`claim_keys`);
    * **value**: the candidate is a ``constant`` and agrees with the entry to
      within the candidate's *own* error bound plus the entry's. Matching to
      the digits you actually determined is a strong test; matching to two
      digits is not, which is why the candidate's uncertainty, not a generous
      global tolerance, sets the bar.

    Returns ``None`` when nothing matches. It never returns a weaker status:
    deciding a candidate is *not* known is the job of the funnel, not of a
    catalogue lookup.
    """
    keys = set(claim_keys(candidate.kind, candidate.claim))
    for entry in catalogue:
        entry_keys = set(entry.keys)
        if entry_keys and entry_keys <= keys:
            return Verdict(
                status=VerdictStatus.KNOWN,
                decided_by=decided_by,
                decided_by_version=decided_by_version,
                decided_at=_utc_now(),
                evidence={
                    "references": [entry.reference],
                    "match_kind": "statement",
                    "entry_id": entry.id,
                    "matched_keys": sorted(entry_keys),
                },
            )
        if candidate.kind is CandidateKind.CONSTANT and entry.value is not None:
            value = _as_decimal(candidate.claim.get("value"))
            target = _as_decimal(entry.value)
            own = _as_decimal(candidate.evidence.get("uncertainty"))
            theirs = _as_decimal(entry.tolerance) or Decimal(0)
            if value is None or target is None or own is None:
                continue
            defect = abs(value - target)
            budget = own + theirs
            if defect <= budget:
                return Verdict(
                    status=VerdictStatus.KNOWN,
                    decided_by=decided_by,
                    decided_by_version=decided_by_version,
                    decided_at=_utc_now(),
                    evidence={
                        "references": [entry.reference],
                        "match_kind": "value",
                        "entry_id": entry.id,
                        "defect": float(defect),
                        "tolerance": float(budget),
                    },
                )
    return None


# ---------------------------------------------------------------------------
# Serialisation: JSON, JSONL, migration
# ---------------------------------------------------------------------------


def to_dict(candidate: Candidate) -> dict[str, Any]:
    """A plain, JSON-ready mapping. Key order is stable for readable diffs."""
    return {
        "schema_version": candidate.schema_version,
        "id": candidate.id,
        "kind": candidate.kind.value,
        "dedup_digits": candidate.dedup_digits,
        "label": candidate.label,
        "related_to": [link.to_dict() for link in candidate.related_to],
        "claim": _thaw(candidate.claim),
        "evidence": _thaw(candidate.evidence),
        "provenance": candidate.provenance.to_dict(),
        "verdict": candidate.verdict.to_dict(),
    }


def from_dict(record: Mapping[str, Any], *, verify_id: bool = True) -> Candidate:
    """Rebuild a candidate, refusing anything malformed.

    Unknown *top-level* keys are ignored (forward compatibility within a major
    version); unknown *claim* keys are refused (they would change identity).
    A stored ``id`` that disagrees with the claim is refused outright.
    """
    if not isinstance(record, Mapping):
        raise ValidationError(f"record must be a mapping, got {type(record).__name__}")
    record = migrate_record(record)
    for required in ("kind", "claim", "provenance"):
        if required not in record:
            raise ValidationError(f"record is missing '{required}'")
    try:
        kind = CandidateKind(record["kind"])
    except ValueError as exc:
        raise ValidationError(f"unknown candidate kind: {record['kind']!r}") from exc
    claim = record["claim"]
    evidence = record.get("evidence", {}) or {}
    if not isinstance(claim, Mapping) or not isinstance(evidence, Mapping):
        raise ValidationError("claim and evidence must be mappings")
    candidate = Candidate(
        kind=kind,
        claim=claim,
        evidence=evidence,
        provenance=Provenance.from_dict(record["provenance"]),
        verdict=Verdict.from_dict(record.get("verdict") or {"status": "open"}),
        dedup_digits=int(record.get("dedup_digits", DEFAULT_DEDUP_DIGITS)),
        label=str(record.get("label", "")),
        related_to=record.get("related_to", ()) or (),
        schema_version=str(record.get("schema_version", SCHEMA_VERSION)),
    )
    stored = record.get("id")
    if verify_id and stored is not None and stored != candidate.id:
        raise ValidationError(
            f"stored id {stored!r} does not match the claim it carries "
            f"({candidate.id!r}): the record was edited or corrupted"
        )
    validate_candidate(candidate)
    return candidate


def migrate_record(record: Mapping[str, Any]) -> Mapping[str, Any]:
    """Bring a stored record up to the current schema, or refuse it.

    Policy. Within major version 1, minor bumps may only *add optional
    fields*: an old reader tolerates them (unknown top-level keys are ignored)
    and a new reader fills defaults, so ids never move. A major bump may change
    canonicalisation and therefore changes every id; when that happens this
    function must rewrite the record and record the old id under
    ``supersedes``. Records from an unknown major are refused rather than
    guessed at.
    """
    version = str(record.get("schema_version", SCHEMA_VERSION))
    try:
        major = int(version.split(".")[0])
    except ValueError as exc:
        raise ValidationError(f"unreadable schema_version {version!r}") from exc
    if major != SCHEMA_MAJOR:
        raise ValidationError(
            f"schema major {major} is not supported by this reader "
            f"(current {SCHEMA_MAJOR}); no migration path is defined"
        )
    return record


def to_json(candidate: Candidate, *, indent: int | None = None) -> str:
    """One candidate as JSON text (``indent=None`` gives a single JSONL line)."""
    return json.dumps(
        to_dict(candidate),
        indent=indent,
        allow_nan=False,
        ensure_ascii=False,
        sort_keys=False,
    )


def from_json(text: str, *, verify_id: bool = True) -> Candidate:
    """Parse one candidate from JSON text."""
    try:
        record = json.loads(text)
    except json.JSONDecodeError as exc:
        raise ValidationError(f"not valid JSON: {exc}") from exc
    return from_dict(record, verify_id=verify_id)


def dumps_jsonl(candidates: Iterable[Candidate]) -> str:
    """Candidates as JSONL text: one record per line, append-friendly."""
    return "".join(to_json(c) + "\n" for c in candidates)


def loads_jsonl(text: str, *, verify_id: bool = True) -> list[Candidate]:
    """Parse JSONL text, naming the line number of the first bad record."""
    out: list[Candidate] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        if not line.strip():
            continue
        try:
            out.append(from_json(line, verify_id=verify_id))
        except ValidationError as exc:
            raise ValidationError(f"line {lineno}: {exc}") from exc
    return out


def append_jsonl(path: str | Path, candidate: Candidate) -> None:
    """Append one record. The log is never rewritten; the last id wins."""
    validate_candidate(candidate)
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open("a", encoding="utf-8") as handle:
        handle.write(to_json(candidate) + "\n")


def read_jsonl(path: str | Path, *, verify_id: bool = True) -> list[Candidate]:
    """Read a whole log. Missing files read as an empty log, not an error."""
    target = Path(path)
    if not target.exists():
        return []
    return loads_jsonl(target.read_text(encoding="utf-8"), verify_id=verify_id)


def write_jsonl(path: str | Path, candidates: Iterable[Candidate]) -> int:
    """Replace a log wholesale; returns the number of records written."""
    items = list(candidates)
    for candidate in items:
        validate_candidate(candidate)
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(dumps_jsonl(items), encoding="utf-8")
    return len(items)


def iter_jsonl(path: str | Path, *, verify_id: bool = True) -> Iterator[Candidate]:
    """Stream a log one record at a time (large logs need not fit in memory)."""
    target = Path(path)
    if not target.exists():
        return
    with target.open("r", encoding="utf-8") as handle:
        for lineno, line in enumerate(handle, start=1):
            if not line.strip():
                continue
            try:
                yield from_json(line, verify_id=verify_id)
            except ValidationError as exc:
                raise ValidationError(f"line {lineno}: {exc}") from exc
