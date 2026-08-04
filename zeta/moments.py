"""External data and finite estimators for the moments programme.

This module deliberately does not compute zeros.  It reads the public text
formats used by Andrew Odlyzko's tables and by the LMFDB zero-list export,
checks their structural invariants, and preserves the published decimal data
without converting absolute ordinates to binary floats.  Its estimator then
accepts a *separate*, explicitly sourced table of sampled ``abs(zeta)`` values
inside one of those imported windows.  Zero ordinates alone do not determine
the values of zeta between them.

At heights near 10^22, neighbouring ordinates differ by much less than one
float64 ulp.  :class:`ExternalZeroTable` therefore stores an exact decimal
``base`` plus exact decimal ``offsets``.  "Exact" here means exact to the text
that was ingested; it does not strengthen the source's stated accuracy.

The finite statistic is a composite-trapezoid approximation to

    1/(B-A) * integral_A^B |zeta(1/2 + it)|^(2k) dt.

Every estimate reports the caller-supplied value error separately from a
fine-versus-nested-coarse sampling-error estimate.  The scorecard likewise
keeps theorem, conjecture, finite measurement, and Euler-product truncation in
separate fields.  Its local-window comparison is a normalization diagnostic,
not a theorem about short intervals and not evidence for RH.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation, ROUND_FLOOR, localcontext
from fractions import Fraction
from functools import lru_cache
import gzip
import hashlib
from math import comb, factorial, isqrt
from pathlib import Path
import re
from typing import Final, Literal

from mpmath import mp

__all__ = [
    "ExternalZeroTable",
    "MomentError",
    "MomentEstimate",
    "MomentReference",
    "MomentScore",
    "MomentScorecard",
    "ODLYZKO_TABLES",
    "OdlyzkoTableSpec",
    "ZeroTableError",
    "estimate_moment",
    "leading_moment_mean",
    "load_lmfdb_zeros",
    "load_odlyzko_zeros",
    "moment_reference",
    "moment_scorecard",
]


class ZeroTableError(ValueError):
    """Raised when an external zero table fails structural validation."""


class MomentError(ValueError):
    """Raised when moment samples or a scorecard fail their stated contract."""


def _exact_sum(left: Decimal, right: Decimal) -> Decimal:
    """Add two finite decimals without the ambient context rounding them."""

    least_place = min(left.as_tuple().exponent, right.as_tuple().exponent)
    greatest_place = max(left.adjusted(), right.adjusted())
    with localcontext() as context:
        context.prec = max(1, greatest_place - least_place + 2)
        return left + right


def _exact_difference(left: Decimal, right: Decimal) -> Decimal:
    """Subtract two finite decimals without the ambient context rounding them."""

    return _exact_sum(left, -right)


@dataclass(frozen=True)
class OdlyzkoTableSpec:
    """Pinned public metadata for one table on Odlyzko's official page."""

    table_id: str
    first_index: int
    count: int
    base: Decimal
    accuracy_note: str
    source_url: str


_ODLYZKO_ROOT: Final = "https://www-users.cse.umn.edu/~odlyzko/zeta_tables"

# The catalogue is metadata, not bundled data.  Its counts and accuracy notes
# follow the official index and, for zeros3--5, the headers in the files.
ODLYZKO_TABLES: Final[dict[str, OdlyzkoTableSpec]] = {
    "zeros1": OdlyzkoTableSpec(
        "zeros1", 1, 100_000, Decimal(0), "within 3e-9", f"{_ODLYZKO_ROOT}/zeros1"
    ),
    "zeros2": OdlyzkoTableSpec(
        "zeros2", 1, 100, Decimal(0), "over 1000 decimal places", f"{_ODLYZKO_ROOT}/zeros2"
    ),
    "zeros3": OdlyzkoTableSpec(
        "zeros3",
        10**12 + 1,
        10_000,
        Decimal("267653395647"),
        "guaranteed within 1e-8",
        f"{_ODLYZKO_ROOT}/zeros3",
    ),
    "zeros4": OdlyzkoTableSpec(
        "zeros4",
        10**21 + 1,
        10_000,
        Decimal("144176897509546973000"),
        "not guaranteed; probably within 1e-6",
        f"{_ODLYZKO_ROOT}/zeros4",
    ),
    "zeros5": OdlyzkoTableSpec(
        "zeros5",
        10**22 + 1,
        10_000,
        Decimal("1370919909931995300000"),
        "not guaranteed; probably within 1e-6",
        f"{_ODLYZKO_ROOT}/zeros5",
    ),
    "zeros6": OdlyzkoTableSpec(
        "zeros6", 1, 2_001_052, Decimal(0), "within 4e-9", f"{_ODLYZKO_ROOT}/zeros6"
    ),
}


@dataclass(frozen=True)
class ExternalZeroTable:
    """A validated table represented as ``base + offsets`` in decimal.

    ``first_index`` uses the conventional one-based numbering of non-trivial
    zeros with positive ordinate.  ``sha256`` covers the bytes supplied to the
    loader (the compressed bytes for a gzip file), making the exact input
    reproducible.  Accuracy text is preserved as a source claim only.
    """

    provider: str
    first_index: int
    base: Decimal
    offsets: tuple[Decimal, ...]
    source_url: str
    sha256: str
    accuracy_note: str

    def __post_init__(self) -> None:
        if self.first_index < 1:
            raise ZeroTableError("first_index must be positive")
        if not self.offsets:
            raise ZeroTableError("zero table is empty")
        if not self.base.is_finite():
            raise ZeroTableError("base must be finite")
        previous: Decimal | None = None
        for position, offset in enumerate(self.offsets):
            ordinate = _exact_sum(self.base, offset)
            if not ordinate.is_finite() or ordinate <= 0:
                raise ZeroTableError(f"ordinate at position {position} is not finite and positive")
            if previous is not None and ordinate <= previous:
                raise ZeroTableError(
                    f"ordinates are not strictly increasing at indices "
                    f"{self.first_index + position - 1} and {self.first_index + position}"
                )
            previous = ordinate

    def __len__(self) -> int:
        return len(self.offsets)

    @property
    def last_index(self) -> int:
        """One-based index of the final zero in the table."""

        return self.first_index + len(self) - 1

    def ordinate(self, index: int) -> Decimal:
        """Return one ordinate as a :class:`~decimal.Decimal`."""

        position = index - self.first_index
        if position < 0 or position >= len(self):
            raise IndexError(f"zero index {index} is outside [{self.first_index}, {self.last_index}]")
        return _exact_sum(self.base, self.offsets[position])

    def spacing_after(self, index: int) -> Decimal:
        """Return ``gamma[index + 1] - gamma[index]`` without float loss."""

        position = index - self.first_index
        if position < 0 or position + 1 >= len(self):
            raise IndexError(f"no spacing after zero index {index} in this table")
        return _exact_difference(self.offsets[position + 1], self.offsets[position])


_DECIMAL_RE = re.compile(r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?")
_ODLYZKO_BASE_RE = re.compile(r"Values of gamma\s*-\s*([\d,]+)", re.IGNORECASE)
_ODLYZKO_RANGE_RE = re.compile(
    r"numbered\s+10\^(\d+)\s*\+\s*(\d+)\s+through\s+10\^\1\s*\+\s*10\^(\d+)",
    re.IGNORECASE,
)


def _read_bytes(path: str | Path) -> tuple[str, str]:
    source_path = Path(path)
    try:
        raw = source_path.read_bytes()
    except OSError as exc:
        raise ZeroTableError(f"cannot read zero table {source_path}: {exc}") from exc
    digest = hashlib.sha256(raw).hexdigest()
    if raw.startswith(b"\x1f\x8b"):
        try:
            raw = gzip.decompress(raw)
        except (gzip.BadGzipFile, EOFError, OSError) as exc:
            raise ZeroTableError(f"invalid or truncated gzip table: {exc}") from exc
    try:
        return raw.decode("ascii"), digest
    except UnicodeDecodeError as exc:
        raise ZeroTableError("zero table must be ASCII text") from exc


def _check_digest(actual: str, expected: str | None) -> None:
    if expected is None:
        return
    normalised = expected.lower()
    if not re.fullmatch(r"[0-9a-f]{64}", normalised):
        raise ZeroTableError("expected_sha256 must contain exactly 64 hexadecimal digits")
    if actual != normalised:
        raise ZeroTableError(f"SHA-256 mismatch: expected {normalised}, got {actual}")


def _decimal(token: str, *, line_number: int) -> Decimal:
    if _DECIMAL_RE.fullmatch(token) is None:
        raise ZeroTableError(f"line {line_number}: invalid decimal {token!r}")
    try:
        value = Decimal(token)
    except InvalidOperation as exc:
        raise ZeroTableError(f"line {line_number}: invalid decimal {token!r}") from exc
    if not value.is_finite():
        raise ZeroTableError(f"line {line_number}: ordinate must be finite")
    return value


def load_lmfdb_zeros(
    path: str | Path,
    *,
    expected_count: int | None = None,
    expected_first_index: int | None = None,
    expected_sha256: str | None = None,
    source_url: str = "https://www.lmfdb.org/zeros/zeta/",
) -> ExternalZeroTable:
    """Load an LMFDB plain-text export containing ``index ordinate`` rows.

    Indices must be positive and contiguous; ordinates must be finite, positive,
    and strictly increasing.  Pass the count and/or published checksum when a
    partial download must be detected.  LMFDB's compressed bulk binary format
    is intentionally outside this loader's scope.
    """

    text, digest = _read_bytes(path)
    _check_digest(digest, expected_sha256)
    rows: list[tuple[int, Decimal]] = []
    for line_number, raw_line in enumerate(text.splitlines(), 1):
        line = raw_line.strip()
        if not line:
            continue
        fields = line.split()
        if len(fields) != 2:
            raise ZeroTableError(f"line {line_number}: expected 'index ordinate'")
        try:
            index = int(fields[0])
        except ValueError as exc:
            raise ZeroTableError(f"line {line_number}: invalid zero index {fields[0]!r}") from exc
        if index < 1:
            raise ZeroTableError(f"line {line_number}: zero index must be positive")
        ordinate = _decimal(fields[1], line_number=line_number)
        if rows and index != rows[-1][0] + 1:
            raise ZeroTableError(
                f"line {line_number}: index {index} does not follow {rows[-1][0]}"
            )
        rows.append((index, ordinate))

    if not rows:
        raise ZeroTableError("zero table is empty")
    first_index = rows[0][0]
    if expected_first_index is not None and first_index != expected_first_index:
        raise ZeroTableError(
            f"first index mismatch: expected {expected_first_index}, got {first_index}"
        )
    if expected_count is not None and len(rows) != expected_count:
        raise ZeroTableError(f"row count mismatch: expected {expected_count}, got {len(rows)}")

    base = rows[0][1].to_integral_value(rounding=ROUND_FLOOR)
    offsets = tuple(_exact_difference(value, base) for _, value in rows)
    return ExternalZeroTable(
        provider="LMFDB",
        first_index=first_index,
        base=base,
        offsets=offsets,
        source_url=source_url,
        sha256=digest,
        accuracy_note="LMFDB reports absolute source precision of 2^-102",
    )


def load_odlyzko_zeros(
    path: str | Path,
    *,
    table_id: str | None = None,
    expected_sha256: str | None = None,
) -> ExternalZeroTable:
    """Load one of the six text tables listed on Odlyzko's official page.

    ``table_id`` is inferred from a basename ``zeros1`` through ``zeros6``;
    pass it explicitly for a renamed download.  High-table prose headers are
    parsed and checked against the pinned catalogue rather than trusted as
    unstructured comments.  The declared row count makes truncation fail.
    """

    source_path = Path(path)
    resolved_id = table_id or source_path.name.removesuffix(".gz")
    try:
        spec = ODLYZKO_TABLES[resolved_id]
    except KeyError as exc:
        raise ZeroTableError(
            "unknown Odlyzko table; pass table_id='zeros1' through 'zeros6'"
        ) from exc

    text, digest = _read_bytes(source_path)
    _check_digest(digest, expected_sha256)
    header = " ".join(line.strip() for line in text.splitlines()[:12])
    base_match = _ODLYZKO_BASE_RE.search(header)
    range_match = _ODLYZKO_RANGE_RE.search(header)
    if base_match is not None:
        header_base = Decimal(base_match.group(1).replace(",", ""))
        if header_base != spec.base:
            raise ZeroTableError(f"header base {header_base} disagrees with {resolved_id} catalogue")
    if range_match is not None:
        exponent, start_delta, end_exponent = map(int, range_match.groups())
        header_first = 10**exponent + start_delta
        header_count = 10**end_exponent - start_delta + 1
        if header_first != spec.first_index or header_count != spec.count:
            raise ZeroTableError(f"header index range disagrees with {resolved_id} catalogue")
    if resolved_id in {"zeros3", "zeros4", "zeros5"} and (
        base_match is None or range_match is None
    ):
        raise ZeroTableError(f"{resolved_id} is missing its required base/index header")

    offsets: list[Decimal] = []
    for line_number, raw_line in enumerate(text.splitlines(), 1):
        token = raw_line.strip()
        if not token or _DECIMAL_RE.fullmatch(token) is None:
            continue
        offsets.append(_decimal(token, line_number=line_number))
    if len(offsets) != spec.count:
        raise ZeroTableError(f"row count mismatch: expected {spec.count}, got {len(offsets)}")

    return ExternalZeroTable(
        provider="Odlyzko",
        first_index=spec.first_index,
        base=spec.base,
        offsets=tuple(offsets),
        source_url=spec.source_url,
        sha256=digest,
        accuracy_note=spec.accuracy_note,
    )


# --------------------------------------------------------------------------- #
# Finite moment estimates from separately supplied critical-line values
# --------------------------------------------------------------------------- #


_DecimalInput = Decimal | str | int
_ErrorKind = Literal["bound", "estimate"]
_LiteratureStatus = Literal["theorem", "conjecture"]


@dataclass(frozen=True)
class MomentEstimate:
    """One finite, provenance-carrying critical-line moment estimate.

    ``mean_value`` approximates

    ``(B-A)^-1 * integral_A^B |zeta(1/2 + it)|^(2k) dt``.

    ``sampling_error_estimate`` is the absolute difference between the
    composite-trapezoid result on the supplied grid and on its every-other
    nested grid.  It is a diagnostic, not a rigorous error bound.
    ``value_error`` propagates the caller-supplied pointwise errors by
    monotonic interval endpoints; ``value_error_kind`` records whether the
    caller described those inputs as bounds or estimates.
    """

    k: int
    power: int
    interval_start: Decimal
    interval_end: Decimal
    width: Decimal
    sample_count: int
    mean_value: Decimal
    sampling_error_estimate: Decimal
    value_error: Decimal
    value_error_kind: _ErrorKind
    value_source: str
    sample_sha256: str
    table_provider: str
    table_sha256: str
    table_first_index: int
    table_last_index: int
    normalization: str
    quadrature: str

    def __post_init__(self) -> None:
        if isinstance(self.k, bool) or not isinstance(self.k, int) or self.k < 1:
            raise MomentError("k must be a positive integer")
        if self.power != 2 * self.k:
            raise MomentError("power must equal 2*k")
        if self.interval_end <= self.interval_start or self.width != _exact_difference(
            self.interval_end, self.interval_start
        ):
            raise MomentError("moment interval and width are inconsistent")
        if self.sample_count < 5 or self.sample_count % 2 == 0:
            raise MomentError("moment estimate requires an odd number of at least five samples")
        for name, value in (
            ("mean_value", self.mean_value),
            ("sampling_error_estimate", self.sampling_error_estimate),
            ("value_error", self.value_error),
        ):
            if not value.is_finite() or value < 0:
                raise MomentError(f"{name} must be finite and non-negative")
        if self.value_error_kind not in {"bound", "estimate"}:
            raise MomentError("value_error_kind must be 'bound' or 'estimate'")
        if not self.value_source.strip():
            raise MomentError("value_source must be non-empty")
        if re.fullmatch(r"[0-9a-f]{64}", self.sample_sha256) is None:
            raise MomentError("sample_sha256 must contain 64 lowercase hexadecimal digits")


@dataclass(frozen=True)
class MomentReference:
    """Leading-order reference for the ``2k``-th zeta moment.

    The convention is

    ``integral_0^T |zeta(1/2+it)|^(2k) dt ~ C_k T (log T)^(k^2)``.

    The coefficient is a theorem only for ``k=1,2``.  For ``k=3,4`` it is the
    Keating--Snaith/CFKRS conjectural coefficient.  The latter uses a finite
    Euler product; ``coefficient_truncation_error`` is a conservative analytic
    bound for omitted Euler factors, but it does not enclose the guarded
    mpmath rounding and therefore is not a certificate.
    """

    k: int
    power: int
    log_power: int
    literature_status: _LiteratureStatus
    leading_coefficient: Decimal
    coefficient_truncation_error: Decimal
    arithmetic_factor: Decimal
    random_matrix_integer: int
    prime_cutoff: int | None
    formula: str
    scope: str
    source: str
    truncation_note: str

    def __post_init__(self) -> None:
        if self.k not in {1, 2, 3, 4}:
            raise MomentError("moment references are implemented for k=1,2,3,4")
        if self.power != 2 * self.k or self.log_power != self.k * self.k:
            raise MomentError("moment-reference powers are inconsistent with k")
        if self.literature_status not in {"theorem", "conjecture"}:
            raise MomentError("literature_status must be 'theorem' or 'conjecture'")
        if not self.leading_coefficient.is_finite() or self.leading_coefficient <= 0:
            raise MomentError("leading_coefficient must be finite and positive")
        if (
            not self.coefficient_truncation_error.is_finite()
            or self.coefficient_truncation_error < 0
        ):
            raise MomentError("coefficient_truncation_error must be finite and non-negative")
        if not self.arithmetic_factor.is_finite() or self.arithmetic_factor <= 0:
            raise MomentError("arithmetic_factor must be finite and positive")
        if self.random_matrix_integer < 1:
            raise MomentError("random_matrix_integer must be positive")


@dataclass(frozen=True)
class MomentScore:
    """One row of a :class:`MomentScorecard`."""

    k: int
    estimate: MomentEstimate
    reference: MomentReference
    leading_prediction: Decimal | None
    prediction_truncation_error: Decimal | None
    ratio_to_leading: Decimal | None
    relative_residual: Decimal | None
    calibration_passed: bool | None
    prediction_released: bool


@dataclass(frozen=True)
class MomentScorecard:
    """Theorem-calibrated comparison of finite measurements and references.

    Rows ``k=3,4`` are withheld unless both theorem rows ``k=1,2`` agree with
    their leading normalizations to the caller's stated relative tolerance.
    Passing this gate validates only this numerical instrument on this sample;
    it is not evidence for the conjectural higher-moment formulas or for RH.
    """

    rows: tuple[MomentScore, ...]
    calibration_relative_tolerance: Decimal
    calibration_passed: bool
    withheld_k: tuple[int, ...]
    scope_note: str


def _moment_decimal(value: object, *, field: str) -> Decimal:
    """Coerce a decimal input while rejecting already-rounded binary floats."""

    if isinstance(value, bool):
        raise MomentError(f"{field} must be a decimal number, not bool")
    if isinstance(value, float):
        raise MomentError(
            f"{field} must not be a binary float; pass Decimal, int, or a decimal string"
        )
    if isinstance(value, Decimal):
        result = value
    elif isinstance(value, (int, str)):
        try:
            result = Decimal(value)
        except (InvalidOperation, ValueError) as exc:
            raise MomentError(f"{field} is not a valid decimal") from exc
    else:
        raise MomentError(f"{field} must be Decimal, int, or a decimal string")
    if not result.is_finite():
        raise MomentError(f"{field} must be finite")
    return result


def _moment_series(values: Sequence[object], *, field: str) -> tuple[Decimal, ...]:
    try:
        raw_values = tuple(values)
    except TypeError as exc:
        raise MomentError(f"{field} must be a finite sequence") from exc
    return tuple(
        _moment_decimal(value, field=f"{field}[{position}]")
        for position, value in enumerate(raw_values)
    )


def _error_series(values: Sequence[object] | _DecimalInput, count: int) -> tuple[Decimal, ...]:
    if isinstance(values, (Decimal, str, int)) and not isinstance(values, bool):
        value = _moment_decimal(values, field="absolute_value_errors")
        return (value,) * count
    errors = _moment_series(values, field="absolute_value_errors")  # type: ignore[arg-type]
    if len(errors) != count:
        raise MomentError("absolute_value_errors must contain one per sample")
    return errors


def _trapezoid(xs: Sequence[Decimal], ys: Sequence[Decimal]) -> Decimal:
    total = Decimal(0)
    two = Decimal(2)
    for left in range(len(xs) - 1):
        width = _exact_difference(xs[left + 1], xs[left])
        total += width * (ys[left] + ys[left + 1]) / two
    return total


def _sample_digest(
    offsets: Sequence[Decimal],
    values: Sequence[Decimal],
    errors: Sequence[Decimal],
    *,
    error_kind: _ErrorKind,
    value_source: str,
) -> str:
    """Fingerprint the exact decimal sample contract independently of ``k``."""

    digest = hashlib.sha256()
    digest.update(b"zeta.moments.sample.v1\0")
    items: list[bytes] = [error_kind.encode("ascii"), value_source.encode("utf-8")]
    for offset, value, error in zip(offsets, values, errors, strict=True):
        items.extend(
            (
                repr(offset.as_tuple()).encode("ascii"),
                repr(value.as_tuple()).encode("ascii"),
                repr(error.as_tuple()).encode("ascii"),
            )
        )
    for item in items:
        digest.update(len(item).to_bytes(8, "big"))
        digest.update(item)
    return digest.hexdigest()


def estimate_moment(
    table: ExternalZeroTable,
    *,
    k: int,
    sample_offsets: Sequence[Decimal | str | int],
    abs_zeta_values: Sequence[Decimal | str | int],
    absolute_value_errors: Sequence[Decimal | str | int] | Decimal | str | int,
    error_kind: Literal["bound", "estimate"],
    value_source: str,
    dps: int = 60,
) -> MomentEstimate:
    """Estimate a finite ``2k``-th moment on an imported-zero window.

    ``sample_offsets`` use the *same base* as ``table.offsets``.  This is
    mandatory at high height: absolute float64 ordinates can collapse distinct
    sample points.  The sample grid must contain an odd number of at least five
    points so its every-other subsequence has the same endpoints and provides a
    visible sampling diagnostic.

    ``abs_zeta_values`` are a separate input: this function never infers zeta
    values from zero ordinates.  ``absolute_value_errors`` may be one decimal
    applied to every value or one decimal per sample.  State whether those
    inputs are claimed ``"bound"`` values or only ``"estimate"`` values, and
    identify their acquisition/evaluator in ``value_source``.
    """

    if not isinstance(table, ExternalZeroTable):
        raise MomentError("table must be an ExternalZeroTable")
    if isinstance(k, bool) or not isinstance(k, int) or k < 1:
        raise MomentError("k must be a positive integer")
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 30:
        raise MomentError("dps must be an integer at least 30")
    if error_kind not in {"bound", "estimate"}:
        raise MomentError("error_kind must be 'bound' or 'estimate'")
    if not isinstance(value_source, str) or not value_source.strip():
        raise MomentError("value_source must be a non-empty string")

    offsets = _moment_series(sample_offsets, field="sample_offsets")
    values = _moment_series(abs_zeta_values, field="abs_zeta_values")
    if len(offsets) != len(values):
        raise MomentError("sample_offsets and abs_zeta_values must have the same length")
    if len(offsets) < 5 or len(offsets) % 2 == 0:
        raise MomentError("the nested-grid diagnostic requires an odd number of at least five samples")
    errors = _error_series(absolute_value_errors, len(offsets))
    normalised_source = value_source.strip()

    for position, (offset, value, error) in enumerate(zip(offsets, values, errors, strict=True)):
        if position and offset <= offsets[position - 1]:
            raise MomentError("sample_offsets must be strictly increasing")
        if offset < table.offsets[0] or offset > table.offsets[-1]:
            raise MomentError(f"sample offset at position {position} is outside the imported window")
        if value < 0:
            raise MomentError("abs_zeta_values must be non-negative")
        if error < 0:
            raise MomentError("absolute_value_errors must be non-negative")

    width = _exact_difference(offsets[-1], offsets[0])
    if width <= 0:
        raise MomentError("sample interval must have positive width")
    power = 2 * k
    significant_digits = max(
        (len(number.as_tuple().digits) for number in (*values, *errors)),
        default=1,
    )
    work_dps = max(dps, power * significant_digits + 20)
    with localcontext() as context:
        context.prec = work_dps
        powered = tuple(value**power for value in values)
        fine_mean = _trapezoid(offsets, powered) / width

        coarse_offsets = offsets[::2]
        coarse_powered = powered[::2]
        coarse_mean = _trapezoid(coarse_offsets, coarse_powered) / width
        sampling_error = abs(fine_mean - coarse_mean)

        lower_powered = tuple(
            max(Decimal(0), value - error) ** power
            for value, error in zip(values, errors, strict=True)
        )
        upper_powered = tuple(
            (value + error) ** power for value, error in zip(values, errors, strict=True)
        )
        lower_mean = _trapezoid(offsets, lower_powered) / width
        upper_mean = _trapezoid(offsets, upper_powered) / width
        value_error = max(abs(fine_mean - lower_mean), abs(upper_mean - fine_mean))

    return MomentEstimate(
        k=k,
        power=power,
        interval_start=_exact_sum(table.base, offsets[0]),
        interval_end=_exact_sum(table.base, offsets[-1]),
        width=width,
        sample_count=len(offsets),
        mean_value=fine_mean,
        sampling_error_estimate=sampling_error,
        value_error=value_error,
        value_error_kind=error_kind,
        value_source=normalised_source,
        sample_sha256=_sample_digest(
            offsets,
            values,
            errors,
            error_kind=error_kind,
            value_source=normalised_source,
        ),
        table_provider=table.provider,
        table_sha256=table.sha256,
        table_first_index=table.first_index,
        table_last_index=table.last_index,
        normalization="1 / (B - A) times integral_A^B |zeta(1/2 + i t)|^(2k) dt",
        quadrature="composite trapezoid; sampling estimate is fine minus every-other nested grid",
    )


# --------------------------------------------------------------------------- #
# Leading constants and the theorem/prediction scorecard
# --------------------------------------------------------------------------- #


@lru_cache(maxsize=16)
def _primes_up_to(limit: int) -> tuple[int, ...]:
    if limit < 2:
        return ()
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start : limit + 1 : prime] = b"\x00" * (((limit - start) // prime) + 1)
    return tuple(index for index, is_prime in enumerate(sieve) if is_prime)


def _random_matrix_integer(k: int) -> int:
    value = Fraction(factorial(k * k), 1)
    for j in range(k):
        value *= Fraction(factorial(j), factorial(k + j))
    if value.denominator != 1:  # pragma: no cover - protects the exact formula
        raise ArithmeticError("Keating--Snaith factor unexpectedly failed to be integral")
    return value.numerator


def _local_factor_coefficients(k: int) -> tuple[int, ...]:
    """Coefficients of the exact integer-k Euler factor in x = 1/p."""

    numerator = [comb(k - 1, j) ** 2 for j in range(k)]
    exponent = (k - 1) ** 2
    binomial = [(-1) ** j * comb(exponent, j) for j in range(exponent + 1)]
    result = [0] * (len(numerator) + len(binomial) - 1)
    for left, left_value in enumerate(numerator):
        for right, right_value in enumerate(binomial):
            result[left + right] += left_value * right_value
    if result[0] != 1 or (len(result) > 1 and result[1] != 0):
        raise ArithmeticError("arithmetic Euler factor failed its constant/linear cancellation")
    return tuple(result)


def _mp_to_decimal(value: object, *, dps: int) -> Decimal:
    return Decimal(mp.nstr(value, n=dps))


@lru_cache(maxsize=32)
def _moment_reference_cached(k: int, prime_cutoff: int, dps: int) -> MomentReference:
    random_matrix_integer = _random_matrix_integer(k)
    status: _LiteratureStatus = "theorem" if k <= 2 else "conjecture"
    source = (
        "Hardy--Littlewood second-moment theorem"
        if k == 1
        else "Ingham fourth-moment theorem"
        if k == 2
        else "Keating--Snaith leading-moment conjecture; CFKRS arithmetic factor"
    )

    with mp.workdps(dps + 25):
        rmt_factor = mp.mpf(random_matrix_integer) / factorial(k * k)
        if k == 1:
            arithmetic_factor = mp.mpf(1)
            coefficient_error = mp.mpf(0)
            recorded_cutoff: int | None = None
            truncation_note = "closed-form theorem coefficient; no Euler-product truncation"
        elif k == 2:
            arithmetic_factor = 6 / mp.pi**2
            coefficient_error = mp.mpf(0)
            recorded_cutoff = None
            truncation_note = "a_2 = 1/zeta(2) = 6/pi^2; no Euler-product truncation"
        else:
            arithmetic_factor = mp.mpf(1)
            for prime in _primes_up_to(prime_cutoff):
                x = mp.mpf(1) / prime
                local = (1 - x) ** ((k - 1) ** 2) * sum(
                    comb(k - 1, j) ** 2 * x**j for j in range(k)
                )
                arithmetic_factor *= local

            # If L_k(x)=1+sum_{r>=2} c_r x^r, then for p>P,
            # |L_k(1/p)-1| <= D/p^2, D=sum |c_r|.  Bound log(1+u) by
            # |u|/(1-|u|), and sum over primes by sum_{n>P} n^-2 < 1/P.
            # This deliberately sacrifices sharpness for an explicit tail.
            coefficients = _local_factor_coefficients(k)
            coefficient_mass = sum(abs(value) for value in coefficients[2:])
            max_u = mp.mpf(coefficient_mass) / (prime_cutoff + 1) ** 2
            if max_u >= 1:  # protected by the public cutoff validation
                raise MomentError("prime_cutoff is too small for the Euler-tail bound")
            log_tail = mp.mpf(coefficient_mass) / (1 - max_u) / prime_cutoff
            relative_tail = mp.exp(log_tail) - 1
            coefficient_error = arithmetic_factor * rmt_factor * relative_tail
            recorded_cutoff = prime_cutoff
            truncation_note = (
                "analytic upper bound for omitted Euler factors; guarded mpmath rounding "
                "is not enclosed, so this is not a certificate"
            )

        coefficient = arithmetic_factor * rmt_factor
        return MomentReference(
            k=k,
            power=2 * k,
            log_power=k * k,
            literature_status=status,
            leading_coefficient=_mp_to_decimal(coefficient, dps=dps),
            coefficient_truncation_error=_mp_to_decimal(coefficient_error, dps=dps),
            arithmetic_factor=_mp_to_decimal(arithmetic_factor, dps=dps),
            random_matrix_integer=random_matrix_integer,
            prime_cutoff=recorded_cutoff,
            formula="C_k = a_k * g_k / (k^2)!",
            scope="global integral from 0 to T as T tends to infinity",
            source=source,
            truncation_note=truncation_note,
        )


def moment_reference(k: int, *, prime_cutoff: int = 100_000, dps: int = 50) -> MomentReference:
    """Return the leading reference for the second through eighth moments.

    ``k=1,2`` recover the proved coefficients ``1`` and ``1/(2*pi^2)``.
    ``k=3,4`` evaluate the conjectural arithmetic Euler product through
    ``prime_cutoff`` and report a separate conservative omitted-factor error.
    """

    if isinstance(k, bool) or not isinstance(k, int) or k not in {1, 2, 3, 4}:
        raise MomentError("moment_reference implements k=1,2,3,4")
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 30:
        raise MomentError("dps must be an integer at least 30")
    if isinstance(prime_cutoff, bool) or not isinstance(prime_cutoff, int):
        raise MomentError("prime_cutoff must be an integer")
    if k >= 3 and prime_cutoff < 100:
        raise MomentError("prime_cutoff must be at least 100 for k=3,4")
    return _moment_reference_cached(k, prime_cutoff, dps)


def _leading_log_mean(
    log_power: int, interval_start: Decimal, interval_end: Decimal, *, dps: int
) -> Decimal:
    if interval_start <= Decimal("6.2831853071795864769252867665590057683943387987502"):
        raise MomentError("leading moment normalization requires A > 2*pi")
    width = _exact_difference(interval_end, interval_start)
    if width <= 0:
        raise MomentError("leading moment normalization requires B > A")

    # F_n(t) = t * sum_{j=0}^n (-1)^j n!/(n-j)! log(t/2pi)^(n-j)
    # differentiates exactly to log(t/2pi)^n.  Extra digits protect the
    # subtraction F(B)-F(A) when a narrow window sits near height 10^22.
    cancellation_digits = max(0, interval_start.adjusted() - width.adjusted())
    with mp.workdps(dps + cancellation_digits + 20):
        start = mp.mpf(str(interval_start))
        end = mp.mpf(str(interval_end))

        def antiderivative(t):
            logarithm = mp.log(t / (2 * mp.pi))
            total = mp.mpf(0)
            falling = 1
            for j in range(log_power + 1):
                if j:
                    falling *= log_power - j + 1
                total += (-1) ** j * falling * logarithm ** (log_power - j)
            return t * total

        mean = (antiderivative(end) - antiderivative(start)) / (end - start)
        return _mp_to_decimal(mean, dps=dps)


def leading_moment_mean(
    reference: MomentReference,
    interval_start: Decimal | str | int,
    interval_end: Decimal | str | int,
    *,
    dps: int = 50,
) -> Decimal:
    """Average the leading density over ``[A,B]`` for normalization.

    This computes

    ``C_k/(B-A) * integral_A^B log(t/(2*pi))^(k^2) dt``.

    For a short or shifted finite window this is a diagnostic extrapolation.
    Even when ``reference.literature_status == "theorem"``, the theorem is a
    global ``[0,T]`` asymptotic and does not turn this local comparison into a
    short-interval theorem.
    """

    if not isinstance(reference, MomentReference):
        raise MomentError("reference must be a MomentReference")
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 30:
        raise MomentError("dps must be an integer at least 30")
    start = _moment_decimal(interval_start, field="interval_start")
    end = _moment_decimal(interval_end, field="interval_end")
    log_mean = _leading_log_mean(reference.log_power, start, end, dps=dps)
    with localcontext() as context:
        context.prec = dps
        return +(reference.leading_coefficient * log_mean)


def moment_scorecard(
    estimates: Sequence[MomentEstimate],
    *,
    calibration_relative_tolerance: Decimal | str | int,
    references: Mapping[int, MomentReference] | None = None,
    prime_cutoff: int = 100_000,
    dps: int = 50,
) -> MomentScorecard:
    """Compare finite estimates with leading references behind a theorem gate.

    Estimates for ``k=1`` and ``k=2`` are mandatory and must share the same
    interval, samples, value source, and imported-table digest as every other
    row.  The conjectural ``k=3,4`` predictions are returned only when both
    theorem rows have raw relative residual at most
    ``calibration_relative_tolerance``.  Numerical error fields remain visible
    but are not subtracted to manufacture a passing calibration.
    """

    try:
        rows_input = tuple(estimates)
    except TypeError as exc:
        raise MomentError("estimates must be a finite sequence") from exc
    if not rows_input:
        raise MomentError("scorecard requires moment estimates")
    if any(not isinstance(estimate, MomentEstimate) for estimate in rows_input):
        raise MomentError("every estimate must be a MomentEstimate")
    by_k = {estimate.k: estimate for estimate in rows_input}
    if len(by_k) != len(rows_input):
        raise MomentError("scorecard accepts at most one estimate for each k")
    if not {1, 2}.issubset(by_k):
        raise MomentError("scorecard calibration requires estimates for k=1 and k=2")
    unsupported = sorted(set(by_k) - {1, 2, 3, 4})
    if unsupported:
        raise MomentError(f"scorecard has no reference for k={unsupported[0]}")

    first = rows_input[0]
    provenance = (
        first.interval_start,
        first.interval_end,
        first.sample_count,
        first.value_source,
        first.sample_sha256,
        first.table_provider,
        first.table_sha256,
        first.table_first_index,
        first.table_last_index,
    )
    for estimate in rows_input[1:]:
        candidate = (
            estimate.interval_start,
            estimate.interval_end,
            estimate.sample_count,
            estimate.value_source,
            estimate.sample_sha256,
            estimate.table_provider,
            estimate.table_sha256,
            estimate.table_first_index,
            estimate.table_last_index,
        )
        if candidate != provenance:
            raise MomentError("all scorecard rows must share one sample window and provenance")

    tolerance = _moment_decimal(
        calibration_relative_tolerance, field="calibration_relative_tolerance"
    )
    if tolerance < 0:
        raise MomentError("calibration_relative_tolerance must be non-negative")
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 30:
        raise MomentError("dps must be an integer at least 30")

    selected_references: dict[int, MomentReference] = {}
    for k in by_k:
        reference = references[k] if references is not None and k in references else None
        if reference is None:
            if references is not None:
                raise MomentError(f"references is missing k={k}")
            reference = moment_reference(k, prime_cutoff=prime_cutoff, dps=dps)
        if not isinstance(reference, MomentReference) or reference.k != k:
            raise MomentError(f"reference for k={k} is inconsistent")
        selected_references[k] = reference
    if any(selected_references[k].literature_status != "theorem" for k in (1, 2)):
        raise MomentError("calibration references for k=1,2 must be theorem rows")

    predictions: dict[int, Decimal] = {}
    prediction_errors: dict[int, Decimal] = {}
    residuals: dict[int, Decimal] = {}
    for k, estimate in by_k.items():
        reference = selected_references[k]
        log_mean = _leading_log_mean(
            reference.log_power, estimate.interval_start, estimate.interval_end, dps=dps
        )
        with localcontext() as context:
            context.prec = dps
            prediction = +(reference.leading_coefficient * log_mean)
            prediction_error = +(reference.coefficient_truncation_error * log_mean)
            residual = +(abs(estimate.mean_value - prediction) / abs(prediction))
        predictions[k] = prediction
        prediction_errors[k] = prediction_error
        residuals[k] = residual

    calibration_by_k = {k: residuals[k] <= tolerance for k in (1, 2)}
    calibration_passed = all(calibration_by_k.values())
    withheld = tuple(k for k in sorted(by_k) if k > 2 and not calibration_passed)

    rows: list[MomentScore] = []
    for k in sorted(by_k):
        released = k <= 2 or calibration_passed
        prediction = predictions[k] if released else None
        prediction_error = prediction_errors[k] if released else None
        with localcontext() as context:
            context.prec = dps
            ratio = +(by_k[k].mean_value / prediction) if prediction is not None else None
        rows.append(
            MomentScore(
                k=k,
                estimate=by_k[k],
                reference=selected_references[k],
                leading_prediction=prediction,
                prediction_truncation_error=prediction_error,
                ratio_to_leading=ratio,
                relative_residual=residuals[k] if released else None,
                calibration_passed=calibration_by_k[k] if k in calibration_by_k else None,
                prediction_released=released,
            )
        )

    return MomentScorecard(
        rows=tuple(rows),
        calibration_relative_tolerance=tolerance,
        calibration_passed=calibration_passed,
        withheld_k=withheld,
        scope_note=(
            "The theorem labels concern global [0,T] asymptotics.  Every local finite-window "
            "comparison here is a normalization diagnostic, not a short-interval theorem, "
            "not validation of a conjecture, and not evidence for RH."
        ),
    )
