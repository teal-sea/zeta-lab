"""External data and finite estimators for the moments programme.

This module deliberately does not compute zeros.  It reads the public text
formats used by Andrew Odlyzko's tables and by the LMFDB zero-list export,
checks their structural invariants, and preserves the published decimal data
without converting absolute ordinates to binary floats.  Its estimator then
accepts a *separate*, explicitly sourced table of sampled ``abs(zeta)`` values
inside one of those imported windows.  Zero ordinates alone do not determine
the values of zeta between them.  The value-table loader preserves exact
decimal tokens, fingerprints the supplied bytes, and binds them to the digest
of the zero table that defines their offset origin.

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
    "CriticalLineSampleTable",
    "ExternalZeroTable",
    "MomentError",
    "MomentEstimate",
    "MomentPolynomial",
    "MomentReference",
    "MomentScore",
    "MomentScorecard",
    "ODLYZKO_TABLES",
    "OdlyzkoTableSpec",
    "ZeroTableError",
    "estimate_moment",
    "estimate_moment_from_samples",
    "leading_moment_mean",
    "moment_polynomial",
    "moment_polynomial_mean",
    "load_lmfdb_zeros",
    "load_critical_line_samples",
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


def _read_bytes(
    path: str | Path,
    *,
    error_type: type[ValueError] = ZeroTableError,
    label: str = "zero table",
) -> tuple[str, str]:
    source_path = Path(path)
    try:
        raw = source_path.read_bytes()
    except OSError as exc:
        raise error_type(f"cannot read {label} {source_path}: {exc}") from exc
    digest = hashlib.sha256(raw).hexdigest()
    if raw.startswith(b"\x1f\x8b"):
        try:
            raw = gzip.decompress(raw)
        except (gzip.BadGzipFile, EOFError, OSError) as exc:
            raise error_type(f"invalid or truncated gzip {label}: {exc}") from exc
    try:
        return raw.decode("ascii"), digest
    except UnicodeDecodeError as exc:
        raise error_type(f"{label} must be ASCII text") from exc


def _check_digest(
    actual: str,
    expected: str | None,
    *,
    error_type: type[ValueError] = ZeroTableError,
) -> None:
    if expected is None:
        return
    if not isinstance(expected, str):
        raise error_type("expected_sha256 must contain exactly 64 hexadecimal digits")
    normalised = expected.lower()
    if not re.fullmatch(r"[0-9a-f]{64}", normalised):
        raise error_type("expected_sha256 must contain exactly 64 hexadecimal digits")
    if actual != normalised:
        raise error_type(f"SHA-256 mismatch: expected {normalised}, got {actual}")


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
class CriticalLineSampleTable:
    """A checked, provenance-carrying table of sampled ``abs(zeta)`` values.

    ``offsets`` share the decimal ``base`` of one :class:`ExternalZeroTable`.
    ``sha256`` covers the exact supplied file bytes, while
    ``zero_table_sha256`` pins the zero window against which the offsets were
    validated.  The table contains measured values, never values reconstructed
    from zero ordinates.
    """

    base: Decimal
    offsets: tuple[Decimal, ...]
    abs_zeta_values: tuple[Decimal, ...]
    absolute_value_errors: tuple[Decimal, ...]
    error_kind: _ErrorKind
    value_source: str
    source_url: str
    sha256: str
    zero_table_sha256: str

    def __post_init__(self) -> None:
        count = len(self.offsets)
        if count < 5 or count % 2 == 0:
            raise MomentError(
                "critical-line samples require an odd number of at least five rows"
            )
        if (
            len(self.abs_zeta_values) != count
            or len(self.absolute_value_errors) != count
        ):
            raise MomentError("sample offsets, values, and errors must have equal lengths")
        if not isinstance(self.base, Decimal) or not self.base.is_finite():
            raise MomentError("sample base must be a finite Decimal")
        previous: Decimal | None = None
        for position, (offset, value, error) in enumerate(
            zip(
                self.offsets,
                self.abs_zeta_values,
                self.absolute_value_errors,
                strict=True,
            )
        ):
            if not all(
                isinstance(item, Decimal) and item.is_finite()
                for item in (offset, value, error)
            ):
                raise MomentError(f"sample row {position} must contain finite Decimals")
            if previous is not None and offset <= previous:
                raise MomentError("sample offsets must be strictly increasing")
            if value < 0:
                raise MomentError("abs_zeta values must be non-negative")
            if error < 0:
                raise MomentError("absolute_error values must be non-negative")
            previous = offset
        if self.error_kind not in {"bound", "estimate"}:
            raise MomentError("error_kind must be 'bound' or 'estimate'")
        if not isinstance(self.value_source, str) or not self.value_source.strip():
            raise MomentError("value_source must be a non-empty string")
        if not isinstance(self.source_url, str) or not self.source_url.strip():
            raise MomentError("source_url must be a non-empty string")
        for name, digest in (
            ("sha256", self.sha256),
            ("zero_table_sha256", self.zero_table_sha256),
        ):
            if (
                not isinstance(digest, str)
                or re.fullmatch(r"[0-9a-f]{64}", digest) is None
            ):
                raise MomentError(f"{name} must contain 64 lowercase hexadecimal digits")

    @property
    def sample_count(self) -> int:
        """Number of sampled critical-line values."""

        return len(self.offsets)


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
class MomentPolynomial:
    """The full degree-``k^2`` moment polynomial ``P_k``.

    ``coefficients`` are in descending order: entry ``r`` multiplies
    ``x^(k^2-r)``.  For ``k=1,2`` the polynomial is a theorem; for ``k=3,4``
    it is the CFKRS conjecture.  Published decimal coefficients are accurate
    rather than certified: their source reports stable digits, not interval
    enclosures, and ``coefficient_note`` preserves that distinction.
    """

    k: int
    power: int
    degree: int
    literature_status: _LiteratureStatus
    coefficients: tuple[Decimal, ...]
    variable: str
    formula: str
    scope: str
    source: str
    coefficient_note: str

    def __post_init__(self) -> None:
        if self.k not in {1, 2, 3, 4}:
            raise MomentError("moment polynomials are implemented for k=1,2,3,4")
        if self.power != 2 * self.k or self.degree != self.k * self.k:
            raise MomentError("moment-polynomial powers are inconsistent with k")
        if self.literature_status not in {"theorem", "conjecture"}:
            raise MomentError("literature_status must be 'theorem' or 'conjecture'")
        if len(self.coefficients) != self.degree + 1:
            raise MomentError("moment polynomial must have degree + 1 coefficients")
        if any(not coefficient.is_finite() for coefficient in self.coefficients):
            raise MomentError("moment-polynomial coefficients must be finite")
        if self.coefficients[0] <= 0:
            raise MomentError("moment-polynomial leading coefficient must be positive")
        if self.variable != "x = log(t/(2*pi))":
            raise MomentError("moment-polynomial variable convention is inconsistent")
        if not self.source.strip() or not self.coefficient_note.strip():
            raise MomentError("moment-polynomial provenance must be non-empty")


@dataclass(frozen=True)
class MomentScore:
    """One row of a :class:`MomentScorecard`.

    The original leading-only fields remain independent diagnostics.
    ``prediction_truncation_error`` belongs to ``leading_prediction``; the
    published full-polynomial decimals have no claimed numerical enclosure.
    """

    k: int
    estimate: MomentEstimate
    reference: MomentReference
    polynomial: MomentPolynomial
    leading_prediction: Decimal | None
    prediction_truncation_error: Decimal | None
    ratio_to_leading: Decimal | None
    relative_residual: Decimal | None
    polynomial_prediction: Decimal | None
    ratio_to_polynomial: Decimal | None
    polynomial_relative_residual: Decimal | None
    calibration_passed: bool | None
    prediction_released: bool


@dataclass(frozen=True)
class MomentScorecard:
    """Theorem-calibrated comparison of finite measurements and references.

    Rows ``k=3,4`` are withheld unless both theorem rows ``k=1,2`` agree with
    their full-polynomial normalizations to the caller's stated tolerance.
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


def load_critical_line_samples(
    path: str | Path,
    *,
    table: ExternalZeroTable,
    error_kind: Literal["bound", "estimate"],
    value_source: str,
    source_url: str,
    expected_count: int | None = None,
    expected_sha256: str | None = None,
) -> CriticalLineSampleTable:
    """Load ``offset abs_zeta absolute_error`` rows for one zero window.

    Blank lines and lines beginning with ``#`` are ignored.  Decimal offsets
    use ``table.base`` as their origin and must lie inside the imported zero
    window.  Gzip is detected by magic bytes.  The raw-file digest and the zero
    table digest are both retained so the two independent inputs cannot be
    silently mixed later.
    """

    if not isinstance(table, ExternalZeroTable):
        raise MomentError("table must be an ExternalZeroTable")
    if expected_count is not None and (
        isinstance(expected_count, bool)
        or not isinstance(expected_count, int)
        or expected_count < 1
    ):
        raise MomentError("expected_count must be a positive integer")
    text, digest = _read_bytes(
        path,
        error_type=MomentError,
        label="critical-line sample table",
    )
    _check_digest(digest, expected_sha256, error_type=MomentError)

    offsets: list[Decimal] = []
    values: list[Decimal] = []
    errors: list[Decimal] = []
    for line_number, raw_line in enumerate(text.splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 3:
            raise MomentError(
                f"line {line_number}: expected three columns: "
                "offset abs_zeta absolute_error"
            )
        try:
            offset, value, error = (
                _moment_decimal(token, field=field)
                for token, field in zip(
                    fields,
                    ("offset", "abs_zeta", "absolute_error"),
                    strict=True,
                )
            )
        except MomentError as exc:
            raise MomentError(f"line {line_number}: {exc}") from exc
        offsets.append(offset)
        values.append(value)
        errors.append(error)

    if expected_count is not None and len(offsets) != expected_count:
        raise MomentError(
            f"row count mismatch: expected {expected_count}, got {len(offsets)}"
        )

    samples = CriticalLineSampleTable(
        base=table.base,
        offsets=tuple(offsets),
        abs_zeta_values=tuple(values),
        absolute_value_errors=tuple(errors),
        error_kind=error_kind,
        value_source=(
            value_source.strip() if isinstance(value_source, str) else value_source
        ),
        source_url=source_url.strip() if isinstance(source_url, str) else source_url,
        sha256=digest,
        zero_table_sha256=table.sha256,
    )
    if (
        samples.offsets[0] < table.offsets[0]
        or samples.offsets[-1] > table.offsets[-1]
    ):
        raise MomentError("critical-line sample offset is outside the imported zero window")
    return samples


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


def estimate_moment_from_samples(
    table: ExternalZeroTable,
    samples: CriticalLineSampleTable,
    *,
    k: int,
    dps: int = 60,
) -> MomentEstimate:
    """Estimate one moment from a loaded, digest-linked sample table."""

    if not isinstance(table, ExternalZeroTable):
        raise MomentError("table must be an ExternalZeroTable")
    if not isinstance(samples, CriticalLineSampleTable):
        raise MomentError("samples must be a CriticalLineSampleTable")
    if samples.base != table.base:
        raise MomentError("sample base does not match the imported zero table")
    if samples.zero_table_sha256 != table.sha256:
        raise MomentError("sample zero-table digest does not match the imported zero table")
    provenance = (
        f"{samples.value_source} "
        f"[source_url={samples.source_url}; sha256={samples.sha256}]"
    )
    return estimate_moment(
        table,
        k=k,
        sample_offsets=samples.offsets,
        abs_zeta_values=samples.abs_zeta_values,
        absolute_value_errors=samples.absolute_value_errors,
        error_kind=samples.error_kind,
        value_source=provenance,
        dps=dps,
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


# Published coefficients c_r(k), ordered as x^(k^2-r).  These are source data,
# not hidden derivations.  k=3 is the CFKRS high-precision table; k=4 is Table 2
# of Rubinstein--Yamagishi (the stable digits from their cubic-accelerant run).
_PUBLISHED_MOMENT_COEFFICIENTS: Final[dict[int, tuple[str, ...]]] = {
    2: (
        "0.0506605918211688857219397316048638",
        "0.69886988487897996984709628427658502",
        "2.425962198846682004756575310160663",
        "3.227907964901254764380689851274668",
        "1.312424385961669226168440066229978",
    ),
    3: (
        "0.000005708527034652788398376841445252313",
        "0.00040502133088411440331215332025984",
        "0.011072455215246998350410400826667",
        "0.14840073080150272680851401518774",
        "1.0459251779054883439385323798059",
        "3.984385094823534724747964073429",
        "8.60731914578120675614834763629",
        "10.274330830703446134183009522",
        "6.59391302064975810465713392",
        "0.9165155076378930590178543",
    ),
    4: (
        "2.4650183919342273540799e-13",
        "5.45014057311718655936e-11",
        "5.287729634791203113849e-9",
        "2.9641143179993979459691e-7",
        "1.0645950068128470513211e-5",
        "2.570298334242634023549e-4",
        "4.26392161631169472187e-3",
        "4.894142451421601027126e-2",
        "3.8785266540195534998e-1",
        "2.10913382864873355",
        "7.832535611882262357",
        "1.98280681249989092e1",
        "3.3888932037383688e1",
        "3.82033062189019e1",
        "2.5604415012270e1",
        "1.0618969379401e1",
        "7.0894645522e-1",
    ),
}


@lru_cache(maxsize=16)
def moment_polynomial(k: int, *, dps: int = 50) -> MomentPolynomial:
    """Return the full CFKRS moment polynomial for ``k=1,2,3,4``.

    The convention is

    ``integral_0^T |zeta(1/2+it)|^(2k) dt ~ integral_0^T P_k(log(t/2pi)) dt``.

    ``k=1`` and the first two coefficients for ``k=2`` are re-derived at the
    requested precision, fixing the factor and logarithm convention against
    the theorem cases.  Remaining coefficients preserve the published decimal
    tokens.  For ``k=3,4`` those tokens are conjectural and have stable reported
    digits but no rigorous numerical enclosure.
    """

    if isinstance(k, bool) or not isinstance(k, int) or k not in {1, 2, 3, 4}:
        raise MomentError("moment_polynomial implements k=1,2,3,4")
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 30:
        raise MomentError("dps must be an integer at least 30")

    status: _LiteratureStatus = "theorem" if k <= 2 else "conjecture"
    if k == 1:
        with mp.workdps(dps + 20):
            coefficients = (Decimal(1), _mp_to_decimal(2 * mp.euler, dps=dps))
        source = "Ingham two-term second-moment theorem"
        note = (
            "coefficients re-derived with guarded mpmath arithmetic; "
            "no interval enclosure"
        )
    elif k == 2:
        published = tuple(Decimal(value) for value in _PUBLISHED_MOMENT_COEFFICIENTS[k])
        with mp.workdps(dps + 20):
            leading = 1 / (2 * mp.pi**2)
            cubic = 8 / mp.pi**4 * (mp.euler * mp.pi**2 - 3 * mp.diff(mp.zeta, 2))
            coefficients = (
                _mp_to_decimal(leading, dps=dps),
                _mp_to_decimal(cubic, dps=dps),
                *published[2:],
            )
        source = "Heath--Brown fourth-moment polynomial; CFKRS convention"
        note = (
            "leading and cubic coefficients re-derived; remaining theorem "
            "coefficients preserve published decimal tokens; no interval enclosure"
        )
    else:
        coefficients = tuple(
            Decimal(value) for value in _PUBLISHED_MOMENT_COEFFICIENTS[k]
        )
        source = (
            "CFKRS full moment table (arXiv:math/0612843)"
            if k == 3
            else "Rubinstein--Yamagishi Table 2 (arXiv:1112.2201)"
        )
        note = (
            "published stable digits from numerical coefficient computation; "
            "no interval enclosure"
        )

    return MomentPolynomial(
        k=k,
        power=2 * k,
        degree=k * k,
        literature_status=status,
        coefficients=coefficients,
        variable="x = log(t/(2*pi))",
        formula="P_k(x) = sum_{r=0}^{k^2} c_r(k) x^(k^2-r)",
        scope="global integral from 0 to T as T tends to infinity",
        source=source,
        coefficient_note=note,
    )


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


def moment_polynomial_mean(
    polynomial: MomentPolynomial,
    interval_start: Decimal | str | int,
    interval_end: Decimal | str | int,
    *,
    dps: int = 50,
) -> Decimal:
    """Average ``P_k(log(t/(2*pi)))`` over ``[A,B]``.

    This integrates every power of the full degree-``k^2`` polynomial rather
    than evaluating it at a midpoint.  The theorem/conjecture label remains a
    global ``[0,T]`` statement; on a shifted finite window this is a diagnostic
    extrapolation, not a short-interval theorem or statistical test.
    """

    if not isinstance(polynomial, MomentPolynomial):
        raise MomentError("polynomial must be a MomentPolynomial")
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 30:
        raise MomentError("dps must be an integer at least 30")
    start = _moment_decimal(interval_start, field="interval_start")
    end = _moment_decimal(interval_end, field="interval_end")
    log_means = tuple(
        _leading_log_mean(power, start, end, dps=dps)
        for power in range(polynomial.degree, -1, -1)
    )
    with localcontext() as context:
        context.prec = dps
        return +sum(
            (
                coefficient * log_mean
                for coefficient, log_mean in zip(
                    polynomial.coefficients, log_means, strict=True
                )
            ),
            Decimal(0),
        )


def moment_scorecard(
    estimates: Sequence[MomentEstimate],
    *,
    calibration_relative_tolerance: Decimal | str | int,
    references: Mapping[int, MomentReference] | None = None,
    polynomials: Mapping[int, MomentPolynomial] | None = None,
    prime_cutoff: int = 100_000,
    dps: int = 50,
) -> MomentScorecard:
    """Compare finite estimates with full moment polynomials behind a theorem gate.

    Estimates for ``k=1`` and ``k=2`` are mandatory and must share the same
    interval, samples, value source, and imported-table digest as every other
    row.  The conjectural ``k=3,4`` predictions are returned only when both
    theorem rows have full-polynomial relative residual at most
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

    selected_polynomials: dict[int, MomentPolynomial] = {}
    for k in by_k:
        polynomial = polynomials[k] if polynomials is not None and k in polynomials else None
        if polynomial is None:
            if polynomials is not None:
                raise MomentError(f"polynomials is missing k={k}")
            polynomial = moment_polynomial(k, dps=dps)
        if not isinstance(polynomial, MomentPolynomial) or polynomial.k != k:
            raise MomentError(f"polynomial for k={k} is inconsistent")
        selected_polynomials[k] = polynomial
    if any(selected_polynomials[k].literature_status != "theorem" for k in (1, 2)):
        raise MomentError("calibration polynomials for k=1,2 must be theorem rows")

    leading_predictions: dict[int, Decimal] = {}
    prediction_errors: dict[int, Decimal] = {}
    leading_residuals: dict[int, Decimal] = {}
    polynomial_predictions: dict[int, Decimal] = {}
    polynomial_residuals: dict[int, Decimal] = {}
    for k, estimate in by_k.items():
        reference = selected_references[k]
        log_mean = _leading_log_mean(
            reference.log_power, estimate.interval_start, estimate.interval_end, dps=dps
        )
        polynomial_prediction = moment_polynomial_mean(
            selected_polynomials[k],
            estimate.interval_start,
            estimate.interval_end,
            dps=dps,
        )
        with localcontext() as context:
            context.prec = dps
            leading_prediction = +(reference.leading_coefficient * log_mean)
            prediction_error = +(reference.coefficient_truncation_error * log_mean)
            leading_residual = +(
                abs(estimate.mean_value - leading_prediction) / abs(leading_prediction)
            )
            polynomial_residual = +(
                abs(estimate.mean_value - polynomial_prediction)
                / abs(polynomial_prediction)
            )
        leading_predictions[k] = leading_prediction
        prediction_errors[k] = prediction_error
        leading_residuals[k] = leading_residual
        polynomial_predictions[k] = polynomial_prediction
        polynomial_residuals[k] = polynomial_residual

    calibration_by_k = {k: polynomial_residuals[k] <= tolerance for k in (1, 2)}
    calibration_passed = all(calibration_by_k.values())
    withheld = tuple(k for k in sorted(by_k) if k > 2 and not calibration_passed)

    rows: list[MomentScore] = []
    for k in sorted(by_k):
        released = k <= 2 or calibration_passed
        leading_prediction = leading_predictions[k] if released else None
        polynomial_prediction = polynomial_predictions[k] if released else None
        prediction_error = prediction_errors[k] if released else None
        with localcontext() as context:
            context.prec = dps
            leading_ratio = (
                +(by_k[k].mean_value / leading_prediction)
                if leading_prediction is not None
                else None
            )
            polynomial_ratio = (
                +(by_k[k].mean_value / polynomial_prediction)
                if polynomial_prediction is not None
                else None
            )
        rows.append(
            MomentScore(
                k=k,
                estimate=by_k[k],
                reference=selected_references[k],
                polynomial=selected_polynomials[k],
                leading_prediction=leading_prediction,
                prediction_truncation_error=prediction_error,
                ratio_to_leading=leading_ratio,
                relative_residual=leading_residuals[k] if released else None,
                polynomial_prediction=polynomial_prediction,
                ratio_to_polynomial=polynomial_ratio,
                polynomial_relative_residual=(
                    polynomial_residuals[k] if released else None
                ),
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
            "full-polynomial comparison here is a normalization diagnostic, not a "
            "short-interval theorem, not validation of a conjecture, and not evidence for RH."
        ),
    )
