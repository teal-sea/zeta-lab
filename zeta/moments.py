"""External zero-table ingestion for the moments programme.

This module deliberately does not compute zeros.  It reads the public text
formats used by Andrew Odlyzko's tables and by the LMFDB zero-list export,
checks their structural invariants, and preserves the published decimal data
without converting absolute ordinates to binary floats.

At heights near 10^22, neighbouring ordinates differ by much less than one
float64 ulp.  :class:`ExternalZeroTable` therefore stores an exact decimal
``base`` plus exact decimal ``offsets``.  "Exact" here means exact to the text
that was ingested; it does not strengthen the source's stated accuracy.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, InvalidOperation, ROUND_FLOOR, localcontext
import gzip
import hashlib
from pathlib import Path
import re
from typing import Final

__all__ = [
    "ExternalZeroTable",
    "ODLYZKO_TABLES",
    "OdlyzkoTableSpec",
    "ZeroTableError",
    "load_lmfdb_zeros",
    "load_odlyzko_zeros",
]


class ZeroTableError(ValueError):
    """Raised when an external zero table fails structural validation."""


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
