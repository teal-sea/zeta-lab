"""Tests for external zero-table ingestion in :mod:`zeta.moments`."""

from __future__ import annotations

import gzip
import hashlib
import math
from pathlib import Path

from decimal import Decimal
import pytest

from zeta.moments import ODLYZKO_TABLES, ZeroTableError, load_lmfdb_zeros, load_odlyzko_zeros


def _write(path: Path, text: str) -> Path:
    path.write_text(text, encoding="ascii")
    return path


def _odlyzko5(*values: str) -> str:
    return (
        "Values of gamma - 1370919909931995300000, where gamma runs over the heights\n"
        "of the zeros of the Riemann zeta numbered 10^22 + 1 through 10^22 + 10^4.\n"
        "Thus zero # 10^22 + 1 is actually\n\n"
        "1/2 + i * 1,370,919,909,931,995,308,226.68016095...\n\n"
        "Values are not guaranteed, and are probably accurate to within 10^(-6).\n\n"
        + "\n".join(values)
        + "\n"
    )


def test_lmfdb_preserves_high_ordinates_as_base_plus_offsets(tmp_path: Path) -> None:
    path = _write(
        tmp_path / "zetazeros",
        "10000000000000000000001 1370919909931995308226.6801609500000000000000000000000\n"
        "10000000000000000000002 1370919909931995308226.7765915200000000000000000000000\n",
    )
    table = load_lmfdb_zeros(path, expected_count=2, expected_first_index=10**22 + 1)

    assert table.base == Decimal("1370919909931995308226")
    assert table.ordinate(10**22 + 1) == Decimal(
        "1370919909931995308226.6801609500000000000000000000000"
    )
    assert table.spacing_after(10**22 + 1) == Decimal("0.0964305700000000000000000000000")
    # This is precisely why absolute float64 ordinates are forbidden here.
    assert float(table.ordinate(10**22 + 1)) == float(table.ordinate(10**22 + 2))
    assert math.ulp(float(table.ordinate(10**22 + 1))) / float(
        table.spacing_after(10**22 + 1)
    ) > 1_000_000


def test_odlyzko_high_table_catalogue_is_pinned() -> None:
    expected = {
        "zeros3": (10**12 + 1, 10_000, Decimal("267653395647")),
        "zeros4": (10**21 + 1, 10_000, Decimal("144176897509546973000")),
        "zeros5": (10**22 + 1, 10_000, Decimal("1370919909931995300000")),
    }
    assert {
        table_id: (spec.first_index, spec.count, spec.base)
        for table_id, spec in ODLYZKO_TABLES.items()
        if table_id in expected
    } == expected


def test_lmfdb_checksum_and_gzip_cover_supplied_bytes(tmp_path: Path) -> None:
    raw = b"7 40.918719012147495187\n8 43.327073280914999519\n"
    path = tmp_path / "zetazeros.gz"
    path.write_bytes(gzip.compress(raw, mtime=0))
    digest = hashlib.sha256(path.read_bytes()).hexdigest()

    table = load_lmfdb_zeros(path, expected_count=2, expected_sha256=digest)

    assert table.sha256 == digest
    assert table.first_index == 7
    assert table.last_index == 8


@pytest.mark.parametrize(
    ("text", "message"),
    [
        ("1 14.1\n3 25.0\n", "does not follow"),
        ("1 14.1\n2 14.1\n", "not strictly increasing"),
        ("1 14.1\n2 13.9\n", "not strictly increasing"),
        ("1 nope\n", "invalid decimal"),
        ("0 14.1\n", "must be positive"),
        ("1 14.1 extra\n", "expected 'index ordinate'"),
    ],
)
def test_lmfdb_rejects_malformed_or_nonmonotone_rows(
    tmp_path: Path, text: str, message: str
) -> None:
    path = _write(tmp_path / "zetazeros", text)
    with pytest.raises(ZeroTableError, match=message):
        load_lmfdb_zeros(path)


def test_lmfdb_rejects_wrong_count_index_and_checksum(tmp_path: Path) -> None:
    path = _write(tmp_path / "zetazeros", "10 49.773832477672302182\n")
    with pytest.raises(ZeroTableError, match="row count mismatch"):
        load_lmfdb_zeros(path, expected_count=2)
    with pytest.raises(ZeroTableError, match="first index mismatch"):
        load_lmfdb_zeros(path, expected_first_index=9)
    with pytest.raises(ZeroTableError, match="SHA-256 mismatch"):
        load_lmfdb_zeros(path, expected_sha256="0" * 64)


def test_odlyzko_high_table_parses_and_cross_checks_header(tmp_path: Path) -> None:
    values = [f"{8226 + i}.68016095" for i in range(10_000)]
    path = _write(tmp_path / "renamed-table", _odlyzko5(*values))

    table = load_odlyzko_zeros(path, table_id="zeros5")

    assert len(table) == 10_000
    assert table.first_index == 10**22 + 1
    assert table.base == Decimal("1370919909931995300000")
    assert table.ordinate(10**22 + 1) == Decimal("1370919909931995308226.68016095")
    assert table.accuracy_note == "not guaranteed; probably within 1e-6"


def test_odlyzko_rejects_truncation_duplicate_and_header_tampering(tmp_path: Path) -> None:
    truncated = _write(tmp_path / "zeros5", _odlyzko5("8226.68016095"))
    with pytest.raises(ZeroTableError, match="row count mismatch"):
        load_odlyzko_zeros(truncated)

    values = [f"{8226 + i}.68016095" for i in range(10_000)]
    values[20] = values[19]
    duplicate = _write(tmp_path / "renamed", _odlyzko5(*values))
    with pytest.raises(ZeroTableError, match="not strictly increasing"):
        load_odlyzko_zeros(duplicate, table_id="zeros5")

    tampered = _write(
        tmp_path / "tampered",
        _odlyzko5(*[f"{8226 + i}.68016095" for i in range(10_000)]).replace(
            "1370919909931995300000", "1370919909931995300001", 1
        ),
    )
    with pytest.raises(ZeroTableError, match="header base"):
        load_odlyzko_zeros(tampered, table_id="zeros5")


def test_odlyzko_unknown_or_headerless_high_table_is_rejected(tmp_path: Path) -> None:
    unknown = _write(tmp_path / "mystery", "14.134725142\n")
    with pytest.raises(ZeroTableError, match="unknown Odlyzko table"):
        load_odlyzko_zeros(unknown)

    headerless = _write(
        tmp_path / "renamed",
        "\n".join(f"{8226 + i}.68016095" for i in range(10_000)) + "\n",
    )
    with pytest.raises(ZeroTableError, match="missing its required base/index header"):
        load_odlyzko_zeros(headerless, table_id="zeros5")


def test_module_contains_no_zero_computation_entry_points() -> None:
    source = (Path(__file__).parents[1] / "zeta" / "moments.py").read_text(encoding="utf-8")
    forbidden = ("zetazero(", "zero_ordinates(", "zeros_from_scratch(", "zeros_by_sign_change(")
    assert not any(name in source for name in forbidden)
