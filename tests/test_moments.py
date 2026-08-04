"""Tests for external windows and finite scorecards in :mod:`zeta.moments`."""

from __future__ import annotations

import gzip
import hashlib
import math
from dataclasses import replace
from pathlib import Path

from decimal import Decimal
from mpmath import mp
import pytest

from zeta.moments import (
    ODLYZKO_TABLES,
    CriticalLineSampleTable,
    ExternalZeroTable,
    MomentError,
    ZeroTableError,
    estimate_moment,
    estimate_moment_from_samples,
    leading_moment_mean,
    load_lmfdb_zeros,
    load_odlyzko_zeros,
    load_critical_line_samples,
    moment_reference,
    moment_scorecard,
)


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


def _high_window() -> ExternalZeroTable:
    return ExternalZeroTable(
        provider="fixture",
        first_index=10**22 + 1,
        base=Decimal("1370919909931995300000"),
        offsets=tuple(Decimal(8226 + i) for i in range(5)),
        source_url="fixture://high-window",
        sha256="a" * 64,
        accuracy_note="synthetic exact-decimal fixture",
    )


def _sample_text(*rows: str) -> str:
    return (
        "# offset-from-zero-table-base abs-zeta absolute-error\n"
        + "\n".join(rows)
        + "\n"
    )


def test_critical_line_sample_loader_preserves_decimals_and_file_provenance(
    tmp_path: Path,
) -> None:
    table = _high_window()
    raw = _sample_text(
        "8226.0 2.000 0.001",
        "8227.0 2.000 0.001",
        "8228.0 2.000 0.001",
        "8229.0 2.000 0.001",
        "8230.0 2.000 0.001",
    ).encode("ascii")
    path = tmp_path / "critical-line-values.txt.gz"
    path.write_bytes(gzip.compress(raw, mtime=0))
    digest = hashlib.sha256(path.read_bytes()).hexdigest()

    samples = load_critical_line_samples(
        path,
        table=table,
        error_kind="estimate",
        value_source="independent evaluator v1",
        source_url="https://example.test/critical-line-values.txt.gz",
        expected_count=5,
        expected_sha256=digest,
    )

    assert isinstance(samples, CriticalLineSampleTable)
    assert samples.base == table.base
    assert samples.offsets[0] == Decimal("8226.0")
    assert samples.abs_zeta_values == (Decimal("2.000"),) * 5
    assert samples.absolute_value_errors == (Decimal("0.001"),) * 5
    assert samples.sha256 == digest
    assert samples.zero_table_sha256 == table.sha256

    estimate = estimate_moment_from_samples(table, samples, k=2)
    assert estimate.mean_value == 16
    assert digest in estimate.value_source
    assert samples.source_url in estimate.value_source


@pytest.mark.parametrize(
    ("rows", "message"),
    [
        (("8226 1 0", "8227 1 0", "8228 1 0", "8229 1 0"), "odd number"),
        (
            ("8226 1 0", "8227 1 0", "8227 1 0", "8229 1 0", "8230 1 0"),
            "strictly increasing",
        ),
        (
            ("8225 1 0", "8227 1 0", "8228 1 0", "8229 1 0", "8230 1 0"),
            "outside",
        ),
        (
            ("8226 1 0", "8227 1 0", "8228 -1 0", "8229 1 0", "8230 1 0"),
            "abs_zeta",
        ),
        (
            ("8226 1 0", "8227 1 0", "8228 1 -1", "8229 1 0", "8230 1 0"),
            "absolute_error",
        ),
        (
            ("8226 1 0", "8227 1 0", "8228 1", "8229 1 0", "8230 1 0"),
            "three columns",
        ),
    ],
)
def test_critical_line_sample_loader_rejects_bad_tables(
    tmp_path: Path, rows: tuple[str, ...], message: str
) -> None:
    path = _write(tmp_path / "values", _sample_text(*rows))
    with pytest.raises(MomentError, match=message):
        load_critical_line_samples(
            path,
            table=_high_window(),
            error_kind="bound",
            value_source="fixture evaluator",
            source_url="fixture://values",
        )


def test_critical_line_sample_loader_checks_count_checksum_and_zero_window(
    tmp_path: Path,
) -> None:
    table = _high_window()
    path = _write(
        tmp_path / "values",
        _sample_text(*(f"{8226 + i} 2 0" for i in range(5))),
    )
    kwargs = dict(
        table=table,
        error_kind="bound",
        value_source="fixture evaluator",
        source_url="fixture://values",
    )
    with pytest.raises(MomentError, match="row count mismatch"):
        load_critical_line_samples(path, expected_count=7, **kwargs)
    with pytest.raises(MomentError, match="SHA-256 mismatch"):
        load_critical_line_samples(path, expected_sha256="0" * 64, **kwargs)

    samples = load_critical_line_samples(path, **kwargs)
    other_table = replace(table, sha256="b" * 64)
    with pytest.raises(MomentError, match="zero-table digest"):
        estimate_moment_from_samples(other_table, samples, k=1)


def test_estimator_preserves_high_window_and_states_finite_normalisation() -> None:
    table = _high_window()
    estimate = estimate_moment(
        table,
        k=2,
        sample_offsets=table.offsets,
        abs_zeta_values=("2",) * 5,
        absolute_value_errors="0",
        error_kind="bound",
        value_source="synthetic constant fixture",
    )

    assert estimate.power == 4
    assert estimate.mean_value == Decimal(16)
    assert estimate.interval_start == Decimal("1370919909931995308226")
    assert estimate.interval_end == Decimal("1370919909931995308230")
    assert estimate.width == Decimal(4)
    assert estimate.sample_count == 5
    assert estimate.sampling_error_estimate == 0
    assert estimate.value_error == 0
    assert estimate.table_sha256 == table.sha256
    assert len(estimate.sample_sha256) == 64
    assert estimate.normalization.startswith("1 / (B - A)")


def test_estimator_keeps_sampling_and_value_errors_separate() -> None:
    table = _high_window()
    estimate = estimate_moment(
        table,
        k=1,
        sample_offsets=table.offsets,
        abs_zeta_values=("1", "2", "3", "4", "5"),
        absolute_value_errors="0.1",
        error_kind="estimate",
        value_source="synthetic ramp fixture",
    )

    # Fine trapezoid mean of 1, 4, 9, 16, 25 is 10.5; the every-other
    # nested grid gives 11, so their difference is reported, not hidden.
    assert estimate.mean_value == Decimal("10.5")
    assert estimate.sampling_error_estimate == Decimal("0.5")
    assert estimate.value_error == Decimal("0.61")
    assert estimate.value_error_kind == "estimate"


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        (
            {
                "sample_offsets": (8226, 8227, 8228, 8229),
                "abs_zeta_values": (1, 2, 3, 4),
            },
            "odd number",
        ),
        ({"sample_offsets": (8225, 8226, 8227, 8228, 8229)}, "outside"),
        ({"sample_offsets": (8226.0, 8227, 8228, 8229, 8230)}, "binary float"),
        ({"abs_zeta_values": (1, 2, -3, 4, 5)}, "non-negative"),
        ({"absolute_value_errors": (0, 0, 0)}, "one per sample"),
    ],
)
def test_estimator_rejects_uncontrolled_sample_contract(kwargs, message: str) -> None:
    table = _high_window()
    call = {
        "table": table,
        "k": 1,
        "sample_offsets": table.offsets,
        "abs_zeta_values": (1, 2, 3, 4, 5),
        "absolute_value_errors": 0,
        "error_kind": "bound",
        "value_source": "fixture",
    }
    call.update(kwargs)
    with pytest.raises(MomentError, match=message):
        estimate_moment(**call)


def test_keating_snaith_constants_recover_the_two_proved_leading_terms() -> None:
    refs = {k: moment_reference(k, prime_cutoff=2_000, dps=50) for k in range(1, 5)}

    assert [refs[k].random_matrix_integer for k in range(1, 5)] == [1, 2, 42, 24024]
    assert refs[1].literature_status == refs[2].literature_status == "theorem"
    assert refs[3].literature_status == refs[4].literature_status == "conjecture"
    assert refs[1].leading_coefficient == 1
    assert abs(float(refs[2].leading_coefficient) - 1 / (2 * math.pi**2)) < 1e-15
    assert refs[1].log_power == 1 and refs[2].log_power == 4
    assert refs[3].log_power == 9 and refs[4].log_power == 16
    assert refs[1].coefficient_truncation_error == refs[2].coefficient_truncation_error == 0
    assert refs[3].coefficient_truncation_error > 0
    assert refs[4].coefficient_truncation_error > 0


@pytest.mark.parametrize("k", [3, 4])
def test_arithmetic_euler_product_tail_bound_contains_a_later_cutoff(k: int) -> None:
    coarse = moment_reference(k, prime_cutoff=1_000, dps=60)
    finer = moment_reference(k, prime_cutoff=20_000, dps=60)

    assert abs(coarse.leading_coefficient - finer.leading_coefficient) < (
        coarse.coefficient_truncation_error
    )


def test_leading_window_normalisation_matches_independent_quadrature() -> None:
    reference = moment_reference(2, dps=60)
    measured = leading_moment_mean(reference, "1000", "1010", dps=60)

    with mp.workdps(80):
        coefficient = mp.mpf(str(reference.leading_coefficient))
        expected = coefficient * mp.quad(
            lambda t: mp.log(t / (2 * mp.pi)) ** 4,
            [mp.mpf(1000), mp.mpf(1010)],
        ) / 10
        assert abs(mp.mpf(str(measured)) - expected) < mp.mpf("1e-55")


def test_scorecard_mutation_gate_withholds_open_moments_after_bad_calibration() -> None:
    table = _high_window()
    refs = {k: moment_reference(k, prime_cutoff=2_000, dps=60) for k in range(1, 5)}
    estimates = []
    for k in range(1, 5):
        measured = estimate_moment(
            table,
            k=k,
            sample_offsets=table.offsets,
            abs_zeta_values=("2",) * 5,
            absolute_value_errors=0,
            error_kind="bound",
            value_source="synthetic scorecard fixture",
        )
        expected = leading_moment_mean(
            refs[k], measured.interval_start, measured.interval_end, dps=60
        )
        estimates.append(replace(measured, mean_value=expected))

    good = moment_scorecard(
        estimates,
        references=refs,
        calibration_relative_tolerance="1e-40",
        dps=60,
    )
    assert good.calibration_passed
    assert good.withheld_k == ()
    assert all(row.prediction_released for row in good.rows)

    # Mutation test: a 2% error in the proved fourth-moment coefficient must
    # fail the calibration and prevent sixth/eighth predictions from leaking.
    bad_refs = refs | {
        2: replace(
            refs[2],
            leading_coefficient=refs[2].leading_coefficient * Decimal("1.02"),
        )
    }
    bad = moment_scorecard(
        estimates,
        references=bad_refs,
        calibration_relative_tolerance="0.001",
        dps=60,
    )
    assert not bad.calibration_passed
    assert bad.withheld_k == (3, 4)
    assert bad.rows[0].prediction_released and bad.rows[1].prediction_released
    assert bad.rows[2].leading_prediction is None and bad.rows[3].leading_prediction is None
    assert "local finite-window" in bad.scope_note


def test_scorecard_rejects_missing_or_mixed_calibration_provenance() -> None:
    table = _high_window()

    def estimate(k: int):
        return estimate_moment(
            table,
            k=k,
            sample_offsets=table.offsets,
            abs_zeta_values=("2",) * 5,
            absolute_value_errors=0,
            error_kind="bound",
            value_source="one acquisition",
        )

    second, fourth = estimate(1), estimate(2)
    with pytest.raises(MomentError, match="k=1 and k=2"):
        moment_scorecard([second], calibration_relative_tolerance="0.5")
    different_samples = estimate_moment(
        table,
        k=2,
        sample_offsets=table.offsets,
        abs_zeta_values=("2", "2", "2", "2", "3"),
        absolute_value_errors=0,
        error_kind="bound",
        value_source="one acquisition",
    )
    assert fourth.sample_sha256 != different_samples.sample_sha256
    with pytest.raises(MomentError, match="share one sample window and provenance"):
        moment_scorecard(
            [second, different_samples],
            calibration_relative_tolerance="0.5",
        )
    with pytest.raises(MomentError, match="binary float"):
        moment_scorecard([second, fourth], calibration_relative_tolerance=0.5)
