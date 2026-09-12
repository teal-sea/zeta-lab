"""Independent upper-column, logarithmic and full signed-basis checks."""
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

from mpmath import mp
from mpmath.ctx_iv import MPIntervalContext
import pytest
from sympy import factorint

from hunts.quotient_certificate import fold_upper as upper

ROOT = Path(__file__).resolve().parents[1]
HUNT = ROOT / "hunts/quotient_certificate"


def prefix_solution(target):
    r = [0] * 100
    for j in range(100, 0, -1):
        r[j - 1] = target[j - 1] - sum(r[s - 1] * (s // j) for s in range(j + 1, 101))
    return r


@pytest.fixture(scope="module")
def independent():
    source = json.loads((HUNT / "fold_upper_input.json").read_text())
    B = {int(q): v for q, v in source["B"].items()}
    Q = sorted({10000 // d for d in range(2, 10001)})
    above = [q for q in Q if q > 100]
    products = {}
    for q in set(above) | set(B):
        products[q] = 1
        for d in range(10000 // (q + 1) + 1, 10000 // q + 1):
            f = factorint(d)
            if len(f) == 1:
                products[q] *= int(next(iter(f)))
    columns = {}
    for a in above:
        parity = [a // j - 2 * ((a // 2) // j) for j in range(1, 101)]
        correction = prefix_solution(parity)
        column = {a: -1, a // 2: 2}
        for q, value in enumerate(correction, 1):
            column[q] = column.get(q, 0) + value
        columns[a] = {q: v for q, v in column.items() if v}
    return source, B, Q, products, columns


def test_every_allowed_column_and_inequality_independently(independent):
    _, B, Q, products, columns = independent
    assert len(Q) == 198 and len(columns) == 98
    assert sum(products[a] == 1 for a in columns) == 63
    actual, rows = upper.check_columns(B, 1387, Q, 100)
    assert actual == columns
    slacks = []
    for a, column in columns.items():
        assert set(column) <= set(Q)
        assert all(sum(v * (q // j) for q, v in column.items()) == 0 for j in range(1, 101))
        gain = sum(column.values())
        dot = sum(B.get(q, 0) * v for q, v in column.items())
        assert dot <= -1387 * gain
        slacks.append(-1387 * gain - dot)
    assert len(rows) == 98 and slacks.count(0) == 52
    assert sum(s > 0 for s in slacks) == 46 and max(slacks) == 13269


def test_bad_sign_and_bad_upper_certificate_are_rejected(independent):
    _, B, Q, _, _ = independent
    wrong = dict(B)
    wrong[33] = -1
    with pytest.raises(ValueError, match="nonnegative integer"):
        upper.check_columns(wrong, 1387, Q, 100)
    with pytest.raises(ArithmeticError, match="upper inequality fails"):
        upper.check_columns({}, 1387, Q, 100)


def test_cost_by_independent_cell_products_and_higher_precision(independent):
    source, B, _, products, _ = independent
    numerator = Counter()
    for q, b in B.items():
        for p, k in factorint(products[q]).items():
            numerator[int(p)] += b * int(k)
    assert dict(sorted(numerator.items())) == {
        2: 16456, 7: 3052, 17: 1248, 23: 7629, 59: 1101,
        191: 2635, 197: 1673, 199: 1673, 229: 754, 293: 1248}
    assert sorted(q for q in B if products[q] > 1) == [34, 43, 50, 52, 169, 204, 434, 1250]
    iv = MPIntervalContext()
    iv.dps = 105
    # This route sums logarithms of integer cell products; the checker
    # first combines all repeated prime-log coefficients.
    cost = sum((b * iv.log(products[q]) for q, b in B.items()), iv.mpf(0)) / 1387
    enclosed = upper.outward_bounds(upper.endpoint(cost, 0), upper.endpoint(cost, 1), 45)
    assert enclosed == source["coordinator_cost_enclosure"]
    with mp.workdps(120):
        value = mp.fsum(b * mp.log(products[q]) for q, b in B.items()) / 1387
        lo, hi = map(mp.mpf, enclosed)
        assert lo <= value <= hi < mp.mpf("66.339")
    assert F(enclosed[1]) < F(66339, 1000) < F(source["comparison"]["gain"])


def test_recurrence_on_an_independent_zero_moment_basis_including_prefix(independent):
    _, _, Q, _, columns = independent
    # Orthogonal construction: expand each full floor row into the prefix,
    # rather than starting with halving-fold columns or a saved witness.
    for a in columns:
        r = prefix_solution([a // j for j in range(1, 101)])
        delta = {a: 1, **{q: -v for q, v in enumerate(r, 1) if v}}
        x = upper.signed_coordinates(delta, Q, 100)
        reconstructed = {q: sum(v * columns[b].get(q, 0) for b, v in x.items()) for q in Q}
        assert all(reconstructed[q] == delta.get(q, 0) for q in Q)
        assert all(v.denominator == 1 for v in x.values())
        assert x[a] == -1  # signed algebra control, no feasibility claim


def test_rational_signed_roundtrip_and_invalid_residual_are_detected(independent):
    _, _, Q, _, columns = independent
    expected = {a: F((-1) ** i * (i + 1), i % 7 + 1) for i, a in enumerate(columns)}
    delta = {q: sum(v * columns[a].get(q, 0) for a, v in expected.items()) for q in Q}
    actual = upper.signed_coordinates(delta, Q, 100)
    assert actual == expected
    assert any(v < 0 for v in actual.values()) and any(v > 0 for v in actual.values())
    broken = dict(delta)
    broken[1] += 1  # leaves high rows unchanged, breaks the required prefix moments
    with pytest.raises(ValueError, match="zero moments"):
        upper.signed_coordinates(broken, Q, 100)
    with pytest.raises(ValueError, match="full prefix"):
        upper.signed_coordinates({}, [q for q in Q if q != 100], 100)
    with pytest.raises(ValueError, match="halved source"):
        upper.signed_coordinates({}, [q for q in Q if q != 1250], 100)


def test_empty_high_basis_edge_case_and_unsupported_vector():
    assert upper.signed_coordinates({}, [1, 2], 2) == {}
    with pytest.raises(ValueError, match="supported"):
        upper.signed_coordinates({3: 1}, [1, 2], 2)


def test_replay_and_manifest_pin_the_run_without_witness_conversion():
    before = mp.dps
    result = upper.analyze()
    saved = json.loads((HUNT / "fold_upper_results.json").read_text())
    assert all(saved[k] == v for k, v in json.loads(json.dumps(result)).items())
    assert mp.dps == before
    assert saved["completed_certificates"] == saved["requested_certificates"] == 1
    assert saved["optimizations"] == saved["witness_coordinate_conversions"] == 0
    manifest = json.loads((HUNT / "fold_upper_manifest.json").read_text())
    assert manifest["run"]["exit_status"] == 0
    assert manifest["mathematics"]["bounds"]["columns"] == 98
    assert not manifest["randomness"]["used"]
    for item in manifest["outputs"] + manifest["mathematics"]["inputs"]:
        assert hashlib.sha256((ROOT / item["path"]).read_bytes()).hexdigest() == item["sha256"]
