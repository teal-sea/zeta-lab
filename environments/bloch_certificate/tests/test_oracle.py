"""Tests for the public demo's trust boundary, not a theorem audit."""
import importlib
import json
import sys
from decimal import Decimal, ROUND_CEILING, localcontext
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))


def oracle_module():
    return importlib.import_module("bloch_certificate.oracle")


def archive_path():
    import os
    configured = os.environ.get("BLOCH_ARCHIVE")
    local = Path(__file__).resolve().parents[3] / ".upstream/bloch/bloch-computations-1.0.0.zip"
    if configured:
        return Path(configured)
    if local.exists():
        return local
    from bloch_certificate.bloch_certificate import DEFAULT_ARCHIVE
    return DEFAULT_ARCHIVE


def test_pinned_archive_reproduces_fixed_certificate_and_rejects_tampering(tmp_path):
    module = oracle_module()
    oracle = module.Oracle(archive_path())
    result = oracle.run("fine")
    assert result["gain"] == "0.0114402996202"
    assert "PASS: all assertions applicable to the fine certificate verified" in result["log"]
    assert result["archive_sha256"] == module.ARCHIVE_SHA256
    bad = tmp_path / "changed.zip"
    bad.write_bytes(archive_path().read_bytes() + b"changed")
    with pytest.raises(module.OracleError, match="digest"):
        module.Oracle(bad).run("fine")
    with pytest.raises(ValueError, match="mode"):
        oracle.run("../../evil.py")


def test_near_branch_accepts_ceiling_and_rejects_overclaim():
    module = oracle_module()
    oracle = module.Oracle(archive_path())
    evidence = oracle.run("near")
    assert evidence["positivity"] > 0
    assert float(evidence["gain"]) == pytest.approx(0.0153040536989472, abs=1e-16)
    assert oracle.grade("near-branch-cutoff", '{"target":"0.0153040536"}')["reward"] == 1.0
    assert oracle.grade("near-branch-cutoff", '{"target":"0.015304053599"}')["reward"] == 1.0
    assert oracle.grade("near-branch-cutoff", '{"target":"0.0153"}')["reward"] == 0.0
    assert oracle.grade("near-branch-cutoff", '{"target":"0.0154"}')["reward"] == 0.0
    # A decimal just above the binary64 bound must not round down into acceptance.
    exact = Decimal.from_float(float(evidence["gain"]))
    with localcontext() as context:
        context.prec = 60
        above = exact.quantize(Decimal("1e-30"), rounding=ROUND_CEILING)
    assert above > exact
    assert oracle.grade("near-branch-cutoff", json.dumps({"target": format(above, "f")}))["reward"] == 0.0
    assert oracle.grade("near-reproduce", '{"target":"0.0153"}')["reward"] == 1.0
    assert oracle.grade("fine-reproduce", '{"target":"0.0114402996202"}')["reward"] == 1.0
    assert oracle.grade("coarse-reproduce", '{"target":"0.0113729923988"}')["reward"] == 1.0
    assert oracle.grade("fine-reproduce", '{"target":"0.0113"}')["reward"] == 0.0
    assert oracle.grade("near-branch-cutoff", '{"target":"NaN"}')["status"] == "invalid_submission"


def test_missing_archive_and_timeout_are_not_wrong_answers(tmp_path):
    module = oracle_module()
    with pytest.raises(module.OracleError):
        module.Oracle(tmp_path / "absent.zip").grade("near-reproduce", '{"target":"0.0153"}')
    with pytest.raises(module.OracleError, match="timed out"):
        module.Oracle(archive_path(), timeout=0.001).run("fine")


def test_target_is_an_exact_bounded_decimal_string():
    parse = oracle_module().parse_target
    assert parse('{"target":"0.0153040536"}') == Decimal("0.0153040536")
    for bad in [
        '{"target":0.0153}', '{"target":"NaN"}', '{"target":"Infinity"}',
        '{"target":"-1"}', '{"target":"1e9999999"}', '{"target":"0.1","target":"0.2"}',
        '{"target":"0.0153","code":"print(1)"}', 'PASS',
        json.dumps({"target": "0." + "1" * 1000}),
    ]:
        with pytest.raises(ValueError):
            parse(bad)
