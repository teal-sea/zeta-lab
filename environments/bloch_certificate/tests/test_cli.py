import pytest
from test_oracle import archive_path, oracle_module


def test_prepare_reuses_only_valid_archive(tmp_path):
    from bloch_certificate.cli import prepare
    assert prepare(archive_path()) == archive_path()
    bad = tmp_path / "bad.zip"
    bad.write_bytes(b"not an archive")
    with pytest.raises(oracle_module().OracleError, match="digest"):
        prepare(bad)
