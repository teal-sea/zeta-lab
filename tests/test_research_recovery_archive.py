"""Pin restored source bytes without promoting the underlying mathematics."""

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "hunts/prime_pair_error/artifacts/recovery_2026_09_13/manifest.json"


def test_recovered_research_sources_are_present_and_unchanged():
    manifest = json.loads(MANIFEST.read_text())
    rows = manifest["files"]
    assert len(rows) == 52
    assert len({row["path"] for row in rows}) == len(rows)
    for row in rows:
        path = ROOT / row["path"]
        assert path.is_relative_to(ROOT)
        data = path.read_bytes()
        assert len(data) == row["bytes"], row["path"]
        assert hashlib.sha256(data).hexdigest() == row["sha256"], row["path"]
