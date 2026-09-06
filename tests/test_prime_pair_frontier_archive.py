import codecs
import hashlib
from pathlib import Path

EXPECTED_SHA256 = "61f4901f8659d13cd2c795b560475b1313db666650da78dabeccd7e03c1807de"


def test_prime_pair_frontier_archive_integrity():
    root = Path(__file__).resolve().parents[1]
    folder = root / "hunts/prime_pair_error/frontier/2026-09-06/archive"
    parts = sorted(folder.glob("part-*.b64"))
    assert parts, "frontier archive chunks are missing"
    encoded = "".join("".join(p.read_text(encoding="ascii").split()) for p in parts)
    assert encoded, "frontier archive encoding is empty"
    archive_bytes = codecs.decode(encoded.encode("ascii"), "base64")
    assert archive_bytes, "frontier archive reconstructed as zero bytes"
    assert hashlib.sha256(archive_bytes).hexdigest() == EXPECTED_SHA256
