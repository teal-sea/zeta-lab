"""Vendored frozen subject for the croniter department.

``frozen_croniter.py`` is a verbatim copy of ``src/croniter/croniter.py`` from
https://github.com/pallets-eco/croniter at commit
32431c655c30b0eab0075f8a9108387cff51d1b2 (branch ``day-or-union``, 2026-08-09):
upstream master d2e8a13 plus one feature commit adding the opt-in
``day_or_union`` parameter. MIT licensed — see ``LICENSE`` beside it.

Vendored rather than pip-installed so the department's subject is *pinned*:
the battery's verdicts are about this exact frozen implementation, and a pip
upgrade cannot silently change what is being refereed. The department loads it
(and its patched rivals/lesions) by executing this source text into fresh
module objects — the file is data here, not an import.
"""

from pathlib import Path

FIXTURES_DIR = Path(__file__).resolve().parent
FROZEN_PATH = FIXTURES_DIR / "frozen_croniter.py"
FROZEN_COMMIT = "32431c655c30b0eab0075f8a9108387cff51d1b2"


def frozen_source() -> str:
    return FROZEN_PATH.read_text(encoding="utf-8")
