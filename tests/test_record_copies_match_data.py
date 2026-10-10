"""Two copies of numbers that drifted from their data (issue #158).

1. ``hunts/field_audit/RESULTS.md`` says this laboratory is "tenth of fifteen
   public claims" while the same file speaks of "these fourteen claims".  Both
   are right once the count is stated: ``rank.py`` orders fifteen entries,
   fourteen follow-ups above ``anthropics/zeta-23-lean`` and Theorem D itself,
   and ours is tenth.  Pinned here against ``rank.py``'s own list and the
   section 2 table, so the prose cannot drift from either again.

2. ``hunts/ainta_seven_point/RUNS.md`` printed ``Phi_3`` and ``Phi_4`` with
   wrong decimal tails that PR #152 corrected elsewhere.  The run log is left
   as recorded and annotated; the annotation's decimals are recomputed here
   from the exact rationals and ``H = 3/2 - 1/(sqrt 2 tan(1/sqrt 2))``, and the
   recorded tails are checked to be the wrong ones, so the check can fail.
"""
from __future__ import annotations

import importlib.util
import re
from decimal import Decimal
from pathlib import Path

from mpmath import mp

ROOT = Path(__file__).resolve().parents[1]
FIELD = ROOT / "hunts" / "field_audit"
RUNS = ROOT / "hunts" / "ainta_seven_point" / "RUNS.md"


def _rank_module():
    spec = importlib.util.spec_from_file_location("field_audit_rank", FIELD / "rank.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_field_audit_count_matches_rank_py_and_the_table():
    rank = _rank_module()
    ordered = sorted(rank.CLAIMS, key=lambda row: Decimal(row[1]), reverse=True)
    names = [name for name, _ in ordered]
    assert len(ordered) == 15
    assert names[-1].startswith("anthropics/zeta-23-lean")
    above_theorem_d = ordered[:-1]
    assert len(above_theorem_d) == 14
    ours = [n for n, _ in above_theorem_d if n.startswith("teal-sea")]
    assert len(ours) == 2 and len(above_theorem_d) - len(ours) == 12
    assert 1 + next(i for i, n in enumerate(names) if n.startswith("teal-sea")) == 10

    text = (FIELD / "RESULTS.md").read_text(encoding="utf-8")
    section2 = text.split("## 2. The ranking", 1)[1].split("\n## ", 1)[0]
    rows = [line for line in section2.splitlines() if re.match(r"^\|[^|]*\| (\*\*)?`0\.67", line)]
    assert len(rows) == len(ordered)
    # every published constant in the table is rank.py's, in rank.py's order
    table_values = [re.search(r"`(0\.67[0-9]+)", row).group(1) for row in rows]
    # (either may carry more digits: rank.py pads with zeros, the table's
    # Theorem D row carries three more published digits)
    for shown, (_, exact) in zip(table_values, ordered):
        exact = exact.rstrip("0")
        common = min(len(shown), len(exact))
        assert shown[:common] == exact[:common], (shown, exact)

    section1 = text.split("## 1.", 1)[1].split("\n## ", 1)[0]
    assert "**tenth**\nof fifteen public claims" in section1
    assert "fourteen follow-up claims" in section1
    assert "`10 of 15`" in section1


def _phis():
    with mp.workdps(50):
        h = mp.mpf(3) / 2 - 1 / (mp.sqrt(2) * mp.tan(1 / mp.sqrt(2)))
        phi3 = (149000000 * h - 99200) / 148800133
        phi4 = (906250 * h - 1085) / 904171
        return tuple(mp.nstr(v, 30, strip_zeros=False) for v in (h, phi3, phi4))


def test_the_annotated_decimals_are_the_exact_rationals_and_the_recorded_ones_are_not():
    h, phi3, phi4 = _phis()
    assert h.startswith("0.67250070367941164573437979")
    assert phi3.startswith("0.67273733450380945032")
    assert phi4.startswith("0.67284701976668882760")

    text = RUNS.read_text(encoding="utf-8")
    # the run log keeps what it recorded ...
    assert "0.67273733450380945875" in text
    assert "0.67284701976668870316" in text
    # ... which is wrong, from the 18th and 16th decimals respectively
    assert not phi3.startswith("0.67273733450380945875")
    assert not phi4.startswith("0.67284701976668870316")
    assert phi3[:19] == "0.67273733450380945" and phi4[:17] == "0.672847019766688"
    # and it is annotated with the right ones
    annotations = [p for p in text.split("\n\n") if p.startswith("> **Annotation, not an edit (issue #158)")]
    assert len(annotations) == 2
    assert "0.67273733450380945032..." in annotations[0]
    assert "0.67284701976668882760..." in annotations[1]
    assert "0.67273733450380945032..." in annotations[1]
