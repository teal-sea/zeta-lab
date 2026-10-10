"""The seventh-power figures on the front door, replayed rather than quoted.

`docs/39` and the review ledger state, from `hunts/oct08_extensions/`, that
given QRH(7/8) and Kadiri, Lumley and Ng's explicit density rows the chain
closes at k = 7: 764 Arb cells covering 2.25 <= log n <= 50 with every margin
above 0.13045, an analytic tail below 0.012961 beyond, and nine exact
witnesses for n <= 9; and that the same bound fails at k = 6 near
log n = 29. That hunt carries no test of its own, so this runs its producer
script and its independent audit's checker, both of which assert their
inequalities in Arb, and compares the producer's output with the recorded
`verification.txt`.

Scope, stated so nobody reads more into a green run than it earns: this
checks that the recorded finite computation reproduces and that the audit's
replay passes. It says nothing about the written reduction, the cited
density constants, the inherited explicit formula or OpenAI's theorem, and
both scripts share hunt #126's base routine, so a defect there would pass
here twice.
"""

from __future__ import annotations

import json
import subprocess
import sys
from math import isqrt
from pathlib import Path

import pytest

pytest.importorskip("flint")

REPO = Path(__file__).resolve().parents[1]
HUNT = REPO / "hunts" / "oct08_extensions"
PRODUCER = HUNT / "routes" / "prime-gap-multistrip" / "layers.py"
RECORDED = HUNT / "routes" / "prime-gap-multistrip" / "verification.txt"
AUDIT = HUNT / "audits" / "prime-gap-multistrip" / "check.py"


def _run(script: Path) -> str:
    result = subprocess.run(
        [sys.executable, "-B", str(script)],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert result.returncode == 0, result.stderr
    return result.stdout


def _ball(text: str) -> tuple[float, float]:
    """An Arb ball as printed, ``[mid +/- rad]``, as (lower, upper) floats."""
    body = text.strip().lstrip("[").rstrip("]")
    mid, _, rad = body.partition("+/-")
    m, r = float(mid), float(rad) if rad else 0.0
    return m - r, m + r


def _parse(text: str) -> tuple[dict, dict[tuple[int, int], tuple[float, float]]]:
    """The summary object, then the (k, log n) -> margin balls printed after it."""
    summary, end = json.JSONDecoder().raw_decode(text)
    margins = {}
    for line in text[end:].strip().splitlines():
        k, logn, ball = line.split(" ", 2)
        margins[(int(k), int(logn))] = _ball(ball)
    return summary, margins


@pytest.fixture(scope="module")
def replay() -> str:
    return _run(PRODUCER)


def test_the_producer_replays_the_recorded_output(replay: str) -> None:
    summary, _ = _parse(replay)
    recorded, _ = _parse(RECORDED.read_text())
    for key in ("intervals", "logn_start", "logn_end", "witnesses"):
        assert summary[key] == recorded[key], key
    assert summary["worst_margin"][1] == recorded["worst_margin"][1]
    assert abs(summary["worst_margin"][0] - recorded["worst_margin"][0]) < 1e-12


def test_the_quoted_figures(replay: str) -> None:
    summary, margins = _parse(replay)
    assert summary["intervals"] == 764
    assert (summary["logn_start"], summary["logn_end"]) == ("2.25", "50")
    assert summary["worst_margin"][0] > 0.13045
    assert _ball(summary["tail_error"])[1] < 0.012961
    witnesses = dict(summary["witnesses"])
    assert sorted(witnesses) == list(range(1, 10))
    for n, p in witnesses.items():
        assert n**7 < p < (n + 1) ** 7
        assert p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))
    # k = 7 positive at every printed height; k = 6 negative near log n = 29.
    assert all(low > 0 for (k, _), (low, _) in margins.items() if k == 7)
    assert margins[(6, 29)][1] < -50


def test_the_independent_audit_replays() -> None:
    out = _run(AUDIT)
    assert "all 764 margins > .13045" in out
    assert "Uniform tail error < .012961" in out
    assert "rejects k6 at L29; accepts k7" in out
    assert "mutants fail" in out
