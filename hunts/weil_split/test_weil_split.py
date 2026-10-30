"""Pins for weil_split's record (added at landing, 2026-10-30)."""

from __future__ import annotations

import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROWS = {r["b"]: r for r in json.loads((HERE / "results.json").read_text())}


def test_the_places_sum_to_the_prime_term() -> None:
    for b, r in ROWS.items():
        assert abs(r["cost_sum"] - r["minus_prime_term"]) <= 1e-12 * r["cost_sum"], b


def test_the_margin_is_w_over_the_prime_cost_by_construction() -> None:
    """cover - 1 = W_zeros / sum_p cost_p: the margin is W normalized by the
    prime cost, not an independent statement about the archimedean term."""
    for b, r in ROWS.items():
        assert abs((r["cover_derived"] - 1) - r["W_from_zeros"] / r["cost_sum"]) < 1e-12, b


def test_the_margin_decay_exponents_are_the_recorded_ones() -> None:
    bs = sorted(ROWS)
    m = [ROWS[b]["cover_derived"] - 1 for b in bs]
    local = [math.log(m[i] / m[i + 1]) / math.log(bs[i + 1] / bs[i]) for i in range(len(bs) - 1)]
    assert 2.1 < min(local) < 2.3 and 5.5 < max(local) < 5.7
    overall = math.log(m[0] / m[-1]) / math.log(bs[-1] / bs[0])
    assert 3.7 < overall < 3.9
