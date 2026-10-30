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


# --- REFEREE.md (landed 2026-10-30) --------------------------------------------

#: REFEREE.md's 50-digit place sums, printed to 40 digits.
REFEREE_SUMS = {
    3: "4.085343727307429696561618503698417636452",
    6: "20.15893548387335264729736861988705707285",
}


def _place_costs(b, mp):
    """cost_p from the rectangle-overlap form, Q_p = (1/b) sum_d p^{-|d|/2} (b - |d| log p)_+,
    and the p-part of the prime term, 2 log p sum_{d >= 1} p^{-d/2} g(d log p), side by side.
    Written from the formulas, not from split.py."""
    from sympy import primerange

    out = []
    for p in primerange(2, int(mp.e ** b) + 1):
        lp = mp.log(p)
        k_max = int(b / lp) + 1
        q = (b + 2 * sum(mp.mpf(p) ** (-mp.mpf(k) / 2) * max(mp.mpf(0), b - k * lp)
                         for k in range(1, k_max + 1))) / b
        part = 2 * lp * sum(mp.mpf(p) ** (-mp.mpf(d) / 2) * max(mp.mpf(0), 1 - d * lp / b)
                            for d in range(1, k_max + 1))
        out.append((p, lp * (q - 1), part))
    return out


def test_the_referee_sums_reproduce_and_the_identity_is_a_regrouping() -> None:
    """At 50 digits the place sums equal REFEREE.md's to every printed digit, and each
    cost_p equals the p-part of the prime term: the identity holds place by place by
    construction, so the 1e-16 check in RESULTS.md tests the code, not mathematics."""
    from mpmath import mp

    with mp.workdps(50):
        for b, want in REFEREE_SUMS.items():
            costs = _place_costs(mp.mpf(b), mp)
            for p, cost, part in costs:
                assert abs(cost - part) < mp.mpf(10) ** -45, (b, p)
            total = sum(c for _, c, _ in costs)
            assert mp.nstr(total, 40) == want, (b, mp.nstr(total, 40))
            assert abs(total - mp.mpf(ROWS[float(b)]["cost_sum"])) < 1e-14
