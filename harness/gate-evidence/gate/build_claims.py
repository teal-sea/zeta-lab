"""Ground truth for the harness A/B gate, established by exhaustive enumeration.

Every claim is a factual assertion about the observable behaviour of the frozen
croniter implementation over a bounded, fully enumerable window. Truth is
decided by counting matches — NOT by the harness's own `distinguishes`
criterion, which would make a PASS circular (a tool that computes X trivially
helps you compute X).

Subject: harness/departments/croniter_fixtures/frozen_croniter.py, byte-pinned,
authored outside this repository. Chosen because it loads with no numerical
dependencies and is the least contaminated registered department.

Run:  python3 build_claims.py            # verify + emit claims.json, key.json
"""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import sys
from pathlib import Path

REPO = Path("/home/user/zeta-lab")
sys.path.insert(0, str(REPO))

from harness.departments.croniter_fixtures.frozen_croniter import (  # noqa: E402
    croniter,
)

START = dt.datetime(2024, 1, 1, 0, 0)
END = dt.datetime(2025, 1, 1, 0, 0)


def fire_dates(expr: str, start: dt.datetime = START, end: dt.datetime = END) -> list[dt.datetime]:
    """Every datetime the frozen implementation emits in [start, end)."""
    it = croniter(expr, start - dt.timedelta(minutes=1))
    out: list[dt.datetime] = []
    while True:
        nxt = it.get_next(dt.datetime)
        if nxt >= end:
            return out
        if nxt >= start:
            out.append(nxt)
        if len(out) > 20000:  # bounded: no claim here needs more
            raise RuntimeError(f"runaway enumeration for {expr!r}")


# --------------------------------------------------------------------------
# Claims. `check` returns the TRUE/FALSE value of the assertion by enumeration.
# `text` is exactly what an evaluating agent is shown — no hints, no framing.
# --------------------------------------------------------------------------

CLAIMS: list[dict] = [
    dict(
        id="C01",
        text="For the expression `0 0 15 * 5`, the schedule fires on every Friday of 2024 "
             "as well as on the 15th of every month of 2024 — that is, the day-of-month "
             "and day-of-week fields combine as a union, not an intersection.",
        check=lambda: (
            {d.date() for d in fire_dates("0 0 15 * 5")}
            == {d.date() for d in fire_dates("0 0 15 * *")}
            | {d.date() for d in fire_dates("0 0 * * 5")}
        ),
    ),
    dict(
        id="C02",
        text="For the expression `0 0 15 * 5`, the schedule fires only on dates that are "
             "both the 15th of a month and a Friday. In 2024 that is exactly 2 dates.",
        check=lambda: len(fire_dates("0 0 15 * 5")) == 2,
    ),
    dict(
        id="C03",
        text="The expression `0 0 * * 5#3` fires exactly 12 times in 2024, once per month.",
        check=lambda: len(fire_dates("0 0 * * 5#3")) == 12,
    ),
    dict(
        id="C04",
        text="The expression `0 0 * * 5#5` fires exactly 12 times in 2024, because every "
             "month contains a fifth Friday.",
        check=lambda: len(fire_dates("0 0 * * 5#5")) == 12,
    ),
    dict(
        id="C05",
        text="The expression `0 0 15W * *` never fires on a Saturday or a Sunday during 2024.",
        check=lambda: all(d.weekday() < 5 for d in fire_dates("0 0 15W * *")),
    ),
    dict(
        id="C06",
        text="For the expression `0 0 1W * *`, when the 1st of a month falls on a Sunday the "
             "schedule fires on the last day of the PRECEDING month. In 2024 this happens "
             "at least once.",
        check=lambda: any(
            d.day != 1 and d.day > 20 for d in fire_dates("0 0 1W * *")
        ),
    ),
    dict(
        id="C07",
        text="In 2024 the expression `0 0 * * 1#1` and the expression `0 0 * * 1` fire on "
             "the same number of dates.",
        check=lambda: len(fire_dates("0 0 * * 1#1")) == len(fire_dates("0 0 * * 1")),
    ),
    dict(
        id="C08",
        text="The expression `0 0 29 2 *` fires exactly once in 2024.",
        check=lambda: len(fire_dates("0 0 29 2 *")) == 1,
    ),
    dict(
        id="C09",
        text="For the expression `0 0 1 * 1`, every Monday of 2024 is a firing date.",
        check=lambda: {d.date() for d in fire_dates("0 0 * * 1")}
        <= {d.date() for d in fire_dates("0 0 1 * 1")},
    ),
    dict(
        id="C10",
        text="The expression `0 0 * * 6#2` fires on the second Saturday of each month of 2024, "
             "and every one of those dates falls in the range day-of-month 8 through 14 inclusive.",
        check=lambda: (
            len(fire_dates("0 0 * * 6#2")) == 12
            and all(8 <= d.day <= 14 for d in fire_dates("0 0 * * 6#2"))
        ),
    ),
    dict(
        id="C11",
        text="Over 2024 the expression `0 0 31 * *` fires exactly 12 times, because the "
             "implementation clamps day 31 to the last day of shorter months.",
        check=lambda: len(fire_dates("0 0 31 * *")) == 12,
    ),
    dict(
        id="C12",
        text="Over 2024 the expression `0 0 * * 0` and the expression `0 0 * * 7` fire on "
             "exactly the same set of dates.",
        check=lambda: {d.date() for d in fire_dates("0 0 * * 0")}
        == {d.date() for d in fire_dates("0 0 * * 7")},
    ),
]


def main() -> int:
    out_dir = Path(__file__).resolve().parent
    key: dict[str, str] = {}
    rows = []
    print(f"{'id':<5} {'truth':<10} evidence")
    for claim in CLAIMS:
        truth = bool(claim["check"]())
        verdict = "SOUND" if truth else "DEFECTIVE"
        key[claim["id"]] = verdict
        rows.append({"id": claim["id"], "text": claim["text"]})
        print(f"{claim['id']:<5} {verdict:<10} enumerated over 2024")

    counts = {"SOUND": sum(v == "SOUND" for v in key.values()),
              "DEFECTIVE": sum(v == "DEFECTIVE" for v in key.values())}
    print(f"\nbalance: {counts}")

    claims_json = json.dumps(rows, indent=2, sort_keys=True)
    key_json = json.dumps(key, indent=2, sort_keys=True)
    (out_dir / "claims.json").write_text(claims_json, encoding="utf-8")
    (out_dir / "key.json").write_text(key_json, encoding="utf-8")

    digest = hashlib.sha256((claims_json + key_json).encode()).hexdigest()
    (out_dir / "FROZEN-DIGEST.txt").write_text(digest + "\n", encoding="utf-8")
    print(f"\nsha256(claims+key) = {digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
