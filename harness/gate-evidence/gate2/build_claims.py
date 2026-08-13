"""Ground truth for harness gate v2. Claims chosen from trap classes.

v1 failed on a ceiling: the control answered 12/12, so no treatment effect was
detectable. The defect was the claim set, not the harness and not the criterion.

v2 selects claims where **a plausible check confirms and a boundary case
refutes** — monthly step resets, the union default being suppressed by `#`/`W`,
the DOW 7->0 alias not applying in the six-field form, `W` clamping where a bare
day does not, iterator endpoint exclusivity. Difficulty was chosen a priori from
those classes, NOT by testing candidate claims against the control arm and
keeping the ones it failed, which would be selection on outcome.

Truth is still exhaustive enumeration, never the harness's own criterion.
"""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, "/home/user/zeta-lab")
from harness.departments.croniter_fixtures.frozen_croniter import (  # noqa: E402
    croniter,
    croniter_range,
)

START = dt.datetime(2024, 1, 1, 0, 0)
END = dt.datetime(2025, 1, 1, 0, 0)


def fires(expr: str, start=START, end=END, **kw) -> list[dt.datetime]:
    it = croniter(expr, start - dt.timedelta(minutes=1), **kw)
    out = []
    while True:
        n = it.get_next(dt.datetime)
        if n >= end:
            return out
        if n >= start:
            out.append(n)
        if len(out) > 20000:
            raise RuntimeError("runaway")


def gaps(expr: str) -> set[int]:
    f = fires(expr)
    return {(b - a).days for a, b in zip(f, f[1:])}


def months_hit(expr: str, **kw) -> set[int]:
    return {d.month for d in fires(expr, **kw)}


CLAIMS = [
    dict(id="D01",
         text="For the expression `0 0 */7 * *`, the interval between consecutive "
              "firings is 7 days throughout 2024.",
         check=lambda: gaps("0 0 */7 * *") == {7}),
    dict(id="D02",
         text="For the expression `0 0 15W * 5` with the constructor's default "
              "settings, the schedule fires on every Friday of 2024 in addition to "
              "the nearest weekday to the 15th of each month.",
         check=lambda: {d.date() for d in fires("0 0 15W * 5")}
         >= {d.date() for d in fires("0 0 * * 5")}),
    dict(id="D03",
         text="In the six-field (seconds-resolution) form, the expressions "
              "`0 0 0 * * 7` and `0 0 0 * * 0` expand to the same internal "
              "representation, because day-of-week 7 is aliased to 0.",
         check=lambda: croniter.expand("0 0 0 * * 7") == croniter.expand("0 0 0 * * 0")),
    dict(id="D04",
         text="The expression `0 0 31W * *` fires in every month of 2024, including "
              "February.",
         check=lambda: months_hit("0 0 31W * *") == set(range(1, 13))),
    dict(id="D05",
         text="A croniter positioned exactly on a firing instant returns that same "
              "instant from get_prev().",
         check=lambda: croniter("0 0 * * 5#3", dt.datetime(2024, 3, 15)).get_prev(
             dt.datetime) == dt.datetime(2024, 3, 15)),
    dict(id="D06",
         text="croniter_range() includes both of its endpoints when those endpoints "
              "are themselves firing instants.",
         check=lambda: {d.date() for d in croniter_range(
             dt.datetime(2024, 1, 5), dt.datetime(2024, 1, 19), "0 0 * * 5")}
         == {dt.date(2024, 1, 5), dt.date(2024, 1, 12), dt.date(2024, 1, 19)}),
    dict(id="D07",
         text="The expression `0 0 * * 1#5` fires in exactly 5 of the 12 months of 2024.",
         check=lambda: len(months_hit("0 0 * * 1#5")) == 5),
    dict(id="D08",
         text="The expression `0 0 1-31/10 * *` fires on day 1, day 11, day 21 and "
              "day 31 of every month of 2024.",
         check=lambda: all(
             {1, 11, 21, 31} <= {d.day for d in fires("0 0 1-31/10 * *") if d.month == m}
             for m in range(1, 13))),
    dict(id="D09",
         text="Passing implement_cron_bug=True changes which dates the expression "
              "`0 0 1 * 1` fires on in 2024.",
         check=lambda: {d.date() for d in fires("0 0 1 * 1")}
         != {d.date() for d in fires("0 0 1 * 1", implement_cron_bug=True)}),
    dict(id="D10",
         text="The expressions `0 0 L * *` and `0 0 l * *` fire on exactly the same "
              "dates in 2024.",
         check=lambda: {d.date() for d in fires("0 0 L * *")}
         == {d.date() for d in fires("0 0 l * *")}),
    dict(id="D11",
         text="For `0 0 15W * 5`, passing day_or_union=True makes the schedule fire "
              "on strictly more dates in 2024 than the default settings do.",
         check=lambda: len(fires("0 0 15W * 5", day_or_union=True))
         > len(fires("0 0 15W * 5"))),
    dict(id="D12",
         text="For the expression `0 0 31 * *`, the number of firings in 2024 equals "
              "the number of firings of `0 0 31W * *` in 2024.",
         check=lambda: len(fires("0 0 31 * *")) == len(fires("0 0 31W * *"))),
    dict(id="D13",
         text="Iterating `0 0 15W * *` backwards with get_prev() from 2025-01-01 "
              "yields exactly the reverse of the forward get_next() sequence over 2024.",
         check=lambda: (
             lambda f: (lambda it: [it.get_prev(dt.datetime) for _ in range(len(f))])(
                 croniter("0 0 15W * *", dt.datetime(2025, 1, 1))) == list(reversed(f))
         )(fires("0 0 15W * *"))),
    dict(id="D14",
         text="For the expression `0 0 */7 * *`, the total number of firings in 2024 "
              "is 52.",
         check=lambda: len(fires("0 0 */7 * *")) == 52),
]


def main() -> int:
    out = Path(__file__).resolve().parent
    key, rows = {}, []
    for c in CLAIMS:
        try:
            truth = bool(c["check"]())
        except Exception as exc:  # a claim whose truth cannot be settled is excluded
            print(f"{c['id']:<5} EXCLUDED  {type(exc).__name__}: {str(exc)[:60]}")
            continue
        key[c["id"]] = "SOUND" if truth else "DEFECTIVE"
        rows.append({"id": c["id"], "text": c["text"]})
        print(f"{c['id']:<5} {key[c['id']]:<10}")
    print(f"\nbalance: SOUND={sum(v=='SOUND' for v in key.values())} "
          f"DEFECTIVE={sum(v=='DEFECTIVE' for v in key.values())}  n={len(key)}")
    cj = json.dumps(rows, indent=2, sort_keys=True)
    kj = json.dumps(key, indent=2, sort_keys=True)
    (out / "claims.json").write_text(cj)
    (out / "key.json").write_text(kj)
    d = hashlib.sha256((cj + kj).encode()).hexdigest()
    (out / "FROZEN-DIGEST.txt").write_text(d + "\n")
    print(f"sha256(claims+key) = {d}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
