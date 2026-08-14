"""Mutation family for gate v3. Ground truth by enumeration, never by the harness.

An item asks whether an evidence bundle ESTABLISHES that an implementation is
correct over a declared scope. Truth = does the bundle kill every mutant in this
family. So the family must be built first, and it must be honest: importable
mutants only, and only those that actually differ from the frozen original
somewhere in scope (equivalent mutants are discarded, not counted as kills).
"""
from __future__ import annotations

import datetime as dt
import importlib.util
import json
import signal
import sys
import types
from pathlib import Path

SRC = Path("/home/user/zeta-lab/harness/departments/croniter_fixtures/frozen_croniter.py")
OUT = Path(__file__).resolve().parent

START, END = dt.datetime(2024, 1, 1), dt.datetime(2025, 1, 1)

# The declared scope: correctness is claimed over exactly these expressions.
SCOPE = [
    "0 0 15 * 5", "0 0 1 * 1", "0 0 31 * *", "0 0 29 2 *",
    "0 0 * * 5#3", "0 0 * * 5#5", "0 0 * * 1#1", "0 0 * * 6#2",
    "0 0 15W * *", "0 0 1W * *", "0 0 31W * *", "0 0 15W * 5",
    "0 0 */7 * *", "0 0 1-31/10 * *", "0 0 L * *", "0 0 * * 0",
    "0 0 * * 7", "0 0 10-20 * *", "0 0 5 * 3", "0 0 * * 3#2",
]

# (id, needle, replacement, what it breaks). Textual, single-point, applied to a
# copy of the source. Chosen to span the union split, the special forms and the
# field ranges -- the parts the scope actually exercises.
MUTATIONS = [
    ("m01", "return t1 if t1 < t2 else t2", "return t1 if t1 > t2 else t2",
     "union picks the later side instead of the earlier"),
    ("m02", "dow_side_nearest = self.nearest_weekday", "dow_side_nearest = set()",
     "W constraint dropped from the DOW side"),
    ("m03", "dom_side_nth = nth_weekday_of_month", "dom_side_nth = {}",
     "# constraint dropped from the DOM side"),
    ("m04", "clean_split = not nth_weekday_of_month and not self.nearest_weekday",
     "clean_split = not nth_weekday_of_month or not self.nearest_weekday",
     "clean-split test weakened from and to or"),
    ("m05", "and self._day_or", "and not self._day_or",
     "union/intersection gate inverted"),
    ("m06", "if t1 is None:", "if t1 is not None:",
     "None-handling on the DOM side inverted"),
    ("m07", "return t1 if t1 > t2 else t2", "return t1 if t1 < t2 else t2",
     "prev direction picks the earlier side instead of the later"),
    ("m08", "w = (day_of_week + 6) % 7", "w = (day_of_week + 5) % 7",
     "nth-weekday calendar offset shifted by one"),
    ("m09", "candidate = c[n - 1]", "candidate = c[n]",
     "nth-weekday index off by one"),
    ("m10", "elif len(c) < n:", "elif len(c) <= n:",
     "fifth-weekday availability test off by one"),
    ("m11", "if weekday < 5:  # Mon-Fri", "if weekday <= 5:  # Mon-Fri",
     "W treats Saturday as a weekday"),
    ("m12", "if day > 1:", "if day > 2:",
     "W Saturday-at-month-start boundary shifted"),
    ("m13", "if day < last_day:", "if day <= last_day:",
     "W Sunday-at-month-end boundary shifted"),
    ("m14", "return day - 2  # Friday (last day is Sun, go back to Fri)",
     "return day - 3  # Friday (last day is Sun, go back to Fri)",
     "W Sunday-at-month-end steps back too far"),
    ("m15", "if month == 2 and _is_leap(year):", "if month == 2 and False:",
     "February never gets its leap day"),
    ("m16", "diff_day_of_week = nearest_diff_method(d.isoweekday() % 7, expanded[DOW_FIELD], 7)",
     "diff_day_of_week = nearest_diff_method(d.isoweekday(), expanded[DOW_FIELD], 7)",
     "Sunday not folded from 7 to 0 in the DOW match"),
    ("m17", "RANGES = ((0, 59), (0, 23), (1, 31), (1, 12), (0, 6), (0, 59), (1970, 2099))",
     "RANGES = ((0, 59), (0, 23), (1, 30), (1, 12), (0, 6), (0, 59), (1970, 2099))",
     "day-of-month range truncated to 30"),
    ("m18", "if c[0][0] == 0:", "if c[0][0] != 0:",
     "partial first week kept/dropped inverted"),
    ("m19", "if (is_prev and candidate <= d.day) or (not is_prev and d.day <= candidate):",
     "if (is_prev and candidate < d.day) or (not is_prev and d.day < candidate):",
     "nth-weekday same-day candidate excluded"),
    ("m20", "return day + 2  # Monday (1st is Sat, so 3rd is Mon)",
     "return day + 1  # Monday (1st is Sat, so 3rd is Mon)",
     "W Saturday-the-1st lands on Sunday"),
    ("m21", "return day + 1  # Monday", "return day + 3  # Monday",
     "W Sunday overshoots Monday"),
]


def load(name: str, source: str) -> types.ModuleType:
    spec = importlib.util.spec_from_loader(name, loader=None)
    mod = importlib.util.module_from_spec(spec)
    mod.__file__ = str(SRC)
    exec(compile(source, str(SRC), "exec"), mod.__dict__)
    return mod


class _Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise _Timeout()


signal.signal(signal.SIGALRM, _alarm)


def fires(mod, expr: str) -> tuple | str:
    """Fire dates in 2024, or an error tag. An error is a behaviour too.

    A mutant that never fires makes croniter search forward for years, so every
    evaluation is wall-clock bounded. A timeout is recorded as its own
    behaviour rather than crashing the build -- it is still a difference.
    """
    signal.setitimer(signal.ITIMER_REAL, 10.0)
    try:
        it = mod.croniter(expr, START - dt.timedelta(minutes=1))
        out = []
        while True:
            n = it.get_next(dt.datetime)
            if n >= END:
                return tuple(d.isoformat() for d in out)
            if n >= START:
                out.append(n)
            if len(out) > 5000:
                return "RUNAWAY"
    except _Timeout:
        return "TIMEOUT"
    except Exception as exc:
        return f"ERROR:{type(exc).__name__}"
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0.0)


def main() -> int:
    src = SRC.read_text()
    base = load("frozen_base", src)
    base_beh = {e: fires(base, e) for e in SCOPE}
    bad = [e for e, v in base_beh.items() if isinstance(v, str)]
    if bad:
        print(f"scope expressions the ORIGINAL cannot evaluate: {bad}")
        return 2

    kept, dropped = {}, []
    for mid, needle, repl, desc in MUTATIONS:
        n = src.count(needle)
        if n != 1:
            dropped.append((mid, f"needle appears {n}x, not exactly once"))
            continue
        try:
            mod = load(f"mut_{mid}", src.replace(needle, repl))
        except Exception as exc:
            dropped.append((mid, f"unimportable: {type(exc).__name__}"))
            continue
        beh = {e: fires(mod, e) for e in SCOPE}
        differs = sorted(e for e in SCOPE if beh[e] != base_beh[e])
        if not differs:
            dropped.append((mid, "equivalent mutant: identical on the whole scope"))
            continue
        kept[mid] = {"desc": desc, "differs_on": differs, "behaviour": beh}
        print(f"{mid}  differs on {len(differs):>2}/{len(SCOPE)}  {desc}")

    for mid, why in dropped:
        print(f"{mid}  DROPPED  {why}")

    OUT.joinpath("family.json").write_text(json.dumps(
        {"scope": SCOPE, "base": base_beh,
         "mutants": {k: {"desc": v["desc"], "differs_on": v["differs_on"],
                         "behaviour": v["behaviour"]} for k, v in kept.items()}},
        indent=2, sort_keys=True))
    print(f"\nfamily: {len(kept)} live mutants, {len(dropped)} dropped, scope {len(SCOPE)}")
    return 0 if kept else 1


if __name__ == "__main__":
    raise SystemExit(main())
