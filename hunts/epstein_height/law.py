"""Fit the loss, and turn it into a guard that can be tested.

The mechanism, re-derived here rather than copied from
`hunts/gate5_p6_c/probe.py`, which states the leading term:

`epstein_completed` forms `first + second/sqrt(d) + 1/(sqrt(d)(s-1)) - 1/s`.
The last two terms are `O(1/t)`.  The value being computed is
`Lambda_Q(s) = (sqrt d / pi)^s Gamma(s) zeta_Q(s)`, and on a vertical line

    |Gamma(sigma + it)| ~ sqrt(2 pi) t^{sigma - 1/2} exp(-pi t / 2).

So the ratio of the largest term formed to the answer is
`(1/t) / |Gamma(s)|`, and the decimal digits lost to cancellation are

    L(sigma, t) = 0.68219 t - (sigma - 1/2) log10 t - 0.39909.

**This formula is incomplete and the line above it, as first written, cancelled
a real term against nothing.** `law2.py` derives the whole thing without any
asymptotic and without a fitted constant; what is missing here is a further
`- log10 t`, a `sigma log10 pi`, and `- log10|zeta_Q(s)|`, and the last of those
is the entire reason this module's residuals are form-dependent. It is kept
because the write-up compares the two, and a model that was wrong in a
measurable way is the evidence that the measurement could see it.

The leading `0.68219 t` is the constant `GUARD_PER_UNIT_HEIGHT = 0.6822`
already recorded inside one hunt.  The `sigma` term is the part that decides
whether a rule derived on one vertical line transfers to another. Every cell
this module was fitted on is at `sigma = 5`, so that transfer was asserted and
not tested; an audit tested it at `sigma = 1/2` against an exact oracle and
found this law's residual there is `+4.66` digits. The critical line is still
the worst case at large `t`, and this law over-provisions it by about 4.7
digits, which is a number a guard would act on. Use `guard2.py`.

`epstein_zeta` opens `workdps(dps + 10)` and then calls `epstein_completed`
with `dps = mp.dps`, which opens `workdps(dps + 10)` again, so the working
precision a caller actually gets is `dps + 20`.  Predicted correct digits are
therefore `dps + 20 - L(sigma, t)`, capped by the oracle's own floor.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

ART = Path(__file__).resolve().parent / "artifacts"

LEAD = math.pi / (2 * math.log(10))          # 0.6821881769...
CONST = math.log10(math.sqrt(2 * math.pi))   # 0.3990899342...


def digits_lost(sigma: float, t: float) -> float:
    if t <= 0:
        return 0.0
    return LEAD * t - (sigma - 0.5) * math.log10(t) - CONST


def predicted_correct(sigma: float, t: float, dps: int, floor: float) -> float:
    return max(0.0, min(floor, dps + 20 - digits_lost(sigma, t)))


def required_dps(sigma: float, t: float, want_digits: int = 10) -> int:
    """The smallest dps whose answer carries `want_digits` correct decimals."""
    return max(15, math.ceil(digits_lost(sigma, t) + want_digits - 20))


def main() -> None:
    rows = json.loads((ART / "surface.json").read_text(encoding="utf-8"))
    # The oracle's ceiling is a property of the ORACLE at each (form, height),
    # set by where the lattice sum was truncated, not of the routine.  Taking
    # one global ceiling would count cells that merely hit the oracle's own
    # limit as cells that confirm the law.  So the ceiling is per (form, t):
    # the best any precision achieved there.
    ceil_by = {}
    for r in rows:
        k = (tuple(r["form"]), r["t"])
        ceil_by[k] = max(ceil_by.get(k, 0.0), r["correct_digits"])
    out, resid = [], []
    for r in rows:
        k = (tuple(r["form"]), r["t"])
        ceiling = ceil_by[k]
        pred = predicted_correct(r["sigma"], r["t"], r["dps"], ceiling)
        d = r["correct_digits"] - pred
        out.append({**r, "oracle_ceiling_here": ceiling,
                    "predicted_correct_digits": pred, "residual": d})
        # a cell tests the law only when it is neither pinned at the oracle's
        # ceiling nor flat at zero: in between, the law is making a prediction
        if 0.5 < r["correct_digits"] < ceiling - 0.5:
            resid.append(d)
    floor = max(r["correct_digits"] for r in rows)
    n = len(resid)
    mean = sum(resid) / n if n else float("nan")
    rms = math.sqrt(sum(x * x for x in resid) / n) if n else float("nan")
    print(f"oracle floor {floor:.1f} digits")
    print(f"cells that test the law (not saturated, not zero): {n} of {len(rows)}")
    print(f"residual observed - predicted: mean {mean:+.2f}, rms {rms:.2f}, "
          f"worst {max(resid, key=abs):+.2f}" if n else "")
    print()
    print("guard rule, digits of margin wanted = 10:")
    print(f"{'t':>6s} {'sigma=0.5':>10s} {'sigma=3':>9s} {'sigma=5':>9s}")
    for t in (20, 40, 60, 85.7, 100, 160, 240):
        print(f"{t:>6.1f} {required_dps(0.5, t):>10d} {required_dps(3, t):>9d} "
              f"{required_dps(5, t):>9d}")
    (ART / "law.json").write_text(json.dumps(
        {"lead_constant": LEAD, "const": CONST, "oracle_floor": floor,
         "n_testing_cells": n, "residual_mean": mean, "residual_rms": rms,
         "rows": out}, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
