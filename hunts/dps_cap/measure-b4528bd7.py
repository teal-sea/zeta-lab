"""One number at two precisions: what the dps cap costs at s = 0.8 + 85.7i.

Run from the repo root:

    .venv/bin/python hunts/dps_cap/measure.py

Writes ``hunts/dps_cap/results.json`` and prints the two magnitudes.
"""

from __future__ import annotations

import json
import pathlib
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from mpmath import mp, mpc  # noqa: E402

from zeta.epstein import epstein_completed  # noqa: E402

FORM = (2, 1, 3)
S = ("0.8", "85.7")
LEVELS = (20, 60, 80)


def _at(dps: int) -> dict:
    with mp.workdps(dps + 20):
        s = mpc(mp.mpf(S[0]), mp.mpf(S[1]))
    t0 = time.perf_counter()
    value = epstein_completed(s, FORM, dps=dps)
    elapsed = time.perf_counter() - t0
    with mp.workdps(dps + 20):
        magnitude = abs(value)
        exponent = None if magnitude == 0 else int(mp.floor(mp.log10(magnitude)))
        return {
            "dps": dps,
            "abs": mp.nstr(magnitude, 12),
            "log10_abs": mp.nstr(mp.log10(magnitude), 8) if magnitude else None,
            "exponent": exponent,
            "re": mp.nstr(mp.re(value), 12),
            "im": mp.nstr(mp.im(value), 12),
            "seconds": round(elapsed, 3),
        }


def main() -> int:
    runs = [_at(d) for d in LEVELS]
    for r in runs:
        print(f"dps={r['dps']:>3}  |Lambda_Q| = {r['abs']:>22}  "
              f"(1e{r['exponent']})  {r['seconds']}s")

    ref = next(r for r in runs if r["dps"] == 60)
    low = next(r for r in runs if r["dps"] == 20)
    check = next(r for r in runs if r["dps"] == 80)
    gap = low["exponent"] - ref["exponent"]
    print(f"\norders of magnitude between dps=20 and dps=60: {gap}")
    print(f"dps=80 exponent (stability check on the reference): 1e{check['exponent']}")

    out = {
        "point": {"s": "0.8 + 85.7i", "form": list(FORM)},
        "runs": runs,
        "orders_of_magnitude_gap_20_vs_60": gap,
        "reference_stable_60_vs_80": check["exponent"] == ref["exponent"],
        "mpmath": __import__("mpmath").__version__,
        "epstein_module": str(pathlib.Path(
            __import__("zeta.epstein", fromlist=["x"]).__file__
        ).relative_to(ROOT)),
    }
    (pathlib.Path(__file__).parent / "results.json").write_text(
        json.dumps(out, indent=2) + "\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
