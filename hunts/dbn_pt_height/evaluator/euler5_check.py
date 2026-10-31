"""The Euler 5 mollified bound F_{N-,N+} of Section 8.5, checked and timed.

Part ``paper``: the printed value F_{69098, 8x10^4} = 0.0263... (debruijn.tex
line 1738), at t = y = 0.2, with the paper's constants (alpha_n carries 1.03,
sigma = 0.599 + 0.1 log N-), under each of the three coefficient truncations
of ``effective.euler_mollified_F``; and the same interval with this module's own
constants (c_gamma and sigma derived from (gamma-bound) and (res-bound)).

Part ``row2``: one interval [N0, N0 + 10^4] at Table 1 row 2's parameters
(t0 = 0.186, y0 = 0.16733), the unit of cost of the row-2 asymptotic sweep.
This is one unit, timed; it is not a sweep and covers nothing beyond its
interval.

Usage:  .venv/bin/python hunts/dbn_pt_height/evaluator/euler5_check.py {paper|row2} OUT.json
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from flint import arb  # noqa: E402

import effective as ef  # noqa: E402


def ball(v: arb, digits: int = 12) -> dict[str, str]:
    return {"str": v.str(digits), "lower": repr(ef._lower_float(v)), "upper": repr(ef._upper_float(v))}


def run_paper() -> dict:
    out = {"interval": [69098, 80000], "t": "0.2", "y": "0.2", "printed": "0.0263...", "runs": []}
    with ef.workprec(ef.PREC):
        c_paper = arb("1.03")
        sig_paper = arb("0.599") + arb("0.1") * arb(69098).log()
    for primes, trunc in (((2, 3, 5), "worst"), ((2, 3, 5), "N_plus"), ((2, 3, 5), "N_minus"),
                          ((2, 3, 5), "none"), ((2, 3, 5, 7), "N_plus"), ((2, 3, 5, 7), "N_minus")):
        r = ef.euler_mollified_F(69098, 80000, "0.2", "0.2", primes=primes, c_gamma=c_paper,
                                 sigma=sig_paper, truncation=trunc)
        out["runs"].append({"constants": "paper", "primes": list(primes), "truncation": trunc, "F": ball(r["F"]),
                            "a1": ball(r["a1"]), "terms": r["terms"], "seconds": round(r["seconds"], 2)})
        print(json.dumps(out["runs"][-1]), flush=True)
    r = ef.euler_mollified_F(69098, 80000, "0.2", "0.2", primes=(2, 3, 5), truncation="worst")
    out["runs"].append({"constants": "derived", "primes": [2, 3, 5], "truncation": "worst", "F": ball(r["F"]), "a1": ball(r["a1"]),
                        "c_gamma": ball(r["c_gamma"]), "sigma": ball(r["sigma"], 15),
                        "terms": r["terms"], "seconds": round(r["seconds"], 2)})
    print(json.dumps(out["runs"][-1]), flush=True)
    return out


def run_row2() -> dict:
    N0 = 630783
    r = ef.euler_mollified_F(N0, N0 + 10000, "0.186", "0.16733", primes=(2, 3, 5), truncation="worst")
    return {"interval": [N0, N0 + 10000], "t": "0.186", "y": "0.16733", "F": ball(r["F"]), "a1": ball(r["a1"]),
            "c_gamma": ball(r["c_gamma"]), "sigma": ball(r["sigma"], 15), "terms": r["terms"],
            "seconds": round(r["seconds"], 2),
            "microseconds_per_term": round(1e6 * r["seconds"] / r["terms"], 2)}


def main() -> None:
    part, out = sys.argv[1], Path(sys.argv[2])
    try:
        load = Path("/proc/loadavg").read_text().split()[:3]
    except OSError:
        load = None
    res = run_paper() if part == "paper" else run_row2()
    res["loadavg_at_start"] = load
    out.write_text(json.dumps(res, indent=1) + "\n")
    print("wrote", out, flush=True)


if __name__ == "__main__":
    main()
