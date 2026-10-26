"""Circularity challenger's check for ccm_arithmetic (hunt #150).

Reads the builder's committed ``data/measure_*.json`` (it recomputes no matrix)
and tests what the sign of lambda_1 can carry:

* the basis e_0, e_k (k <= N) of NOTES section 2 is nested in N, so the band-N
  matrix is a principal submatrix of the band-N' matrix for N < N' and, by
  Cauchy interlacing, lambda_1(N') <= lambda_1(N): every band-N value is an
  upper bound on the infimum of the window form, never a lower bound;
* a Rayleigh quotient of any vector is likewise >= lambda_1, so a positive
  Rayleigh ball carries no positivity, while a negative one does carry a
  negative value of the form.

Writes nothing into the tree.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

from mpmath import mp

DATA = Path(__file__).resolve().parent.parent / "data"


def lambda1_by_window(kind: str) -> dict:
    d = json.loads((DATA / f"measure_{kind}.json").read_text())
    cells = d["cells"]
    cells = list(cells.values()) if isinstance(cells, dict) else cells
    by: dict = {}
    with mp.workdps(30):
        for c in cells:
            by.setdefault(str(c["c"]), {})[int(c["N"])] = mp.mpf(c["lambda_mid"][0])
    return by


def interlacing_report(kind: str) -> dict:
    by = lambda1_by_window(kind)
    out = {}
    for c, row in by.items():
        Ns = sorted(row)
        if len(Ns) < 2:
            continue
        vals = [row[N] for N in Ns]
        mono = all(b <= a for a, b in zip(vals, vals[1:]))
        pos = [v for v in vals if v > 0]
        drop = (mp.log10(pos[0]) - mp.log10(pos[-1])) if len(pos) == len(vals) else None
        out[c] = {"N": Ns, "nonincreasing": mono, "orders_dropped": drop, "all_positive": len(pos) == len(vals)}
    return out


def main() -> int:
    for kind in ("zeta", "dedekind", "dh"):
        rep = interlacing_report(kind)
        bad = [c for c, r in rep.items() if not r["nonincreasing"]]
        print(kind, "windows with >= 2 bands:", len(rep), "| violations of lambda_1 nonincreasing in N:", bad)
        for c, r in rep.items():
            if r["orders_dropped"] is not None:
                print("   c = %-6s N = %-14s lambda_1 drops by %s orders" % (c, r["N"], mp.nstr(r["orders_dropped"], 5)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
