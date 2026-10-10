"""Rival control: Weil zero-side sums for zeta vs Davenport-Heilbronn.

For positive-type h, both zero sides must be positive (null expected).
A sign difference would be a distinguishing signal worth chasing;
matching positivity closes this lane per the hunt kill conditions.
Grade: measured float.
"""
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from mpmath import mp


def dh_online_ordinates(t_max=150, dps=15):
    from zeta.epstein import Z_dh, _dh_mean_spacing
    mp.dps = dps
    step = float(_dh_mean_spacing(t_max)) / 20
    n = int(math.ceil(t_max / step)) + 1
    ts = [t_max * k / (n - 1) for k in range(n)]
    vals = [float(Z_dh(t, dps=dps)) for t in ts]
    ords = []
    for k in range(1, n):
        a, b = vals[k - 1], vals[k]
        if a != 0 and b != 0 and (a > 0) != (b > 0):
            lo, hi = ts[k - 1], ts[k]
            for _ in range(40):
                mid = (lo + hi) / 2
                m = float(Z_dh(mid, dps=dps))
                if (a > 0) == (m > 0):
                    lo = mid
                else:
                    hi = mid
            ords.append((lo + hi) / 2)
    return ords


def main():
    from zeta.zeros import first_n_zeros
    mp.dps = 25
    dh = dh_online_ordinates()
    # pinned off-line pair (zeta/epstein.py docstring, find_offline_zero)
    OFF = [(0.808517, 85.699348)]
    z = [float(g) for g in first_n_zeros(400, dps=30)]
    out = {"grade": "measured-float", "dh_online_count": len(dh), "rows": []}
    for a in [0.5, 1.0, 2.0]:
        h = lambda t, a=a: math.exp(-a * t * t)
        sz = sum(h(t) for t in z)
        # Weil zero side sums h(gamma) over zeros with gamma > 0, with multiplicity;
        # the off-line pair contributes 2*h(85.699) (zeros at 0.8085 and 0.1915 + 85.699i)
        sd = sum(h(t) for t in dh) + 2 * h(85.699348)
        out["rows"].append({"a": a, "zeta_zero_side": sz, "dh_zero_side": sd,
                            "both_positive": bool(sz > 0 and sd > 0)})
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "rival_weil.json")
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
