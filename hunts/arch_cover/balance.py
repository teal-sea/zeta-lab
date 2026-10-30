"""hunts/arch_cover/balance.py

The cancellation depth of three pieces, on two families that probe opposite
regimes:

  centred Gaussian    h = e^{-a r^2}: g is a bump at 0, so the prime side sees
                      only n = 1 (nothing). W is carried by pole + arch.
  prime-tuned comb    h = |f^|^2 with f a comb at spacing log 2: g sits on
                      log 2, log 4, ..., so the prime side is O(1). h is broad
                      in r, so ~10^2-10^3 zeros contribute.

Reported: the pieces, W, and the cancellation depth

    depth = log10( max(|pole|, |arch|, |prime|) / |W| ),

the number of digits by which the three O(1) pieces cancel to give W. A
family with depth ~0 is a genuine inequality between comparable quantities; a
family with depth growing without bound is an identity in disguise, and no
estimate can be extracted from it.

Not a result about RH.
"""

from __future__ import annotations

import json
import os

import mpmath as mp

from zeta.weil import autocorrelation_pair, explicit_formula_sides, gaussian_pair

DPS = 30


def _row(tag: str, h, g) -> dict:
    d = explicit_formula_sides(h, g, dps=DPS)
    pole = mp.mpf(d["pole_term"])
    arch = mp.mpf(d["arch_term"])
    prime = mp.mpf(d["prime_term"])
    W = mp.mpf(d["arithmetic_side"])
    big = max(abs(pole), abs(arch), abs(prime))
    depth = mp.log10(big / abs(W)) if W != 0 else mp.inf
    return {
        "tag": tag,
        "pole": float(pole),
        "arch": float(arch),
        "prime": float(prime),
        "W": float(W),
        "depth_digits": float(depth),
        "n_zeros": d["n_zeros_used"],
        "n_max": d["n_max"],
        "agreement_log10": float(mp.log10(mp.mpf(d["agreement"]))) if d["agreement"] > 0 else -999,
    }


def main() -> dict:
    rows = []
    for a in (0.005, 0.05, 0.2):
        h, g = gaussian_pair(a)
        rows.append(_row(f"gaussian a={a}", h, g))
    for coeffs, tag in (([1, -1], "comb2"), ([1, 1, 1], "comb3")):
        for sg in (0.01, 0.02, 0.05, 0.1):
            h, g = autocorrelation_pair(coeffs, spacing=mp.log(2), sigma=sg)
            rows.append(_row(f"{tag} s=log2 sigma={sg}", h, g))
    for r in rows:
        print(
            f"{r['tag']:26s} pole={r['pole']:+.3e} arch={r['arch']:+.3e} "
            f"prime={r['prime']:+.3e} W={r['W']:+.3e} depth={r['depth_digits']:5.2f}d "
            f"nz={r['n_zeros']:5d} agree=1e{r['agreement_log10']:.0f}",
            flush=True,
        )
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "balance.json"), "w") as f:
        json.dump(rows, f, indent=1)
    return {"rows": rows}


if __name__ == "__main__":
    main()
