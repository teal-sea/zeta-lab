"""hunts/weil_gram/refine.py

Does the bottom eigenvalue of the Weil form stay put when the span is refined
_within the broad range_, with no concentrated element added?

`results_dps*.json` shows lambda_min collapsing when sigma = 0.45 joins the
basis, but the eigenvector there is the coordinate vector: that collapse is the
single-element degeneracy already measured in hunts/arch_cover, not a collective
effect. The remaining question is whether the broad span itself has a stable
gap, i.e. whether the 3.6e-7 measured on {0.10, 0.15, 0.20} survives extra
broad elements.

If it does, the form has a genuine gap on broad Gaussians and the collapse is
purely the concentrated direction. If it does not, then the gap is unstable
under refinement even where no element misses the zeros, which is stronger.

Run:  python hunts/weil_gram/refine.py [dps]
"""

from __future__ import annotations

import json
import os
import sys

import mpmath as mp

import gram

ORDER = [0.10, 0.15, 0.20, 0.05, 0.25, 0.30]


def main() -> dict:
    dps = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    cache: dict = {}
    out = []
    for k in range(2, len(ORDER) + 1):
        sig = ORDER[:k]
        with mp.workdps(dps):          # no global mpmath state (review, 2026-10-30)
            r = gram.run_base(f"prefix{k}", sig, cache, dps)
        out.append(
            {
                "k": k,
                "sigmas": sig,
                "lambda_min": r["lambda_min"],
                "lambda_min_from_zeros": r["lambda_min_from_zeros"],
                "eigvec": r["eigvec_min"],
                "worst_entry_rel_diff": r["worst_entry_rel_diff"],
                "n_uncovered": r["n_uncovered"],
            }
        )
        print(
            f"k={k} sigmas={sig} lambda_min={r['lambda_min']:+.6e} "
            f"(zeros {r['lambda_min_from_zeros']:+.6e}) "
            f"vec={['%+.3f' % x for x in r['eigvec_min']]}",
            flush=True,
        )
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, f"refine_dps{dps}.json"), "w") as f:
        json.dump(out, f, indent=1)
    return {"rows": out}


if __name__ == "__main__":
    main()
