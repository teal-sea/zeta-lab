"""The failure surface of ``epstein_completed`` in (height, precision).

`hunts/gate5_p6_c/probe.py` derives the mechanism and states the rule:

    epstein_completed forms  first + second/sqrt(d) + 1/(sqrt(d)(s-1)) - 1/s,
    whose last two terms are O(1/t), while the answer decays like
    |Gamma(s)| ~ exp(-pi t / 2), so roughly pi t / (2 ln 10) = 0.6822 t digits
    cancel.

`hunts/dps_cap` (#113) measured the cost of that at one point, `0.8 + 85.7i`
on the form `(2,1,3)`.  What neither produced is the surface: for a given
height `t`, what working precision does the routine actually need before its
answer has any correct digits, and what does it return below that.

This probe measures it against an oracle the routine shares no code with: at
`Re s = 5`, which is this module's default and the value every artifact uses, the
defining lattice sum converges absolutely, so it can be summed
directly to a stated truncation bound and used as ground truth at any height.
`epstein_completed` reaches the same value through the split Mellin transform
and the incomplete gamma, so agreement is a statement about the continuation
and disagreement localises the loss.

Nothing here is evidence about RH (`docs/08`).  It is a measurement of an
implementation.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

from mpmath import mp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from zeta.epstein import epstein_zeta  # noqa: E402

ART = Path(__file__).resolve().parent / "artifacts"

#: the rule stated inside hunts/gate5_p6_c/probe.py, re-derived here rather
#: than copied: |Gamma(sigma + it)| ~ exp(-pi t / 2), so the number of decimal
#: digits lost to cancellation is (pi t / 2) / ln 10.
DIGITS_PER_UNIT_HEIGHT = math.pi / (2 * math.log(10))


def representation_counts(form, qmax: int) -> dict[int, int]:
    """r_Q(q) = #{(m,k) != 0 : Q(m,k) = q} for q <= qmax, by enumeration.

    The enumeration bound comes from the form itself: Q(m,k) >= lam_min (m^2 + k^2)
    with lam_min the smaller eigenvalue of the matrix [[a, b/2], [b/2, c]], so no
    lattice point with Q <= qmax has |m| or |k| above sqrt(qmax / lam_min).
    """
    a, b, c = (int(v) for v in form)
    lam_min = (a + c - math.sqrt((a - c) ** 2 + b * b)) / 2
    R = int(math.sqrt(qmax / lam_min)) + 2
    counts: dict[int, int] = {}
    for m in range(-R, R + 1):
        for k in range(-R, R + 1):
            if m == 0 and k == 0:
                continue
            q = a * m * m + b * m * k + c * k * k
            if 0 < q <= qmax:
                counts[q] = counts.get(q, 0) + 1
    return counts


def direct_lattice(s, form, qmax: int):
    """sum_{(m,k) != 0} Q(m,k)^{-s} truncated at Q <= qmax, with a tail bound.

    Absolutely convergent for Re s > 1.  Grouping the lattice points by the value
    they represent turns the double sum into one sum over q, and the tail uses
    the exact counting fact that the number of lattice points with Q <= x is
    (2 pi / sqrt|D|) x + O(sqrt x): bounding the count above by K x with a
    measured K gives  |tail| <= K * sigma / (sigma - 1) * qmax^{1 - sigma}.
    """
    counts = representation_counts(form, qmax)
    total = mp.mpc(0)
    for q, r in counts.items():
        total += r * mp.mpf(q) ** (-s)
    n_points = sum(counts.values())
    K = n_points / qmax                       # measured, not assumed
    sig = float(mp.re(s))
    tail = K * sig / (sig - 1) * qmax ** (1 - sig)
    return total, float(tail)


def surface(form, heights, dpss, sigma=5, qmax=20000, work=40) -> list[dict]:
    rows = []
    for t in heights:
        with mp.workdps(work + int(DIGITS_PER_UNIT_HEIGHT * t) + 20):
            truth, tail = direct_lattice(mp.mpc(sigma, t), form, qmax)
            truth_abs = abs(truth)
        for dps in dpss:
            t0 = time.time()
            try:
                got = epstein_zeta(mp.mpc(sigma, t), form, dps=dps)
                err = float(abs(mp.mpc(got) - truth) / truth_abs)
                failed = None
            except Exception as exc:                      # pragma: no cover
                err, failed = float("inf"), f"{type(exc).__name__}: {exc}"
            rows.append({
                "form": list(form), "sigma": sigma, "t": t, "dps": dps,
                "relative_error": err,
                "correct_digits": (-math.log10(err) if 0 < err < 1 else 0.0),
                # zeta.epstein._GUARD is 10 and it is applied TWICE: epstein_zeta
                # opens workdps(dps + 10) and hands mp.dps to epstein_completed,
                # which opens another. The caller receives dps + 20. This field
                # said dps + 10 in every row of the first surface.
                "digits_available": dps + 20,
                "digits_predicted_lost": DIGITS_PER_UNIT_HEIGHT * t,
                "oracle_truncation_bound": tail,
                "oracle_abs": float(truth_abs),
                "seconds": round(time.time() - t0, 2),
                "exception": failed,
            })
            print(f"form={tuple(form)} t={t:6.1f} dps={dps:4d} "
                  f"rel_err={err:10.3e} correct_digits={rows[-1]['correct_digits']:6.1f} "
                  f"({rows[-1]['seconds']}s)", flush=True)
    return rows


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--forms", default="1,1,4;2,1,3;1,0,1")
    ap.add_argument("--heights", type=float, nargs="+",
                    default=[10, 20, 40, 60, 80, 100, 120, 160])
    ap.add_argument("--dps", type=int, nargs="+", default=[15, 20, 30, 50, 80])
    ap.add_argument("--qmax", type=int, default=20000)
    ap.add_argument("--sigma", type=float, default=5.0)
    ap.add_argument("--out", default="surface.json")
    args = ap.parse_args()

    forms = [tuple(int(v) for v in f.split(",")) for f in args.forms.split(";")]
    rows = []
    for f in forms:
        rows += surface(f, args.heights, args.dps, sigma=args.sigma, qmax=args.qmax)
    ART.mkdir(exist_ok=True)
    (ART / args.out).write_text(json.dumps(rows, indent=1), encoding="utf-8")
    print(f"-> {ART / args.out}")


if __name__ == "__main__":
    main()
