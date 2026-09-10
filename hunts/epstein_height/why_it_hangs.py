"""Answering the question `hunts/dps_cap/reach_check.py` left open.

That file asks whether the precision cap costs a wrong answer or a refusal, and
records that neither run returned: the uncapped comparison was stopped after 30
minutes and the capped path after 25.  It offers a hypothesis and says plainly
that it did not test it:

> A plausible cause is `_edge_variation` subdividing without converging when
> the contour samples carry no correct digits, but that is a hypothesis this
> run did not test.

It is testable without running the thing that does not return.

`_arg_variation` accepts a segment when the endpoint arguments differ by less
than `pi/3`, and otherwise bisects, to a depth limit of 45 at which it returns
the principal value anyway rather than raising.  So the branching factor is
`2 (1 - p)` where `p` is the probability that a segment is accepted.  When the
evaluator carries correct digits, `p` is near 1 at any sensible step and the
recursion stops at once.  When it carries none, the phase is noise, the
endpoint difference is uniform on `(-pi, pi]`, and `p` falls to `1/3` by
symmetry, giving a branching factor of `4/3` and a subtree of about
`(4/3)^45 = 4e5` evaluations per segment.

So `p` is the whole question, and `p` costs two samples per segment to measure.
This measures it at both precisions with a few dozen evaluations, and the cost
of the recursion follows from it arithmetically rather than by waiting.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

from mpmath import mp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from zeta.epstein import _principal, epstein_completed  # noqa: E402

ART = Path(__file__).resolve().parent / "artifacts"
FORM = (2, 1, 3)
MAX_DEPTH = 45          # zeta.epstein._arg_variation's own limit


def sample_acceptance(t0: float, dps: int, n_segments: int, step: float) -> dict:
    """Fraction of segments of length `step` at height ~t0 that the rule accepts."""
    accepted, diffs = 0, []
    with mp.workdps(dps + 10):
        for k in range(n_segments):
            # segments march up the sigma = -1 edge, the edge count_zeros_box uses
            y0 = mp.mpf(t0) + mp.mpf(k) * mp.mpf(step)
            y1 = y0 + mp.mpf(step)
            a = epstein_completed(mp.mpc(-1, y0), FORM, dps=dps)
            b = epstein_completed(mp.mpc(-1, y1), FORM, dps=dps)
            d = _principal(mp.arg(b) - mp.arg(a))
            diffs.append(float(d))
            if abs(d) < mp.pi / 3:
                accepted += 1
    p = accepted / n_segments
    branch = 2 * (1 - p)
    return {
        "t0": t0, "dps": dps, "n_segments": n_segments, "step": step,
        "accepted": accepted, "p_accept": p,
        "branching_factor": branch,
        "expected_evaluations_per_segment":
            (branch ** MAX_DEPTH if branch > 1 else float(1 / (1 - branch / 2)))
            if branch != 2 else float("inf"),
        "endpoint_differences": diffs,
    }


def main() -> None:
    # the step count_zeros_box would choose at this height
    tmax = 120.0
    step = float(1 / (2 * math.log(5 * tmax / (2 * math.pi))))
    rows = []
    for dps in (15, 100):
        r = sample_acceptance(tmax, dps, n_segments=24, step=step)
        rows.append(r)
        print(f"dps={dps:>4d}  step={step:.4f}  accepted {r['accepted']}/24  "
              f"p={r['p_accept']:.3f}  branching {r['branching_factor']:.3f}  "
              f"expected evaluations per segment "
              f"{r['expected_evaluations_per_segment']:.3g}")
    p_noise = 1 / 3
    print()
    print(f"a phase that is uniform noise accepts with probability {p_noise:.3f}, "
          f"branching {2*(1-p_noise):.3f}, subtree {(2*(1-p_noise))**MAX_DEPTH:.3g}")
    print("at two seconds per evaluation that is "
          f"{(2*(1-p_noise))**MAX_DEPTH * 2 / 86400:.0f} days for ONE segment")
    ART.mkdir(exist_ok=True)
    (ART / "why_it_hangs.json").write_text(json.dumps(rows, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
