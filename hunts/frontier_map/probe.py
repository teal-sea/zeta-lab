"""Standing controls for the frontier map.

Four controls, per MISSION.md. Nothing in here decides anything; each
function returns its measurements and the caller (or RESULTS) records them.

1. cross-check: the numeric zeta curve against the paper's closed form
   (eq. 7.4), pointwise over the whole band — an independent analytic route
   that was not used to build the optimiser.
2. lesion: the same comparison against a deliberately mis-set closed form
   (the sqrt(2) in eq. 7.4 replaced by 1.5, a ~6 percent wound). The
   comparison must light up here, or an agreeing cross-check means nothing.
3. convergence response: the two lambda = 1 constants re-run up a
   basis/quadrature ladder, reporting settled digits — the laboratory's
   precision-response rule applied to the map's two headline points.
4. monotonicity: H(lambda) must not decrease on a refinement grid strictly
   between the map's samples; a violation would say interpolation on the
   published grid misleads.

Run from the repo root:  .venv/bin/python hunts/frontier_map/probe.py
"""

from __future__ import annotations

import math
import sys
from pathlib import Path
from typing import Any

_HERE = Path(__file__).resolve().parent
_REPO_ROOT = _HERE.parents[1]
for p in (str(_HERE), str(_REPO_ROOT / "hunts" / "wide_search")):
    if p not in sys.path:
        sys.path.insert(0, p)

from frontier import zeta_H_closed  # noqa: E402
from xiprime import optimise  # noqa: E402

#: the two headline constants the map pins at lambda = 1
ZETA_H_1 = 0.6725007036794117  # paper Theorem D
XIPRIME_H_1 = 0.86864150052976706411  # wide_search RESULTS-xiprime.md


def crosscheck_zeta_curve(lams: list[float] | None = None) -> dict[str, Any]:
    """Control 1: numeric optimum vs paper eq. (7.4), pointwise."""
    if lams is None:
        lams = [round(0.1 * k, 2) for k in range(1, 11)]
    devs = []
    for lam in lams:
        num = optimise(lam=lam, kernel="zeta")["H"]
        devs.append({"lambda": lam, "numeric": num, "closed": zeta_H_closed(lam),
                     "abs_dev": abs(num - zeta_H_closed(lam))})
    return {"points": devs, "max_abs_dev": max(d["abs_dev"] for d in devs)}


def _wounded_closed(lam: float) -> float:
    """Eq. (7.4) with its sqrt(2) mis-set to 1.5 — the planted fault."""
    theta = lam / 1.5
    t = math.tan(theta)
    c = 1.5 * t / (1.0 + theta * t)
    return 2.0 - 1.0 / c


def lesion(lams: list[float] | None = None) -> dict[str, Any]:
    """Control 3 (lesion): the comparison must see the planted mis-constant."""
    if lams is None:
        lams = [0.4, 0.7, 1.0]
    devs = [abs(optimise(lam=lam, kernel="zeta")["H"] - _wounded_closed(lam))
            for lam in lams]
    return {"lambdas": lams, "abs_devs": devs, "min_abs_dev": min(devs)}


def convergence_response() -> dict[str, Any]:
    """Control 4: the two headline constants up a basis/quadrature ladder."""
    ladder = [(8, 160), (11, 240), (14, 320), (17, 400)]
    out: dict[str, Any] = {}
    for kernel, ref in (("zeta", ZETA_H_1), ("xiprime", XIPRIME_H_1)):
        vals = [optimise(lam=1.0, kernel=kernel, n_basis=nb, n_r=nq, n_s=nq)["H"]
                for nb, nq in ladder]
        moves = [abs(b - a) for a, b in zip(vals, vals[1:])]
        out[kernel] = {
            "ladder": ladder,
            "values": vals,
            "moves": moves,
            "final_vs_pinned": abs(vals[-1] - ref),
        }
    return out


def monotonicity(kernel: str, n: int = 12) -> dict[str, Any]:
    """H(lambda) on an off-grid refinement; report any decrease."""
    lams = [0.35 + (1.0 - 0.35) * (k + 0.5) / n for k in range(n)]
    hs = [optimise(lam=lam, kernel=kernel)["H"] for lam in lams]
    drops = [(a, b) for a, b in zip(hs, hs[1:]) if b < a]
    return {"lambdas": lams, "H": hs, "decreases": drops}


def main() -> None:
    cc = crosscheck_zeta_curve()
    print(f"control 1  cross-check   max |numeric - closed| = {cc['max_abs_dev']:.3e}")
    le = lesion()
    print(f"control 3  lesion        min |numeric - wounded| = {le['min_abs_dev']:.3e}"
          f"  (must be far above control 1)")
    cr = convergence_response()
    for k, r in cr.items():
        print(f"control 4  convergence   {k}: moves {['%.1e' % m for m in r['moves']]}, "
              f"final vs pinned {r['final_vs_pinned']:.3e}")
    for k in ("zeta", "xiprime"):
        mo = monotonicity(k)
        print(f"control 2' monotonicity  {k}: decreases on refinement grid: "
              f"{len(mo['decreases'])}")


if __name__ == "__main__":
    main()
