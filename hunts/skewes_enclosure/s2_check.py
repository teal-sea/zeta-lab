"""Post-hoc check (2026-10-27, review of PR #360, NOT pre-registered): the
second-order sum S2 and Revers's printed S* for the Saouter-Demichel region.

Grade: measured. S2 is an Arb ball over the first N zeros only; the tail beyond
gamma_N is a main-term estimate, not a rigorous bound. The other inputs are
printed decimals from [Rev25] (arXiv:2501.04488 v2, subsections 6.2 and 6.3),
and the ball sums S come from the committed shards.

With S = S1 + S2 split as in Theorem 3.1,

    S1 = sum e^{i gamma omega} / rho              e^{-gamma^2 / 2 alpha},
    S2 = sum e^{i gamma omega} / (omega rho^2)    e^{-gamma^2 / 2 alpha},

over 0 < |gamma| <= T (2 Re of the sum over gamma > 0), the comparisons are:

* Revers's 6.3 S* against Saouter-Demichel's printed first-order value S_D
  (which Revers quotes) minus S2 at omega = 727.951335792;
* the pre-registered rule gap S - S* against 2 S2;
* our S1 = S - S2 against S_D, an end-to-end check of the 2.2e7-zero list;
* target A: S_A - S2_A against Chao-Plymen's printed -1.006569 (first order);
* the alternative omega = 727.9513358 (727.951335792 to seven decimals), by
  interpolating the pre-registered omega grid.

    .venv/bin/python hunts/skewes_enclosure/s2_check.py compute --n 20000 \
        --out hunts/skewes_enclosure/s2_first20000.json      # about 5 min, 1 core
    .venv/bin/python hunts/skewes_enclosure/s2_check.py compare \
        --out hunts/skewes_enclosure/s2_comparison.json      # seconds
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import flint
from flint import acb, arb

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import skewes_terms as st  # noqa: E402
import zero_layer as zl  # noqa: E402

#: label -> (omega, alpha). B points use alpha = 6e12, A uses 1.34e11.
POINTS = {
    "B 727.951335792": ("727.951335792", "6e12"),
    "B 727.9513358": ("727.9513358", "6e12"),
    "B 727.95134": ("727.95134", "6e12"),
    "B 727.951335426": ("727.951335426", "6e12"),
    "A 727.952018": ("727.952018", "1.34e11"),
}
CHECKPOINTS = (1000, 5000, 20000)

#: [Rev25] 6.3 quotes "the Saouter-Demichel machine value with size
#: -1.002906086981405"; 6.2 quotes Chao-Plymen's "-1.006569". Both are
#: first-order (Lehman) sums, S1 only.
SD_PRINTED_S1 = "-1.002906086981405"
CP_PRINTED_S1 = "-1.006569"
B_OMEGA = "727.951335792"
ALT_OMEGA = "727.9513358"


def split_sums(gammas, omega, alpha, checkpoints=()) -> dict:
    """S1 and S2 as balls over ``gammas``, also at each count in ``checkpoints``.

    S1 + S2 is ``skewes_terms.lehman_sum`` (pinned by a test)."""
    old = flint.ctx.prec
    flint.ctx.prec = st.PREC
    try:
        w, al2 = arb(omega), 2 * arb(alpha)
        half = arb(1) / 2
        s1, s2 = acb(0), acb(0)
        out = {}
        for i, g in enumerate(gammas, start=1):
            inv = 1 / acb(half, g)
            e = acb(0, g * w).exp() * (-(g * g) / al2).exp()
            s1 += e * inv
            s2 += e * inv * inv / w
            if i in checkpoints:
                out[i] = (2 * s1.real, 2 * s2.real)
        out[len(gammas)] = (2 * s1.real, 2 * s2.real)
        return out
    finally:
        flint.ctx.prec = old


def tail_estimate(gamma_last: float, omega: float) -> float:
    """Main-term estimate of sum_{gamma > Gamma} 2 / (omega gamma^2), which
    bounds |S2 tail| if N(t) followed its main term (1/2 pi) t log(t / 2 pi).
    An estimate, not a rigorous bound: S(t) and the lower-order terms of N(t)
    are ignored."""
    import math

    G = gamma_last
    return (2 / omega) * (math.log(G / (2 * math.pi)) + 1) / (2 * math.pi * G)


def compute(n: int) -> dict:
    t0 = time.perf_counter()
    gammas, _ = zl.arb_zeros(1, n, 5000, 64)
    t_zeros = time.perf_counter() - t0
    cps = tuple(c for c in CHECKPOINTS if c < n)
    res = {"n": n, "isolation_prec_bits": 64, "seconds_zeros": t_zeros,
           "gamma_at_checkpoint": {str(c): gammas[c - 1].str(20) for c in cps + (n,)},
           "points": {}}
    for label, (w, al) in POINTS.items():
        sums = split_sums(gammas, w, al, cps)
        res["points"][label] = {
            "omega": w, "alpha": al,
            "by_count": {str(c): {"S1": s1.str(25), "S2": s2.str(25)}
                         for c, (s1, s2) in sorted(sums.items())},
        }
    for label, d in res["points"].items():
        d["tail_estimate_after_n"] = tail_estimate(
            float(gammas[-1].mid()), float(arb(d["omega"]).mid()))
    return res


def _shard_sum(shard_dir: Path, key, count: int) -> arb:
    total = arb(0)
    for k in range(1, count + 1):
        d = json.loads((shard_dir / f"shard_{k:03d}.json").read_text())
        total += arb(key(d))
    return total


def grid_from_shards(shard_dir: Path) -> dict:
    """omega string -> ball sum over all 220 B2 shards."""
    omegas = json.loads((HERE / "omega_grid.json").read_text())["omegas"]
    totals = {w: arb(0) for w in omegas}
    for k in range(1, 221):
        d = json.loads((shard_dir / f"shard_{k:03d}.json").read_text())
        for w in omegas:
            totals[w] += arb(d["grid_sums"][w])
    return totals


def interpolate(grid: dict, center: str, step: str, at: str, npts: int = 8) -> float:
    """Degree npts-1 polynomial through the npts on-grid points nearest ``at``
    (ball midpoints), evaluated at ``at``. Descriptive, float grade."""
    from mpmath import lu_solve, matrix, mp, mpf

    with mp.workdps(40):
        c, h = mpf(center), mpf(step)
        pts = []
        for w, s in grid.items():
            x = (mpf(w) - c) / h
            if abs(x - int(mp.nint(x))) < mpf("1e-6"):
                pts.append((int(mp.nint(x)), mpf(s.mid().str(30, radius=False))))
        x0 = (mpf(at) - c) / h
        near = sorted(pts, key=lambda p: abs(p[0] - x0))[:npts]
        A = matrix(npts, npts)
        b = matrix(npts, 1)
        for i, (x, s) in enumerate(near):
            for j in range(npts):
                A[i, j] = mpf(x) ** j
            b[i] = s
        coef = lu_solve(A, b)
        return float(sum(coef[j] * x0 ** j for j in range(npts)))


def compare(s2_file: Path, shards_a: Path, shards_b2: Path) -> dict:
    flint.ctx.prec = st.PREC
    s2d = json.loads(s2_file.read_text())
    n = str(s2d["n"])

    def S1S2(label):
        d = s2d["points"][label]["by_count"][n]
        return arb(d["S1"]), arb(d["S2"])

    grid = grid_from_shards(shards_b2)
    S_B = grid[B_OMEGA]
    S_A = _shard_sum(shards_a, lambda d: d["partial_sums"]["chao_plymen"], 20)
    s_star_B = arb(st.REVERS_S_STAR["saouter_demichel"])
    s_star_A = arb(st.REVERS_S_STAR["chao_plymen"])
    S_D, CP = arb(SD_PRINTED_S1), arb(CP_PRINTED_S1)
    _, S2_B = S1S2("B " + B_OMEGA)
    _, S2_A = S1S2("A 727.952018")
    alt = interpolate(grid, B_OMEGA, "5e-8", ALT_OMEGA)
    sign_slip = S_D - S2_B - s_star_B

    def s(x):
        # more=True keeps the midpoint digits; the printed ball still encloses x
        return x.str(12, more=True)

    return {
        "grade": "measured; post-hoc (2026-10-27), not pre-registered",
        "n_zeros_for_S2": s2d["n"],
        "S2_tail_estimate_B": s2d["points"]["B " + B_OMEGA]["tail_estimate_after_n"],
        "S2_B_at_727.951335792": s(S2_B),
        "S2_A_at_727.952018": s(S2_A),
        "S_B_at_727.951335792": S_B.str(15),
        "S_A": S_A.str(15),
        "SD_minus_S2_minus_Sstar (sign-slip identity)": s(sign_slip),
        "SD_plus_S2_minus_Sstar (Theorem 3.1's sign)": s(S_D + S2_B - s_star_B),
        "rule_gap_S_minus_Sstar": s(S_B - s_star_B),
        "two_S2": s(2 * S2_B),
        "gap_minus_two_S2": s(S_B - s_star_B - 2 * S2_B),
        "our_S1_minus_SD (end-to-end check of the 2.2e7 zeros)": s(S_B - S2_B - S_D),
        "A_our_S1_minus_CP (CP printed to 6 decimals)": s(S_A - S2_A - CP),
        "A_S_minus_Sstar (plus S2, as Theorem 3.1)": s(S_A - s_star_A),
        "A_S_minus_2S2_minus_Sstar (minus S2 convention)": s(S_A - 2 * S2_A - s_star_A),
        "alt_omega_727.9513358_interpolated_S_minus_Sstar": alt - float(s_star_B.mid()),
        "alt_over_sign_slip_residual": abs(alt - float(s_star_B.mid()))
        / abs(float(sign_slip.mid())),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("compute")
    c.add_argument("--n", type=int, default=20000)
    c.add_argument("--out", type=Path, required=True)
    m = sub.add_parser("compare")
    m.add_argument("--s2", type=Path, default=HERE / "s2_first20000.json")
    m.add_argument("--shards-a", type=Path, default=HERE / "shards")
    m.add_argument("--shards-b2", type=Path, default=HERE / "shards_b2")
    m.add_argument("--out", type=Path)
    a = ap.parse_args()
    if a.cmd == "compute":
        res = compute(a.n)
    else:
        res = compare(a.s2, a.shards_a, a.shards_b2)
    text = json.dumps(res, indent=1)
    if a.out:
        a.out.write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
