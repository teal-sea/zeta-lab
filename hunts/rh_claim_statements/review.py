"""Numbers for the review section of RESULTS.md, computed rather than typed.

    .venv/bin/python -m hunts.rh_claim_statements.review            # writes review.json (about 90 s, one core)

Two attackers reviewed this hunt on 2026-11-20. This script reproduces the
numbers their findings turn on, and the numbers RESULTS.md sections 4, 5, 8
and 9 quote:

1. `c17_floor`: the Euler-product floor zeta(2 sigma)/zeta(sigma) at sigma = 26/25,
   which decides which integer constants make C17 (`dhl_inv`) true.
   `c28_series`: the value of C28's series by a second route, which labels the
   truth of the weakened C28 constants.
2. `c15_edge`: the hunt's own C15 test (`gamma_decay`, full parameters) at strip
   edges between 11/2 and 6, and Arb values of the ratio far above the tested
   height at the edges it accepts.
3. `resolution`: weakened mutants of the sharp claims, run through the hunt's
   own tests at full parameters (C17 at fast parameters: its verdict turns on the
   floor, not on the search range). Each row carries the truth of the weakened
   statement, from the stated derivation, and what the test returns.
4. `wide_ball_radii`: section 8, the radius of the real part of zeta on four
   boxes, direct Arb evaluation against the Taylor model.
5. `precision_deltas`: section 9, how far the recorded margins move when every
   working precision is doubled (results.json against results_prec2.json).

Nothing here reads the archive.
"""
from __future__ import annotations

import json
import time
from pathlib import Path

from flint import acb, arb, ctx

from . import checks_analytic as ca
from . import runner

HERE = Path(__file__).resolve().parent


def _run(claims, cid, over, level="full"):
    c = claims[cid]
    p = dict(runner.base_params(c, level) or c["test"]["params"])
    p.update(over)
    t0 = time.perf_counter()
    r = runner.run_check(c["test"]["fn"], p)
    return dict(holds=r["holds"], tail_covered=r.get("tail_covered"),
                rejected=r["holds"] is False, witness=r.get("witness"),
                sup_ratio=r.get("sup_ratio"), seconds=round(time.perf_counter() - t0, 2))


def c17_floor():
    with ctx.workprec(128):
        s = arb(26) / 25
        fl = (2 * s).zeta() / s.zeta()
        out = dict(floor=[float(fl.lower()), float(fl.upper())],
                   inverse=[float((1 / fl).lower()), float((1 / fl).upper())])
        for K in (16, 17, 26):
            v = K * fl
            out[f"K={K}"] = dict(K_times_floor=[float(v.lower()), float(v.upper())],
                                 statement_true=bool(v >= 1), statement_false=bool(v < 1))
    out["reading"] = ("the infimum of |L(26/25 + it, psi)| over all psi and t is the floor (Euler product; for the "
                      "principal character it is approached by Kronecker's theorem and not attained), so K * floor >= 1 "
                      "makes the statement true and K * floor < 1 makes it false")
    return out


def _gamma_ratio_lower(sigma, t, K=3, E=5):
    """A rigorous lower bound for |Gamma(w)| e^(pi |t|/2) / (K |w+1|^E) at w = sigma + it."""
    with ctx.workprec(128):
        w = acb(arb(sigma), arb(t))
        v = (w.lgamma().real + arb.pi() * arb(t) / 2 - arb(K).log() - E * arb((w + 1).abs_upper()).log()).exp()
        return float(v.lower())


def c15_edge(claims):
    rows = {}
    for edge in ("6", "56/10", "555/100", "552/100", "551/100"):
        rows[edge] = _run(claims, "C15", dict(sigma_hi=edge))
    far = {f"sigma={s}, t={t:g}": _gamma_ratio_lower(s, t) for s, t in
           (("5.52", 1e4), ("5.52", 1e5), ("5.51", 1e12), ("5.5", 1e12))}
    return dict(test_at_T_200=rows, ratio_lower_far_above_T=far,
                reading="on Re w = sigma_hi > 11/2 the ratio grows like |Im w|^(sigma_hi - 11/2); the test sees an "
                        "edge error only once that growth shows below |Im w| = 200")


def c28_series():
    """sum over primes of log p / p^2 = -sum_k mu(k) zeta'(2k)/zeta(2k) (from P(s) = sum_k mu(k)/k log zeta(ks)).

    Terms k <= 60 in Arb; for k > 60, |zeta'/zeta(2k)| <= sum_{n>=2} log n n^-2k <= 2^(1-2k), so the
    tail is below 2^-120 and is added as a radius."""
    from flint import acb_series
    mu = {1: 1}
    for k in range(2, 61):
        n, f, sq, m = k, 2, False, 1
        while f * f <= n:
            if n % f == 0:
                n //= f; m = -m
                if n % f == 0:
                    sq = True; break
            else:
                f += 1
        if not sq and n > 1:
            m = -m
        mu[k] = 0 if sq else m
    with ctx.workprec(128):
        S = arb(0)
        for k in range(1, 61):
            if mu[k]:
                z = acb_series([acb(2 * k), 1], prec=2).zeta()
                S -= mu[k] * (z[1] / z[0]).real
        S = S + arb(0, 2.0 ** -119)
        return dict(value=[float(S.lower()), float(S.upper())],
                    route="Moebius inversion of log zeta, Arb, k <= 60 plus a tail radius 2^-119")


# (claim, override, is the weakened statement true?, why)
RESOLUTION = [
    ("C21", {"K": "12550588/10000000"}, True, "max of pi(m) log m / m below 2^17 is 1.25505871 (m = 113)"),
    ("C21", {"K": "125505871/100000000"}, False, "below the maximum at m = 113"),
    ("C01", {"K": "1460355/1000000"}, True, "sup |zeta| on the circle is |zeta(1/2)| = 1.4603545"),
    ("C01", {"K": "1460354/1000000"}, False, "below |zeta(1/2)|"),
    ("C28", {"K": "4930928/10000000"}, True, "above the enclosure [0.4930910, 0.4930927] of the series"),
    ("C28", {"K": "4930920/10000000"}, True, "the series is 0.4930911094 (c28_series below; the reviewer found the same)"),
    ("C28", {"K": "4930911/10000000"}, False, "the series is 0.4930911094 (c28_series), above 0.4930911"),
    ("C28", {"K": "4930909/10000000"}, False, "below the partial sum over primes <= 10^7"),
    ("C62", {"c": "3678794/10000000"}, True, "the largest admissible coefficient is 1/e = 0.36787944"),
    ("C62", {"c": "3678795/10000000"}, False, "above 1/e"),
    ("C07", {"c": "1306/1000"}, True, "the infimum of |zeta_1(3/2 + it)| is 1.30619 at t = 0"),
    ("C07", {"c": "13063/10000"}, False, "above 1.30619"),
    ("C16", {"K": "4134/10000"}, False, "the binding case is q = 3 with sharp constant 0.41350"),
    ("C70", {"K": "1999999/1000000"}, False, "the ratio tends to 1 from below along x = 1/8, p = 2"),
    ("C74", {"const": "1749/1000"}, False, "equality at (l, g, h, j) = (3, 0, 6, 1) with 7/4"),
    ("C05", {"c": "4999/10000"}, False, "the ratio tends to 1/2 as s -> 0+, so any c < 1/2 is false"),
    ("C05", {"c": "49999/100000"}, False, "as above"),
    ("C65", {"K": "3999/1000"}, False, "equality at v = lam = 1 needs K >= 4"),
    ("C65", {"e_rhs": "3901/10000"}, False, "the exact reduction needs e_lam <= 1 - e_rhs, and 0.61 > 0.6099"),
    ("C17", {"K": "17"}, True, "17 * zeta(52/25)/zeta(26/25) = 1.047 >= 1"),
    ("C17", {"K": "16"}, False, "16 * zeta(52/25)/zeta(26/25) = 0.986 < 1, and the floor is approached (Kronecker)"),
]


def resolution(claims):
    out = []
    for cid, over, truth, why in RESOLUTION:
        r = _run(claims, cid, over, level="fast" if cid == "C17" else "full")
        if r["holds"] is False:
            seen = "rejected with a witness"
        elif r["holds"] is None:
            seen = "undecided"
        elif claims[cid]["grade_if_it_holds"] == "complete_cover" and r["tail_covered"] is not True:
            seen = "holds on the range only (would be graded measured, not complete cover)"
        else:
            seen = "holds"
        out.append(dict(claim=cid, override=over, statement_true=truth, why=why, test_returns=seen,
                        correct=(truth and r["holds"] is True) or (not truth and r["holds"] is False),
                        **{k: r[k] for k in ("holds", "tail_covered", "seconds")}))
    return out


def wide_ball_radii():
    rows = {}
    with ctx.workprec(64):
        for (x, y, r) in [(0.5, 3.0, 0.04), (0.2, 0.1, 0.04), (0.6, 14.1, 0.1), (1.05, 0.35, 0.02)]:
            S = acb(arb(x, r), arb(y, r))
            tb = ca._zeta_tb(S)
            rows[f"{x}+{y}i, half-width {r}"] = dict(direct=float(S.zeta().real.rad()),
                                                    taylor_model=float(tb[0].real.rad()))
    return rows


def precision_deltas():
    one = {r["id"]: r for r in json.loads((HERE / "results.json").read_text(encoding="utf-8"))["claims"]}
    two = {r["id"]: r for r in json.loads((HERE / "results_prec2.json").read_text(encoding="utf-8"))["claims"]}
    sup_hi, sup_lo, margin = {}, {}, {}
    for cid, b in two.items():
        a = one[cid]
        if isinstance(a.get("sup_ratio"), list) and isinstance(b.get("sup_ratio"), list):
            sup_hi[cid] = abs(a["sup_ratio"][1] - b["sup_ratio"][1])
            sup_lo[cid] = abs(a["sup_ratio"][0] - b["sup_ratio"][0])
        else:
            key = "margin_on_range" if "margin_on_range" in a else "margin"
            if isinstance(a.get(key), (int, float)) and isinstance(b.get(key), (int, float)):
                margin[cid] = abs(a[key] - b[key])
    top = lambda d: max(d.items(), key=lambda kv: kv[1]) if d else None
    return dict(largest_upper_end_move=top(sup_hi), largest_lower_end_move=top(sup_lo),
                largest_other_margin_move=top(margin),
                other_margin_moves={k: v for k, v in sorted(margin.items(), key=lambda kv: -kv[1]) if v > 0})


def main():
    claims = {c["id"]: c for c in runner.load_claims()["claims"]}
    t0 = time.perf_counter()
    out = dict(c17_floor=c17_floor(), c28_series=c28_series(), c15_edge=c15_edge(claims), resolution=resolution(claims),
               wide_ball_radii=wide_ball_radii(), precision_deltas=precision_deltas())
    out["seconds"] = round(time.perf_counter() - t0, 1)
    (HERE / "review.json").write_text(json.dumps(out, ensure_ascii=False, indent=1, default=str) + "\n", encoding="utf-8")
    for row in out["resolution"]:
        print(row["claim"], row["override"], "true" if row["statement_true"] else "false", "->", row["test_returns"])
    print(json.dumps(out["c17_floor"]), json.dumps(out["wide_ball_radii"]), json.dumps(out["precision_deltas"]), sep="\n")
    print("wrote review.json in", out["seconds"], "s")


if __name__ == "__main__":
    main()
