"""Replay the whole chain of RESULTS.md from exact inputs and write the JSON records.

    PYTHONPATH=. .venv/bin/python -m hunts.qrh_prime_powers.verify

Parts:
  chain    Theorem 1 (k = 9, theta = 7/8): analytic cover of n >= 10, the tail
           n >= e^100, and Pratt witnesses for n <= 9.
  noRH     the same chain with no verified height (every zero gets theta).
  weaker   Theorem 1' (k = 13, theta = 11/12), with and without the height,
           and the failure of k = 12.
  control  theta = 15/16 at k = 17 (full chain) and the failures of the method
           at k = 8 (theta = 7/8) and k = 16 (theta = 15/16).
  short    Theorem 2: a prime in (x, x + (1/2) x^(7/8) log x] for x >= e^8.
  psi      Theorem 3: |psi(x) - x| < x^(7/8) log^2 x/(128 pi) for x >= e^10.
  height   measured sensitivity of the k = 9 peak to the verified height H0
           (pointwise scan only, not part of any proof).
"""

from __future__ import annotations

import json
import sys
import time
from contextlib import contextmanager
from fractions import Fraction
from pathlib import Path

from flint import arb

from hunts.qrh_prime_powers import bound as B
from hunts.qrh_prime_powers import pratt

HERE = Path(__file__).resolve().parent
SEVEN_EIGHTHS = Fraction(7, 8)
ELEVEN_TWELFTHS = Fraction(11, 12)
PSI_START = 10
FIFTEEN_SIXTEENTHS = Fraction(15, 16)


def s(x: arb, digits: int = 12) -> str:
    return x.str(digits, radius=False)


def log_floor(n: int, den: int = 2 ** 20) -> Fraction:
    """A dyadic rational L with L <= log n, checked in Arb."""
    approx = (arb(n).log() * den).lower().floor()
    L = Fraction(int(approx.unique_fmpz()), den)
    assert B.a_(L) < arb(n).log()
    return L


def cover(family, theta: Fraction, L_start: Fraction, L_end: Fraction,
          step0=Fraction(1, 16), max_step=Fraction(1, 16)) -> dict:
    """Close [L_start, L_end] by intervals on which margin > 0 is certain."""
    rows, La, step, attempts = [], L_start, step0, 0
    while La < L_end:
        Lb = min(La + step, L_end)
        attempts += 1
        try:
            r = B.interval_bound(family, theta, B.a_(La), B.a_(Lb))
            ok = bool(r["margin"] > 0)
        except ArithmeticError:
            ok = False
        if ok:
            rows.append((La, Lb, r))
            La = Lb
            if r["margin"] > B.a_(Fraction(1, 2)):
                step = min(step * 2, max_step)
        else:
            step /= 2
            if step < Fraction(1, 2 ** 24):
                return {"closed": False, "stuck_at": float(La), "intervals": len(rows)}
    worst = min(rows, key=lambda t: float(t[2]["margin"].lower().mid()))
    return {
        "closed": True,
        "L_start": str(L_start), "L_end": str(L_end),
        "intervals": len(rows), "attempts": attempts,
        "worst_interval": [str(worst[0]), str(worst[1])],
        "worst_margin_lower": s(worst[2]["margin"].lower()),
        "worst_E_upper": s(worst[2]["E"].upper()),
    }


def psi_cover(theta: Fraction, L_start: Fraction, L_end: Fraction,
              step0=Fraction(1, 64), max_step=Fraction(1, 16)) -> dict:
    """Close |psi(x) - x| < x^theta (1-theta)^2 log^2 x/(2 pi) on log x in [L_start, L_end]."""
    rows, La, step, attempts = [], L_start, step0, 0
    while La < L_end:
        Lb = min(La + step, L_end)
        attempts += 1
        try:
            r = B.psi_interval(theta, B.a_(La), B.a_(Lb))
            ok = bool(r["margin"] > 0)
        except ArithmeticError:
            ok = False
        if ok:
            rows.append((La, Lb, r))
            La = Lb
            step = min(step * 2, max_step)
        else:
            step /= 2
            if step < Fraction(1, 2 ** 24):
                return {"closed": False, "stuck_at": float(La), "intervals": len(rows)}
    rel = [(t[2]["margin"] / t[2]["target"]).lower() for t in rows]
    i = min(range(len(rows)), key=lambda j: float(rel[j].mid()))
    return {"closed": True, "L_start": str(L_start), "L_end": str(L_end),
            "intervals": len(rows), "attempts": attempts,
            "worst_relative_margin": s(rel[i]),
            "worst_interval": [str(rows[i][0]), str(rows[i][1])]}


def point(family, theta: Fraction, L: arb) -> dict:
    r = B.interval_bound(family, theta, L, L)
    return {"E_upper": s(r["E"].upper()), "low_upper": s(r["low"].upper()),
            "high_upper": s(r["high"].upper()),
            "share_upper": s(r["prime_power_share"].upper()),
            "margin": s(r["margin"]), "margin_positive": bool(r["margin"] > 0),
            "margin_negative": bool(r["margin"] < 0)}


def first_failure(family, theta: Fraction, L_lo: float, L_hi: float, step: float = 0.05) -> dict:
    """First sampled log n where the bound certainly exceeds the margin, then bisect."""
    L = L_lo
    prev = L
    while L <= L_hi:
        if B.interval_bound(family, theta, arb(L), arb(L))["margin"] < 0:
            lo, hi = prev, L
            for _ in range(40):
                mid = (lo + hi) / 2
                if B.interval_bound(family, theta, arb(mid), arb(mid))["margin"] < 0:
                    hi = mid
                else:
                    lo = mid
            return {"found": True, "logn_first_fail_sampled": L, "logn_bisected": hi}
        prev = L
        L += step
    return {"found": False}


def stays_failing(family, theta: Fraction, L_from: float, L_to: float, step: float) -> dict:
    fails, total, L = 0, 0, L_from
    vals = []
    while L <= L_to:
        r = B.interval_bound(family, theta, arb(L), arb(L))
        total += 1
        fails += bool(r["margin"] < 0)
        if abs(L - round(L / 100) * 100) < step / 2:
            vals.append([L, s(r["E"].lower(), 6)])
        L += step
    return {"sampled": total, "failing": fails, "E_lower_samples": vals}


def witnesses(k: int, n_max: int) -> list:
    out = []
    for n in range(1, n_max + 1):
        w = pratt.witness(n, k)
        assert w["inside"] and pratt.check_witness(w), (n, k)
        out.append(w)
    return out


def chain(k: int, theta: Fraction, L_inf: Fraction, n_witness: int = 9) -> dict:
    fam = B.KthPowers(k)
    t0 = time.monotonic()
    L_start = log_floor(n_witness + 1)
    grid = cover(fam, theta, L_start, L_inf)
    tail = B.kth_power_tail(k, theta, L_inf)
    wit = witnesses(k, n_witness)
    boundaries = {
        "witness_to_analytic_n10": point(fam, theta, arb(n_witness + 1).log()),
        "analytic_to_tail_logn_" + str(L_inf): point(fam, theta, B.a_(L_inf)),
    }
    if B.H0:
        transition = (arb(k) * B.H0 / B.a_(B.U1)).log()   # where a* U1 = H0
        boundaries["transition_logn_" + s(transition, 6)] = point(fam, theta, transition)
    return {
        "k": k, "theta": str(theta), "H0": B.H0,
        "N_remainder": [str(B.C1), str(B.C2), str(B.C3)],
        "witness_range": [1, n_witness],
        "witnesses": [{"n": w["n"], "prime": w["prime"]} for w in wit],
        "analytic_cover": grid,
        "tail": {"L_inf": str(L_inf), "closed": tail["closed"],
                 "decreasing": tail.get("decreasing"),
                 "sup_bound": s(tail["sup_bound"].upper()) if "sup_bound" in tail else None},
        "boundary_margins": boundaries,
        "closed": bool(grid["closed"] and tail["closed"]),
        "seconds": round(time.monotonic() - t0, 2),
    }, wit


@contextmanager
def height(h0: int):
    old = B.H0
    B.H0 = h0
    try:
        yield
    finally:
        B.H0 = old


def main(parts) -> None:
    B.set_precision()
    out = {}
    if "chain" in parts:
        res, wit = chain(9, SEVEN_EIGHTHS, Fraction(100))
        out["theorem1_k9"] = res
        (HERE / "witnesses_k9.json").write_text(json.dumps(wit, indent=1) + "\n")
        print(json.dumps(res, indent=1))
    if "noRH" in parts:
        with height(0):
            res, _ = chain(9, SEVEN_EIGHTHS, Fraction(100))
        out["theorem1_k9_without_RH_verification"] = res
        print(json.dumps(res["analytic_cover"], indent=1), res["tail"], res["closed"])
    if "weaker" in parts:
        res, wit = chain(13, ELEVEN_TWELFTHS, Fraction(200))
        (HERE / "witnesses_k13.json").write_text(json.dumps(wit, indent=1) + "\n")
        with height(0):
            res0, _ = chain(13, ELEVEN_TWELFTHS, Fraction(200))
        ff = first_failure(B.KthPowers(12), ELEVEN_TWELFTHS, 2.3, 60.0)
        out["theorem1prime_k13_eleven_twelfths"] = {
            "with_height": res, "without_RH_verification": res0, "k12_first_failure": ff}
        print(json.dumps(res["analytic_cover"], indent=1), res0["closed"], ff)
    if "control" in parts:
        res, wit = chain(17, FIFTEEN_SIXTEENTHS, Fraction(200))
        (HERE / "witnesses_k17.json").write_text(json.dumps(wit, indent=1) + "\n")
        ctl = {"theta15_16_k17": res}
        for k, th in [(8, SEVEN_EIGHTHS), (16, FIFTEEN_SIXTEENTHS)]:
            fam = B.KthPowers(k)
            ff = first_failure(fam, th, 2.3, 60.0)
            st = stays_failing(fam, th, ff["logn_first_fail_sampled"], 1000.0, 0.5)
            ctl[f"theta{th.numerator}_{th.denominator}_k{k}"] = {
                "first_failure": ff, "after_first_failure": st,
                "tail": {kk: (s(v) if isinstance(v, arb) else v)
                         for kk, v in B.kth_power_tail(k, th, Fraction(100)).items()},
            }
        out["controls"] = ctl
        print(json.dumps(ctl, indent=1))
    if "short" in parts:
        fam = B.PowerLog(Fraction(1, 2), SEVEN_EIGHTHS)
        t0 = time.monotonic()
        grid = cover(fam, SEVEN_EIGHTHS, Fraction(8), Fraction(400))
        tail = B.powerlog_tail(Fraction(1, 2), SEVEN_EIGHTHS, Fraction(400))
        res = {"c": "1/2", "theta": "7/8", "x1": "e^8",
               "analytic_cover": grid,
               "tail": {"closed": tail["closed"], "limit": s(tail["limit"]),
                        "sup_bound": s(tail["sup_bound"].upper())},
               "boundary_margins": {"logx_8": point(fam, SEVEN_EIGHTHS, arb(8)),
                                    "logx_400": point(fam, SEVEN_EIGHTHS, arb(400))},
               "closed": bool(grid["closed"] and tail["closed"]),
               "seconds": round(time.monotonic() - t0, 2)}
        out["theorem2_short"] = res
        print(json.dumps(res, indent=1))
    if "psi" in parts:
        t0 = time.monotonic()
        grid = psi_cover(SEVEN_EIGHTHS, Fraction(PSI_START), Fraction(200))
        tail = B.psi_tail(SEVEN_EIGHTHS, Fraction(200))
        res = {"bound": "|psi(x) - x| < x^(7/8) log^2 x / (128 pi)", "x0": f"e^{PSI_START}",
               "cover": grid,
               "tail": {"L_inf": "200", "closed": tail["closed"], "D": s(tail["D"].lower()),
                        "dD_lower": s(tail["dD_lower"].lower())},
               "closed": bool(grid["closed"] and tail["closed"]),
               "seconds": round(time.monotonic() - t0, 2)}
        out["theorem3_psi"] = res
        print(json.dumps(res, indent=1))
    if "height" in parts:
        fam, rows = B.KthPowers(9), []
        for h0 in [0, 10 ** 4, 10 ** 6, 10 ** 8, 10 ** 10, B.H0]:
            with height(h0):
                worst = None
                L = 2.4
                while L <= 120:
                    E = B.interval_bound(fam, SEVEN_EIGHTHS, arb(L), arb(L))["E"]
                    if worst is None or E.mid() > worst[1].mid():
                        worst = (L, E)
                    L += 0.25
            rows.append({"H0": h0, "peak_logn": worst[0], "peak_E": s(worst[1], 6)})
        out["height_sensitivity_measured"] = rows
        print(json.dumps(rows, indent=1))
    name = ("verification.json" if set(parts) >= {"chain", "noRH", "weaker", "control", "short", "psi"}
            else "partial.json")
    (HERE / name).write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main(sys.argv[1:] or ["chain", "noRH", "weaker", "control", "short", "psi", "height"])
