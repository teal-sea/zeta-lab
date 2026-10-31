"""hunts/decay_law/decay.py

Covering margin for two compact families on the grid fixed in MISSION.md.

    f rectangle:  b^{-1/2} on [-b/2, b/2],   h(r) = b sinc^2(b r / 2)
    f tent:       sqrt(3/b) (1 - 2|x|/b)_+ , h(r) = (3b/4) sinc^4(b r / 4)

    C = -prime_term = sum_p cost_p
    margin = W_zeros / C
    alpha_X = ln(X(2) / X(8)) / ln(4)

W_zeros is the sum of h over verified ordinates of both signs, up to height
10^4. The prime cost is the finite prime-power sum. The archimedean integral
is computed only to record the disagreement with the zero side. The margin
does not use it.

Run from the repo root:  python hunts/decay_law/decay.py
"""

from __future__ import annotations

import json
import math
import os
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

import mpmath as mp
import numpy as np

from zeta.statistics import zero_ordinates
from zeta.weil import explicit_formula_sides, fejer_pair

HERE = Path(__file__).resolve().parent
LANDED_PATH = HERE.parent / "weil_split" / "results.json"
GAMMA_MAX = 10000.0
DPS = 25
WORKERS = 6
# Primary grid, fixed in MISSION.md before the tent measurement.
GRID = tuple(2.0 + 0.25 * k for k in range(25))
TOLERANCE = 0.5


def sinc(x):
    if x == 0:
        return mp.mpf(1)
    return mp.sin(x) / x


def rect_g(b, u):
    bb = mp.mpf(b)
    v = abs(u) / bb
    if v >= 1:
        return mp.mpf(0)
    return 1 - v


def rect_h(b, r):
    bb = mp.mpf(b)
    if r == 0:
        return bb
    return bb * sinc(bb * r / 2) ** 2


def tent_g(b, u):
    """Autocorrelation of the unit-mass tent. Derived in MISSION.md."""
    bb = mp.mpf(b)
    v = abs(u) / bb
    if v >= 1:
        return mp.mpf(0)
    if v <= mp.mpf("0.5"):
        return 1 - 6 * v ** 2 + 6 * v ** 3
    return 2 * (1 - v) ** 3


def tent_h(b, r):
    bb = mp.mpf(b)
    if r == 0:
        return 3 * bb / 4
    return (3 * bb / 4) * sinc(bb * r / 4) ** 4


def tent_envelope(b, t):
    """Nonincreasing majorant of tent h: min(3b/4, 192/(b^3 t^4))."""
    bb = mp.mpf(b)
    cap = 3 * bb / 4
    tt = mp.mpf(t)
    if tt <= 4 / bb:
        return cap
    return 192 / (bb ** 3 * tt ** 4)


def tent_env_avg(b, t):
    """Mean of sin^4 is 3/8, so the mean envelope is 72/(b^3 t^4) past 4/b."""
    bb = mp.mpf(b)
    tt = mp.mpf(t)
    if tt <= 4 / bb:
        return (3 * bb / 4) * mp.mpf("0.375")
    return 72 / (bb ** 3 * tt ** 4)


FAMILIES = {
    "rectangle": (rect_g, rect_h),
    "tent": (tent_g, tent_h),
}


def _primes_upto(n: int) -> list[int]:
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(2, n + 1) if sieve[i]]


def prime_powers(n_max: int) -> list[tuple[int, int]]:
    primes = _primes_upto(n_max)
    table = []
    for p in primes:
        pk = p
        while pk <= n_max:
            table.append((pk, p))
            pk *= p
    table.sort()
    return table


def prime_term(b, g, powers) -> mp.mpf:
    """-2 sum Lambda(n) n^{-1/2} g(log n), n <= floor(e^b)."""
    total = mp.mpf(0)
    for n, p in powers:
        gu = g(b, mp.log(n))
        if gu == 0:
            continue
        total += mp.log(p) / mp.sqrt(n) * gu
    return -2 * total


def place_costs(b, g) -> list[dict]:
    """Per-place cost. cost_p = log p * (Q_p - 1), Q_p = (1-1/p) ||Phi_p f||^2.

    ||Phi_p f||^2 = sum_k g(k log p) p^{-k/2} sum_{n>=max(0,-k)} p^{-n}.
    Only primes with log p < b contribute: g vanishes for |u| >= b.
    """
    bb = mp.mpf(b)
    pmax = int(mp.floor(mp.e ** bb))
    out = []
    for p in _primes_upto(pmax):
        lp = mp.log(p)
        if lp >= bb:
            continue
        M = int(mp.floor(bb / lp)) + 2
        tot = mp.mpf(0)
        geo_den = 1 - mp.mpf(1) / p
        for k in range(-M, M + 1):
            gk = g(b, k * lp)
            if gk == 0:
                continue
            n0 = max(0, -k)
            geo = mp.power(p, -n0) / geo_den
            tot += gk * mp.power(p, -mp.mpf(k) / 2) * geo
        q = (1 - mp.mpf(1) / p) * tot
        out.append({"p": int(p), "cost_p": float(mp.log(p) * (q - 1))})
    return out


def pole_term(h, b) -> mp.mpf:
    """h(i/2) + h(-i/2), real part. Same evaluation the explicit formula uses."""
    v = h(b, mp.mpc(0, mp.mpf("0.5"))) + h(b, mp.mpc(0, mp.mpf("-0.5")))
    return mp.re(v)


def zero_breakdown(b, h, gammas) -> dict:
    """W and the share carried by the first few positive ordinates."""
    terms = []
    for gma in gammas:
        terms.append(2 * h(b, mp.mpf(gma)))
    W = mp.fsum(terms)
    def share(k):
        if W == 0:
            return None
        return float(mp.fsum(terms[:k]) / W)
    return {
        "W_zeros": float(W),
        "h_gamma1": float(h(b, mp.mpf(gammas[0]))),
        "first1_share": share(1),
        "first3_share": share(3),
        "first10_share": share(10),
        "n_zeros": len(gammas),
    }


def row_fast(family: str, b: float, gammas, powers) -> dict:
    g, h = FAMILIES[family]
    with mp.workdps(DPS):
        br = zero_breakdown(b, h, gammas)
        prime = prime_term(b, g, powers)
        places = place_costs(b, g)
        cost_places = mp.fsum(mp.mpf(x["cost_p"]) for x in places)
        cost = -prime
        W = mp.mpf(br["W_zeros"])
        order = sorted(places, key=lambda x: -x["cost_p"])
        top3 = sum(x["cost_p"] for x in order[:3])
        return {
            "family": family,
            "b": b,
            "W_zeros": br["W_zeros"],
            "h_gamma1": br["h_gamma1"],
            "first1_share": br["first1_share"],
            "first3_share": br["first3_share"],
            "first10_share": br["first10_share"],
            "n_zeros": br["n_zeros"],
            "prime_term": float(prime),
            "cost": float(cost),
            "margin": float(W / cost),
            "cover": float(1 + W / cost),
            "n_primes": len(places),
            "place_sum": float(cost_places),
            "place_gap": float(cost_places - cost),
            "top3_share": float(top3 / cost) if cost != 0 else None,
            "largest_places": [(x["p"], x["cost_p"]) for x in order[:3]],
            "pole": float(pole_term(h, b)),
        }


def _arch_density(r):
    return mp.re(mp.digamma(mp.mpf("0.25") + mp.mpc(0, 1) * r / 2)) - mp.log(mp.pi)


def tent_arch(b, dps: int = 20) -> mp.mpf:
    """(1/2π) int h(r) [Re ψ(1/4+ir/2) - log π] dr, even, so (1/π) int_0^∞.

    Main region on period-aligned panels. Tail split by the identity
    sin^4 θ = (3 - 4 cos 2θ + cos 4θ)/8, with θ = b r / 4, and integrated
    as one smooth piece plus two oscillatory pieces. The split is the
    source of the quadrature floor recorded beside the arithmetic side.
    """
    with mp.workdps(dps):
        bb = mp.mpf(b)
        period = 2 * mp.pi / bb
        A = mp.mpf(8)
        n = int(mp.ceil(float(A / period)))
        nodes = [k * period for k in range(n + 1)]
        main = mp.quad(lambda r: tent_h(b, r) * _arch_density(r), nodes)
        c = 24 / bb ** 3
        A0 = nodes[-1]
        with mp.workdps(15):
            A0t = +A0
            ct = +c
            bbt = +bb
            smooth = mp.quad(
                lambda r: 3 * ct * _arch_density(r) / r ** 4,
                [A0t, 2 * A0t, mp.inf],
            )
            osc1 = mp.quadosc(
                lambda r: -4 * ct * _arch_density(r) / r ** 4 * mp.cos(bbt * r / 2),
                [A0t, mp.inf],
                omega=bbt / 2,
            )
            osc2 = mp.quadosc(
                lambda r: ct * _arch_density(r) / r ** 4 * mp.cos(bbt * r),
                [A0t, mp.inf],
                omega=bbt,
            )
        return (main + smooth + osc1 + osc2) / mp.pi


def tent_tail(b) -> dict:
    """Zero-side tail bound past GAMMA_MAX, same partial-summation instrument
    the explicit formula uses. Imported from that module so the bound is not
    a second implementation."""
    from zeta.weil import _zero_tail_bound, _zero_tail_estimate

    def h(r):
        return tent_h(b, r)

    h.weil_hints = {
        "envelope": lambda t: tent_envelope(b, t),
        "env_avg": lambda t: tent_env_avg(b, t),
    }
    with mp.workdps(20):
        bound = _zero_tail_bound(h, GAMMA_MAX, 20)
        est = _zero_tail_estimate(h, GAMMA_MAX)
    return {
        "zero_tail_bound": float(bound),
        "zero_tail_estimate": None if est is None else float(est),
    }


def agreement_tent(b: float) -> dict:
    with mp.workdps(DPS):
        g = tent_g
        prime = prime_term(b, g, prime_powers(int(mp.floor(mp.e ** mp.mpf(b)))))
        pole = pole_term(tent_h, b)
        arch = tent_arch(b)
        tail = tent_tail(b)
    return {
        "family": "tent",
        "b": b,
        "arith_prime": float(prime),
        "arith_pole": float(pole),
        "arith_arch": float(arch),
        "prime_tail_bound": 0.0,
        **tail,
    }


def agreement_rectangle(b: float) -> dict:
    """Rectangle h is b times the Fejer pair at half-width b/2. The margin
    is unchanged by that factor. Pieces below are scaled back to the
    rectangle normalization used for W_zeros."""
    d = explicit_formula_sides(*fejer_pair(b / 2), gamma_max=GAMMA_MAX, dps=25)
    scale = b
    return {
        "family": "rectangle",
        "b": b,
        "arith_prime": scale * float(d["prime_term"]),
        "arith_pole": scale * float(d["pole_term"]),
        "arith_arch": scale * float(d["arch_term"]),
        "fejer_zero": scale * float(d["zero_side"]),
        "fejer_agreement": float(d["agreement"]),
        "fejer_abs_diff": scale * float(d["abs_diff"]),
        "zero_tail_bound": scale * float(d["zero_side_tail_bound"]),
        "zero_tail_estimate": (
            None
            if d["zero_side_tail_estimate"] is None
            else scale * float(d["zero_side_tail_estimate"])
        ),
        "prime_tail_bound": scale * float(d["prime_tail_bound"]),
    }


def _agree_worker(task):
    family, b = task
    if family == "tent":
        return agreement_tent(b)
    return agreement_rectangle(b)


def endpoint_alpha(rows, key) -> float:
    by_b = {r["b"]: r for r in rows}
    return math.log(by_b[2.0][key] / by_b[8.0][key]) / math.log(4)


def local_exponents(rows, key) -> list[float]:
    rows = sorted(rows, key=lambda r: r["b"])
    out = []
    for a, c in zip(rows, rows[1:]):
        out.append(
            math.log(a[key] / c[key]) / math.log(c["b"] / a["b"])
        )
    return out


def loglog_fit(rows, key) -> dict:
    """Least squares of ln X = A - alpha ln b. Residual is RMS in ln units."""
    rows = sorted(rows, key=lambda r: r["b"])
    x = np.array([math.log(r["b"]) for r in rows])
    y = np.array([math.log(r[key]) for r in rows])
    design = np.column_stack([np.ones_like(x), -x])
    coef, *_ = np.linalg.lstsq(design, y, rcond=None)
    A, alpha = (float(coef[0]), float(coef[1]))
    resid = y - (A - alpha * x)
    return {
        "alpha": alpha,
        "A": A,
        "rms_ln": float(np.sqrt(np.mean(resid ** 2))),
        "max_abs_ln": float(np.max(np.abs(resid))),
        "n": len(rows),
    }


def _corr(xs, ys) -> float | None:
    if len(xs) < 3:
        return None
    x = np.array(xs, dtype=float)
    y = np.array(ys, dtype=float)
    if np.std(x) == 0 or np.std(y) == 0:
        return None
    return float(np.corrcoef(x, y)[0, 1])


def family_summary(rows) -> dict:
    rows = sorted(rows, key=lambda r: r["b"])
    local_m = local_exponents(rows, "margin")
    local_W = local_exponents(rows, "W_zeros")
    local_C = local_exponents(rows, "cost")
    local_h = local_exponents(rows, "h_gamma1")
    return {
        "alpha_m": endpoint_alpha(rows, "margin"),
        "alpha_W": endpoint_alpha(rows, "W_zeros"),
        "alpha_C": endpoint_alpha(rows, "cost"),
        "fit_margin": loglog_fit(rows, "margin"),
        "fit_W": loglog_fit(rows, "W_zeros"),
        "fit_C": loglog_fit(rows, "cost"),
        "local_margin": local_m,
        "local_W": local_W,
        "local_C": local_C,
        "local_h_gamma1": local_h,
        "local_margin_min": min(local_m),
        "local_margin_max": max(local_m),
        "local_margin_span": max(local_m) - min(local_m),
        "local_W_span": max(local_W) - min(local_W),
        "local_C_span": max(local_C) - min(local_C),
        "n_W_increases": sum(1 for v in local_W if v < 0),
        "corr_local_m_with_h1": _corr(local_m, local_h),
        "corr_local_W_with_h1": _corr(local_W, local_h),
        "first1_share_min": min(r["first1_share"] for r in rows),
        "first1_share_max": max(r["first1_share"] for r in rows),
        "first3_share_min": min(r["first3_share"] for r in rows),
        "first3_share_max": max(r["first3_share"] for r in rows),
        "single_exponent_defensible": (max(local_m) - min(local_m)) <= TOLERANCE,
    }


def kill_report(rect_rows, tent_rows, landed_alphas) -> dict:
    """Rectangle side of the kill is the landed table, as pre-registered.
    The recomputed rectangle is recorded beside it, not substituted."""
    recomputed = {
        "alpha_m": endpoint_alpha(rect_rows, "margin"),
        "alpha_W": endpoint_alpha(rect_rows, "W_zeros"),
        "alpha_C": endpoint_alpha(rect_rows, "cost"),
    }
    tent = {
        "alpha_m": endpoint_alpha(tent_rows, "margin"),
        "alpha_W": endpoint_alpha(tent_rows, "W_zeros"),
        "alpha_C": endpoint_alpha(tent_rows, "cost"),
    }
    diffs = {
        key: tent[key] - landed_alphas[key]
        for key in ("alpha_m", "alpha_W", "alpha_C")
    }
    fired_on = [key for key, d in diffs.items() if abs(d) > TOLERANCE]
    return {
        "tolerance": TOLERANCE,
        "rectangle_landed": landed_alphas,
        "rectangle_recomputed": recomputed,
        "tent": tent,
        "tent_minus_landed": diffs,
        "fired": bool(fired_on),
        "fired_on": fired_on,
    }


def merge_agreement(row, extra) -> dict:
    out = dict(row)
    pole = extra["arith_pole"]
    arch = extra["arith_arch"]
    prime = extra["arith_prime"]
    arith = pole + arch + prime
    W = row["W_zeros"]
    diff = arith - W
    scale = max(abs(W), abs(arith), 1e-30)
    out.update({
        "arith_pole": pole,
        "arith_arch": arch,
        "arith_prime": prime,
        "arithmetic_side": arith,
        "abs_diff": abs(diff),
        "signed_diff": diff,
        "agreement": abs(diff) / scale,
        "prime_crosscheck": prime - row["prime_term"],
        "zero_tail_bound": extra.get("zero_tail_bound"),
        "zero_tail_estimate": extra.get("zero_tail_estimate"),
        "prime_tail_bound": extra.get("prime_tail_bound"),
        "fejer_zero": extra.get("fejer_zero"),
        "fejer_agreement": extra.get("fejer_agreement"),
        "fejer_abs_diff": extra.get("fejer_abs_diff"),
    })
    return out


def landed_alphas() -> dict:
    rows = json.loads(LANDED_PATH.read_text())
    by_b = {r["b"]: r for r in rows}

    def X(b, key):
        return by_b[b][key]

    # landed keys: W_from_zeros, cost_sum, cover_derived - 1
    def margin(b):
        return X(b, "cover_derived") - 1

    ln4 = math.log(4)
    return {
        "alpha_m": math.log(margin(2.0) / margin(8.0)) / ln4,
        "alpha_W": math.log(X(2.0, "W_from_zeros") / X(8.0, "W_from_zeros")) / ln4,
        "alpha_C": math.log(X(2.0, "cost_sum") / X(8.0, "cost_sum")) / ln4,
        "source": "hunts/weil_split/results.json",
    }


def main() -> dict:
    gammas = [float(g) for g in zero_ordinates(t_max=GAMMA_MAX)]
    powers = {}
    with mp.workdps(DPS):
        for b in GRID:
            powers[b] = prime_powers(int(mp.floor(mp.e ** mp.mpf(b))))

    rows = []
    ckpt = HERE / "rows.jsonl"
    if ckpt.exists():
        ckpt.unlink()
    for family in ("rectangle", "tent"):
        for b in GRID:
            r = row_fast(family, b, gammas, powers[b])
            rows.append(r)
            with ckpt.open("a") as fh:
                fh.write(json.dumps(r) + "\n")
            print(
                f"{family:9s} b={b:4.2f} W={r['W_zeros']:.6e} C={r['cost']:.6e} "
                f"m={r['margin']:.6e} place_gap={r['place_gap']:.1e} "
                f"h1_share={r['first1_share']:.3f}",
                flush=True,
            )

    tasks = [(r["family"], r["b"]) for r in rows]
    extras = {}
    with ProcessPoolExecutor(max_workers=WORKERS) as pool:
        futs = {pool.submit(_agree_worker, t): t for t in tasks}
        for fut in as_completed(futs):
            family, b = futs[fut]
            extra = fut.result()
            extras[(family, b)] = extra
            print(f"agreement {family} b={b:4.2f} done", flush=True)

    merged = [merge_agreement(r, extras[(r["family"], r["b"])]) for r in rows]
    by_family = {
        "rectangle": [r for r in merged if r["family"] == "rectangle"],
        "tent": [r for r in merged if r["family"] == "tent"],
    }
    landed = landed_alphas()
    summary = {
        "grid": list(GRID),
        "gamma_max": GAMMA_MAX,
        "dps": DPS,
        "tolerance": TOLERANCE,
        "landed_alphas": landed,
        "rectangle": family_summary(by_family["rectangle"]),
        "tent": family_summary(by_family["tent"]),
        "kill": kill_report(by_family["rectangle"], by_family["tent"], landed),
        "worst_agreement": {
            fam: max(r["agreement"] for r in by_family[fam])
            for fam in by_family
        },
        "worst_place_gap": {
            fam: max(abs(r["place_gap"]) for r in by_family[fam])
            for fam in by_family
        },
    }
    payload = {"summary": summary, "rows": merged}
    (HERE / "results.json").write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(summary["kill"], indent=1), flush=True)
    print("worst agreement", summary["worst_agreement"], flush=True)
    print("worst place gap", summary["worst_place_gap"], flush=True)
    return payload


if __name__ == "__main__":
    main()
