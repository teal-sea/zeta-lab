"""hunts/weil_split/split.py

Per-place energy of the prime side, exactly, for the rectangle test function
f = b^{-1/2} 1_{[-b/2, b/2]} (so ||f||^2 = 1), whose autocorrelation is the
triangle g.

    Phi_p f = sum_{m>=0} p^{-m/2} f(. - m log p),   finite because f is compact
    ||Phi_p f||^2 = (1/b) sum_{m,n>=0} p^{-(m+n)/2} (b - |m-n| log p)_+
    Q_p = (1 - 1/p) ||Phi_p f||^2
    e_p = log p (1 - Q_p)                     (||f||^2 = 1)
    E   = sum_p e_p        must equal -prime_term
    W   = pole + arch - E  must equal the zero side

The sum over m,n is finite: terms vanish once |m-n| log p >= b, so only primes
with log p < b contribute, i.e. p <= e^b.

Run:  python hunts/weil_split/split.py
"""

from __future__ import annotations

import json
import os

import mpmath as mp

from zeta.weil import explicit_formula_sides

DPS = 40


def pair(b: float):
    """h = transform of the triangle of half-width b, g = the triangle."""
    bb = mp.mpf(b)

    def h(r):
        if r == 0:
            return bb
        return (2 / bb) * (1 - mp.cos(bb * r)) / (r * r)

    def g(u):
        return (1 / bb) * max(mp.mpf(0), bb - abs(u))

    return h, g


def norm_phi2(b: float, p: int) -> mp.mpf:
    """||Phi_p f||^2 exactly, as a finite rectangle-overlap sum."""
    bb = mp.mpf(b)
    lp = mp.log(p)
    if lp >= bb:
        # no pair of distinct shifts overlaps; the geometric series is exact
        return 1 / (1 - mp.mpf(1) / p)
    M = int(mp.floor(bb / lp)) + 2          # |m-n| <= M
    tot = mp.mpf(0)
    for k in range(-M, M + 1):
        overlap = bb - abs(k) * lp
        if overlap <= 0:
            continue
        # sum over n >= max(0, -k) of p^{-(2n+k)/2} = p^{-k/2} sum_n p^{-n}
        n0 = max(0, -k)
        geo = p ** (-n0) / (1 - mp.mpf(1) / p)
        tot += overlap * p ** (-mp.mpf(k) / 2) * geo
    return tot / bb


def _primes_upto(n: int) -> list[int]:
    if n < 2:
        return []
    sieve = bytearray([1]) * (n + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(2, n + 1) if sieve[i]]


def place_energies(b: float, prime_cap: int | None = None) -> list[dict]:
    bb = mp.mpf(b)
    pmax = int(mp.e ** bb) + 2 if prime_cap is None else prime_cap
    primes = _primes_upto(pmax)
    out = []
    for p in primes:
        q = (1 - mp.mpf(1) / p) * norm_phi2(b, p)
        out.append(
            {
                "p": int(p),
                "log_p": float(mp.log(p)),
                "Q_p": float(q),
                # cost_p = log p (Q_p - 1) >= 0 when the shifts pile up
                "cost_p": float(mp.log(p) * (q - 1)),
            }
        )
    return out


def row(b: float, dps: int = DPS) -> dict:
    with mp.workdps(dps):
        h, g = pair(b)
        d = explicit_formula_sides(h, g, dps=dps)
        places = place_energies(b)
        cost = mp.fsum(mp.mpf(x["cost_p"]) for x in places)
        arith = mp.mpf(d["arithmetic_side"])
        prime = mp.mpf(d["prime_term"])
        zero = mp.mpf(d["zero_side"])
        top = mp.mpf(d["pole_term"]) + mp.mpf(d["arch_term"])
        # pole+arch derived from the zero side instead of the arch quadrature:
        # W = pole + arch + prime, and W = zero side. This removes the slow
        # archimedean integral (h decays only like 1/r^2 here) from the cover.
        top_derived = zero - prime
        order = sorted(places, key=lambda x: -x["cost_p"])
        top3 = sum(x["cost_p"] for x in order[:3])
        return {
            "b": b,
            "n_primes": len(places),
            "cost_sum": float(cost),
            "minus_prime_term": float(-prime),
            "decomposition_gap": float(cost + prime),   # must be ~0
            "pole_plus_arch_quad": float(top),
            "pole_plus_arch_derived": float(top_derived),
            "W": float(arith),
            "W_from_zeros": float(zero),
            "agreement": float(d["agreement"]),
            "cover_quad": float(top / cost) if cost != 0 else None,
            "cover_derived": float(top_derived / cost) if cost != 0 else None,
            "top3_share": float(top3 / cost) if cost != 0 else None,
            "largest_places": [(x["p"], x["cost_p"]) for x in order[:3]],
            "places": places,
        }


def main() -> dict:
    rows = []
    for b in (2.0, 3.0, 4.5, 6.0, 8.0):
        r = row(b)
        rows.append(r)
        print(
            f"b={r['b']:<4g} primes={r['n_primes']:<3d} cost={r['cost_sum']:+.6e} "
            f"-prime={r['minus_prime_term']:+.6e} gap={r['decomposition_gap']:+.1e} "
            f"top(quad)={r['pole_plus_arch_quad']:+.6f} "
            f"top(derived)={r['pole_plus_arch_derived']:+.6f} "
            f"cover={r['cover_derived']:.9f} top3={r['top3_share']:.3f} "
            f"top={r['largest_places']}",
            flush=True,
        )
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results.json"), "w") as f:
        json.dump(rows, f, indent=1)
    return {"rows": rows}


if __name__ == "__main__":
    main()
