#!/usr/bin/env python3
"""All-n witness certificate based on a balanced 37-periodic word.

The gap word has 18 twos and 19 ones per period.  Every window sum is
an integer, so w has a particularly simple exact formula and its tail is
O(s^-4).  Finite n below a cutoff are checked by interval arithmetic; an
explicit periodic-average error bound handles every larger n at once.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np

from interval_verify import endpoint


PERIOD = 37
TWOS = 18


def position(index: int) -> int:
    return index + (TWOS * index) // PERIOD


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--finite-through", type=int, default=599)
    parser.add_argument("--tail-from", type=int, default=600)
    parser.add_argument("--series-terms", type=int, default=5000)
    parser.add_argument("--output", type=Path, default=Path("results/periodic-certificate.json"))
    args = parser.parse_args()
    if args.tail_from != args.finite_through + 1:
        raise ValueError("tail-from must be finite-through + 1")

    mp.iv.dps = 100
    mp.mp.dps = 140
    iv = mp.iv
    q = 1 / iv.sqrt(2)
    h = iv.mpf(3) / 2 - q / iv.tan(q)
    target = iv.mpf("0.6751676068")
    w_threshold = target / h - 1

    def w_integer(index: int):
        # k(j)=(-1)^(j+1) q^2/(pi^2 j^2-q^2), q^2=1/2.
        j = iv.mpf(index)
        return 1 / (4 * (iv.pi**2 * j**2 - iv.mpf(1) / 2) ** 2)

    max_distance = position(args.finite_through - 1)
    w_values = [iv.mpf(0)] + [w_integer(j) for j in range(1, max_distance + 1)]
    prefix = np.array([position(j) for j in range(args.finite_through)], dtype=int)

    requested = {7, 8, 9, 10, 11, 12, 14, 16, 20, 30, 56, 100}
    requested_values: dict[str, dict] = {}
    failures: list[int] = []
    maximum_upper = mp.mpf("-inf")
    maximum_n = None
    maximum_interval = None
    passing_maximum_upper = mp.mpf("-inf")
    passing_maximum_n = None
    passing_maximum_interval = None

    for n in range(3, args.finite_through + 1):
        energy = iv.mpf(0)
        for s in range(1, n):
            distances = prefix[s:n] - prefix[: n - s]
            values, counts = np.unique(distances, return_counts=True)
            window_sum = iv.mpf(0)
            for value, count in zip(values, counts, strict=True):
                window_sum += int(count) * w_values[int(value)]
            energy += iv.mpf(2) / (n - s) * window_sum

        upper = mp.mpf(energy._mpi_[1])
        if upper > maximum_upper:
            maximum_upper = upper
            maximum_n = n
            maximum_interval = energy
        if n >= 8 and upper > passing_maximum_upper:
            passing_maximum_upper = upper
            passing_maximum_n = n
            passing_maximum_interval = energy
        if not (energy.b <= w_threshold.a):
            failures.append(n)
        if n in requested:
            bound = h * (1 + energy)
            requested_values[str(n)] = {
                "W_lower": endpoint(energy, False),
                "W_upper": endpoint(energy, True),
                "bound_upper": endpoint(bound, True),
                "sum": position(n - 1),
                "cap_accepted": iv.mpf(position(n - 1)).b <= ((n - 1) / h).a,
            }

    # Infinite phase average.  For s gaps, each 37 starting phases sees
    # floor(18s/37) or ceil(18s/37) twos, with exact multiplicities.
    series = iv.mpf(0)
    for s in range(1, args.series_terms + 1):
        low_twos = (TWOS * s) // PERIOD
        high_count = TWOS * s - PERIOD * low_twos
        low_distance = s + low_twos
        mean = (
            (PERIOD - high_count) * w_integer(low_distance)
            + high_count * w_integer(low_distance + 1)
        ) / PERIOD
        series += 2 * mean

    c = 1 / (4 * (iv.pi**2 - iv.mpf(1) / 2) ** 2)
    tail = 2 * c / (3 * args.series_terms**3)
    infinite_energy = iv.mpf([series.a, (series + tail).b])

    # If A_{s,N} is the mean over N consecutive phases and mu_s the full
    # 37-phase mean, A_{s,N} <= mu_s + 37 M_s/N.  Since each integer
    # distance is >=s, M_s <= C/s^4.  Splitting s at n/2 gives the explicit
    # decreasing upper bound below.
    n0 = args.tail_from
    zeta4 = iv.pi**4 / 90
    # H_{ceil(n/2)} <= 1+log(n); (1+log n)/n^4 decreases for n>=1,
    # so substituting n0 is valid simultaneously for every n>=n0.
    convolution_bound = 2 * zeta4 / n0 + 16 * (1 + iv.log(n0)) / n0**4
    finite_phase_error = 74 * c * convolution_bound
    all_large_energy_upper = infinite_energy + finite_phase_error
    all_large_bound = h * (1 + all_large_energy_upper)

    # A shorter all-n proof needs no phase-limit comparison.  For q=n-1>=11,
    # the prefix contains at least a 5/12 fraction of twos.  The singleton
    # contribution is therefore bounded by the corresponding mixture of
    # w(1),w(2).  Every longer integer window has distance >=s, and
    # w(s)<=w(1)/s^4.
    w1 = w_integer(1)
    w2 = w_integer(2)
    simple_energy_bound = (
        2 * (iv.mpf(7) / 12 * w1 + iv.mpf(5) / 12 * w2)
        + 2 * w1 * (iv.pi**4 / 90 - 1)
    )
    simple_phi_bound = h * (1 + simple_energy_bound)

    cap_ratio = iv.mpf(55) / 37
    payload = {
        "word": "g_i = 1 + floor(18 i/37) - floor(18(i-1)/37)",
        "cap_ratio_upper": endpoint(cap_ratio, True),
        "one_over_H_lower": endpoint(1 / h, False),
        "cap_all_prefixes_accepted": cap_ratio.b <= (1 / h).a,
        "finite_checked_n": [3, args.finite_through],
        "finite_failures_of_claimed_threshold": failures,
        "finite_maximum": {
            "n": maximum_n,
            "W_lower": endpoint(maximum_interval, False),
            "W_upper": endpoint(maximum_interval, True),
            "threshold_lower": endpoint(w_threshold, False),
        },
        "finite_maximum_n_ge_8": {
            "n": passing_maximum_n,
            "W_lower": endpoint(passing_maximum_interval, False),
            "W_upper": endpoint(passing_maximum_interval, True),
            "threshold_lower": endpoint(w_threshold, False),
        },
        "requested_word_witnesses": requested_values,
        "infinite_energy_lower": endpoint(infinite_energy, False),
        "infinite_energy_upper": endpoint(infinite_energy, True),
        "series_terms": args.series_terms,
        "series_tail_upper": endpoint(tail, True),
        "large_n_from": n0,
        "large_n_phase_error_upper": endpoint(finite_phase_error, True),
        "large_n_W_upper": endpoint(all_large_energy_upper, True),
        "large_n_bound_upper": endpoint(all_large_bound, True),
        "large_n_claim_accepted": all_large_bound.b <= target.a,
        "simple_all_n_from": 12,
        "simple_W_upper": endpoint(simple_energy_bound, True),
        "simple_bound_upper": endpoint(simple_phi_bound, True),
        "simple_claim_accepted": simple_phi_bound.b <= target.a,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
