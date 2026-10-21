"""Check the finite adversary without importing the optimizer or its evaluator.

For any probability measure on gap vectors, the expected functional is at
most 2 sum_s max_i E[W(d_i,s)] + B max_r E[g_r], uniformly in every feasible
pair weight and pressure. Its infimum is at most this expectation.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx
from mpmath import mp

HERE = Path(__file__).resolve().parent


def ball(q):
    q = Fraction(q)
    return arb(q.numerator) / q.denominator


def rational_points(data):
    total = Fraction(0)
    points = []
    for orbit in data["orbits"]:
        p = Fraction(orbit["weight"])
        gaps = list(map(Fraction, orbit["gaps"]))
        if p < 0 or len(gaps) != 6 or min(gaps) < 0:
            raise ValueError("Invalid probability or gap vector")
        total += p
        points.extend([(p / 2, gaps), (p / 2, gaps[::-1])])
    if total != 1:
        raise ValueError("Probability mass is not exactly one")
    if Fraction(data["pressure_budget"]) != Fraction(93, 23000):
        raise ValueError("Wrong pressure budget")
    if Fraction(data["span_budget"]) != 2:
        raise ValueError("Wrong span budget")
    return points


def window_transform(x, data):
    pi = arb.pi()
    value = arb(0)
    for j, numerator in enumerate(data["window_numerators"]):
        frequency = arb(2).sqrt() if j == 0 else 2 * pi * j
        for argument in (frequency / 2 - pi * x, frequency / 2 + pi * x):
            # Arb's sinc is the entire sin(z)/z, including at zero.
            value += ball(Fraction(numerator, data["window_denominator"])) * argument.sinc() / 2
    return value


def check(data, bits=160):
    points = rational_points(data)
    with ctx.workprec(bits):
        k0 = window_transform(arb(0), data)
        if not k0 > 0:
            raise ValueError("Normalization has no positive lower bound")
        moments = {(i, j): arb(0) for i in range(7) for j in range(i + 1, 7)}
        mean_gaps = [Fraction(0)] * 6
        for probability, gaps in points:
            position = [Fraction(0)]
            for gap in gaps:
                position.append(position[-1] + gap)
            for key in moments:
                i, j = key
                transform = window_transform(ball(position[j] - position[i]), data)
                moments[key] += ball(probability) * (transform / k0)**2
            for r, gap in enumerate(gaps):
                mean_gaps[r] += probability * gap
        # Every returned upper endpoint is an outward bound. Max is taken
        # with arb.max, preserving enclosure even when intervals overlap.
        caps = []
        for span in range(1, 7):
            cap = moments[0, span]
            for i in range(1, 7 - span):
                cap = cap.max(moments[i, i + span])
            caps.append(cap)
        upper = 2 * sum(caps, arb(0)) + ball(data["pressure_budget"]) * ball(max(mean_gaps))
        target = ball(data["upper_target"])
        old = ball(data["reported_lower_endpoint"])
        rational_caps = list(map(Fraction, data["span_caps"]))
        if len(rational_caps) != 6:
            raise ValueError("Expected six span caps")
        for span, cap in enumerate(rational_caps, 1):
            for i in range(7 - span):
                if not moments[i, i + span] < ball(cap):
                    raise ValueError("A rational span cap fails")
        gap_cap = Fraction(data["mean_gap_cap"])
        if not max(mean_gaps) < gap_cap:
            raise ValueError("The rational mean gap cap fails")
        rational_upper = 2 * sum(rational_caps) + Fraction(data["pressure_budget"]) * gap_cap
        if not rational_upper < Fraction(data["upper_target"]):
            raise ValueError("The exact budget arithmetic fails")
        if not upper < target:
            raise ValueError(f"Upper target not established: {upper} versus {target}")
        if not target < old:
            raise ValueError("Upper target does not refute the reported lower endpoint")
        return {"bits": bits, "upper_enclosure": str(upper),
                "exact_budget_upper": str(rational_upper),
                "rational_upper": data["upper_target"],
                "separation_from_reported_lower": str(Fraction(data["reported_lower_endpoint"])
                                                       - Fraction(data["upper_target"])),
                "orbit_count": len(data["orbits"]),
                "span_max_enclosures": [str(x) for x in caps],
                "mean_gaps": [str(x) for x in mean_gaps]}


def quadrature_control(data, dps=60):
    """A different transform route at each distance used by the artifact."""
    points = rational_points(data)
    distances = {Fraction(0)}
    for _, gaps in points:
        for i in range(6):
            for j in range(i + 1, 7):
                distances.add(sum(gaps[i:j]))
    with mp.workdps(dps):
        coefficients = [mp.mpf(n) / data["window_denominator"] for n in data["window_numerators"]]
        frequencies = [mp.sqrt(2)] + [2 * mp.pi * j for j in range(1, len(coefficients))]
        largest = mp.mpf(0)
        for rational in sorted(distances):
            x = mp.mpf(rational.numerator) / rational.denominator
            direct = 2 * mp.quad(lambda t: sum(c * mp.cos(w * t) for c, w in
                                              zip(coefficients, frequencies)) * mp.cos(2 * mp.pi * x * t),
                                 [mp.mpf(j) / 16 for j in range(9)])
            closed = sum(c * (mp.sinc(w / 2 - mp.pi * x) + mp.sinc(w / 2 + mp.pi * x)) / 2
                         for c, w in zip(coefficients, frequencies))
            largest = max(largest, abs(direct - closed))
            with ctx.workprec(256):
                residual = abs(window_transform(ball(rational), data)
                               - arb(mp.nstr(direct, dps - 10)))
                if not residual < ball(Fraction(1, 10**45)):
                    raise ValueError("Direct quadrature disagrees with Arb transform")
        if largest >= mp.mpf("1e-45"):
            raise ValueError("Quadrature and analytic transform disagree")
        return {"dps": dps, "distinct_distances": len(distances),
                "largest_quadrature_defect": mp.nstr(largest, 12)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--quadrature", action="store_true")
    args = parser.parse_args()
    data = json.loads((HERE / "adversary.json").read_text())
    results = {"interval_checks": [check(data, bits) for bits in (128, 256)]}
    if args.quadrature:
        results["quadrature"] = quadrature_control(data)
    (HERE / "verification.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
