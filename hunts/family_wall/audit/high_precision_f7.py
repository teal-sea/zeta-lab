#!/usr/bin/env python3
"""High-precision stationary solve and point interval check for F_{7,3000}."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np

from audit import hessian
from interval_verify import endpoint


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=Path("results/f7.json"))
    parser.add_argument("--output", type=Path, default=Path("results/f7-high-precision.json"))
    parser.add_argument("--dps", type=int, default=100)
    args = parser.parse_args()
    payload = json.loads(args.input.read_text())
    start_values = payload["result"].get("gaps_decimal") or [repr(x) for x in payload["result"]["gaps"]]

    mp.mp.dps = args.dps
    q = 1 / mp.sqrt(2)
    kzero = mp.sin(q) / q

    def sinc(z):
        return mp.mpf(1) if z == 0 else mp.sin(z) / z

    def sinc_prime(z):
        return mp.mpf(0) if z == 0 else (z * mp.cos(z) - mp.sin(z)) / z**2

    def kernel(x):
        return (sinc(q - mp.pi * x) + sinc(q + mp.pi * x)) / 2

    def kernel_prime(x):
        return mp.pi * (-sinc_prime(q - mp.pi * x) + sinc_prime(q + mp.pi * x)) / 2

    def weight(x):
        return (kernel(x) / kzero) ** 2

    def weight_prime(x):
        return 2 * kernel(x) * kernel_prime(x) / kzero**2

    def gradient(*gaps):
        result = []
        for gap_index in range(6):
            value = mp.mpf(1) / 3000
            for s in range(1, 7):
                coefficient = mp.mpf(2) / (7 - s)
                for i in range(7 - s):
                    if i <= gap_index < i + s:
                        value += coefficient * weight_prime(mp.fsum(gaps[i : i + s]))
            result.append(value)
        return tuple(result)

    start = tuple(mp.mpf(x) for x in start_values)
    root = mp.findroot(
        gradient,
        start,
        solver="mdnewton",
        tol=mp.mpf(10) ** (-(args.dps - 20)),
        maxsteps=100,
    )
    value = mp.fsum(root) / 3000
    energy = mp.mpf(0)
    for s in range(1, 7):
        for i in range(7 - s):
            energy += mp.mpf(2) / (7 - s) * weight(mp.fsum(root[i : i + s]))
    value += energy

    gap_strings = [mp.nstr(x, 50) for x in root]
    displayed = [mp.nstr(x, 36) for x in root]

    # Re-evaluate the displayed finite decimals with directed intervals.
    mp.iv.dps = args.dps
    iv = mp.iv
    qi = 1 / iv.sqrt(2)

    def iv_sinc(z):
        if 0 in z:
            raise ValueError("unexpected sinc singularity")
        return iv.sin(z) / z

    kzero_i = iv_sinc(qi)

    def iv_weight(x):
        kval = (iv_sinc(qi - iv.pi * x) + iv_sinc(qi + iv.pi * x)) / 2
        return (kval / kzero_i) ** 2

    displayed_iv = [iv.mpf(x) for x in displayed]
    interval_value = sum(displayed_iv, iv.mpf(0)) / 3000
    for s in range(1, 7):
        for i in range(7 - s):
            interval_value += iv.mpf(2) / (7 - s) * iv_weight(sum(displayed_iv[i : i + s], iv.mpf(0)))

    eigenvalues = np.linalg.eigvalsh(hessian(np.array([float(x) for x in root])))
    output = {
        "pressure": 3000,
        "stationary_gaps": gap_strings,
        "displayed_decimal_gaps": displayed,
        "sum": mp.nstr(mp.fsum(root), 70),
        "W": mp.nstr(energy, 70),
        "F": mp.nstr(value, 80),
        "gradient_inf": mp.nstr(max(abs(x) for x in gradient(*root)), 12),
        "hessian_eigenvalues": [format(float(x), ".16g") for x in eigenvalues],
        "displayed_point_interval_lower": endpoint(interval_value, False, 60),
        "displayed_point_interval_upper": endpoint(interval_value, True, 60),
        "global_certificate": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
