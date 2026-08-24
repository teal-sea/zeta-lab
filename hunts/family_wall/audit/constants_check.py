#!/usr/bin/env python3
"""High-precision constants and closed-form-versus-quadrature checks."""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp

from interval_verify import endpoint


def main() -> None:
    mp.mp.dps = 100
    q = 1 / mp.sqrt(2)

    def sinc(z):
        return mp.mpf(1) if z == 0 else mp.sin(z) / z

    def closed(x):
        return (sinc(q - mp.pi * x) + sinc(q + mp.pi * x)) / 2

    points = [mp.mpf(x) for x in ("0", "0.0000001", "0.2250790790392765", "0.5", "1", "3.75", "19")]
    errors = []
    for x in points:
        quadrature = mp.quad(
            lambda t: mp.cos(mp.sqrt(2) * t) * mp.cos(2 * mp.pi * x * t),
            [-mp.mpf("0.5"), mp.mpf("0.5")],
        )
        errors.append(abs(closed(x) - quadrature))

    kzero = sinc(q)
    h = mp.mpf(3) / 2 - q / mp.tan(q)

    mp.iv.dps = 100
    mp.mp.dps = 140
    iv = mp.iv
    qi = 1 / iv.sqrt(2)
    kzero_i = iv.sin(qi) / qi
    h_i = iv.mpf(3) / 2 - qi / iv.tan(qi)
    output = {
        "K0": mp.nstr(kzero, 90),
        "H": mp.nstr(h, 90),
        "K0_interval_lower": endpoint(kzero_i, False, 60),
        "K0_interval_upper": endpoint(kzero_i, True, 60),
        "H_interval_lower": endpoint(h_i, False, 60),
        "H_interval_upper": endpoint(h_i, True, 60),
        "closed_form_quadrature_points": [mp.nstr(x, 25) for x in points],
        "maximum_closed_form_quadrature_error": mp.nstr(max(errors), 20),
        "claimed_W_threshold": mp.nstr(mp.mpf("0.6751676068") / h - 1, 80),
        "target_W_threshold": mp.nstr(mp.mpf("0.6818286874638") / h - 1, 80),
    }
    path = Path("results/constants.json")
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
