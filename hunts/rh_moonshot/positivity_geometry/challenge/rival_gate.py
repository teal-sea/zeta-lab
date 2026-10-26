"""Independent rival-gate calculations for positivity_geometry.

This file deliberately does not import the mechanism's modules.  It uses only
the public rival functions in ``zeta.epstein`` and implements the logarithmic
derivative recurrence and the golden-fake arithmetic locally.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from mpmath import mp

from zeta.core import xi
from zeta.epstein import (
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    dh_coefficient,
    dh_f,
    epstein_representation_count,
    epstein_zeta,
    shifted_coefficient,
    shifted_completed,
)

FORM_116 = (1, 1, 6)
EPSTEIN_ZERO = ("0.9532604748", "16.2902157204")
GAMMA_1 = "14.1347251417346937904572519836"
DELTA = mp.mpf("0.1")


def _prime_power(n: int) -> bool:
    """Return whether n is p^a for a prime p, using integer arithmetic."""
    if n < 2:
        return False
    p = 2
    while p * p <= n and n % p:
        p += 1
    if n % p:
        return True
    while n % p == 0:
        n //= p
    return n == 1


def log_derivative_coefficients(coefficient, n_max: int, dps: int = 50):
    """Recover Lambda_F from Dirichlet coefficients by a local recurrence."""
    with mp.workdps(dps):
        a1 = mp.mpf(coefficient(1))
        if not a1:
            raise ValueError("a_1 must be nonzero")
        b = [mp.mpf(0)] + [mp.mpf(coefficient(n)) / a1 for n in range(1, n_max + 1)]
        lam = [mp.mpf(0)] * (n_max + 1)
        for n in range(2, n_max + 1):
            value = b[n] * mp.log(n)
            for d in range(2, n):
                if n % d == 0:
                    value -= lam[d] * b[n // d]
            lam[n] = value
        return lam


def first_negative(lam, tolerance=mp.mpf("1e-35")):
    for n, value in enumerate(lam[2:], 2):
        if value < -tolerance:
            return n, value
    return None


def first_off_prime_power(lam, tolerance=mp.mpf("1e-35")):
    for n, value in enumerate(lam[2:], 2):
        if not _prime_power(n) and abs(value) > tolerance:
            return n, value
    return None


def coefficient_defect(coefficient, m: int, n: int):
    a1 = mp.mpf(coefficient(1))
    return mp.mpf(coefficient(m * n)) / a1 - (
        mp.mpf(coefficient(m)) / a1
    ) * (mp.mpf(coefficient(n)) / a1)


def _mobius(n: int) -> int:
    value = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    return -value if n > 1 else value


def golden_fake(n_max: int = 80) -> dict:
    """Compute the fake's traces, point counts, and closed-place counts exactly."""
    q, a = 5, 5
    traces = [2, a]
    for _ in range(2, n_max + 1):
        traces.append(a * traces[-1] - q * traces[-2])
    points = [0] + [q**n + 1 - traces[n] for n in range(1, n_max + 1)]
    places = []
    for n in range(1, n_max + 1):
        total = sum(_mobius(d) * points[n // d] for d in range(1, n + 1) if n % d == 0)
        assert total % n == 0
        places.append(total // n)
    with mp.workdps(60):
        alpha = (a + mp.sqrt(a * a - 4 * q)) / 2
        beta = q / alpha
        ratios = [alpha / mp.sqrt(q), beta / mp.sqrt(q)]
    return {
        "points_1_to_6": points[1:7],
        "places_1_to_6": places[:6],
        "minimum_place_count_to_n_max": min(places),
        "n_max": n_max,
        "normalized_root_moduli": [mp.nstr(x, 30) for x in ratios],
        "castelnuovo_severi_margin_n1": 4 * q - a * a,
    }


def shifted_symmetry(delta=DELTA, dps: int = 50) -> dict:
    """Check the actual and incorrectly fixed symmetry centers for xi(s-delta)."""
    with mp.workdps(dps):
        delta = mp.mpf(delta)
        s = mp.mpc("0.37", "7.25")
        value = xi(s - delta, dps=dps)
        actual = xi(1 + 2 * delta - s - delta, dps=dps)
        fixed = xi(1 - s - delta, dps=dps)
        return {
            "delta": mp.nstr(delta, 12),
            "actual_center": mp.nstr(mp.mpf("0.5") + delta, 12),
            "actual_symmetry_defect": mp.nstr(abs(value - actual), 12),
            "fixed_half_symmetry_defect": mp.nstr(abs(value - fixed), 12),
            "pole": mp.nstr(1 + delta, 12),
        }


def report(n_max: int = 60, dps: int = 50) -> dict:
    with mp.workdps(dps):
        coefficient_rows = {
            "zeta": lambda n: mp.mpf(1),
            "davenport_heilbronn": lambda n: dh_coefficient(n, dps=dps),
            "epstein_1_1_6": lambda n: epstein_representation_count(n, FORM_116),
            "W_1_4": lambda n: shifted_coefficient(n, mp.mpf(1) / 4, dps=dps),
            "zeta_shift_delta_0_1": lambda n: mp.mpf(n) ** DELTA,
        }
        arithmetic = {}
        for name, coefficient in coefficient_rows.items():
            lam = log_derivative_coefficients(coefficient, n_max, dps=dps)
            neg = first_negative(lam)
            off = first_off_prime_power(lam)
            arithmetic[name] = {
                "first_negative": None if neg is None else [neg[0], mp.nstr(neg[1], 18)],
                "first_non_prime_power": None if off is None else [off[0], mp.nstr(off[1], 18)],
                "coefficient_defect_2_3": mp.nstr(coefficient_defect(coefficient, 2, 3), 18),
            }

        dh_zero = mp.mpc(str(OFFLINE_ZERO_RE), str(OFFLINE_ZERO_IM))
        epstein_zero = mp.mpc(*EPSTEIN_ZERO)
        zeta_shift_zero = mp.mpc(mp.mpf("0.5") + DELTA, GAMMA_1)
        wa_zero = mp.mpc(mp.mpf("0.75"), GAMMA_1)
        zero_residuals = {
            "davenport_heilbronn": mp.nstr(abs(dh_f(dh_zero, dps=dps)), 12),
            "epstein_1_1_6": mp.nstr(abs(epstein_zeta(epstein_zero, FORM_116, dps=dps)), 12),
            "W_1_4": mp.nstr(abs(shifted_completed(wa_zero, mp.mpf(1) / 4, dps=dps)), 12),
            "zeta_shift_delta_0_1": mp.nstr(abs(xi(zeta_shift_zero - DELTA, dps=dps)), 12),
        }

        return {
            "parameters": {"n_max": n_max, "dps": dps, "delta": "0.1"},
            "arithmetic": arithmetic,
            "zero_residuals": zero_residuals,
            "shifted_zeta_normalization": shifted_symmetry(DELTA, dps=dps),
            "golden_fake": golden_fake(80),
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()
    payload = report()
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
