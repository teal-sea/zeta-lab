"""Independent rival-gate calculations for probe_tower.

The exact template algebra is reimplemented with ``Fraction``.  Rival checks
use the public functions in ``zeta.epstein`` and no mechanism module.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

from mpmath import mp

from zeta.core import xi
from zeta.epstein import (
    L_chi,
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    dh_coefficient,
    dh_f,
    epstein_representation_count,
    epstein_zeta,
    kappa,
    shifted_completed,
)

F = Fraction
FORM_116 = (1, 1, 6)
EPSTEIN_ZERO = ("0.9532604748", "16.2902157204")
GAMMA_1 = "14.1347251417346937904572519836"


def sigma0(k: int, ell: F, total: F) -> F:
    """Boundary from a comparison pole 1/k and the paper-form geometry."""
    return F(1) - F(1, k) + (total - 2 * ell) / (2 * k)


def tower_increment(k: int, ell: F, total: F) -> F:
    return sigma0(k + 1, ell, total) - sigma0(k, ell, total)


def dual_length_wall(k: int) -> F:
    return F(1) - F(2, k)


def floor_wall(k: int, delta0: F = F(0)) -> F:
    return F(1) - F(4, (5 + 6 * delta0) * k)


def floor_dual_identity(k: int, delta0: F, ell: F, total: F, offset: F):
    """Return both sides of the LP dual identity used for the floor wall."""
    denom = 5 + 6 * delta0
    mstar = (2 + 12 * delta0) / denom
    y1 = 12 / denom
    y2 = 4 / denom
    y3 = y1 * (F(1, 4) - F(1, 2 * k))
    floor_expr = (
        F(1, 2)
        + ell / 2
        - 3 * total / 4
        + offset * (F(1, 4) - F(1, 2 * k))
        + (1 + ell - total / 2) * delta0
    )
    left = (total - 2 * ell) - mstar
    right = y1 * (-floor_expr) + y2 * (1 - total - ell) + y3 * offset
    return left, right, (y1, y2, y3, mstar)


def _mobius_table(limit: int) -> list[int]:
    mu = [1] * (limit + 1)
    prime = [True] * (limit + 1)
    mu[0] = 0
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p, limit + 1, p):
                prime[n] = False if n != p else prime[n]
                mu[n] *= -1
            square = p * p
            for n in range(square, limit + 1, square):
                mu[n] = 0
    return mu


def _primes(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (((limit - p * p) // p) + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def squarefree_row(coefficient, s, limit: int = 20_000):
    mu = _mobius_table(limit)
    with mp.workdps(50):
        return mp.fsum(
            mu[n] * coefficient(n) * mp.power(n, -s)
            for n in range(1, limit + 1)
            if mu[n]
        )


def dh_reciprocal_check(dps: int = 50) -> dict:
    with mp.workdps(dps):
        kap = kappa(dps=dps)
        c1 = (1 - mp.j * kap) / 2
        c2 = mp.conj(c1)

        def visible(s):
            return c1 / L_chi(s, dps=dps) + c2 / L_chi(s, conjugate=True, dps=dps)

        s2 = mp.mpf(2)
        row = squarefree_row(lambda n: dh_coefficient(n, dps=dps), s2)
        closed = visible(s2)
        scalar = 1 / dh_f(s2, dps=dps)
        rho = mp.mpc(OFFLINE_ZERO_RE, OFFLINE_ZERO_IM)
        h_at_zero = dh_f(rho, dps=dps) * visible(rho)
        return {
            "squarefree_row_s2": mp.nstr(row, 18),
            "constituent_reciprocals_s2": mp.nstr(closed, 18),
            "row_to_constituents_gap": mp.nstr(abs(row - closed), 12),
            "row_to_scalar_reciprocal_gap": mp.nstr(abs(row - scalar), 12),
            "zero_residual": mp.nstr(abs(dh_f(rho, dps=dps)), 12),
            "H_minus_1_at_zero": mp.nstr(abs(h_at_zero - 1), 12),
        }


def shifted_zeta_check(delta=mp.mpf("0.1"), dps: int = 50) -> dict:
    with mp.workdps(dps):
        delta = mp.mpf(delta)
        s = mp.mpf(2)
        row = squarefree_row(lambda n: mp.power(n, delta), s)
        reciprocal = 1 / mp.zeta(s - delta)
        zero = mp.mpc(mp.mpf("0.5") + delta, GAMMA_1)
        return {
            "delta": mp.nstr(delta, 12),
            "squarefree_row_s2": mp.nstr(row, 18),
            "reciprocal_s2": mp.nstr(reciprocal, 18),
            "truncation_gap": mp.nstr(abs(row - reciprocal), 12),
            "local_modulus_at_2": mp.nstr(mp.power(2, delta), 18),
            "actual_symmetry_center": mp.nstr(mp.mpf("0.5") + delta, 12),
            "zero_residual": mp.nstr(abs(xi(zero - delta, dps=dps)), 12),
        }


def wa_correction(s, shift=mp.mpf("0.25"), prime_limit: int = 100_000, dps: int = 50):
    """Finite Euler-product route to the squarefree correction for W_a."""
    with mp.workdps(dps):
        s, shift = mp.mpc(s), mp.mpf(shift)
        product = mp.mpc(1)
        for p in _primes(prime_limit):
            p = mp.mpf(p)
            product *= 1 - mp.power(p, -2 * s) / (
                (1 - mp.power(p, shift - s)) * (1 - mp.power(p, -shift - s))
            )
        return product


def wa_check(dps: int = 50) -> dict:
    with mp.workdps(dps):
        shift = mp.mpf("0.25")
        zero = mp.mpc(mp.mpf("0.75"), GAMMA_1)
        correction = wa_correction(zero, shift, dps=dps)
        return {
            "zero_residual": mp.nstr(abs(shifted_completed(zero, shift, dps=dps)), 12),
            "prime_limit": 100_000,
            "correction_minus_1_at_zero": mp.nstr(abs(correction - 1), 12),
            "local_root_moduli_at_2": [
                mp.nstr(mp.power(2, shift), 18),
                mp.nstr(mp.power(2, -shift), 18),
            ],
        }


def epstein_check(dps: int = 50) -> dict:
    with mp.workdps(dps):
        a1 = epstein_representation_count(1, FORM_116)
        defect = epstein_representation_count(6, FORM_116) / a1 - (
            epstein_representation_count(2, FORM_116) / a1
        ) * (epstein_representation_count(3, FORM_116) / a1)
        zero = mp.mpc(*EPSTEIN_ZERO)
        return {
            "coefficient_defect_2_3": mp.nstr(defect, 18),
            "zero_residual": mp.nstr(abs(epstein_zeta(zero, FORM_116, dps=dps)), 12),
        }


def exact_template_report() -> dict:
    paper = (F(1, 6), F(5, 6))
    rows = {}
    for k in (2, 3, 4, 5, 6, 7, 8, 12, 100):
        rows[str(k)] = {
            "paper_geometry": str(sigma0(k, *paper)),
            "dual_length_wall": str(dual_length_wall(k)),
            "floor_wall_limit": str(floor_wall(k)),
        }
    return {
        "rows": rows,
        "paper_k6": str(sigma0(6, *paper)),
        "paper_increment_k6_to_k7": str(tower_increment(6, *paper)),
        "best_floor_wall_k_ge_2": str(min(floor_wall(k) for k in range(2, 201))),
        "formal_k1_balanced": str(sigma0(1, F(0), F(1))),
    }


def report(dps: int = 50) -> dict:
    return {
        "parameters": {"dps": dps, "squarefree_limit": 20_000},
        "template": exact_template_report(),
        "davenport_heilbronn": dh_reciprocal_check(dps=dps),
        "epstein_1_1_6": epstein_check(dps=dps),
        "W_1_4": wa_check(dps=dps),
        "zeta_shift_delta_0_1": shifted_zeta_check(dps=dps),
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
