"""Independent rival-gate calculations for li_arithmetic.

No module from the mechanism is imported.  Small Li coefficients come from a
local Cauchy extractor.  The high-index W_1/4 check is a separate zero-side
calculation using the public zeta zero table.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from mpmath import mp

from zeta.core import xi
from zeta.epstein import (
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    completed_dh,
    dh_coefficient,
    dh_f,
    epstein_representation_count,
    epstein_zeta,
    shifted_completed,
)
from zeta.zeros import first_n_zeros

FORM_116 = (1, 1, 6)
EPSTEIN_ZERO = ("0.9532604748", "16.2902157204")
GAMMA_1 = "14.1347251417346937904572519836"


def _prime_power(n: int) -> bool:
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
    with mp.workdps(dps):
        a1 = mp.mpf(coefficient(1))
        b = [mp.mpf(0)] + [mp.mpf(coefficient(n)) / a1 for n in range(1, n_max + 1)]
        lam = [mp.mpf(0)] * (n_max + 1)
        for n in range(2, n_max + 1):
            value = b[n] * mp.log(n)
            for d in range(2, n):
                if n % d == 0:
                    value -= lam[d] * b[n // d]
            lam[n] = value
        return lam


def coefficient_gate(coefficient, n_max: int = 60) -> dict:
    lam = log_derivative_coefficients(coefficient, n_max)
    negative = next(((n, lam[n]) for n in range(2, n_max + 1) if lam[n] < -mp.mpf("1e-35")), None)
    off_support = next(
        ((n, lam[n]) for n in range(2, n_max + 1) if not _prime_power(n) and abs(lam[n]) > mp.mpf("1e-35")),
        None,
    )
    return {
        "first_negative": None if negative is None else [negative[0], mp.nstr(negative[1], 18)],
        "first_non_prime_power": None
        if off_support is None
        else [off_support[0], mp.nstr(off_support[1], 18)],
    }


def _unwrap(arguments):
    out = [arguments[0]]
    for value in arguments[1:]:
        while value - out[-1] > mp.pi:
            value -= 2 * mp.pi
        while value - out[-1] < -mp.pi:
            value += 2 * mp.pi
        out.append(value)
    return out


def li_cauchy(completed, n_max: int = 12, radius="0.4", nodes: int = 512, dps: int = 50):
    """Extract n[z^n] log F(1/(1-z)) by a roots-of-unity sum."""
    with mp.workdps(dps):
        radius = mp.mpf(radius)
        zs = [radius * mp.exp(2 * mp.pi * mp.j * k / nodes) for k in range(nodes)]
        values = [completed(1 / (1 - z)) for z in zs]
        phases = _unwrap([mp.arg(value) for value in values])
        logs = [mp.log(abs(value)) + mp.j * phase for value, phase in zip(values, phases)]
        result = []
        for n in range(1, n_max + 1):
            coefficient = mp.fsum(
                logs[k] * mp.exp(-2 * mp.pi * mp.j * n * k / nodes)
                for k in range(nodes)
            ) / (nodes * radius**n)
            result.append(n * mp.re(coefficient))
        return result


def _rs_theta(t):
    return mp.im(mp.loggamma(mp.mpc(mp.mpf(1) / 4, t / 2))) - t * mp.log(mp.pi) / 2


def _density(t):
    return (
        mp.re(mp.digamma(mp.mpc(mp.mpf(1) / 4, t / 2))) / 2
        - mp.log(mp.pi) / 2
    ) / mp.pi


def _wa_quadruple_term(n: int, gamma, shift):
    right_zero = mp.mpc(mp.mpf(1) / 2 + shift, gamma)
    image = 1 - 1 / right_zero
    logarithm = mp.log(image)
    return 4 - 2 * (
        mp.exp(n * mp.re(logarithm)) + mp.exp(-n * mp.re(logarithm))
    ) * mp.cos(n * mp.im(logarithm))


def wa_li_zero_side(
    n: int = 8260,
    shift="0.25",
    zero_count: int = 1000,
    dps: int = 30,
):
    """Li coefficient of W_a from zero quadruples and the smooth tail."""
    gammas = first_n_zeros(zero_count, cache=True, dps=30)
    with mp.workdps(dps + 10):
        shift = mp.mpf(shift)
        target = mp.pi * (mp.mpf(zero_count) - mp.mpf(1) / 2)
        cutoff = mp.findroot(lambda t: _rs_theta(t) - target, gammas[-1] + 1)
        discrepancy = mp.mpf(zero_count) - _rs_theta(cutoff) / mp.pi - 1
        head = mp.fsum(_wa_quadruple_term(n, gamma, shift) for gamma in gammas)
        tail = mp.quad(
            lambda t: _wa_quadruple_term(n, t, shift) * _density(t),
            [cutoff, 2 * cutoff, 10 * cutoff, 100 * cutoff, mp.inf],
        )
        value = head + tail - _wa_quadruple_term(n, cutoff, shift) * discrepancy
        return {
            "n": n,
            "shift": mp.nstr(shift, 12),
            "zero_count": zero_count,
            "cutoff": mp.nstr(cutoff, 18),
            "value": mp.nstr(value, 18),
        }


def shifted_zeta(delta="0.1", dps: int = 50) -> dict:
    with mp.workdps(dps):
        delta = mp.mpf(delta)
        zero = mp.mpc(mp.mpf("0.5") + delta, GAMMA_1)
        test = mp.mpc("0.37", "7.25")
        value = xi(test - delta, dps=dps)
        actual = xi(1 + 2 * delta - test - delta, dps=dps)
        fixed = xi(1 - test - delta, dps=dps)
        return {
            "delta": mp.nstr(delta, 12),
            "local_modulus_at_2": mp.nstr(mp.power(2, delta), 18),
            "actual_center": mp.nstr(mp.mpf("0.5") + delta, 12),
            "actual_defect": mp.nstr(abs(value - actual), 12),
            "fixed_center_defect": mp.nstr(abs(value - fixed), 12),
            "zero_residual": mp.nstr(abs(xi(zero - delta, dps=dps)), 12),
        }


def report() -> dict:
    with mp.workdps(50):
        zeta_li = li_cauchy(lambda s: xi(s, dps=55), dps=50)
        dh_li = li_cauchy(lambda s: completed_dh(s, dps=55), dps=50)
        coefficient_rows = {
            "zeta": coefficient_gate(lambda n: mp.mpf(1)),
            "davenport_heilbronn": coefficient_gate(lambda n: dh_coefficient(n, dps=50)),
            "epstein_1_1_6": coefficient_gate(lambda n: epstein_representation_count(n, FORM_116)),
            "W_1_4": coefficient_gate(
                lambda n: mp.fsum(mp.power(d, -mp.mpf(1) / 4) * mp.power(n // d, mp.mpf(1) / 4)
                                  for d in range(1, n + 1) if n % d == 0)
            ),
            "zeta_shift_delta_0_1": coefficient_gate(lambda n: mp.power(n, mp.mpf("0.1"))),
        }
        epstein_zero = mp.mpc(*EPSTEIN_ZERO)
        wa_zero = mp.mpc(mp.mpf("0.75"), GAMMA_1)
        dh_zero = mp.mpc(OFFLINE_ZERO_RE, OFFLINE_ZERO_IM)
        return {
            "parameters": {"coefficient_n_max": 60, "small_li_n_max": 12},
            "small_li": {
                "zeta": [mp.nstr(value, 18) for value in zeta_li],
                "davenport_heilbronn": [mp.nstr(value, 18) for value in dh_li],
            },
            "coefficient_gate": coefficient_rows,
            "W_1_4_li": wa_li_zero_side(),
            "shifted_zeta": shifted_zeta(),
            "zero_residuals": {
                "davenport_heilbronn": mp.nstr(abs(dh_f(dh_zero, dps=50)), 12),
                "epstein_1_1_6": mp.nstr(abs(epstein_zeta(epstein_zero, FORM_116, dps=50)), 12),
                "W_1_4": mp.nstr(abs(shifted_completed(wa_zero, mp.mpf(1) / 4, dps=50)), 12),
            },
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
