"""Independent rival gate for the finite CCM spectral operator.

This file directly assembles the truncated Weil form and the rank-one
operator.  It imports no mechanism or other-hunt module.  Public zeta routines
provide only Dirichlet coefficients and the stated rival-zero diagnostics.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from mpmath import mp

from zeta.core import xi
from zeta.epstein import (
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    dh_coefficient,
    epstein_representation_count,
)

FORM_116 = (1, 1, 6)
GAMMA_1 = "14.1347251417346937904572519836"
EPSTEIN_ZERO = ("0.9532604748", "16.2902157204")
SHIFT_DELTA = "0.1"


def _prime_base(n: int) -> int | None:
    for p in range(2, int(math.sqrt(n)) + 2):
        if n % p == 0:
            value = n
            while value % p == 0:
                value //= p
            return p if value == 1 else None
    return n if n >= 2 else None


def _log_derivative(coefficient, n_max: int):
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


def _arch_sequences(c, band: int, parameter, conductor_term, dps: int):
    length = mp.log(c)
    terms = int(mp.ceil((dps + 20) * mp.log(10) / (2 * length))) + 5
    mus = [2 * (j + parameter) for j in range(terms)]
    exponentials = [mp.exp(-mu * length) for mu in mus]
    tail_integral = mp.fsum(e / mu for e, mu in zip(exponentials, mus))
    psi_a = mp.digamma(parameter)
    sine, diagonal = [], []
    for k in range(band + 1):
        omega = 2 * mp.pi * k / length
        psi0 = mp.digamma(parameter + mp.j * omega / 2)
        psi1 = mp.polygamma(1, parameter + mp.j * omega / 2)
        if k == 0:
            sine.append(mp.mpf(0))
            cosine_sum = mp.mpf(0)
        else:
            sine.append(
                mp.im(psi0) / 2
                - mp.fsum(e * omega / (mu * mu + omega * omega)
                          for e, mu in zip(exponentials, mus))
            )
            cosine_sum = -(mp.re(psi0) - psi_a) / 2 + mp.fsum(
                e * omega * omega / (mu * (mu * mu + omega * omega))
                for e, mu in zip(exponentials, mus)
            )
        geometric_x = mp.fsum(
            e
            * ((mu * mu - omega * omega) / (mu * mu + omega * omega) ** 2
               + mu * length / (mu * mu + omega * omega))
            for e, mu in zip(exponentials, mus)
        )
        x_cosine_sum = mp.re(psi1) / 4 - geometric_x
        dg = 2 * cosine_sum - 2 * x_cosine_sum / length
        diagonal.append(conductor_term + psi_a - dg + 2 * tail_integral)
    return sine, diagonal


def _prime_sequences(c, band: int, coefficients):
    length = mp.log(c)
    sine = [mp.mpf(0)] * (band + 1)
    diagonal = [mp.mpf(0)] * (band + 1)
    for n, value in coefficients:
        y = mp.log(n)
        weight = value / mp.sqrt(n)
        for k in range(band + 1):
            omega = 2 * mp.pi * k / length
            sine[k] += weight * mp.sin(omega * y)
            diagonal[k] += 2 * weight * (1 - y / length) * mp.cos(omega * y)
    return sine, diagonal


def _prime_coefficients(kind: str, c):
    n_max = int(mp.floor(c))
    if kind == "zeta":
        return [(n, mp.log(p)) for n in range(2, n_max + 1)
                if (p := _prime_base(n)) is not None]
    if kind == "zeta_shift_recentered":
        delta = mp.mpf(SHIFT_DELTA)
        center = mp.mpf(1) / 2 + delta
        return [
            (n, mp.log(p) * mp.power(n, delta) * mp.power(n, mp.mpf(1) / 2 - center))
            for n in range(2, n_max + 1)
            if (p := _prime_base(n)) is not None
        ]
    if kind == "dh":
        lam = _log_derivative(lambda n: dh_coefficient(n, dps=60), n_max)
        return [(n, lam[n]) for n in range(2, n_max + 1)]
    if kind == "epstein":
        lam = _log_derivative(lambda n: epstein_representation_count(n, FORM_116), n_max)
        return [(n, lam[n]) for n in range(2, n_max + 1)]
    if kind == "wa":
        shift = mp.mpf(1) / 4
        return [
            (n, mp.log(p) * (mp.power(n, shift) + mp.power(n, -shift)))
            for n in range(2, n_max + 1)
            if (p := _prime_base(n)) is not None
        ]
    raise ValueError(kind)


def _signed(sequence, index: int):
    return sequence[index] if index >= 0 else -sequence[-index]


def _entry(sine, diagonal, prime_sine, prime_diagonal, n: int, m: int):
    if n == m:
        return diagonal[abs(n)] - prime_diagonal[abs(n)]
    tm = _signed(sine, m) + _signed(prime_sine, m)
    tn = _signed(sine, n) + _signed(prime_sine, n)
    return -(tm - tn) / (mp.pi * (n - m))


def _components(kind: str, c, band: int, dps: int):
    zero = [mp.mpf(0)] * (band + 1)
    prime_sine, prime_diagonal = _prime_sequences(
        c, band, _prime_coefficients(kind, c)
    )
    identity = mp.mpf(0)
    poles = []
    pieces = []
    if kind in {"zeta", "zeta_shift_recentered", "dh"}:
        if kind == "zeta_shift_recentered":
            delta = mp.mpf(SHIFT_DELTA)
            center = mp.mpf(1) / 2 + delta
            parameter = (center - delta) / 2
            conductor = -mp.log(mp.pi)
        else:
            parameter = mp.mpf(1) / 4 if kind == "zeta" else mp.mpf(3) / 4
            conductor = -mp.log(mp.pi) if kind == "zeta" else -mp.log(mp.pi / 5)
        sine, diagonal = _arch_sequences(c, band, parameter, conductor, dps)
        pieces.append((sine, diagonal, prime_sine, prime_diagonal))
        if kind != "dh":
            poles = [mp.mpf(1) / 2]
    elif kind == "epstein":
        s1, d1 = _arch_sequences(c, band, mp.mpf(1) / 4, -mp.log(mp.pi), dps)
        s2, d2 = _arch_sequences(c, band, mp.mpf(3) / 4, -mp.log(mp.pi / 5), dps)
        pieces.extend([(s1, d1, zero, zero), (s2, d2, zero, zero)])
        pieces.append((zero, zero, prime_sine, prime_diagonal))
        identity = mp.log(mp.mpf(23) / 5)
        poles = [mp.mpf(1) / 2]
    elif kind == "wa":
        shift = mp.mpf(1) / 4
        for parameter in (mp.mpf(1) / 4 + shift / 2, mp.mpf(1) / 4 - shift / 2):
            sine, diagonal = _arch_sequences(c, band, parameter, -mp.log(mp.pi), dps)
            pieces.append((sine, diagonal, zero, zero))
        pieces.append((zero, zero, prime_sine, prime_diagonal))
        poles = [mp.mpf(1) / 2 + shift, mp.mpf(1) / 2 - shift]
    else:
        raise ValueError(kind)
    return pieces, identity, poles


def form_matrices(kind: str, c, band: int, dps: int = 60):
    """Return full, even and odd truncated-form matrices."""
    with mp.workdps(dps):
        c = mp.mpf(c)
        pieces, identity, poles = _components(kind, c, band, dps)
        size = 2 * band + 1
        full = mp.matrix(size)
        even = mp.matrix(band + 1)
        odd = mp.matrix(band)
        for sine, diagonal, prime_sine, prime_diagonal in pieces:
            for n in range(-band, band + 1):
                for m in range(-band, band + 1):
                    full[n + band, m + band] += _entry(
                        sine, diagonal, prime_sine, prime_diagonal, n, m
                    )
            even[0, 0] += _entry(sine, diagonal, prime_sine, prime_diagonal, 0, 0)
            for k in range(1, band + 1):
                value = mp.sqrt(2) * _entry(
                    sine, diagonal, prime_sine, prime_diagonal, 0, k
                )
                even[0, k] += value
                even[k, 0] += value
            for j in range(1, band + 1):
                for k in range(1, band + 1):
                    plus = _entry(sine, diagonal, prime_sine, prime_diagonal, j, k)
                    reflected = _entry(sine, diagonal, prime_sine, prime_diagonal, j, -k)
                    even[j, k] += plus + reflected
                    odd[j - 1, k - 1] += plus - reflected
        for i in range(size):
            full[i, i] += identity
        for i in range(band + 1):
            even[i, i] += identity
        for i in range(band):
            odd[i, i] += identity
        length = mp.log(c)
        for beta in poles:
            sh = mp.sinh(beta * length / 2)
            full_even_vector = []
            full_odd_vector = []
            for n in range(-band, band + 1):
                omega = 2 * mp.pi * n / length
                denominator = beta * beta + omega * omega
                full_even_vector.append(2 * beta * sh / denominator)
                full_odd_vector.append(2 * omega * sh / denominator)
            even_vector = [full_even_vector[band]] + [
                mp.sqrt(2) * full_even_vector[band + k] for k in range(1, band + 1)
            ]
            odd_vector = [
                mp.sqrt(2) * full_odd_vector[band + k] for k in range(1, band + 1)
            ]
            for i in range(size):
                for j in range(size):
                    full[i, j] += 2 * (
                        full_even_vector[i] * full_even_vector[j]
                        - full_odd_vector[i] * full_odd_vector[j]
                    ) / length
            for i in range(band + 1):
                for j in range(band + 1):
                    even[i, j] += 2 * even_vector[i] * even_vector[j] / length
            for i in range(band):
                for j in range(band):
                    odd[i, j] -= 2 * odd_vector[i] * odd_vector[j] / length
        return full, even, odd


def _operator_cell(kind: str, c, band: int, beta, gamma, center="0.5", dps: int = 60):
    with mp.workdps(dps):
        full, even, odd = form_matrices(kind, c, band, dps=dps)
        even_values, even_vectors = mp.eigsy(even)
        odd_values = mp.eigsy(odd, eigvals_only=True)
        epsilon = even_values[0]
        gap = min(even_values[1], odd_values[0]) - epsilon
        vector = [even_vectors[i, 0] for i in range(band + 1)]
        half = [vector[k] / mp.sqrt(2) for k in range(1, band + 1)]
        xi_vector = list(reversed(half)) + [vector[0]] + half
        total = mp.fsum(xi_vector)
        xi_vector = [value / total for value in xi_vector]
        indices = list(range(-band, band + 1))
        scale = max(abs(full[i, j] - (epsilon if i == j else 0))
                    for i in range(2 * band + 1) for j in range(2 * band + 1))
        row_terms = [
            mp.fsum(
                (full[i, k] - (epsilon if i == k else 0))
                * indices[k]
                * xi_vector[k]
                for k in range(2 * band + 1)
            )
            for i in range(2 * band + 1)
        ]
        worst = mp.mpf(0)
        for i in range(2 * band + 1):
            for j in range(2 * band + 1):
                wij = full[i, j] - (epsilon if i == j else 0)
                wd_ij = wij * indices[j] - row_terms[i]
                wd_ji = wij * indices[i] - row_terms[j]
                worst = max(worst, abs(wd_ij - wd_ji))
        operator_mp = mp.matrix(2 * band + 1)
        operator = np.empty((2 * band + 1, 2 * band + 1), dtype=float)
        for i, n in enumerate(indices):
            for j in range(2 * band + 1):
                value = (n if i == j else 0) - n * xi_vector[i]
                operator_mp[i, j] = value
                operator[i, j] = float(value)
        spectral_scale = 2 * mp.pi / mp.log(c)
        if kind == "zeta_shift_recentered":
            raw_spectrum = [value * spectral_scale for value in mp.eig(
                operator_mp, left=False, right=False
            )]
            max_imag = max(abs(mp.im(value)) for value in raw_spectrum)
            real_spectrum = sorted(mp.re(value) for value in raw_spectrum if mp.re(value) > 0)
        else:
            raw_spectrum = np.linalg.eigvals(operator) * (2 * math.pi / math.log(float(c)))
            max_imag = max(abs(value.imag) for value in raw_spectrum)
            real_spectrum = sorted(mp.mpf(value.real) for value in raw_spectrum if value.real > 0)
        gamma = mp.mpf(gamma)
        beta = mp.mpf(beta)
        center = mp.mpf(center)
        nearest = min(real_spectrum, key=lambda value: abs(value - gamma))
        offset = abs(beta - center)
        distance = abs(mp.mpc(mp.mpf(nearest) - gamma, offset))
        return {
            "kind": kind,
            "c": str(c),
            "band": band,
            "symmetry_center": mp.nstr(center, 12),
            "epsilon": mp.nstr(epsilon, 18),
            "even_gap": mp.nstr(gap, 18),
            "commutator_defect": mp.nstr(worst / scale, 14),
            "max_abs_spectrum_imag": mp.nstr(max_imag, 14),
            "positive_spectrum_count": len(real_spectrum),
            "spectrum_max": mp.nstr(real_spectrum[-1], 14),
            "off_line_zero_real_offset": mp.nstr(offset, 14),
            "off_line_zero_ordinate": mp.nstr(gamma, 18),
            "nearest_real_spectral_point": mp.nstr(nearest, 14),
            "distance_to_off_line_zero": mp.nstr(distance, 14),
        }


def report() -> dict:
    with mp.workdps(60):
        cells = [
            _operator_cell("dh", 13, 40, OFFLINE_ZERO_RE, OFFLINE_ZERO_IM),
            _operator_cell("epstein", 13, 20, EPSTEIN_ZERO[0], EPSTEIN_ZERO[1]),
            _operator_cell("wa", 2, 8, "0.75", GAMMA_1),
            _operator_cell(
                "zeta_shift_recentered", 13, 16, "0.6", GAMMA_1,
                center="0.6", dps=120
            ),
        ]
        shifted, _, _ = form_matrices("zeta_shift_recentered", 6, 4, dps=60)
        zeta, _, _ = form_matrices("zeta", 6, 4, dps=60)
        translation_defect = max(
            abs(shifted[i, j] - zeta[i, j]) for i in range(9) for j in range(9)
        )
        s = mp.mpc("0.37", "7.25")
        delta = mp.mpf(SHIFT_DELTA)
        fixed_defect = abs(xi(s - delta, dps=60) - xi(1 - s - delta, dps=60))
        return {
            "parameters": {"matrix_dps": 60, "shift_delta": "0.1"},
            "cells": cells,
            "shifted_zeta": {
                "recentered_matrix_defect": mp.nstr(translation_defect, 14),
                "fixed_half_symmetry_defect": mp.nstr(fixed_defect, 14),
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
