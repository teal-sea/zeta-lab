"""Independent float route to the CCM rival gate.

The even-sector matrices are assembled directly from the displayed Galerkin
formulas.  No module in ``ccm_arithmetic`` or another hunt is imported.  The
public completed functions in ``zeta`` supply only the radical diagnostics.
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
    completed_dh,
    dh_coefficient,
    epstein_completed,
    epstein_representation_count,
    shifted_completed,
)

FORM_116 = (1, 1, 6)


def _prime_base(n: int) -> int | None:
    for p in range(2, int(math.sqrt(n)) + 2):
        if n % p == 0:
            value = n
            while value % p == 0:
                value //= p
            return p if value == 1 else None
    return n if n >= 2 else None


def _log_derivative(coefficient, n_max: int):
    with mp.workdps(60):
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


def _arch_sequences(c: float, band: int, parameter, conductor_term, dps: int):
    """Archimedean S_k and diagonal sequence, with a negligible cut tail."""
    with mp.workdps(dps):
        c = mp.mpf(c)
        parameter = mp.mpf(parameter)
        conductor_term = mp.mpf(conductor_term)
        length = mp.log(c)
        z = mp.exp(-2 * length)
        terms = int(mp.ceil((dps + 20) * mp.log(10) / (2 * length))) + 5
        mus = [2 * (j + parameter) for j in range(terms)]
        exponentials = [mp.exp(-mu * length) for mu in mus]
        tail_integral = mp.fsum(e / mu for e, mu in zip(exponentials, mus))
        psi_a = mp.digamma(parameter)
        S, diagonal = [], []
        for k in range(band + 1):
            omega = 2 * mp.pi * k / length
            psi0 = mp.digamma(parameter + mp.j * omega / 2)
            psi1 = mp.polygamma(1, parameter + mp.j * omega / 2)
            if k == 0:
                S.append(mp.mpf(0))
                cosine_sum = mp.mpf(0)
            else:
                geometric = mp.fsum(
                    e * omega / (mu * mu + omega * omega)
                    for e, mu in zip(exponentials, mus)
                )
                S.append(mp.im(psi0) / 2 - geometric)
                geometric1 = mp.fsum(
                    e * omega * omega / (mu * (mu * mu + omega * omega))
                    for e, mu in zip(exponentials, mus)
                )
                cosine_sum = -(mp.re(psi0) - psi_a) / 2 + geometric1
            geometric_x = mp.fsum(
                e
                * (
                    (mu * mu - omega * omega) / (mu * mu + omega * omega) ** 2
                    + mu * length / (mu * mu + omega * omega)
                )
                for e, mu in zip(exponentials, mus)
            )
            x_cosine_sum = mp.re(psi1) / 4 - geometric_x
            dg = 2 * cosine_sum - 2 * x_cosine_sum / length
            diagonal.append(conductor_term + psi_a - dg + 2 * tail_integral)
        return S, diagonal


def _prime_sequences(c: float, band: int, coefficients):
    with mp.workdps(60):
        length = mp.log(c)
        P = [mp.mpf(0)] * (band + 1)
        R = [mp.mpf(0)] * (band + 1)
        for n, value in coefficients:
            y = mp.log(n)
            weight = value / mp.sqrt(n)
            for k in range(band + 1):
                omega = 2 * mp.pi * k / length
                P[k] += weight * mp.sin(omega * y)
                R[k] += 2 * weight * (1 - y / length) * mp.cos(omega * y)
        return P, R


def _sequence_matrix(S, diagonal, P, R):
    band = len(S) - 1

    def signed(sequence, index):
        return sequence[index] if index >= 0 else -sequence[-index]

    def entry(n, m):
        if n == m:
            return diagonal[abs(n)] - R[abs(n)]
        tm = signed(S, m) + signed(P, m)
        tn = signed(S, n) + signed(P, n)
        return -(tm - tn) / (mp.pi * (n - m))

    matrix = mp.matrix(band + 1)
    matrix[0, 0] = entry(0, 0)
    for k in range(1, band + 1):
        value = mp.sqrt(2) * entry(0, k)
        matrix[0, k] = matrix[k, 0] = value
    for j in range(1, band + 1):
        for k in range(j, band + 1):
            value = entry(j, k) + entry(j, -k)
            matrix[j, k] = matrix[k, j] = value
    return matrix


def _pole_matrix(c: float, band: int, betas):
    with mp.workdps(60):
        length = mp.log(c)
        matrix = mp.matrix(band + 1)
        for beta in betas:
            beta = mp.mpf(beta)
            sh = mp.sinh(beta * length / 2)
            vector = [2 * sh / beta]
            for k in range(1, band + 1):
                omega = 2 * mp.pi * k / length
                vector.append(2 * mp.sqrt(2) * beta * sh / (beta * beta + omega * omega))
            for i in range(band + 1):
                for j in range(band + 1):
                    matrix[i, j] += 2 * vector[i] * vector[j] / length
        return matrix


def _add(*matrices):
    result = mp.matrix(matrices[0])
    for matrix in matrices[1:]:
        result += matrix
    return result


def _identity(size: int, scale):
    matrix = mp.matrix(size)
    for i in range(size):
        matrix[i, i] = scale
    return matrix


def _prime_coefficients(kind: str, c: float, shift=mp.mpf("0.25")):
    n_max = int(math.floor(c + 1e-12))
    if kind == "zeta":
        return [
            (n, mp.log(p))
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
        return [
            (n, mp.log(p) * (mp.power(n, shift) + mp.power(n, -shift)))
            for n in range(2, n_max + 1)
            if (p := _prime_base(n)) is not None
        ]
    raise ValueError(kind)


def matrix(kind: str, c: float, band: int, dps: int = 70):
    """Direct assembly of one even-sector truncated form."""
    with mp.workdps(dps):
        zero = [mp.mpf(0)] * (band + 1)
        if kind in {"zeta", "dh"}:
            parameter = mp.mpf(1) / 4 if kind == "zeta" else mp.mpf(3) / 4
            conductor_term = -mp.log(mp.pi) if kind == "zeta" else -mp.log(mp.pi / 5)
            S, diagonal = _arch_sequences(c, band, parameter, conductor_term, dps)
            P, R = _prime_sequences(c, band, _prime_coefficients(kind, c))
            base = _sequence_matrix(S, diagonal, P, R)
            return _add(base, _pole_matrix(c, band, [mp.mpf(1) / 2])) if kind == "zeta" else base
        if kind == "epstein":
            s1, d1 = _arch_sequences(c, band, mp.mpf(1) / 4, -mp.log(mp.pi), dps)
            s2, d2 = _arch_sequences(c, band, mp.mpf(3) / 4, -mp.log(mp.pi / 5), dps)
            P, R = _prime_sequences(c, band, _prime_coefficients(kind, c))
            a1 = _sequence_matrix(s1, d1, zero, zero)
            a2 = _sequence_matrix(s2, d2, zero, zero)
            prime = _sequence_matrix(zero, zero, P, R)
            return _add(
                a1,
                a2,
                prime,
                _identity(band + 1, mp.log(mp.mpf(23) / 5)),
                _pole_matrix(c, band, [mp.mpf(1) / 2]),
            )
        if kind == "wa":
            shift = mp.mpf(1) / 4
            pieces = []
            for parameter in (mp.mpf(1) / 4 + shift / 2, mp.mpf(1) / 4 - shift / 2):
                S, diagonal = _arch_sequences(c, band, parameter, -mp.log(mp.pi), dps)
                pieces.append(_sequence_matrix(S, diagonal, zero, zero))
            P, R = _prime_sequences(c, band, _prime_coefficients(kind, c, shift))
            pieces.append(_sequence_matrix(zero, zero, P, R))
            pieces.append(_pole_matrix(c, band, [mp.mpf(1) / 2 + shift, mp.mpf(1) / 2 - shift]))
            return _add(*pieces)
        raise ValueError(kind)


def ground_pair(kind: str, c: float, band: int, dps: int = 70):
    with mp.workdps(dps):
        form = matrix(kind, c, band, dps=dps)
        values, vectors = mp.eigsy(form)
        vector = [vectors[i, 0] for i in range(band + 1)]
        as_float = np.array(
            [[float(form[i, j]) for j in range(band + 1)] for i in range(band + 1)]
        )
        numpy_value = np.linalg.eigvalsh(as_float)[0]
        return values[0], vector, numpy_value


def _completed(kind: str, t, dps: int):
    s = mp.mpf(1) / 2 + mp.j * t
    if kind == "zeta":
        return xi(s, dps=dps)
    if kind == "dh":
        return completed_dh(s, dps=dps)
    if kind == "epstein":
        return epstein_completed(s, FORM_116, dps=dps)
    if kind == "wa":
        return shifted_completed(s, mp.mpf(1) / 4, dps=dps)
    raise ValueError(kind)


def radical_misfit(kind: str, c: float, vector, dps: int = 50):
    with mp.workdps(dps):
        length = mp.log(c)
        radical = [mp.re(_completed(kind, 0, dps)) / mp.sqrt(length)]
        for k in range(1, len(vector)):
            omega = 2 * mp.pi * k / length
            radical.append(
                mp.sqrt(2 / length) * (-1) ** k * mp.re(_completed(kind, omega, dps))
            )
        dot = mp.fsum(a * b for a, b in zip(vector, radical))
        nv = mp.fsum(a * a for a in vector)
        nr = mp.fsum(a * a for a in radical)
        return 1 - dot * dot / (nv * nr)


def cell(kind: str, c: float, band: int, capture: bool, dps: int = 70) -> dict:
    value, vector, numpy_value = ground_pair(kind, c, band, dps=dps)
    row = {
        "kind": kind,
        "c": str(c),
        "band": band,
        "lambda_1": mp.nstr(value, 16),
        "lambda_1_numpy": f"{numpy_value:.16e}",
    }
    if capture:
        row["radical_misfit"] = mp.nstr(radical_misfit(kind, c, vector, dps=50), 16)
    return row


def shifted_normalization(delta=mp.mpf("0.1"), dps: int = 50):
    with mp.workdps(dps):
        s = mp.mpc("0.37", "7.25")
        value = xi(s - delta, dps=dps)
        actual = xi(1 + 2 * delta - s - delta, dps=dps)
        fixed = xi(1 - s - delta, dps=dps)
        return {
            "delta": mp.nstr(delta, 12),
            "actual_center": mp.nstr(mp.mpf("0.5") + delta, 12),
            "actual_defect": mp.nstr(abs(value - actual), 12),
            "fixed_center_defect": mp.nstr(abs(value - fixed), 12),
        }


def report() -> dict:
    cells = [
        cell("dh", 31, 64, True),
        cell("dh", 33, 64, True),
        cell("epstein", 29, 32, False),
        cell("epstein", 29.5, 32, False),
        cell("wa", 2, 32, True),
        cell("wa", 3, 32, True),
    ]
    return {
        "parameters": {"matrix_dps": 70, "radical_dps": 50},
        "cells": cells,
        "shifted_zeta_normalization": shifted_normalization(),
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
