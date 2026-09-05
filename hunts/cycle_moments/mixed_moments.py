"""Measured mixed-cycle constants, including every Rudnick-Sarnak pairing.

Run from the repository root with .venv/bin/python. This evaluates explicit
integrals on a uniform grid. The endpoint profiles used here need smooth
interior approximation before an application of the source theorem. The
diagonal-centering expressions additionally need a matched finite sampling
model; see MIXED-MOMENTS.md. No zeta proportion is computed by this script.
"""

from __future__ import annotations

import argparse
import json
from math import sqrt

import numpy as np

_X = np.empty(0)
_DX = 0.0


def _configure_grid(points: int) -> None:
    global _X, _DX
    if points < 101:
        raise ValueError("at least 101 grid points are required")
    _X = np.linspace(-0.6, 0.6, points)
    _DX = float(_X[1] - _X[0])


def _integral(a: np.ndarray) -> float:
    return float(np.sum(a) * _DX)


def _potential(a: np.ndarray) -> np.ndarray:
    """Grid quadrature of integral |x-y| a(y) dy, using cumulative sums."""
    mass = np.cumsum(a) * _DX
    moment = np.cumsum(_X * a) * _DX
    return _X * (2 * mass - mass[-1]) - (2 * moment - moment[-1])


def _interaction(a: np.ndarray, b: np.ndarray) -> float:
    return _integral(a * _potential(b))


def _cycle2(a: np.ndarray, b: np.ndarray) -> float:
    return _integral(a * b) + _interaction(a, b)


def _cycle3(a: np.ndarray, b: np.ndarray, c: np.ndarray) -> float:
    return _integral(
        a * b * c + b * c * _potential(a)
        + a * c * _potential(b) + a * b * _potential(c)
    )


def _shift(a: np.ndarray, offset: int) -> np.ndarray:
    out = np.zeros(len(a))
    if offset >= 0:
        out[:len(a) - offset] = a[offset:]
    else:
        out[-offset:] = a[:len(a) + offset]
    return out


def _cycle4_parts(a, b, c, d) -> dict[str, float]:
    """One zero-frequency term, six single pairs, three double pairs."""
    single = (
        _interaction(a, b * c * d) + _interaction(b, a * c * d)
        + _interaction(c, a * b * d) + _interaction(d, a * b * c)
        + _interaction(a * b, c * d) + _interaction(b * c, a * d)
    )
    adjacent = _integral(
        b * d * _potential(a) * _potential(c)
        + a * c * _potential(b) * _potential(d)
    )
    crossing = 0.0
    for offset in range(-len(_X) + 1, len(_X)):
        cd = _shift(c, offset) * d
        if not np.any(cd):
            continue
        ab = a * _shift(b, offset)
        if np.any(ab):
            crossing += abs(offset * _DX) * _interaction(cd, ab) * _DX
    return {
        "zero_frequency": _integral(a * b * c * d),
        "six_single_pairs": single,
        "two_adjacent_double_pairs": adjacent,
        "crossing_double_pair": crossing,
    }


def _cycle4(a, b, c, d) -> float:
    return sum(_cycle4_parts(a, b, c, d).values())


def _profiles(mu: float, center: float, lam: float):
    p = np.where(abs(_X) < lam, np.cos(_X / (sqrt(2) * lam)), 0.0)
    p /= _integral(p)
    u = (_X - center) / mu
    r = np.where(abs(u) < 1, (1 - u * u) ** 2, 0.0)
    r /= _integral(r)
    return p, r, np.sqrt(p * r)


def _measure(mu: float, center: float, lam: float) -> dict:
    if abs(center) + mu >= lam:
        raise ValueError("the narrow interval must lie inside the wide one")
    p, r, q = _profiles(mu, center, lam)
    ab2 = _cycle3(q, r, q)
    a2b2_parts = _cycle4_parts(p, q, r, q)
    a2b2 = sum(a2b2_parts.values())
    b2 = _cycle2(r, r)
    b4 = _cycle4(r, r, r, r)
    raw = 3 * ab2 - a2b2 - 2 * b2

    # Deterministic diagonal centering belongs to a finite sampling model.
    cross = 3 * _cycle2(q * r, q) - _cycle3(p, q, q * r) - 2 * _integral(r * r)
    diagonal = 3 * _integral(p * r * r) - _cycle2(p * r * r, p) - 2 * _integral(r * r)
    e = 3 * p - p * p - p * _potential(p) - 2
    w = q * q * (3 - p - _potential(p))
    w += q * ((3 - p) * _potential(q) - _potential(p * q)) - 2 * r
    optimal_diagonal = raw - _integral(w * w / e) if np.max(e) < 0 else None
    support = 2 * lam + 2 * abs(center) + 6 * mu
    return {
        "mu": mu, "center": center, "lambda": lam,
        "mixed_fourier_support_bound": support,
        "narrow_fourth_fourier_support_bound": 8 * mu,
        "inside_RS_support": support < 2 and 8 * mu < 2,
        "c2_p": _cycle2(p, p), "c_AB2": ab2,
        "c_A2B2": a2b2, "c_A2B2_parts": a2b2_parts,
        "c_B2": b2, "c_B4": b4, "J": raw,
        "finite_mixed_gain_if_moments_match": max(raw, 0.0) ** 2 / (9 * b4),
        "formal_sampled_J_centered_by_r": raw - 2 * cross + diagonal,
        "formal_sampled_J_optimal_diagonal": optimal_diagonal,
    }


def _self_check() -> dict:
    # Uniform profile on an interval of length w: all pairing terms are
    # independently integrable. The effective grid width avoids endpoint bias.
    a = (abs(_X) < 0.1).astype(float)
    width = _integral(a)
    a /= width
    expected = (1 / width + width / 3, 1 / width ** 2 + 1,
                1 / width ** 3 + 2 / width + 4 * width / 15)
    measured = (_cycle2(a, a), _cycle3(a, a, a), _cycle4(a, a, a, a))
    relative = [abs(v - e) / abs(e) for v, e in zip(measured, expected)]
    assert max(relative) < 0.002, relative
    p, r, q = _profiles(0.12, 0.0, 0.499)
    forward = _cycle4(p, q, r, q)
    rotated = _cycle4(q, r, q, p)
    assert abs(forward - rotated) < 1e-10 * abs(forward)
    # The cumulative-sum potential must agree with a direct quadrature route.
    for index in (len(_X) // 3, len(_X) // 2, 2 * len(_X) // 3):
        direct = _integral(abs(_X[index] - _X) * q)
        assert abs(direct - _potential(q)[index]) < 1e-12
    # Exact finite example: A eigenvalues 1/2,3/2; B=(3/2) times the second
    # eigenspace projector. The mixed inequality gains exactly 1/144.
    j = 3 * (3 / 2) ** 3 - (3 / 2) ** 4 - 2 * (3 / 2) ** 2
    gain = j * j / (9 * (3 / 2) ** 4)
    assert abs(gain - 1 / 144) < 1e-16
    return {"uniform_profile_relative_errors": relative,
            "cycle_rotation_defect": abs(forward - rotated),
            "finite_example_gain": gain}


def _main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--grid-points", type=int, default=2401)
    parser.add_argument("--self-check", action="store_true")
    args = parser.parse_args()
    _configure_grid(args.grid_points)
    checks = _self_check() if args.self_check else None
    cases = [(0.04, 0.0), (0.08, 0.0), (0.12, 0.0), (0.16, 0.0),
             (0.11, 0.15), (0.06, 0.30), (0.025, 0.42)]
    result = {"grade": "measured explicit integrals",
              "grid_points": args.grid_points,
              "rows": [_measure(mu, center, 0.499) for mu, center in cases]}
    if checks is not None:
        result["self_check"] = checks
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    _main()
