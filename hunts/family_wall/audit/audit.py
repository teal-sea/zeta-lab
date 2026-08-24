#!/usr/bin/env python3
"""Independent numerical audit for the barrier claim in BRIEF.md.

This module implements only the definitions in BRIEF.md.  It provides stable
kernel derivatives, O(n^2) objective/gradient evaluation, deterministic and
randomized multistart searches, and high-precision witness re-evaluation.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

import mpmath as mp
import numpy as np
from scipy.optimize import differential_evolution, minimize


SQRT2 = math.sqrt(2.0)
Q = 1.0 / SQRT2
PI = math.pi
K0 = math.sin(Q) / Q
H = 1.5 - Q / math.tan(Q)


def sinc(z: np.ndarray | float) -> np.ndarray:
    """Unnormalised sinc, sin(z)/z, evaluated stably near zero."""
    z = np.asarray(z, dtype=float)
    out = np.empty_like(z)
    small = np.abs(z) < 1.0e-4
    z2 = z[small] * z[small]
    out[small] = 1.0 + z2 * (-1.0 / 6.0 + z2 * (1.0 / 120.0 - z2 / 5040.0))
    out[~small] = np.sin(z[~small]) / z[~small]
    return out


def sinc_prime(z: np.ndarray | float) -> np.ndarray:
    """First derivative of unnormalised sinc."""
    z = np.asarray(z, dtype=float)
    out = np.empty_like(z)
    small = np.abs(z) < 2.0e-3
    zs = z[small]
    z2 = zs * zs
    out[small] = zs * (-1.0 / 3.0 + z2 * (1.0 / 30.0 + z2 * (-1.0 / 840.0 + z2 / 45360.0)))
    zn = z[~small]
    out[~small] = (zn * np.cos(zn) - np.sin(zn)) / (zn * zn)
    return out


def sinc_second(z: np.ndarray | float) -> np.ndarray:
    """Second derivative of unnormalised sinc."""
    z = np.asarray(z, dtype=float)
    out = np.empty_like(z)
    small = np.abs(z) < 1.0e-2
    z2 = z[small] * z[small]
    out[small] = -1.0 / 3.0 + z2 * (1.0 / 10.0 + z2 * (-1.0 / 168.0 + z2 / 6480.0))
    zn = z[~small]
    out[~small] = (
        -np.sin(zn) / zn
        - 2.0 * np.cos(zn) / (zn * zn)
        + 2.0 * np.sin(zn) / (zn * zn * zn)
    )
    return out


def kernel_all(x: np.ndarray | float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return K(x), K'(x), and K''(x) from the derived two-sinc formula."""
    x = np.asarray(x, dtype=float)
    zm = Q - PI * x
    zp = Q + PI * x
    kval = 0.5 * (sinc(zm) + sinc(zp))
    kprime = 0.5 * PI * (-sinc_prime(zm) + sinc_prime(zp))
    ksecond = 0.5 * PI * PI * (sinc_second(zm) + sinc_second(zp))
    return kval, kprime, ksecond


def kernel_value(x: np.ndarray | float) -> np.ndarray:
    """K(x) without derivative work, for population-based searches."""
    x = np.asarray(x, dtype=float)
    return 0.5 * (sinc(Q - PI * x) + sinc(Q + PI * x))


def weight_value(x: np.ndarray | float) -> np.ndarray:
    kval = kernel_value(x)
    return (kval / K0) ** 2


def weight_all(x: np.ndarray | float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return w(x), w'(x), and w''(x)."""
    kval, kp, kpp = kernel_all(x)
    scale = 1.0 / (K0 * K0)
    return kval * kval * scale, 2.0 * kval * kp * scale, 2.0 * (kp * kp + kval * kpp) * scale


def objective_and_gradient(gaps: np.ndarray, pressure: float | None = None) -> tuple[float, np.ndarray]:
    """Evaluate W, or F when pressure is supplied, and its exact gradient."""
    g = np.asarray(gaps, dtype=float)
    k = g.size
    n = k + 1
    prefix = np.empty(n, dtype=float)
    prefix[0] = 0.0
    np.cumsum(g, out=prefix[1:])

    value = 0.0
    gradient_delta = np.zeros(n, dtype=float)
    for s in range(1, n):
        distances = prefix[s:] - prefix[:-s]
        weights, derivatives, _ = weight_all(distances)
        coefficient = 2.0 / (n - s)
        value += coefficient * float(np.sum(weights))
        contributions = coefficient * derivatives
        np.add.at(gradient_delta, np.arange(n - s), contributions)
        np.add.at(gradient_delta, np.arange(s, n), -contributions)

    gradient = np.cumsum(gradient_delta[:-1])
    if pressure is not None:
        value += float(np.sum(g)) / pressure
        gradient += 1.0 / pressure
    return value, gradient


def objective(gaps: np.ndarray, pressure: float | None = None) -> float:
    g = np.asarray(gaps, dtype=float)
    n = g.size + 1
    prefix = np.concatenate(([0.0], np.cumsum(g)))
    value = 0.0
    for s in range(1, n):
        value += 2.0 / (n - s) * float(np.sum(weight_value(prefix[s:] - prefix[:-s])))
    if pressure is not None:
        value += float(np.sum(g)) / pressure
    return value


def hessian(gaps: np.ndarray) -> np.ndarray:
    """Dense exact Hessian of W, intended for stationarity diagnostics."""
    g = np.asarray(gaps, dtype=float)
    k = g.size
    n = k + 1
    prefix = np.concatenate(([0.0], np.cumsum(g)))
    result = np.zeros((k, k), dtype=float)
    for s in range(1, n):
        distances = prefix[s:] - prefix[:-s]
        _, _, second = weight_all(distances)
        coefficient = 2.0 / (n - s)
        for i, curvature in enumerate(coefficient * second):
            result[i : i + s, i : i + s] += curvature
    return result


def regular_start(n: int, cap: float, fraction: float = 1.0) -> np.ndarray:
    return np.full(n - 1, fraction * cap / (n - 1), dtype=float)


def structured_starts(n: int, cap: float, rng: np.random.Generator, random_count: int) -> Iterable[np.ndarray]:
    """Yield broad starts, including irregular and clustered configurations."""
    k = n - 1
    for fraction in (1.0, 0.98, 0.9, 0.75, 0.5):
        yield regular_start(n, cap, fraction)

    base = cap / k
    for amplitude in (0.1, 0.3, 0.6, 0.9):
        alternating = base * (1.0 + amplitude * (-1.0) ** np.arange(k))
        alternating *= cap / alternating.sum()
        yield alternating
        yield alternating[::-1]

    for period in (3, 4, 5, 7):
        if period <= k:
            phase = 2.0 * PI * np.arange(k) / period
            patterned = base * (1.0 + 0.65 * np.cos(phase))
            patterned *= cap / patterned.sum()
            yield patterned

    # Explicit clusters and edge-heavy patterns.
    for zeros in (1, max(1, k // 10), max(1, k // 4), max(1, k // 2)):
        clustered = np.full(k, base)
        indices = np.linspace(0, k - 1, zeros, dtype=int)
        clustered[indices] = 0.0
        if clustered.sum() > 0.0:
            clustered *= cap / clustered.sum()
        yield clustered
        yield clustered[::-1]

    x = np.linspace(-1.0, 1.0, k)
    for shape in (0.35, 0.7, 1.4):
        edge = 1.0 + shape * x * x
        edge *= cap / edge.sum()
        yield edge
        centre = 1.0 / edge
        centre *= cap / centre.sum()
        yield centre

    # Dirichlet starts span smooth through highly sparse configurations.
    alphas = (0.15, 0.35, 0.7, 1.0, 2.0, 5.0, 20.0)
    for j in range(random_count):
        alpha = alphas[j % len(alphas)]
        fraction = rng.uniform(0.55, 1.0) if j % 5 else 1.0
        yield fraction * cap * rng.dirichlet(np.full(k, alpha))


@dataclass
class SearchResult:
    n: int
    objective: float
    gaps: list[float]
    gaps_decimal: list[str]
    total: float
    cap: float | None
    success: bool
    status: str
    gradient_inf: float
    min_hessian_eigenvalue: float | None
    starts: int


def polish_simplex(x0: np.ndarray, cap: float, ftol: float = 1.0e-13, maxiter: int = 4000):
    k = x0.size
    constraint = {
        "type": "ineq",
        "fun": lambda x: cap - float(np.sum(x)),
        "jac": lambda x: -np.ones(k),
    }
    return minimize(
        fun=lambda x: objective_and_gradient(x),
        x0=np.clip(x0, 0.0, cap),
        jac=True,
        method="SLSQP",
        bounds=[(0.0, cap)] * k,
        constraints=[constraint],
        options={"ftol": ftol, "maxiter": maxiter, "disp": False},
    )


def search_w(n: int, random_count: int, seed: int, incumbent: np.ndarray | None = None) -> SearchResult:
    cap = (n - 1) / H
    rng = np.random.default_rng(seed)
    starts = list(structured_starts(n, cap, rng, random_count))
    if incumbent is not None:
        starts.insert(0, np.asarray(incumbent, dtype=float))
    best = None
    for x0 in starts:
        result = polish_simplex(x0, cap)
        if np.all(result.x >= -1e-9) and result.x.sum() <= cap + 1e-8:
            if best is None or result.fun < best.fun:
                best = result
    if best is None:
        raise RuntimeError(f"no feasible result for n={n}")

    # A second pass from the best point with a slightly relaxed tolerance often
    # removes SLSQP's last few ulps of active-constraint noise.
    best = polish_simplex(np.maximum(best.x, 0.0), cap, ftol=1.0e-14, maxiter=10000)
    grad = objective_and_gradient(best.x)[1]
    eig = None
    if n <= 30:
        eig = float(np.linalg.eigvalsh(hessian(best.x))[0])
    return SearchResult(
        n=n,
        objective=float(best.fun),
        gaps=[float(x) for x in best.x],
        gaps_decimal=[format(float(x), ".17g") for x in best.x],
        total=float(np.sum(best.x)),
        cap=cap,
        success=bool(best.success),
        status=str(best.message),
        gradient_inf=float(np.max(np.abs(grad))),
        min_hessian_eigenvalue=eig,
        starts=len(starts),
    )


def search_f7(
    pressure: float,
    seed: int,
    de_runs: int = 4,
    de_maxiter: int = 800,
    de_popsize: int = 20,
) -> SearchResult:
    """Serious global search for F_7,p followed by analytic-gradient polishing."""
    n = 7
    k = 6
    # F >= S/p.  Any incumbent U proves that a global minimizer lies in
    # S <= p U, hence every individual gap is <= p U.  Start with a safe
    # crude incumbent and tighten the box after every DE run.
    rng = np.random.default_rng(seed)
    seeds = [
        np.array([1.04, 1.97, 1.04, 1.97, 1.04, 1.04]),
        np.array([1.04, 1.97, 1.04, 1.04, 1.97, 1.04]),
    ]
    seeds.extend(np.full(k, spacing) for spacing in np.linspace(0.4, 20.0, 60))
    for _ in range(500):
        total = rng.uniform(3.0, 35.0)
        alpha = rng.choice((0.25, 0.5, 1.0, 2.0, 5.0))
        seeds.append(total * rng.dirichlet(np.full(k, alpha)))

    incumbent = None
    for x0 in seeds:
        local = minimize(
            fun=lambda x: objective_and_gradient(x, pressure),
            x0=x0,
            jac=True,
            method="L-BFGS-B",
            bounds=[(0.0, 100.0)] * k,
            options={"ftol": 1e-15, "gtol": 1e-12, "maxiter": 10000, "maxls": 50},
        )
        if incumbent is None or local.fun < incumbent.fun:
            incumbent = local
    assert incumbent is not None
    upper = float(incumbent.fun)
    bound = pressure * upper
    best = incumbent
    for run in range(de_runs):
        de = differential_evolution(
            func=lambda x: objective(x, pressure),
            bounds=[(0.0, bound)] * k,
            seed=seed + run,
            strategy="randtobest1bin" if run % 2 else "best1bin",
            popsize=de_popsize,
            maxiter=de_maxiter,
            tol=1e-9,
            atol=1e-13,
            mutation=(0.45, 1.35),
            recombination=0.8,
            polish=False,
            updating="immediate",
            workers=1,
        )
        polished = minimize(
            fun=lambda x: objective_and_gradient(x, pressure),
            x0=de.x,
            jac=True,
            method="L-BFGS-B",
            bounds=[(0.0, bound)] * k,
            options={"ftol": 1e-15, "gtol": 1e-13, "maxiter": 20000, "maxls": 50},
        )
        if polished.fun < best.fun:
            best = polished
            upper = float(best.fun)
            bound = pressure * upper

    grad = objective_and_gradient(best.x, pressure)[1]
    eig = float(np.linalg.eigvalsh(hessian(best.x))[0])
    return SearchResult(
        n=n,
        objective=float(best.fun),
        gaps=[float(x) for x in best.x],
        gaps_decimal=[format(float(x), ".17g") for x in best.x],
        total=float(np.sum(best.x)),
        cap=bound,
        success=bool(best.success),
        status=str(best.message),
        gradient_inf=float(np.max(np.abs(grad))),
        min_hessian_eigenvalue=eig,
        starts=de_runs,
    )


def mp_weight(x: mp.mpf) -> mp.mpf:
    q = 1 / mp.sqrt(2)
    s = lambda z: mp.mpf(1) if z == 0 else mp.sin(z) / z
    kval = (s(q - mp.pi * x) + s(q + mp.pi * x)) / 2
    kzero = s(q)
    return (kval / kzero) ** 2


def mp_objective(gaps: Iterable[float | str], pressure: float | None = None, dps: int = 80) -> mp.mpf:
    with mp.workdps(dps):
        g = [mp.mpf(str(x)) for x in gaps]
        n = len(g) + 1
        total = mp.mpf(0)
        for s in range(1, n):
            for i in range(n - s):
                total += mp.mpf(2) / (n - s) * mp_weight(mp.fsum(g[i : i + s]))
        if pressure is not None:
            total += mp.fsum(g) / pressure
        return +total


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    p_w = sub.add_parser("w", help="search constrained W witnesses")
    p_w.add_argument("--n", type=int, nargs="+", required=True)
    p_w.add_argument("--random-count", type=int, default=80)
    p_w.add_argument("--seed", type=int, default=20260823)
    p_w.add_argument("--output", type=Path)
    p_f = sub.add_parser("f7", help="global-search F_7,p")
    p_f.add_argument("--pressure", type=float, default=3000.0)
    p_f.add_argument("--seed", type=int, default=20260823)
    p_f.add_argument("--de-runs", type=int, default=4)
    p_f.add_argument("--de-maxiter", type=int, default=800)
    p_f.add_argument("--de-popsize", type=int, default=20)
    p_f.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.command == "w":
        records = []
        for index, n in enumerate(args.n):
            result = search_w(n, args.random_count, args.seed + 1009 * index)
            records.append(asdict(result))
            print(json.dumps(records[-1], indent=2))
        payload = {"H": H, "K0": K0, "results": records}
    else:
        result = search_f7(
            args.pressure,
            args.seed,
            args.de_runs,
            args.de_maxiter,
            args.de_popsize,
        )
        record = asdict(result)
        record["mp_objective_80dps"] = str(mp_objective(result.gaps, args.pressure, 80))
        print(json.dumps(record, indent=2))
        payload = {"H": H, "K0": K0, "pressure": args.pressure, "result": record}

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()
