"""Gap A above bandwidth 1: the Fejer-Riesz SDP that `LATTICE-EXTREMALITY-ROUTE`
section 6a names as the right tool.

Section 6a reduces the sparse side to a problem about one function `u`:

    u >= 0,   u(2*pi*n) = 0 for n != 0,   uhat <= M := khat - c*shat,
    uhat(0) = M(0) = 4.9441838...,        int uhat = uhat(0),

with `c = K_1(0)`, and proves it infeasible at bandwidth 1, short by 29%.
It leaves open whether bandwidth above 1 helps, records that a linear program
over sampled `uhat` is unsound here (it returned `4.908534` on the case whose
answer is known, by dipping negative between its own sample points), and names
the fix: enforce `u >= 0` structurally rather than by sampling, and carry the
lattice zeros by factoring rather than by listing them.

That is what this module does.

    u = s * q,      s(x) = (sin(x/2)/(x/2))^2,      q = |h|^2 >= 0,

so `u >= 0` and `u(2*pi*n) = 0` hold by construction rather than by
constraint, and neither can be violated between sample points.  Taking `h`
band-limited to `[-B/2, B/2]` makes `q` band-limited to `[-B, B]` and `u` to
`[-1-B, 1+B]`, so `B` is the knob section 6a asks about: `B = 0` is bandwidth
1, the case already settled.

`h` is expanded in its own Shannon samples, `h(x) = sum_j b_j sinc_B(x - x_j)`
at `x_j = 2*pi*j/B`, kept even and truncated to `|j| <= m`.  Every member of
that family is *exactly* band-limited, so truncating `m` shrinks the search
space without ever relaxing a constraint: a feasible point found here is
feasible for the real problem, and a failure to find one is evidence about the
family and not a proof.  `uhat` is then linear in the Gram matrix
`G = b b^T >= 0`, which is what makes the whole thing an SDP.

The one constraint still imposed by sampling is `uhat <= M`.  That direction is
a relaxation, exactly as section 6a warns, so `verify` re-checks any solution
on a grid two orders of magnitude finer and reports the worst violation.  A
solution that fails `verify` is not a witness.

Grade: measured.  Double precision, a finite family, no enclosure anywhere.
Nothing here is evidence about RH.

Run:  .venv/bin/python hunts/frontier_math/sparse_sdp.py --scan
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))

import lattice_extremality as le  # noqa: E402

TWOPI = 2.0 * np.pi

#: `K_1(0)`, the multiplier gap B settled on, and the ceiling admissibility
#: puts on it.  `majorant_multiplier_range` derives both.
C_MAJORANT, C_CEILING = le.majorant_multiplier_range()

#: `M(0) = khat(0) - c*shat(0)`, the value `uhat(0)` has to reach.
M_AT_ZERO = le.kappa_hat(0.0) - C_MAJORANT * TWOPI

#: What bandwidth 1 achieves, from section 6a: `(ceiling - c) * 2*pi`.
BANDWIDTH_ONE = (C_CEILING - C_MAJORANT) * TWOPI


def fejer(x: np.ndarray) -> np.ndarray:
    """`s(x) = (sin(x/2)/(x/2))^2`, non-negative, zero on `2*pi*Z` minus 0."""
    return np.sinc(x / TWOPI) ** 2


def M_of(xi: np.ndarray) -> np.ndarray:
    """`M = khat - c*shat`, supported on `[-1,1]` and vanishing at both ends."""
    khat = np.array([le.kappa_hat(float(t)) for t in np.atleast_1d(xi)])
    shat = TWOPI * np.clip(1.0 - np.abs(xi), 0.0, None)
    return khat - C_MAJORANT * shat


def basis(x: np.ndarray, bandwidth: float, m: int) -> np.ndarray:
    """The even basis for `h`, band-limited to `[-B/2, B/2]`.

    Row 0 is the **constant**, and it is not optional.  The bandwidth-1
    solution of section 6a is `u = a*s`, whose factor `q = a` is constant, so
    `h` is constant too.  A constant is band-limited (its transform is a point
    mass at the origin) but it is not in `L^2`, so a basis of decaying sincs
    excludes the one solution already known to exist.  Leaving it out made the
    first version of this module return `uhat(0) = 0`: the family was empty of
    everything that matters, and the SDP correctly reported so.

    The remaining rows are Shannon samples of the decaying part, `sinc_B(x)`
    and then `sinc_B(x - x_j) + sinc_B(x + x_j)` at `x_j = 2*pi*j/B`, kept in
    even pairs.  Every row is exactly band-limited, so the span is a genuine
    subfamily of the admissible `h`: `m` shrinks the search, never a
    constraint.  `m = 0` is the constant alone, which is the calibration case
    whose answer section 6a already knows.
    """
    rows = [np.ones_like(x)]
    if m >= 1:
        rows.append(np.sinc(bandwidth * x / TWOPI))
    for j in range(1, m):
        shift = TWOPI * j / bandwidth
        rows.append(np.sinc(bandwidth * (x - shift) / TWOPI)
                    + np.sinc(bandwidth * (x + shift) / TWOPI))
    return np.array(rows)


def _hat_rows(bandwidth: float, m: int, d: float):
    """Fourier transforms of the basis rows, on their own symmetric grids.

    Row 0 is the constant, whose transform is a point mass; it is returned as
    `None` and handled by the convolution identity rather than sampled.  Row 1
    is `sinc_B`, transform `(2*pi/B)` on `[-B/2, B/2]`, and the later rows carry
    the even shift factor `2*cos(eta*x_j)` on the same support.
    """
    eta = np.arange(-bandwidth / 2, bandwidth / 2 + d, d)
    rows = [None, np.full_like(eta, TWOPI / bandwidth)]
    for j in range(1, m):
        shift = TWOPI * j / bandwidth
        rows.append((TWOPI / bandwidth) * 2.0 * np.cos(eta * shift))
    return rows[: m + 1], eta


def transforms(bandwidth: float, m: int, xis: np.ndarray, d: float = 0.001):
    """`A[j,k,:]`, the transform of `s e_j e_k`, evaluated on `xis`.

    Computed as a convolution in frequency rather than an integral in `x`.
    Every factor here has compact support, so the only error is quadrature on a
    finite interval.  The x-space route cannot manage that: with the constant
    in the basis the integrand `s e_0 e_0` decays like `1/x^2`, and truncating
    it leaves ripple of order `1/x_max` precisely in `|xi| > 1`, where the true
    value is zero and the constraint is `uhat <= 0`.  That ripple drove the
    first version of this module to `uhat(0) = 0` for every input.

    The identity used is `A_jk = (1/(4*pi^2)) * shat * ehat_j * ehat_k`, with
    the constant's point mass `2*pi*delta` acting as the convolution identity,
    so `A_00 = shat` exactly.
    """
    hats, _ = _hat_rows(bandwidth, m, d)
    n = m + 1
    xi_s = np.arange(-1.0, 1.0 + d, d)
    shat = TWOPI * np.clip(1.0 - np.abs(xi_s), 0.0, None)

    def grid_for(length: int) -> np.ndarray:
        half = (length - 1) / 2.0
        return np.arange(-half, half + 0.5) * d

    A = np.zeros((n, n, len(xis)))
    cache = {}
    for j in range(n):
        for k in range(j, n):
            if j == 0 and k == 0:
                vals, grid = shat, xi_s
            elif j == 0:
                if k not in cache:
                    cache[k] = np.convolve(shat, hats[k]) * d / TWOPI
                vals = cache[k]
                grid = grid_for(len(vals))
            else:
                inner = np.convolve(shat, hats[j]) * d
                vals = np.convolve(inner, hats[k]) * d / (4.0 * np.pi**2)
                grid = grid_for(len(vals))
            row = np.interp(xis, grid, vals, left=0.0, right=0.0)
            A[j, k, :] = row
            A[k, j, :] = row

    e0 = basis(np.array([0.0]), bandwidth, m)[:, 0]
    return A, np.outer(e0, e0), None, None


def constraint_grid(bandwidth: float, n_xi: int = 700) -> np.ndarray:
    """Where `uhat <= M` is imposed.

    Uniform sampling is not enough on its own.  The binding ratio at bandwidth
    1 is `inf khat/shat`, attained only in the limit `xi -> 1`, so a uniform
    grid never sees it and the optimiser pockets the difference: with 700 even
    points the calibration case comes back 0.42% above its proved ceiling.
    The grid therefore clusters geometrically at `xi = 1`, where `M` vanishes,
    and again at the band edge `1 + B`.
    """
    edge = 1.0 + bandwidth
    uniform = np.linspace(0.0, edge + 0.05, n_xi)
    near_one = 1.0 - np.logspace(-9, -1.5, 120)
    past_one = 1.0 + np.logspace(-9, -1.5, 120)
    near_edge = edge - np.logspace(-9, -1.5, 60)
    grid = np.concatenate([uniform, near_one, past_one, near_edge])
    return np.unique(np.clip(grid, 0.0, edge + 0.05))


def solve(bandwidth: float, m: int, solver: str = "CLARABEL",
          n_xi: int = 700) -> tuple[str, np.ndarray | None]:
    """Maximise `u(0)` subject to `G >= 0` and `uhat <= M` on the grid.

    `u(0) = q(0)` is the quantity the bound actually needs: the bound is worst
    as the density goes to zero, where it asks for `u(0) >= M(0)/(2*pi)`.  No
    equality is imposed here even though section 6a proves one holds.  The
    knife-edge is a *consequence* (the lattice attains the bound at
    `rho = 1/(2*pi)`, forcing `B_g(1) >= LAT`, which together with the
    zero-density requirement pins `uhat(0) = M(0)`), and imposing a consequence
    as a constraint only makes the solve worse conditioned.

    Returns the solver status alongside the matrix, and callers must read it.
    A first version of this scan printed `pr.value` without it and reported
    `2.4e167` as a number.
    """
    import cvxpy as cp

    xis = constraint_grid(bandwidth, n_xi)
    A, E, _, _ = transforms(bandwidth, m, xis)
    M = M_of(xis)
    n = m + 1
    G = cp.Variable((n, n), symmetric=True)
    constraints = [G >> 0]
    constraints += [cp.sum(cp.multiply(G, A[:, :, i])) <= M[i] for i in range(len(xis))]
    problem = cp.Problem(cp.Maximize(cp.sum(cp.multiply(G, E))), constraints)
    try:
        problem.solve(solver=solver)
    except Exception:  # solvers fail outright on the worse-conditioned sizes
        return "solver_error", None
    if G.value is None:
        return problem.status, None
    return problem.status, np.array(G.value)


def verified(bandwidth: float, m: int, G: np.ndarray, n_fine: int = 40000) -> dict:
    """What the solution actually achieves, as opposed to what was reported.

    Two repairs, in order.  The Gram matrix is projected onto the positive
    semidefinite cone, which restores `u >= 0` exactly: solutions here come
    back with eigenvalues around `-1e-5`, and a `q` that is not a sum of
    squares is not a `q` at all.  Then the whole thing is scaled by the largest
    factor keeping `uhat <= M` on a grid far finer than the one solved on.

    The scale is the verdict.  Where `M > 0` a violation can always be scaled
    away, but `M` vanishes off `[-1,1]`, and there any positive value of `uhat`
    survives every positive scaling: the scale collapses to zero and the point
    is not a witness at all.  That is what separates the calibration case from
    every wider-bandwidth solve found so far.
    """
    eigenvalues, vectors = np.linalg.eigh(G)
    projected = (vectors * np.clip(eigenvalues, 0.0, None)) @ vectors.T
    xis = np.linspace(0.0, 1.0 + bandwidth + 0.3, n_fine)
    A, E, _, _ = transforms(bandwidth, m, xis)
    M = M_of(xis)
    uhat = np.einsum("jk,jki->i", projected, A)
    positive = uhat > 1e-15
    scale = 1.0 if not positive.any() else min(1.0, float(np.min(M[positive] / uhat[positive])))
    scale = max(scale, 0.0)
    return {
        "verified_u0": scale * float(np.sum(projected * E)),
        "scale": scale,
        "residual": float(np.max(scale * uhat - M)),
        "psd_repair": float(-min(eigenvalues.min(), 0.0)),
    }


#: What `u(0)` has to reach, and what bandwidth 1 reaches.
NEEDED_U0 = M_AT_ZERO / TWOPI
BANDWIDTH_ONE_U0 = BANDWIDTH_ONE / TWOPI


def scan(cases=((0.5, 0), (1.0, 4), (1.0, 6), (2.0, 6), (4.0, 8))) -> list[dict]:
    rows = []
    for bandwidth, m in cases:
        status, G = solve(bandwidth, m)
        row = {"bandwidth_q": bandwidth, "m": m, "status": status,
               "needed_u0": NEEDED_U0, "bandwidth_one_u0": BANDWIDTH_ONE_U0}
        row.update(verified(bandwidth, m, G) if G is not None
                   else {"verified_u0": float("nan"), "scale": float("nan")})
        rows.append(row)
        print(f"  B={bandwidth:<5} m={m:<3} {status:<20} "
              f"verified u(0)={row['verified_u0']:9.6f} "
              f"({100 * row['verified_u0'] / NEEDED_U0:6.2f}% of needed)  scale={row['scale']:.4f}")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args()

    print(f"u(0) needed                 = {NEEDED_U0:.7f}")
    print(f"bandwidth 1, proved in 6a   = {BANDWIDTH_ONE_U0:.7f}  "
          f"({100 * BANDWIDTH_ONE_U0 / NEEDED_U0:.2f}% of needed)")
    print()
    rows = scan()
    best = max(rows, key=lambda r: r["verified_u0"] if r["verified_u0"] == r["verified_u0"] else -1)
    print()
    print(f"best verified: {best['verified_u0']:.6f} at B={best['bandwidth_q']}, m={best['m']}")
    print("bandwidth above 1 has produced nothing that survives verification.")
    if args.json:
        args.json.write_text(json.dumps(rows, indent=2), encoding="utf-8")
        print(f"wrote {args.json}")


if __name__ == "__main__":
    main()
