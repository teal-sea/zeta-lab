"""White's lower-bound convex program for Erdos's minimum overlap constant.

Reference: E. P. White, *A new bound for Erdos' minimum overlap problem*,
arXiv:2201.05704v1, published as Acta Arithmetica 208 (2023), 235-255.
Section 4 is the simplified linear program; section 5 is the full program.
Every constraint number below is White's.

Why this file exists
--------------------
The lab's ceiling procedure needs the published method as a *runnable object*
with its free parameters exposed, so that the parameters can be swept and the
method's own limit measured. White never released code; this is a
reimplementation from the paper's displayed constraints.

Two deliberate departures, both in the direction that can only *weaken* the
bound this file computes:

1. **The quadratic constraints (5.5) and (5.11) are replaced by outer
   approximations.** White's program is a second-order cone program. This
   file has numpy and scipy only, and scipy has no conic solver, so the two
   convex quadratic families are approximated from outside by supporting
   hyperplanes, added iteratively at the current LP optimum. An outer
   approximation of a convex feasible set *contains* it, so the LP optimum is
   **at most** the SOCP optimum, and any value this file reports is still a
   valid lower bound on the constant. The cut loop drives it upward toward
   White's value; the gap left when the loop stops is reported, never hidden.

2. **(5.6) and (5.7) use the factor 4, not the 8 printed in the paper.**
   White's own Lemma 3 eq. (3.6) gives `B_m = -(4/(m*pi)) sin(m*pi/2) b_m`,
   and Lemma 5 sandwiches that same `B_m`, so 4 is what the sandwich needs.
   The `8` in the displayed (5.6)/(5.7) is a factor-of-two typo. Using 8 makes
   the constraint *tighter* than the mathematics licenses, which is the unsafe
   direction for a lower bound, so 4 is the default here and 8 is available
   behind a flag purely as a sensitivity check.

Nothing in this file is a proof of anything. It is an evaluator.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

TWO_OVER_PI = 2.0 / math.pi


# ---------------------------------------------------------------------------
# variable layout
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Layout:
    """Index bookkeeping for the variable vector of White's section 5."""

    N: int
    T: int
    R: int

    @property
    def n_vars(self) -> int:
        # Omega | w | v | c | d | eps | delta | S_m | A_m | B_m.
        # The last three blocks are auxiliaries: S_m carries the cell sum of
        # (5.5), A_m and B_m carry the Fourier coefficients. They exist so a
        # supporting hyperplane for (5.5) is a row with three nonzeros instead
        # of a row dense in all 2N+2T structural variables, which is the whole
        # difference between a sweep that runs and one that does not.
        return 1 + 2 * self.N + 2 * self.T + 2 * self.R + 6 * self.R

    @property
    def i_omega(self) -> int:
        return 0

    @property
    def w0(self) -> int:
        return 1

    @property
    def v0(self) -> int:
        return 1 + self.N

    @property
    def c0(self) -> int:
        return 1 + 2 * self.N

    @property
    def d0(self) -> int:
        return 1 + 2 * self.N + self.T

    @property
    def e0(self) -> int:
        return 1 + 2 * self.N + 2 * self.T

    @property
    def g0(self) -> int:
        return 1 + 2 * self.N + 2 * self.T + self.R

    @property
    def s0(self) -> int:
        return 1 + 2 * self.N + 2 * self.T + 2 * self.R

    @property
    def a0(self) -> int:
        return self.s0 + 2 * self.R

    @property
    def b0(self) -> int:
        return self.s0 + 4 * self.R


def _sin_half(m: int) -> float:
    """sin(m*pi/2): 0 for even m, +1 for m = 1 mod 4, -1 for m = 3 mod 4."""
    if m % 2 == 0:
        return 0.0
    return 1.0 if m % 4 == 1 else -1.0


def affine_ab(lay: Layout, m: int) -> tuple[np.ndarray, float, np.ndarray, float]:
    """Return `(coef_a, const_a, coef_b, const_b)` for White's `a_m`, `b_m`.

    These are the Fourier coefficients of `f` on `[-2,2]`, expressed as affine
    functions of the program variables via White's (3.3), (3.4) with the tail
    beyond `T` absorbed into the slack variables of (5.8), (5.9).
    """
    T = lay.T
    ca = np.zeros(lay.n_vars)
    cb = np.zeros(lay.n_vars)
    const_a = 0.0
    const_b = 0.0
    if m % 2 == 0:
        s = m // 2
        if s <= T:
            ca[lay.c0 + s - 1] = 0.5
            cb[lay.d0 + s - 1] = 0.5
        # s > T: the coefficient is inside the discarded tail; it is bounded by
        # Parseval and its contribution is dominated by the (5.8)/(5.9) slacks,
        # so it is dropped, which only weakens the constraint it appears in.
        return ca, const_a, cb, const_b

    sgn = _sin_half(m)
    t = (m + 1) // 2  # eps_{2t-1} = eps_m
    if t <= lay.R:
        ca[lay.e0 + t - 1] = 1.0
        cb[lay.g0 + t - 1] = 1.0
    k = np.arange(1, T + 1, dtype=float)
    denom = m * m - 4.0 * k * k
    signs = np.where(k.astype(int) % 2 == 0, 1.0, -1.0)  # (-1)^k
    ca[lay.c0 : lay.c0 + T] = (2.0 * m * sgn / math.pi) * (signs / denom)
    const_a = (2.0 * m * sgn / math.pi) * (1.0 / (2.0 * m * m))
    cb[lay.d0 : lay.d0 + T] = (4.0 * sgn / math.pi) * (k * signs / denom)
    return ca, const_a, cb, const_b


# ---------------------------------------------------------------------------
# the program
# ---------------------------------------------------------------------------


@dataclass
class Box:
    """White's divide-and-conquer cell: bounds on E(M), c_1 and d_1."""

    h1: float
    h2: float
    p1: float
    p2: float
    q1: float
    q2: float


def fourier_maps(T: int, R: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """The linear maps `c -> a` and `d -> b` of White (3.3), (3.4).

    Returns `(A, B, const)` with `A, B` of shape `(2R, T)` and `const` of
    shape `(2R,)`, so that (before the tail slacks)
    `a = A c + const` and `b = B d`.
    """
    A = np.zeros((2 * R, T))
    B = np.zeros((2 * R, T))
    const = np.zeros(2 * R)
    k = np.arange(1, T + 1, dtype=float)
    signs = np.where(k.astype(int) % 2 == 0, 1.0, -1.0)
    for m in range(1, 2 * R + 1):
        i = m - 1
        if m % 2 == 0:
            s = m // 2
            if s <= T:
                A[i, s - 1] = 0.5
                B[i, s - 1] = 0.5
            continue
        sgn = _sin_half(m)
        denom = m * m - 4.0 * k * k
        A[i] = (2.0 * m * sgn / math.pi) * (signs / denom)
        const[i] = (2.0 * m * sgn / math.pi) * (1.0 / (2.0 * m * m))
        B[i] = (4.0 * sgn / math.pi) * (k * signs / denom)
    return A, B, const


def parseval_sqrt(T: int, R: int) -> tuple[np.ndarray, np.ndarray]:
    """White's Parseval ball, pushed into the coordinates the program uses.

    (5.11) is `sum_k (c_k^2 + d_k^2) <= 1/2`, a ball in `2T` dimensions, and
    `c`, `d` are used only through the `4R` numbers `a_m`, `b_m`. So write
    `c = A^T gamma`, which is no restriction because the minimum-norm `c`
    producing a given `a` already lies in the row space of `A`. Then
    `a = (A A^T) gamma` and `sum c^2 = gamma^T (A A^T) gamma`, and (5.11)
    becomes one quadratic form in `4R` variables:

        a = F_a s,   sum s^2 + sum u^2 <= 1/2,   F = U sqrt(Lambda),

    where `A A^T = U Lambda U^T`. Writing `gamma = U Lambda^{-1/2} s` turns
    the cost `gamma^T (A A^T) gamma` into the plain squared norm of `s`, so
    the Parseval constraint becomes the unit ball and nothing is inverted.

    This is not an optimisation, it is what makes the constraint exist at all.
    Cut-planing the original ball in `2T` dimensions does not work -- one
    supporting hyperplane per round in 7000 dimensions leaves it unenforced,
    the measured violation stays above 200 after thirty rounds, and the
    program silently degenerates into one where `a_m` and `b_m` are free. The
    obvious alternative, an ellipsoid `alpha^T (A A^T)^{-1} alpha <= 1/2`, is
    the same constraint but numerically dead: `A A^T` has a condition number
    past 1e15 here, and its computed inverse is not even positive on the
    iterates. Using `A A^T` directly is no better -- the cut loop then chases
    `gamma` out to 1e7 with the ball violated by 1e10. Only the square-root
    coordinates, in which the constraint is the unit ball, converge.
    """
    A, B, _ = fourier_maps(T, R)
    out = []
    for X in (A, B):
        lam, U = np.linalg.eigh(X @ X.T)
        out.append(U @ np.diag(np.sqrt(np.maximum(lam, 0.0))))
    return out[0], out[1]


class WhiteProgram:
    """White's section 5 program in reduced coordinates.

    The `2T` Fourier variables of the published formulation are eliminated
    exactly (see `parseval_ellipsoid`), leaving `1 + 2N + 12R` variables:

        Omega | w (N) | v (N) | eps (R) | delta (R)
              | S (2R) | a (2R) | b (2R) | alpha (2R) | beta (2R)

    `S_m` is the cell sum of (5.5), `alpha`/`beta` are `a`/`b` with the tail
    slacks and the constant removed, so that the Parseval ellipsoid is a
    quadratic form in them alone.

    The feasible set of the resulting LP *contains* the feasible set of
    White's SOCP, so the optimum is at most his and is a valid lower bound on
    the minimum overlap constant under the box hypotheses of his Prop. 9.
    """

    def __init__(self, N: int, T: int, R: int, box: Box, sine_factor: float = 4.0):
        self.N, self.T, self.R = N, T, R
        self.box = box
        self.L = 2.0 / N
        self.sine_factor = sine_factor
        self.nv = 1 + 2 * N + 12 * R
        self.i_w = 1
        self.i_v = 1 + N
        self.i_eps = 1 + 2 * N
        self.i_del = 1 + 2 * N + R
        self.i_S = 1 + 2 * N + 2 * R
        self.i_a = self.i_S + 2 * R
        self.i_b = self.i_S + 4 * R
        self.i_ga = self.i_S + 6 * R
        self.i_et = self.i_S + 8 * R
        self.Fa, self.Fb = parseval_sqrt(T, R)
        _, _, self.const = fourier_maps(T, R)
        self._build()

    def _build(self) -> None:
        N, T, R, L = self.N, self.T, self.R, self.L
        j = np.arange(1, N + 1, dtype=float)
        wv = np.arange(self.i_w, self.i_w + 2 * N)
        ub: list[tuple[np.ndarray, np.ndarray]] = []
        ub_rhs: list[float] = []
        eq: list[tuple[np.ndarray, np.ndarray]] = []
        eq_rhs: list[float] = []

        def add_ub(cols, data, rhs):
            ub.append((np.asarray(cols, dtype=int), np.asarray(data, dtype=float)))
            ub_rhs.append(float(rhs))

        def add_eq(cols, data, rhs):
            eq.append((np.asarray(cols, dtype=int), np.asarray(data, dtype=float)))
            eq_rhs.append(float(rhs))

        # (5.2)
        add_eq(wv, np.full(2 * N, L), 1.0)
        # (5.3)
        add_ub(wv, np.concatenate([-(L * L) * j, (L * L) * (j - 1.0)]), -self.box.h1)
        # (5.4)
        sq = (L**3) * (j - 1.0) ** 2
        add_ub(wv, np.concatenate([sq, sq]), 2.0 / 3.0 + self.box.h2**2 / 2.0)
        # (5.13)
        ap2 = np.cos(math.pi * 2 * L * (j - 0.5) / 2.0) + math.pi * 2 * L / 4.0
        add_ub(wv, np.concatenate([-(L / 2.0) * ap2, -(L / 2.0) * ap2]),
               0.5 * (self.box.p2**2 + max(self.box.q1**2, self.box.q2**2)))

        for m in range(1, 2 * R + 1):
            i = m - 1
            # S_m = (L/2) sum alpha^-_{j,m} (w+v)
            am = np.cos(math.pi * m * L * (j - 0.5) / 2.0) - math.pi * m * L / 4.0
            add_eq(np.concatenate([wv, [self.i_S + i]]),
                   np.concatenate([(L / 2.0) * am, (L / 2.0) * am, [-1.0]]), 0.0)
            # a_m = (M_a gamma)_m + eps_m + const_m ; b_m = (M_b eta)_m + delta_m
            gcols = np.arange(self.i_ga, self.i_ga + 2 * R)
            ecols = np.arange(self.i_et, self.i_et + 2 * R)
            if m % 2 == 1:
                t = (m + 1) // 2
                add_eq(np.concatenate([[self.i_a + i, self.i_eps + t - 1], gcols]),
                       np.concatenate([[1.0, -1.0], -self.Fa[i]]), self.const[i])
                add_eq(np.concatenate([[self.i_b + i, self.i_del + t - 1], ecols]),
                       np.concatenate([[1.0, -1.0], -self.Fb[i]]), 0.0)
            else:
                add_eq(np.concatenate([[self.i_a + i], gcols]),
                       np.concatenate([[1.0], -self.Fa[i]]), 0.0)
                add_eq(np.concatenate([[self.i_b + i], ecols]),
                       np.concatenate([[1.0], -self.Fb[i]]), 0.0)
            # (5.6) / (5.7)
            coef = self.sine_factor * _sin_half(m) / (m * math.pi)
            bmi = np.sin(math.pi * m * L * (j - 0.5) / 2.0) - math.pi * m * L / 4.0
            bpl = np.sin(math.pi * m * L * (j - 0.5) / 2.0) + math.pi * m * L / 4.0
            add_ub(np.concatenate([wv, [self.i_b + i]]),
                   np.concatenate([(L / 2.0) * bmi, -(L / 2.0) * bpl, [coef]]), 0.0)
            add_ub(np.concatenate([wv, [self.i_b + i]]),
                   np.concatenate([-(L / 2.0) * bpl, (L / 2.0) * bmi, [-coef]]), 0.0)

        self._ub, self._ub_rhs = ub, ub_rhs
        self._eq = self._to_sparse(eq, self.nv)
        self._eq_rhs = np.array(eq_rhs)
        self._static_ub = self._to_sparse(ub, self.nv)

        idx = np.arange(2 * N)
        self._omega = sparse.coo_matrix(
            (np.concatenate([np.ones(2 * N), -np.ones(2 * N)]),
             (np.concatenate([idx, idx]),
              np.concatenate([self.i_w + idx, np.zeros(2 * N, dtype=int)]))),
            shape=(2 * N, self.nv)).tocsr()

        bounds: list[tuple[float | None, float | None]] = [(0.0, 1.0)]
        bounds += [(0.0, None)] * (2 * N)
        for m in range(1, R + 1):
            im = 2 * m - 1
            bounds.append(_pm((1.0 / (4.0 - (im / T) ** 2))
                              * (2.0 * im / (math.pi * math.sqrt(6.0 * T**3)))))
        for m in range(1, R + 1):
            im = 2 * m - 1
            bounds.append(_pm((1.0 / (4.0 - (im / T) ** 2))
                              * (4.0 / (math.pi * math.sqrt(2.0 * T)))))
        bounds += [(None, None)] * (6 * R)
        # s and u live in the ball of radius sqrt(1/2); stating it as a bound
        # rather than leaving it to the cuts is what keeps the loop stable.
        rad = math.sqrt(0.5)
        bounds += [(-rad, rad)] * (4 * R)
        # (5.12): a_2 = c_1/2 and b_2 = d_1/2, so the box on c_1, d_1 is a box
        # on a_2, b_2 in these coordinates.
        bounds[self.i_a + 1] = (self.box.p1 / 2.0, self.box.p2 / 2.0)
        bounds[self.i_b + 1] = (self.box.q1 / 2.0, self.box.q2 / 2.0)
        self._bounds = bounds

        self._cos_lin = [-(4.0 * _sin_half(m) / (m * math.pi))
                         for m in range(1, 2 * R + 1)]

    @staticmethod
    def _to_sparse(rows, nv):
        if not rows:
            return sparse.csr_matrix((0, nv))
        r_idx = np.concatenate([np.full(len(c), i) for i, (c, _) in enumerate(rows)])
        c_idx = np.concatenate([c for c, _ in rows])
        data = np.concatenate([d for _, d in rows])
        return sparse.coo_matrix((data, (r_idx, c_idx)), shape=(len(rows), nv)).tocsr()

    # -- cuts --------------------------------------------------------------

    def _cos_cut(self, m: int, a0: float, b0: float):
        """Supporting hyperplane for (5.5) at `(a0, b0)`; three nonzeros."""
        i = m - 1
        return ([self.i_S + i, self.i_a + i, self.i_b + i],
                [1.0, self._cos_lin[i] + 4.0 * a0, 4.0 * b0],
                2.0 * (a0 * a0 + b0 * b0))

    def _par_cut(self, ga: np.ndarray, et: np.ndarray):
        """Supporting hyperplane for the Parseval quadratic form."""
        cols = np.concatenate([np.arange(self.i_ga, self.i_ga + 2 * self.R),
                               np.arange(self.i_et, self.i_et + 2 * self.R)])
        data = 2.0 * np.concatenate([ga, et])
        return cols, data, 0.5 + float(ga @ ga + et @ et)

    def par_value(self, ga: np.ndarray, et: np.ndarray) -> float:
        return float(ga @ ga + et @ et)

    # -- solve -------------------------------------------------------------

    def solve(self, cut_rounds: int = 40, tol: float = 1e-9,
              method: str = "highs-ipm") -> dict:
        R, nv = self.R, self.nv
        obj = np.zeros(nv)
        obj[0] = 1.0
        cut_rows: list[tuple[np.ndarray, np.ndarray]] = []
        cut_rhs: list[float] = []
        for m in range(1, 2 * R + 1):
            c, d, r = self._cos_cut(m, 0.0, 0.0)
            cut_rows.append((np.asarray(c, dtype=int), np.asarray(d, dtype=float)))
            cut_rhs.append(r)
        c, d, r = self._par_cut(np.zeros(2 * R), np.zeros(2 * R))
        cut_rows.append((c, d))
        cut_rhs.append(r)

        trace: list[float] = []
        cos_res: list[float] = []
        par_res: list[float] = []
        value, x = None, None
        for _ in range(cut_rounds):
            A = sparse.vstack([self._omega, self._static_ub,
                               self._to_sparse(cut_rows, nv)]).tocsc()
            b = np.concatenate([np.zeros(2 * self.N), np.array(self._ub_rhs),
                                np.array(cut_rhs)])
            res = linprog(obj, A_ub=A, b_ub=b, A_eq=self._eq, b_eq=self._eq_rhs,
                          bounds=self._bounds, method=method)
            if not res.success:
                return {"value": value, "status": res.message, "trace": trace,
                        "cos_residuals": cos_res, "par_residuals": par_res,
                        "converged": False, "cuts": len(cut_rows)}
            x = res.x
            value = float(res.fun)
            trace.append(value)
            worst = 0.0
            for m in range(1, 2 * R + 1):
                i = m - 1
                a0, b0 = float(x[self.i_a + i]), float(x[self.i_b + i])
                worst = max(worst, float(x[self.i_S + i]) + self._cos_lin[i] * a0
                            + 2.0 * (a0 * a0 + b0 * b0))
                cc, dd, rr = self._cos_cut(m, a0, b0)
                cut_rows.append((np.asarray(cc, dtype=int), np.asarray(dd, dtype=float)))
                cut_rhs.append(rr)
            gm = x[self.i_ga : self.i_ga + 2 * R]
            et = x[self.i_et : self.i_et + 2 * R]
            par = self.par_value(gm, et) - 0.5
            cc, dd, rr = self._par_cut(gm, et)
            cut_rows.append((cc, dd))
            cut_rhs.append(rr)
            cos_res.append(worst)
            par_res.append(par)
            if max(worst, par) <= tol:
                break
        return {"value": value, "status": "ok", "trace": trace,
                "cos_residuals": cos_res, "par_residuals": par_res,
                "converged": bool(cos_res and max(cos_res[-1], par_res[-1]) <= tol),
                "cuts": len(cut_rows), "x": x}


def _pm(cap: float) -> tuple[float, float]:
    return (-cap, cap)


# ---------------------------------------------------------------------------
# White's section 4 simplified linear program, verbatim
# ---------------------------------------------------------------------------


def simplified_lp(N: int, R: int, method: str = "highs-ipm") -> dict:
    """White (4.1)-(4.4): the even-`M` linear program.

    Minimize Omega subject to `0 <= w_j <= Omega`, `sum w_j = N/4`,
    `sum alpha^-_{j,2m} w_j <= 0` for `1 <= m <= R`, and
    `L^3 sum (j-1)^2 w_j <= 1/3`. White reports 0.375169005340707 at
    `N, R = 80000, 20` and asserts the limit of the approach is below 0.3755.
    """
    L = 2.0 / N
    j = np.arange(1, N + 1, dtype=float)
    nv = N + 1  # Omega, then w_1..w_N

    rows = []
    rhs = []
    for m in range(1, R + 1):
        mm = 2 * m
        alpha_minus = np.cos(math.pi * mm * L * (j - 0.5) / 2.0) - math.pi * mm * L / 4.0
        r = np.zeros(nv)
        r[1:] = alpha_minus
        rows.append(r)
        rhs.append(0.0)
    r = np.zeros(nv)
    r[1:] = (L**3) * (j - 1.0) ** 2
    rows.append(r)
    rhs.append(1.0 / 3.0)

    idx = np.arange(N)
    omega_block = sparse.coo_matrix(
        (
            np.concatenate([np.ones(N), -np.ones(N)]),
            (np.concatenate([idx, idx]), np.concatenate([1 + idx, np.zeros(N, dtype=int)])),
        ),
        shape=(N, nv),
    )
    A = sparse.vstack([omega_block, sparse.csr_matrix(np.array(rows))]).tocsc()
    b = np.concatenate([np.zeros(N), np.array(rhs)])
    eq = np.zeros(nv)
    eq[1:] = 1.0
    obj = np.zeros(nv)
    obj[0] = 1.0
    res = linprog(
        obj,
        A_ub=A,
        b_ub=b,
        A_eq=sparse.csr_matrix(eq.reshape(1, -1)),
        b_eq=np.array([N / 4.0]),
        bounds=[(0.0, 1.0)] + [(0.0, None)] * N,
        method=method,
    )
    return {
        "N": N,
        "R": R,
        "value": float(res.fun) if res.success else None,
        "status": res.message if not res.success else "ok",
    }
