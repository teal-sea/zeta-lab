"""Joint out-of-band envelopes with a supremum bound on the whole torus.

Hunt weil_dh_line (#146). The prime comb on the window [-L, L] is
P_L(t) = Phi(t ell), with ell = (log p) over the primes p < e^{2L} and

    Phi(theta) = sum_p sum_{m <= m_p} 2 w_{p^m} cos(m theta_p)   on T^r.

**Cluster structure.** Cover the comb by clusters c (sets of primes) and give
every comb term n a weight wt_c(n) >= 0 in each cluster that contains all its
primes, with sum_c wt_c(n) = 1 exactly (Fractions). Disjoint clusters use
weight 1; overlapping clusters split a shared prime's terms. Then
P_L = sum_c P_c with P_c(t) = Phi_c(t ell_c) a function of the cluster's
coordinates only. Take H(t) = sum_c H_c(t ell_c) with

    H_c(theta_c) = sum_{k in Omega_c} h_k cos(k . theta_c),   |k . ell_c| >= 2L,

every inequality decided in Arb, so every frequency k . ell_c of H is at least
2L and H is admissible (oob_envelope theory, Lemma 1; a finite cosine sum).
P_L - H is the restriction of the function sum_c (Phi_c - H_c) on T^r to the
line t -> t ell, so

    sup_t (P_L - H)(t) <= sum_c sup_t (Phi_c - H_c)(t ell_c) <= sum_c sup_{T^{d_c}} (Phi_c - H_c).

The supremum of a sum is at most the sum of the suprema, and the line maps
into each torus; Kronecker's theorem is not needed for this direction. A
cluster's supremum is a problem in d_c <= 4 dimensions.

**Construction (float, proposes only).** For each cluster, an exchange LP
(HiGHS) over the coefficients h_k, k in a box of out-of-band lattice points,
optionally restricted to the near-band shell 2L <= |k . ell| <= Lambda,
minimizing the largest sampled value of Phi_c - H_c. Each round adds the
Newton-polished local maxima of a finer FFT grid as cuts and drops samples far
from active. The coefficients are then rounded to dyadic rationals, which are
the H actually reported.

**The bound (the claim).** ``sup_bound`` runs a branch and bound over boxes
covering the half torus {u_1 in [0, 1/2]} (the function is even), theta =
2 pi u. On a box with centre c and half-widths r_i every point obeys

    f(c + x) <= f(c) + q(x) + R3,   q(x) = g.x + (1/2) x^T H x,
    R3 = (1/6) sum_k |a_k| (sum_i |k_i| r_i)^3,

with g, H the gradient and Hessian at c. Two bounds for max q over the box
are used, the smaller wins: the separable one
sum |g_i| r_i + (1/2) sum max(H_ii, 0) r_i^2 + sum_{i<j} |H_ij| r_i r_j, and,
where -H >= mu I with mu > 0 is verified (Sylvester's criterion with a priori
rounding margins), the global one q(y) + |g + H y|^2 / (2 mu) for any y
(here y = -H^{-1} g). Both hold for every point of the box, not only at
samples. Centre values are computed in float64 from tables of
e^{2 pi i m / 2^30} (each entry rounded once from a 30-digit mpmath value)
and every float error is bounded a priori under IEEE 754 round to nearest
(``_errors``), so the bound is rigorous given the stated rounding model;
``arb_spot_check`` and ``arb_box_check`` re-evaluate centre values and whole
box bounds in Arb as a second route. A box is discarded once its bound is at
most LB + tau, LB a proven lower bound on the supremum (a value at a dyadic
point minus its error). The returned U is an upper bound for the supremum of
Phi_c - H_c on the whole torus.
"""
from __future__ import annotations

import itertools
import json
import math
import time
from fractions import Fraction

import numpy as np
from flint import arb, ctx
from mpmath import mp, cos as mcos, sin as msin, pi as mpi
from scipy.optimize import linprog

import price

U53 = 2.0 ** -53
TAB_BITS = 15                 # two-level table: m = m1 * 2^15 + m0, B = 30
B_TOTAL = 2 * TAB_BITS
_TABLES = {}


def _tables():
    """T1[m1] = e^{2 pi i m1 2^15 / 2^30}, T0[m0] = e^{2 pi i m0 / 2^30}, each
    entry the float64 nearest to a 30-digit mpmath value (error <= 2^-53 per
    real component, since every component lies in [-1, 1])."""
    if "T" not in _TABLES:
        n = 2 ** TAB_BITS
        with mp.workdps(30):
            t1 = np.array([complex(float(mcos(2 * mpi * m / n)), float(msin(2 * mpi * m / n))) for m in range(n)])
            t0 = np.array([complex(float(mcos(2 * mpi * m / 2 ** B_TOTAL)), float(msin(2 * mpi * m / 2 ** B_TOTAL)))
                           for m in range(n)])
        _TABLES["T"] = (t1, t0)
    return _TABLES["T"]


# ------------------------------------------------------------ cluster data

def _exponents(n: int, primes: list[int]):
    k, m = [0] * len(primes), n
    for i, p in enumerate(primes):
        while m % p == 0:
            m //= p
            k[i] += 1
    return tuple(k), m


def cluster_comb(L: Fraction, primes: list[int], kind: str = "zeta", weights=None):
    """Comb terms of the cluster: list of (k tuple, coefficient as arb).

    kind "zeta": the prime powers p^m of the cluster's primes, coefficient
    2 w_{p^m} = 2 log p / p^{m/2}. kind "dh" (or "epstein"): every n < e^{2L}
    whose prime factors all lie in the cluster, with k the exponent vector of
    n and coefficient 2 Lambda(n)/sqrt(n) of the Davenport-Heilbronn comb (or
    of the Epstein (1,1,6) comb). `weights` maps n to a Fraction multiplier
    (overlapping clusters); a term with weight 0 is omitted."""
    out = []
    with ctx.workprec(price.PREC):
        if kind == "zeta":
            source = [(n, 2 * price.w_arb(p, m)) for n, p, m in price.prime_powers(L) if p in primes]
        elif kind == "dh":
            source = price.dh_comb(L)
        elif kind == "epstein":
            source = price.epstein_comb(L)
        else:
            raise ValueError(kind)
        for n, c in source:
            k, rest = _exponents(n, primes)
            if rest != 1:
                continue
            wt = Fraction(1) if weights is None else Fraction(weights.get(n, 0))
            if wt == 0:
                continue
            out.append((k, c if wt == 1 else c * price.to_arb(wt), n))
    return [(k, c) for k, c, _ in out]


def omega(L: Fraction, primes: list[int], D: list[int], shell=None):
    """Out-of-band lattice points: k in Z^d with |k_i| <= D_i, first nonzero
    coordinate positive (one of each pair +-k), |k . ell| >= 2L decided in Arb.
    With `shell` = Lambda, only points with |k . ell| <= Lambda are kept (a
    float selection; admissibility needs only the lower inequality).
    Returns (kept, n_inband_skipped)."""
    with ctx.workprec(price.PREC):
        twoL = 2 * price.to_arb(L)
        logs = [arb(p).log() for p in primes]
        logs_f = [math.log(p) for p in primes]
        kept, skipped = [], 0
        for k in itertools.product(*[range(-Di, Di + 1) for Di in D]):
            nz = [x for x in k if x != 0]
            if not nz or nz[0] < 0:
                continue
            sf = abs(sum(ki * li for ki, li in zip(k, logs_f)))
            if shell is not None and sf > float(shell):
                continue
            s = abs(sum((ki * li for ki, li in zip(k, logs)), arb(0)))
            if bool(s >= twoL):
                kept.append(k)
            elif bool(s < twoL):
                skipped += 1
            else:
                raise RuntimeError(f"undecided frequency {k}")
    return kept, skipped


def frequency_audit(L: Fraction, primes: list[int], ks) -> dict:
    """Independent check that every k . ell is at least 2L (Arb at 512 bits),
    returning the least margin |k . ell| - 2L as a ball lower endpoint."""
    with ctx.workprec(512):
        twoL = 2 * price.to_arb(L)
        logs = [arb(p).log() for p in primes]
        least = None
        for k in ks:
            s = abs(sum((ki * li for ki, li in zip(k, logs)), arb(0))) - twoL
            if not bool(s >= 0):
                return {"ok": False, "bad": list(k)}
            lo = arb(s.lower())
            least = lo if least is None or bool(lo < least) else least
    return {"ok": True, "least_margin": float(least) if least is not None else None, "count": len(ks)}


# ------------------------------------------------------------- evaluation

def _eval_grid(n, terms_k, terms_a):
    """Values of sum_k a_k cos(2 pi k . j / n) on the full grid (float, FFT)."""
    A = np.zeros(tuple(n), dtype=complex)
    for k, a in zip(terms_k, terms_a):
        A[tuple(ki % ni for ki, ni in zip(k, n))] += a / 2
        A[tuple((-ki) % ni for ki, ni in zip(k, n))] += a / 2
    return np.real(np.fft.ifftn(A)) * np.prod(n)


def _eval_points(U, K, a):
    """f, grad, Hessian at points U (npts x d, in u units) for terms K (P x d)."""
    ph = 2 * np.pi * (U @ K.T)              # npts x P
    c, s = np.cos(ph), np.sin(ph)
    f = c @ a
    g = -(s * a) @ K
    Hs = -np.einsum("np,pi,pj->nij", c * a, K, K)
    return f, g * 2 * np.pi, Hs * (2 * np.pi) ** 2


def _eval_values(U, K, a, chunk=2000):
    out = np.empty(U.shape[0])
    for s0 in range(0, U.shape[0], chunk):
        out[s0:s0 + chunk] = np.cos(2 * np.pi * (U[s0:s0 + chunk] @ K.T)) @ a
    return out


def _polish(U0, K, a, iters=25):
    """Damped Newton ascent (float) from starting points U0, in u units
    (theta = 2 pi u): a Newton step where the Hessian is negative definite,
    a gradient step otherwise, each accepted only if f increases."""
    U = U0.copy()
    f, g, Hs = _eval_points(U, K, a)
    lip = float(np.sum(np.abs(a) * np.sum(np.abs(K), axis=1) ** 2)) * (2 * np.pi) ** 2 + 1.0
    for _ in range(iters):
        w = np.linalg.eigvalsh(Hs)
        neg = np.all(w < 0, axis=1)
        step = g / lip
        if np.any(neg):
            step[neg] = -np.linalg.solve(Hs[neg], g[neg][..., None])[..., 0]
        step = np.clip(step, -0.02, 0.02)
        for _ in range(6):
            Un = (U + step) % 1.0
            fn, gn, Hn = _eval_points(Un, K, a)
            better = fn >= f
            U = np.where(better[:, None], Un, U)
            f = np.where(better, fn, f)
            g = np.where(better[:, None], gn, g)
            Hs = np.where(better[:, None, None], Hn, Hs)
            if np.all(better):
                break
            step = np.where(better[:, None], step, step / 4)
    return U


def _grid_local_maxima(F):
    """Indices of grid points not smaller than any of their 3^d - 1 neighbours."""
    d = F.ndim
    is_max = np.ones(F.shape, dtype=bool)
    for off in itertools.product((-1, 0, 1), repeat=d):
        if all(o == 0 for o in off):
            continue
        is_max &= F >= np.roll(F, shift=off, axis=tuple(range(d)))
    return np.argwhere(is_max)


def _fold(U):
    """Map points to the half torus u_1 in [0, 1/2] (the function is even)."""
    U = U % 1.0
    return np.where(U[:, :1] > 0.5, (-U) % 1.0, U)


# -------------------------------------------------------------------- the LP

def _solve_lp(Cm, phi, nvar, hbound):
    A_ub = np.hstack([-np.ones((Cm.shape[0], 1)), -Cm])
    c = np.concatenate([[1.0], np.zeros(nvar)])
    bounds = [(None, None)] + [(-hbound, hbound)] * nvar
    last = None
    for method in ("highs-ipm", "highs-ds"):
        res = linprog(c, A_ub=A_ub, b_ub=-phi, bounds=bounds, method=method)
        if res.status == 0:
            return res
        last = res
        if res.x is not None and np.all(A_ub @ res.x <= -phi + 1e-9):
            return res
    raise RuntimeError(f"LP failed: {last.message}")


def lp_envelope(L: Fraction, primes: list[int], D: list[int], shell=None, rounds: int = 40,
                over: int = 2, fine: int = 3, tol: float = 2e-5, extra=None, hbound: float = 8.0,
                verbose: bool = False, kind: str = "zeta", weights=None, cap_new: int = 4000,
                keep_factor: int = 6):
    """Exchange LP: minimize t subject to Phi_c(u_s) - H_c(u_s) <= t at the
    sample points u_s (|h_k| <= hbound). Starts from a grid with `over` points
    per half-period of the top degree, adds the Newton-polished local maxima
    of a grid `fine` times finer that exceed t + tol, and keeps the active and
    near-active samples (at most keep_factor * nvar). Float throughout: the LP
    only proposes H; the bound is ``sup_bound``."""
    comb = cluster_comb(L, primes, kind, weights)
    ck = np.array([k for k, _ in comb], dtype=float)
    ca = np.array([float(a.mid()) for _, a in comb])
    Om, skipped = omega(L, primes, D, shell)
    K = np.array(Om, dtype=float).reshape(-1, len(primes))
    Kall = np.vstack([ck, K])
    d = len(primes)
    deg = [int(max(abs(Kall[:, i]).max(), 1)) for i in range(d)]
    n0 = [2 * over * deg[i] + 2 for i in range(d)]
    grid = np.stack(np.meshgrid(*[np.arange(n) / n for n in n0], indexing="ij"), -1).reshape(-1, d)
    pts = grid[grid[:, 0] <= 0.5]
    if extra is not None and len(extra):
        pts = np.vstack([pts, _fold(np.asarray(extra))])
    nf = [fine * n for n in n0]
    keys = [tuple(int(x) for x in k) for k in Kall]
    hist = []
    t = None
    h = np.zeros(len(Om))
    for rnd in range(rounds):
        t_round = time.time()
        Cm = np.cos(2 * np.pi * (pts @ K.T))
        phi = np.cos(2 * np.pi * (pts @ ck.T)) @ ca
        res = _solve_lp(Cm, phi, len(Om), hbound)
        t = float(res.x[0])
        h = res.x[1:]
        vals = np.concatenate([ca, -h])
        F = _eval_grid(nf, keys, vals)
        locs = _grid_local_maxima(F)
        lv = F[tuple(locs.T)]
        order = np.argsort(lv)[::-1]
        sel = locs[order[:cap_new]]
        sel = sel[F[tuple(sel.T)] > t - 0.05 * max(1e-2, abs(t))]
        U0 = sel / np.array(nf)
        Up = _polish(U0, Kall, vals) if U0.shape[0] else U0
        fp = _eval_values(Up, Kall, vals) if Up.shape[0] else np.zeros(0)
        worst = max(float(F.max()), float(fp.max()) if fp.size else -np.inf)
        hist.append((t, worst, int(pts.shape[0])))
        if verbose:
            print(f"  round {rnd}: LP t = {t:.8f}, worst = {worst:.8f}, samples = {pts.shape[0]}, "
                  f"vars = {len(Om)}, {time.time() - t_round:.1f} s", flush=True)
        if worst <= t + tol:
            break
        new = np.vstack([U0[F[tuple(sel.T)] > t + tol], Up[fp > t + tol]])
        new = _fold(new)
        # keep the active and near-active samples only
        slack = t - (phi - Cm @ h)
        cap = max(keep_factor * len(Om), 2000)
        if pts.shape[0] > cap:
            keep = np.argsort(slack)[:cap]
            pts = pts[keep]
        pts = np.vstack([pts, new])
    n_at_bound = int(np.sum(np.abs(h) > hbound * (1 - 1e-6)))
    return {"primes": primes, "D": D, "shell": shell, "omega": Om, "h_float": h, "t_lp": t,
            "history": hist, "inband_skipped": skipped, "samples": pts, "n_at_hbound": n_at_bound}


def lse_envelope(L: Fraction, primes: list[int], D: list[int], shell=None, over: int = 4,
                 betas=(10, 30, 100, 300, 1000, 3000, 10000, 30000), maxiter: int = 400,
                 hbound: float = 8.0, verbose: bool = False, kind: str = "zeta", weights=None, h0=None,
                 exchange: int = 8, fine: int = 2, extra=None, tol: float = 2e-5, cap: int = 3000):
    """Smoothed minimax (float, proposes only). Minimize the log-sum-exp
    (1/beta) log sum_g exp(beta (Phi_c - H_c)(u_g)) over a full grid of
    2 over deg_i + 2 points per dimension plus a growing set E of extra
    points, by L-BFGS-B with |h_k| <= hbound and a continuation in beta.
    Grid values and gradients by FFT. After each pass the local maxima of a
    grid `fine` times finer are Newton-polished (true local maxima of the
    trigonometric polynomial) and those above the current maximum go into E,
    so the optimizer cannot hide peaks between grid points (an exchange
    step). Stops when no polished maximum exceeds the sampled maximum by more
    than tol. Returns h and the history."""
    from scipy.optimize import minimize
    comb = cluster_comb(L, primes, kind, weights)
    Om, skipped = omega(L, primes, D, shell)
    d = len(primes)
    ck = [k for k, _ in comb]
    ca = np.array([float(a.mid()) for _, a in comb])
    allk = ck + [tuple(k) for k in Om]
    Kall = np.array(allk, dtype=float).reshape(-1, d)
    K = np.array(Om, dtype=float).reshape(-1, d)
    ckf = np.array(ck, dtype=float).reshape(-1, d)
    deg = [max(1, max(abs(k[i]) for k in allk)) for i in range(d)]
    n = [2 * over * deg[i] + 2 for i in range(d)]
    Phi = _eval_grid(n, ck, ca)
    idx_p = tuple(np.array([k[i] % n[i] for k in Om]) for i in range(d))
    idx_m = tuple(np.array([(-k[i]) % n[i] for k in Om]) for i in range(d))
    nprod = float(np.prod(n))
    nf = [fine * x for x in n]

    def hgrid(h):
        A = np.zeros(tuple(n), dtype=complex)
        np.add.at(A, idx_p, h / 2)
        np.add.at(A, idx_m, h / 2)
        return np.real(np.fft.ifftn(A)) * nprod

    E = np.zeros((0, d)) if extra is None else _fold(np.asarray(extra, dtype=float).reshape(-1, d))
    h = np.zeros(len(Om)) if h0 is None else np.array(h0, dtype=float)
    hist = []
    for outer in range(exchange):
        PhiE = np.cos(2 * np.pi * (E @ ckf.T)) @ ca if E.shape[0] else np.zeros(0)
        CE = np.cos(2 * np.pi * (E @ K.T)) if E.shape[0] else np.zeros((0, len(Om)))
        stage = betas if (outer == 0 and h0 is None) else betas[-3:]
        for beta in stage:
            def fun(hv):
                f = Phi - hgrid(hv)
                fE = PhiE - CE @ hv
                M = max(f.max(), fE.max() if fE.size else -np.inf)
                e = np.exp(beta * (f - M))
                eE = np.exp(beta * (fE - M))
                Z = e.sum() + eE.sum()
                val = M + math.log(Z) / beta
                Fh = np.fft.fftn(e / Z)
                gk = -0.5 * (np.real(Fh[idx_p]) + np.real(Fh[idx_m]))
                if fE.size:
                    gk = gk - (eE / Z) @ CE
                return val, gk
            res = minimize(fun, h, jac=True, method="L-BFGS-B", bounds=[(-hbound, hbound)] * len(Om),
                           options={"maxiter": maxiter, "maxcor": 30, "ftol": 1e-15, "gtol": 1e-12})
            h = res.x
        fgrid = Phi - hgrid(h)
        sampled = max(float(fgrid.max()), float((PhiE - CE @ h).max()) if E.shape[0] else -np.inf)
        vals = np.concatenate([ca, -h])
        F = _eval_grid(nf, [tuple(int(x) for x in k) for k in Kall], vals)
        locs = _grid_local_maxima(F)
        lv = F[tuple(locs.T)]
        order = np.argsort(lv)[::-1][:cap]
        sel = locs[order]
        sel = sel[F[tuple(sel.T)] > sampled - 0.1 * max(1e-2, abs(sampled))]
        U0 = sel / np.array(nf)
        Up = _polish(U0, Kall, vals) if U0.shape[0] else U0
        fp = _eval_values(Up, Kall, vals) if Up.shape[0] else np.zeros(0)
        worst = max(float(F.max()), float(fp.max()) if fp.size else -np.inf)
        hist.append((outer, float(res.fun), sampled, worst, int(E.shape[0])))
        if verbose:
            print(f"  lse pass {outer}: smooth {res.fun:.8f}, sampled max {sampled:.8f}, polished max {worst:.8f}, "
                  f"extra {E.shape[0]}", flush=True)
        if worst <= sampled + tol:
            break
        add = _fold(Up[fp > sampled - 0.02 * max(1e-2, abs(sampled))])
        E = np.vstack([E, add])
    return {"omega": Om, "h_float": h, "grid": n, "history": hist, "inband_skipped": skipped,
            "extra": E, "t_sampled": sampled, "t_polished": worst}


def dyadic(h: np.ndarray, bits: int = 36) -> list[Fraction]:
    return [Fraction(int(round(x * 2 ** bits)), 2 ** bits) for x in h]


# ----------------------------------------------------------- the bound

def _terms(L, primes, Om, hq, kind="zeta", weights=None):
    """All terms of f = Phi_c - H_c: integer k (P x d), float a, upper bounds
    on |a| and on |a - float(a)|."""
    comb = cluster_comb(L, primes, kind, weights)
    ks = [k for k, _ in comb] + [tuple(k) for k in Om]
    a, a_abs, a_err = [], [], []
    for _, c in comb:
        af = float(c.mid())
        a.append(af)
        a_abs.append(float(abs(c).upper()) * (1 + 2 * U53))
        a_err.append(float(c.rad()) + abs(af) * U53 + float(abs(c).upper()) * U53)
    for x in hq:
        xf = float(x)
        if Fraction(xf) != x:
            raise ValueError("H coefficient not exact in float64")
        a.append(-xf)
        a_abs.append(abs(xf))
        a_err.append(0.0)
    return (np.array(ks, dtype=np.int64).reshape(-1, len(primes)), np.array(a), np.array(a_abs),
            np.array(a_err))


def _errors(K, a_abs, a_err, P):
    """A priori float error bounds for f, grad and Hessian at a centre.
    Each table value carries |error| <= 8u (two rounded table entries and one
    complex product); a dot product of P terms in any summation order adds
    gamma_P = P u / (1 - P u) relative to the sum of absolute terms."""
    gam = (P + 4) * U53 / (1 - (P + 4) * U53)
    eps_val = 8 * U53
    base = a_abs * (1 + eps_val)
    per = a_err + a_abs * eps_val + gam * base
    Ev = float(np.sum(per)) * 1.01
    absK = np.abs(K).astype(float)
    Eg = (per @ absK) * 1.01          # theta units
    EH = np.einsum("p,pi,pj->ij", per, absK, absK) * 1.01
    return Ev, Eg, EH


def _phases(Mu, K):
    """Integer phases (k . u) * 2^30 mod 2^30 for integer points Mu = u * 2^30."""
    return (Mu @ K.T) & ((1 << B_TOTAL) - 1)


def _values_at(Mu, K, a, t1, t0, derivs=True):
    m = _phases(Mu, K)
    z = t1[m >> TAB_BITS] * t0[m & ((1 << TAB_BITS) - 1)]
    c, s = z.real, z.imag
    f = c @ a
    if not derivs:
        return f
    g = -(s * a) @ K                     # derivatives in theta = 2 pi u
    Kf = K.astype(float)
    Hs = -np.einsum("np,pi,pj->nij", c * a, Kf, Kf)
    return f, g, Hs


def _box_values(J, Bv, K, a, t1, t0):
    """Centre values for boxes J (centre index), levels Bv (per dimension)."""
    shift = (B_TOTAL - Bv - 1)                      # nbox x d
    num = (2 * J + 1) << shift                      # u_i * 2^30, exact integers
    return _values_at(num, K, a, t1, t0)


def _leibniz_minors(B):
    """Leading principal minors of the stacked symmetric matrices B (n x d x d)
    by the Leibniz formula, with the sums of absolute products (permanents of
    |B|) that bound their rounding errors."""
    n, d, _ = B.shape
    dets, perms = [], []
    for k in range(1, d + 1):
        det = np.zeros(n)
        per = np.zeros(n)
        for sigma in itertools.permutations(range(k)):
            inv = sum(1 for i in range(k) for j in range(i + 1, k) if sigma[i] > sigma[j])
            term = np.ones(n)
            for i in range(k):
                term = term * B[:, i, sigma[i]]
            det += term if inv % 2 == 0 else -term
            per += np.abs(term)
        dets.append(det)
        perms.append(per)
    return dets, perms


def _quadratic_bound(f, g, Hs, Eg, EH, d):
    """Rigorous upper bound Q >= max over all x of q_true(x) = g_true . x +
    (1/2) x^T H_true x where |g_true - g| <= Eg and |H_true - Hs| <= EH
    entrywise, for boxes whose -Hs is verified positive definite; +inf
    elsewhere. See the module docstring."""
    n = f.shape[0]
    Q = np.full(n, np.inf)
    A = -Hs
    try:
        lam = np.linalg.eigvalsh(A)[:, 0]
    except np.linalg.LinAlgError:
        return Q
    nEH = float(np.sqrt(np.sum(EH ** 2))) * 1.01
    cand = np.where(lam > 8 * nEH + 1e-12)[0]
    if cand.size == 0:
        return Q
    Ac = A[cand]
    mu_hat = 0.5 * lam[cand]
    Bm = Ac.copy()
    idx = np.arange(d)
    Bm[:, idx, idx] = Ac[:, idx, idx] - mu_hat[:, None]
    dets, perms = _leibniz_minors(Bm)
    ok = np.ones(cand.size, dtype=bool)
    for k, (det, per) in enumerate(zip(dets, perms), start=1):
        ok &= det > (2 * (k + math.factorial(k)) + 4) * U53 * per + 1e-300
    diag_max = np.max(np.abs(Bm[:, idx, idx]), axis=1)
    mu = mu_hat * (1 - 4 * U53) - 1.01 * U53 * diag_max - nEH
    ok &= mu > 0
    if not np.any(ok):
        return Q
    cand, Ac, mu = cand[ok], Ac[ok], mu[ok]
    gc = g[cand]
    y = np.linalg.solve(Ac, gc[..., None])[..., 0]
    Ay = np.einsum("nij,nj->ni", Ac, y)
    qhat = np.sum(gc * y, axis=1) - 0.5 * np.sum(y * Ay, axis=1)
    s1 = np.sum(np.abs(gc * y), axis=1)
    s2 = np.einsum("ni,nij,nj->n", np.abs(y), np.abs(Ac), np.abs(y))
    err_q = 2 * (d + 4) * U53 * (s1 + s2)
    ay = np.abs(y)
    pert = ay @ Eg + 0.5 * np.einsum("ni,ij,nj->n", ay, EH, ay)
    res = np.abs(gc - Ay) + 2 * (d + 2) * U53 * (np.abs(gc) + np.einsum("nij,nj->ni", np.abs(Ac), ay)) \
        + Eg[None, :] + ay @ EH.T
    rq = np.sum(res * res, axis=1) * (1 + 8 * U53) / (2 * mu)
    Q[cand] = (qhat + err_q + pert + rq) * (1 + 8 * U53) + 1e-300
    return Q


def sup_bound(L: Fraction, primes: list[int], Om, hq: list[Fraction], tau: float = 2e-4,
              max_level: int = 28, batch: int = 4000, max_boxes: int = 60_000_000, verbose=False,
              kind: str = "zeta", weights=None, quadratic: bool = True, time_limit: float | None = None):
    """Rigorous upper bound U >= sup over T^d of Phi_c - H_c (see the module
    docstring). Returns U as a float rounded upward, with statistics."""
    t1, t0 = _tables()
    K, a, a_abs, a_err = _terms(L, primes, Om, hq, kind, weights)
    P, d = K.shape
    Ev, Eg, EH = _errors(K, a_abs, a_err, P)
    absK = np.abs(K).astype(float)
    b0 = np.array([max(2, math.ceil(math.log2(4 * max(1, int(absK[:, i].max()))))) for i in range(d)])
    ranges = [range(2 ** (b0[0] - 1))] + [range(2 ** b0[i]) for i in range(1, d)]
    J = np.array(list(itertools.product(*ranges)), dtype=np.int64)
    Bv = np.tile(b0, (J.shape[0], 1)).astype(np.int64)
    LB = -math.inf
    unresolved_ub = -math.inf
    evaluated = 0
    quad_used = 0
    t_start = time.time()
    rounds = 0
    best_pts: list = []
    while J.shape[0]:
        rounds += 1
        keepJ, keepB = [], []
        for s0 in range(0, J.shape[0], batch):
            Jb, Bb = J[s0:s0 + batch], Bv[s0:s0 + batch]
            f, g, Hs = _box_values(Jb, Bb, K, a, t1, t0)
            evaluated += Jb.shape[0]
            top = np.argsort(f)[-8:]
            for q in top:
                best_pts.append((float(f[q]), (2 * Jb[q] + 1) / np.ldexp(1.0, (Bb[q] + 1).astype(int))))
            best_pts.sort(key=lambda z: -z[0])
            del best_pts[64:]
            LB = max(LB, float(np.max(f)) - Ev)
            r = 2 * np.pi * (1 + 4 * U53) * np.ldexp(1.0, -(Bb + 1).astype(int))     # nbox x d, upper
            rk = r @ absK.T                                  # nbox x P: sum_i |k_i| r_i
            R3 = (rk ** 3 @ a_abs) / 6.0 * (1 + 2 * (P + 16) * U53)
            lin = np.sum((np.abs(g) + Eg) * r, axis=1)
            diag = 0.5 * np.sum((np.maximum(np.einsum("nii->ni", Hs), 0) + np.diag(EH)) * r * r, axis=1)
            off = np.zeros(Jb.shape[0])
            for i in range(d):
                for j in range(i + 1, d):
                    off += (np.abs(Hs[:, i, j]) + EH[i, j]) * r[:, i] * r[:, j]
            # lin, diag and off are float sums of nonnegative terms, each within
            # gamma_{P+16} of its exact value; inflate them by twice that.
            q1 = (lin + diag + off) * (1 + 2 * (P + 16) * U53)
            if quadratic and d >= 1:
                q2 = _quadratic_bound(f, g, Hs, Eg, EH, d)
                quad_used += int(np.sum(q2 < q1))
                qq = np.minimum(q1, q2)
                # Newton points: better proven lower ends where the model peak
                # lies inside its box
                fin = np.isfinite(q2)
                if np.any(fin):
                    ii = np.where(fin)[0]
                    ii = ii[np.argsort(f[ii] + q2[ii])[-64:]]
                    y = np.linalg.solve(-Hs[ii], g[ii][..., None])[..., 0]
                    inside = np.all(np.abs(y) <= r[ii], axis=1)
                    if np.any(inside):
                        ii, y = ii[inside], y[inside]
                        cu = (2 * Jb[ii] + 1).astype(float) / np.ldexp(1.0, (Bb[ii] + 1).astype(int))
                        Mu = np.rint(((cu + y / (2 * np.pi)) % 1.0) * 2 ** B_TOTAL).astype(np.int64)
                        fN = _values_at(Mu, K, a, t1, t0, derivs=False)
                        LB = max(LB, float(np.max(fN)) - Ev)
            else:
                qq = q1
            target = LB + tau
            ub = f + Ev + qq + R3 + 8 * U53 * (np.abs(f) + Ev + qq + R3 + 1)
            live = ub > target
            if not np.any(live):
                continue
            Jl, Bl = Jb[live], Bb[live]
            # split the dimension with the largest first- plus second-order slack
            share = (np.abs(g[live]) + Eg) * r[live] + 0.5 * (np.abs(np.einsum("nii->ni", Hs[live])) + np.diag(EH)) * r[live] ** 2
            share = share + (rk[live] ** 2 @ (a_abs[:, None] * absK)) * r[live] / 2.0
            at_max = Bl >= max_level
            share[at_max] = -1.0
            dim = np.argmax(share, axis=1)
            stuck = np.all(at_max, axis=1)
            if np.any(stuck):
                unresolved_ub = max(unresolved_ub, float(np.max(ub[live][stuck])))
            Jl, Bl, dim = Jl[~stuck], Bl[~stuck], dim[~stuck]
            rows = np.arange(Jl.shape[0])
            J2a, J2b = Jl.copy(), Jl.copy()
            J2a[rows, dim] = 2 * Jl[rows, dim]
            J2b[rows, dim] = 2 * Jl[rows, dim] + 1
            B2 = Bl.copy()
            B2[rows, dim] += 1
            keepJ += [J2a, J2b]
            keepB += [B2, B2]
        if keepJ:
            J = np.vstack(keepJ)
            Bv = np.vstack(keepB)
        else:
            J = np.zeros((0, d), dtype=np.int64)
        if verbose:
            print(f"    level-round {rounds}: live {J.shape[0]}, evaluated {evaluated}, LB {LB:.10f}, "
                  f"{time.time() - t_start:.0f} s", flush=True)
        if evaluated > max_boxes:
            raise RuntimeError("box budget exhausted")
        if time_limit is not None and time.time() - t_start > time_limit:
            raise RuntimeError("time limit")
    U = max(LB + tau, unresolved_ub)
    U_up = U * (1 + 4 * U53) + 4 * U53
    return {"U": U_up, "LB": LB, "tau": tau, "boxes": evaluated, "rounds": rounds,
            "unresolved": unresolved_ub > -math.inf, "seconds": time.time() - t_start,
            "P": int(P), "Ev": Ev, "quadratic_wins": quad_used,
            "best_points": np.array([u for _, u in best_pts])}


def arb_spot_check(L: Fraction, primes: list[int], Om, hq, n: int = 200, seed: int = 1, level: int = 12,
                   kind: str = "zeta", weights=None):
    """Second route for the centre values: n random dyadic centres, f in Arb
    against the float table route; returns the largest deviation and the
    a priori error bound it must respect."""
    t1, t0 = _tables()
    K, a, a_abs, a_err = _terms(L, primes, Om, hq, kind, weights)
    P, d = K.shape
    Ev, _, _ = _errors(K, a_abs, a_err, P)
    rng = np.random.default_rng(seed)
    J = rng.integers(0, 2 ** level, size=(n, d), dtype=np.int64)
    Bv = np.full((n, d), level, dtype=np.int64)
    f, _, _ = _box_values(J, Bv, K, a, t1, t0)
    comb = cluster_comb(L, primes, kind, weights)
    worst = 0.0
    with ctx.workprec(200):
        coef = [c for _, c in comb] + [-price.to_arb(x) for x in hq]
        two_pi = 2 * arb.pi()
        for b in range(n):
            u = [price.to_arb(Fraction(2 * int(J[b, i]) + 1, 2 ** (level + 1))) for i in range(d)]
            val = arb(0)
            for kk, cc in zip(K, coef):
                ph = two_pi * sum((int(kk[i]) * u[i] for i in range(d)), arb(0))
                val += cc * ph.cos()
            worst = max(worst, abs(float(val.mid()) - f[b]) + float(val.rad()))
    return {"max_deviation": float(worst), "a_priori_bound": float(Ev), "ok": bool(worst <= Ev)}


def arb_box_check(L: Fraction, primes: list[int], Om, hq, n: int = 30, seed: int = 2, level: int = 9,
                  kind: str = "zeta", weights=None):
    """Second route for the whole box bound: on n random boxes of a fixed
    level, the separable Taylor bound (f(c) + sum |g_i| r_i + (1/2) sum
    max(H_ii, 0) r_i^2 + sum |H_ij| r_i r_j + R3) recomputed entirely in Arb
    must not exceed the float bound; and Arb evaluation of f at 27 points of
    each box must stay below the Arb bound."""
    t1, t0 = _tables()
    K, a, a_abs, a_err = _terms(L, primes, Om, hq, kind, weights)
    P, d = K.shape
    Ev, Eg, EH = _errors(K, a_abs, a_err, P)
    absK = np.abs(K).astype(float)
    rng = np.random.default_rng(seed)
    J = rng.integers(0, 2 ** level, size=(n, d), dtype=np.int64)
    Bv = np.full((n, d), level, dtype=np.int64)
    f, g, Hs = _box_values(J, Bv, K, a, t1, t0)
    r = 2 * np.pi * (1 + 4 * U53) * np.ldexp(1.0, -(Bv + 1).astype(int))
    rk = r @ absK.T
    R3 = (rk ** 3 @ a_abs) / 6.0 * (1 + 2 * (P + 16) * U53)
    lin = np.sum((np.abs(g) + Eg) * r, axis=1)
    diag = 0.5 * np.sum((np.maximum(np.einsum("nii->ni", Hs), 0) + np.diag(EH)) * r * r, axis=1)
    off = np.zeros(n)
    for i in range(d):
        for j in range(i + 1, d):
            off += (np.abs(Hs[:, i, j]) + EH[i, j]) * r[:, i] * r[:, j]
    q1 = (lin + diag + off) * (1 + 2 * (P + 16) * U53)
    ub_float = f + Ev + q1 + R3 + 8 * U53 * (np.abs(f) + Ev + q1 + R3 + 1)
    comb = cluster_comb(L, primes, kind, weights)
    worst_gap, worst_sample = math.inf, math.inf
    with ctx.workprec(200):
        coef = [c for _, c in comb] + [-price.to_arb(x) for x in hq]
        two_pi = 2 * arb.pi()
        for b in range(n):
            cu = [price.to_arb(Fraction(2 * int(J[b, i]) + 1, 2 ** (level + 1))) for i in range(d)]
            ra = [two_pi / 2 ** (level + 1) for _ in range(d)]
            val, grad, hess = arb(0), [arb(0)] * d, [[arb(0)] * d for _ in range(d)]
            R3a = arb(0)
            for kk, cc in zip(K, coef):
                ph = two_pi * sum((int(kk[i]) * cu[i] for i in range(d)), arb(0))
                s_, c_ = ph.sin_cos()
                val += cc * c_
                for i in range(d):
                    grad[i] = grad[i] - cc * s_ * int(kk[i])
                    for j in range(d):
                        hess[i][j] = hess[i][j] - cc * c_ * int(kk[i]) * int(kk[j])
                R3a += abs(cc) * sum((abs(int(kk[i])) * ra[i] for i in range(d)), arb(0)) ** 3 / 6
            ub = val + R3a
            for i in range(d):
                ub += abs(grad[i]) * ra[i]
                hii = hess[i][i]
                ub += hii.max(arb(0)) * ra[i] ** 2 / 2
                for j in range(i + 1, d):
                    ub += abs(hess[i][j]) * ra[i] * ra[j]
            worst_gap = min(worst_gap, ub_float[b] - float(ub.upper()))
            for off3 in itertools.product((-1, 0, 1), repeat=d):
                pt = [cu[i] + price.to_arb(Fraction(off3[i], 2 ** (level + 1))) for i in range(d)]
                v = arb(0)
                for kk, cc in zip(K, coef):
                    v += cc * (two_pi * sum((int(kk[i]) * pt[i] for i in range(d)), arb(0))).cos()
                worst_sample = min(worst_sample, float((ub - v).lower()))
    return {"n": int(n), "min_float_minus_arb_bound": float(worst_gap), "min_bound_minus_sample": float(worst_sample),
            "ok": bool(worst_gap >= 0 and worst_sample >= 0)}


def build_cluster(L: Fraction, primes: list[int], D: list[int], tau: float = 2e-4, shell=None,
                  method: str = "lse", outer: int = 3, verbose: bool = False, kind: str = "zeta", weights=None,
                  opt_kwargs=None, sb_kwargs=None):
    """Optimizer (smoothed minimax with exchange, or the exchange LP), then the
    whole-torus bound; if the bound's proven lower end exceeds the optimizer's
    sampled maximum by more than 5 tau, the bound's best centres go back into
    the optimizer as extra samples and it restarts from the current h."""
    extra = None
    h0 = None
    opt = sb = hq = None
    opt_kwargs = dict(opt_kwargs or {})
    sb_kwargs = dict(sb_kwargs or {})
    t0 = time.time()
    t_opt = None
    for it in range(outer):
        if method == "lse":
            opt = lse_envelope(L, primes, D, shell=shell, extra=extra, h0=h0, verbose=verbose, kind=kind,
                               weights=weights, **opt_kwargs)
            t_opt = opt["t_polished"]
        else:
            opt = lp_envelope(L, primes, D, shell=shell, extra=extra, verbose=verbose, kind=kind, weights=weights,
                              **opt_kwargs)
            t_opt = opt["t_lp"]
        hq = dyadic(opt["h_float"])
        sb = sup_bound(L, primes, opt["omega"], hq, tau=tau, verbose=verbose, kind=kind, weights=weights,
                       **sb_kwargs)
        if verbose:
            print(f"  outer {it}: optimizer {t_opt:.8f}, proven LB {sb['LB']:.8f}, U {sb['U']:.8f}", flush=True)
        if sb["LB"] <= t_opt + 5 * tau or it == outer - 1:
            break
        bp = _fold(sb["best_points"])
        prev = opt["extra"] if method == "lse" else opt["samples"]
        extra = np.vstack([prev, bp])
        h0 = opt["h_float"]
    audit = frequency_audit(L, primes, opt["omega"])
    sb = dict(sb)
    sb.pop("best_points", None)
    return {"primes": primes, "D": D, "shell": None if shell is None else float(shell), "kind": kind,
            "method": method,
            "weights": None if weights is None else {str(n): str(Fraction(w)) for n, w in weights.items()},
            "t_opt": t_opt, "U": sb["U"], "sup_bound": sb,
            "frequency_audit": audit, "omega": [list(k) for k in opt["omega"]],
            "h": [f"{x.numerator}/{x.denominator}" for x in hq],
            "h_l1": float(sum(abs(x) for x in hq)), "h_max": float(max(abs(x) for x in hq)) if hq else 0.0,
            "max_frequency": max(abs(sum(k[i] * math.log(primes[i]) for i in range(len(primes)))) for k in opt["omega"])
            if opt["omega"] else 0.0,
            "outer_iterations": it + 1, "seconds_total": time.time() - t0,
            "optimizer_history": opt["history"]}


# ------------------------------------------------------------------ a coarse bound with every step in Arb
#
# sup_bound above is rigorous under an IEEE 754 rounding model. This is the same
# question at a coarse tolerance with no rounding model: centre values and
# gradients in Arb, and the second-order Taylor remainder
#
#     f(c + x) <= f(c) + sum_i |g_i| r + (1/2) r^2 sum_k |a_k| |k|_1^2,   |x_i| <= r,
#
# since |x^T Hess f x| = |sum_k a_k (k.x)^2 cos(.)| <= sum_k |a_k| (|k|_1 r)^2.
# Boxes cover the half torus u_1 in [0, 1/2], u in [0, 1)^(d-1), theta = 2 pi u
# (f is a cosine sum, so f(-u) = f(u)); a box is discarded once its bound is at
# most `target`, otherwise split into 2^d children.

def arb_sup_bound(L: Fraction, primes: list[int], Om, hq, target: Fraction, kind: str = "zeta", weights=None,
                  level0: int = 3, max_level: int = 18, prec: int = 128, max_boxes: int | None = None,
                  log_every: int = 0, boxes0=None) -> dict:
    """Prove sup_{T^d} (Phi_c - H_c) <= target with Arb, or report that it was
    not reached within max_level / max_boxes. Returns ok, boxes evaluated per
    level, the largest bound among discarded boxes, and the largest centre
    value seen (a lower bound on the supremum). boxes0, if given, is the list
    of starting boxes at level0 (index tuples), so that disjoint parts of the
    level0 grid can run in separate processes; the parts must cover the grid."""
    t_start = time.time()
    with ctx.workprec(prec):
        comb = cluster_comb(L, primes, kind, weights)
        terms = [(tuple(int(x) for x in k), c) for k, c in comb] + \
                [(tuple(int(x) for x in k), -price.to_arb(h)) for k, h in zip(Om, hq)]
        d = len(primes)
        K = [k for k, _ in terms]
        A = [a for _, a in terms]
        absA = [abs(a) for a in A]
        M2 = sum((absA[j] * sum(abs(x) for x in K[j]) ** 2 for j in range(len(K))), arb(0))
        T = price.to_arb(Fraction(target))
        two_pi = 2 * arb.pi()
        cache: dict = {}

        def sc(level, m):
            key = (level, m)
            v = cache.get(key)
            if v is None:
                v = (two_pi * m / 2 ** (level + 1)).sin_cos()
                cache[key] = v
            return v

        level = level0
        boxes = list(boxes0) if boxes0 is not None else \
            [tuple(j) for j in itertools.product(range(2 ** (level0 - 1)), *[range(2 ** level0)] * (d - 1))]
        per_level, max_disc, best_centre, n_eval = {}, None, None, 0
        ok = True
        while boxes:
            if level > max_level or (max_boxes is not None and n_eval + len(boxes) > max_boxes):
                ok = False
                break
            r = two_pi / 2 ** (level + 1)
            rem = M2 * r * r / 2
            mod = 2 ** (level + 1)
            nxt = []
            for J in boxes:
                odd = [2 * j + 1 for j in J]
                f = arb(0)
                g = [arb(0)] * d
                for k, a in zip(K, A):
                    m = sum(ki * oi for ki, oi in zip(k, odd)) % mod
                    s_, c_ = sc(level, m)
                    f += a * c_
                    as_ = a * s_
                    for i in range(d):
                        if k[i]:
                            g[i] -= as_ * k[i]
                ub = f + r * sum((abs(x) for x in g), arb(0)) + rem
                n_eval += 1
                if best_centre is None or bool(f.lower() > best_centre):
                    best_centre = arb(f.lower())
                if bool(ub <= T):
                    max_disc = ub.upper() if max_disc is None else max(max_disc, ub.upper())
                else:
                    for off in itertools.product((0, 1), repeat=d):
                        nxt.append(tuple(2 * j + o for j, o in zip(J, off)))
                if log_every and n_eval % log_every == 0:
                    print(json.dumps({"primes": primes, "level": level, "evaluated": n_eval, "queued": len(nxt),
                                      "seconds": round(time.time() - t_start, 1)}), flush=True)
            per_level[level] = len(boxes)
            boxes = nxt
            level += 1
            cache.clear()
    return {"primes": primes, "target": str(Fraction(target)), "ok": ok, "boxes_per_level": per_level,
            "evaluated": n_eval, "max_discarded_bound": None if max_disc is None else float(arb(max_disc).upper()),
            "best_centre_value_lower": None if best_centre is None else float(best_centre.lower()),
            "M2": float(M2.upper()), "terms": len(K), "prec": prec, "seconds": time.time() - t_start}


def m2_bound(L: Fraction, primes: list[int], Om, hq, kind: str = "zeta", weights=None, prec: int = 128) -> float:
    """sum_k |a_k| |k|_1^2 for f = Phi_c - H_c (the constant of arb_sup_bound's remainder)."""
    with ctx.workprec(prec):
        comb = cluster_comb(L, primes, kind, weights)
        tot = sum((abs(c) * sum(abs(int(x)) for x in k) ** 2 for k, c in comb), arb(0))
        tot += sum((abs(price.to_arb(h)) * sum(abs(int(x)) for x in k) ** 2 for k, h in zip(Om, hq)), arb(0))
        return float(tot.upper())
