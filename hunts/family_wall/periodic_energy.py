"""Exact infinite-periodic energy per particle, with analytic gradient.

w = FT(G)/K0^2, G = f*f supported on [-1,1], f(t)=cos(sqrt2 t) 1_{[-1/2,1/2]}.
Poisson over a period-T lattice truncates exactly at |nu| <= T.
Energy per particle of P points per period:
    Winf = (1/(P T K0^2)) sum_{|nu|<=T} G(nu/T)|S_nu|^2 - 1,  S_nu = sum_j exp(-2 pi i nu x_j/T)
"""
import math, itertools
import numpy as np
from scipy.optimize import minimize

S2 = math.sqrt(2.0)
INV = 1.0 / S2
H = 1.5 - INV / math.tan(INV)
K0 = 0.5 * (math.sin(-INV) / (-INV) + math.sin(INV) / INV)   # = sqrt(2) sin(1/sqrt2)
Z1, Z2 = 1.0572782910088552, 2.030067530128161


def G(u):
    u = np.abs(np.asarray(u, dtype=float))
    out = 0.5 * (1 - u) * np.cos(S2 * u) + np.sin(S2 * (1 - u)) / (2 * S2)
    return np.where(u <= 1.0, out, 0.0)


class Cell:
    def __init__(self, T, P):
        self.T, self.P = T, P
        M = int(math.floor(T))
        self.nu = np.arange(-M, M + 1)
        self.Gv = G(self.nu / T)
        self.pref = 1.0 / (P * T * K0 ** 2)

    def energy(self, x):
        ph = np.exp(-2j * math.pi * np.outer(self.nu, x) / self.T)
        S = ph.sum(axis=1)
        return float(np.sum(self.Gv * np.abs(S) ** 2).real) * self.pref - 1.0

    def energy_grad(self, x):
        ph = np.exp(-2j * math.pi * np.outer(self.nu, x) / self.T)
        S = ph.sum(axis=1)
        E = float(np.sum(self.Gv * np.abs(S) ** 2).real) * self.pref - 1.0
        coef = (-2j * math.pi * self.nu / self.T)
        # d|S|^2/dx_j = 2 Re( conj(S) * coef * ph[:,j] )
        d = 2.0 * np.real(np.conj(S)[:, None] * coef[:, None] * ph)
        gr = (self.Gv[:, None] * d).sum(axis=0) * self.pref
        return E, gr


def min_energy(gbar, Pmax=8, ntry=200, rng=None, npolish=20, seeds_extra=()):
    """min energy per particle over infinite configs of mean gap gbar."""
    rng = rng or np.random.default_rng(0)
    best = (np.inf, None, None)
    for P in range(1, Pmax + 1):
        T = P * gbar
        cell = Cell(T, P)
        if P == 1:
            v = cell.energy(np.array([0.0]))
            if v < best[0]:
                best = (v, 1, np.array([0.0]))
            continue
        seeds = []
        for wd in itertools.product([Z1, Z2], repeat=P):
            a = np.array(wd) * (T / sum(wd))
            seeds.append(np.cumsum(a)[:-1])
        for _ in range(ntry):
            seeds.append(np.sort(rng.uniform(0, T, P - 1)))
        for s in seeds_extra:
            if len(s) == P - 1:
                seeds.append(np.asarray(s, float))
        f = lambda y: cell.energy_grad(np.concatenate(([0.0], y)))[0:1][0]

        def fg(y):
            E, gr = cell.energy_grad(np.concatenate(([0.0], y)))
            return E, gr[1:]
        vals = np.array([cell.energy(np.concatenate(([0.0], s))) for s in seeds])
        for i in np.argsort(vals)[:npolish]:
            r = minimize(fg, seeds[i], jac=True, method='L-BFGS-B',
                         options={'maxiter': 3000, 'ftol': 1e-18, 'gtol': 1e-14})
            if r.fun < best[0]:
                best = (float(r.fun), P, np.concatenate(([0.0], r.x)))
    return best
