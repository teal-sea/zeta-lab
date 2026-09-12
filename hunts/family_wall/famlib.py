"""Core numerics for the n-point pressure family."""
import math
import numpy as np

SQRT2 = math.sqrt(2.0)
INV = 1.0 / SQRT2
H = 1.5 - INV / math.tan(INV)          # 0.6725007036794116
CEIL = 0.6818286874638                  # configuration ceiling


def Kraw(x):
    x = np.asarray(x, dtype=float)
    u = math.pi * x - INV
    v = math.pi * x + INV
    su = np.where(np.abs(u) < 1e-12, 1.0 - u * u / 6.0, np.sin(u) / np.where(u == 0, 1.0, u))
    sv = np.where(np.abs(v) < 1e-12, 1.0 - v * v / 6.0, np.sin(v) / np.where(v == 0, 1.0, v))
    return 0.5 * (su + sv)


K0 = float(Kraw(0.0))


def kfun(x):
    return Kraw(x) / K0


def w(x):
    return kfun(x) ** 2


def dKraw(x):
    x = np.asarray(x, dtype=float)
    u = math.pi * x - INV
    v = math.pi * x + INV
    du = math.pi * (u * np.cos(u) - np.sin(u)) / (u * u)
    dv = math.pi * (v * np.cos(v) - np.sin(v)) / (v * v)
    return 0.5 * (du + dv)


def dw(x):
    return 2.0 * kfun(x) * (dKraw(x) / K0)


def Wsum(g):
    """W(g) = sum_s (2/(n-s)) sum_i w(window sum)  -- the pressure-free part."""
    g = np.asarray(g, dtype=float)
    k = len(g)
    n = k + 1
    cs = np.concatenate(([0.0], np.cumsum(g)))
    tot = 0.0
    for s in range(1, n):
        wins = cs[s:] - cs[:-s] if s < len(cs) else None
        wins = cs[s:k + 1] - cs[0:k + 1 - s]
        tot += (2.0 / (n - s)) * np.sum(w(wins))
    return float(tot)


def Wsum_grad(g):
    g = np.asarray(g, dtype=float)
    k = len(g)
    n = k + 1
    cs = np.concatenate(([0.0], np.cumsum(g)))
    tot = 0.0
    diff = np.zeros(k + 1)
    for s in range(1, n):
        wins = cs[s:k + 1] - cs[0:k + 1 - s]
        coef = 2.0 / (n - s)
        tot += coef * np.sum(w(wins))
        d = coef * dw(wins)          # one per window i = 0..k-s
        # window i covers gaps i .. i+s-1
        np.add.at(diff, np.arange(0, k - s + 1), d)
        np.add.at(diff, np.arange(s, k + 1), -d)
    grad = np.cumsum(diff[:k])
    return float(tot), grad


def F(g, p):
    return Wsum(g) + float(np.sum(g)) / p


def F_grad(g, p):
    Wv, gr = Wsum_grad(g)
    return Wv + float(np.sum(g)) / p, gr + 1.0 / p


def phi_exact(c, m, p, n):
    k = n - 1
    return (H - k * (m - 1) / (p * m)) / (1.0 - c * (m - k) / m)


def m_cap(c, n):
    return (n - 1) + int(math.floor(1.0 / c))
