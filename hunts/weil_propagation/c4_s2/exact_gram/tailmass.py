"""exact_gram/: the Mellin tail mass of the zeta modes beyond S, measured (LEMMA.md s5).

Closed form, no w-quadrature (Tate's local functional equation, as two_adic/ta_mellin's
docstring states it: M[F xi](z) = 2 Gamma(z) cos(pi z/2) (2 pi)^{-z} M[xi](1 - z)):

  zeta^_n(s) = norm_n [ 2 Gamma(z) cos(pi z / 2) (2 pi)^{-z} sum_r c_r m_k(-1/2 + i s)
                        - sum_m d_m / (2m + 1/2 - i s) ],   z = 1/2 - i s,

  m_k(mu)  = int_0^1 x^mu P_k(x) dx = sqrt(pi) 2^{-mu-1} Gamma(1+mu) / (Gamma(1+mu/2-k/2) Gamma(mu/2+k/2+3/2)),
  d_m      = sum_r c_r (-1)^m sqrt(pi) pi^{2m} / (Gamma(1+m-k/2) Gamma(m+k/2+3/2))   (zero for 2m < k),

the second sum being the Mellin transform of F xi on [0, 1] from its power series. The tail
mass of mode n beyond S is tau_n(S) = 1 - (1/pi) int_0^S |zeta^_n|^2 ds (||zeta_n|| = 1), by
Gauss panels of width 1/4 with 8 nodes. Float64 (numpy, scipy): measured grade.

    <venv python> hunts/weil_propagation/c4_s2/exact_gram/tailmass.py   # about a minute
"""

from __future__ import annotations

import json
import math
import os
import sys

import numpy as np
from scipy.special import loggamma

HERE = os.path.dirname(os.path.abspath(__file__))
KERNEL = os.path.normpath(os.path.join(HERE, "..", "kernel"))
OUT = os.path.join(HERE, "tailmass.json")
S_LIST = (1200.0, 2266.1020257693895, 6000.0, 10000.0)


def mode_arrays(nvec, dps=40):
    if KERNEL not in sys.path:
        sys.path.insert(0, KERNEL)
    import sonin

    pv, pd = sonin.prolate_vectors(dps, 0, nvec), sonin.prolate_data(dps, 0)
    ks = np.array(pv["ks"], dtype=int)
    C = np.array([[float(c) for c in row] for row in pv["coef"]])  # (nvec, Kdim)
    lam = [float(x) for x in pd["lam"]] + [0.0] * nvec
    norm = 1 / np.sqrt(1 - np.array(lam[:nvec]) ** 2)
    return ks, C, norm


def _rgamma_log(x):
    """log Gamma(x) for real x, and a mask where 1/Gamma(x) = 0 (x a non-positive integer)."""
    x = np.asarray(x, dtype=float)
    pole = (x <= 0) & (np.abs(x - np.round(x)) < 1e-12)
    return np.where(pole, 0.0, np.real(loggamma(np.where(pole, 1.0, x)))), pole


def d_coeffs(ks, C, mmax=None):
    if mmax is None:
        mmax = int(ks.max() // 2) + 60
    m = np.arange(mmax)[:, None]
    k = ks[None, :]
    lg1, p1 = _rgamma_log(1 + m - k / 2)
    lg2, _ = _rgamma_log(m + k / 2 + 1.5)
    logmag = 0.5 * math.log(math.pi) + 2 * m * math.log(math.pi) - lg1 - lg2
    T = np.where(p1, 0.0, np.exp(np.minimum(logmag, 700.0)) * (-1.0) ** m)  # (mmax, Kdim)
    return C @ T.T  # (nvec, mmax)


def zeta_hat(s, ks, C, norm, D):
    """zeta^_n(s) for s an array (s > 0): shape (len(s), nvec)."""
    s = np.asarray(s, dtype=float)
    mu = -0.5 + 1j * s
    lm = (0.5 * math.log(math.pi) - (mu[:, None] + 1) * math.log(2) + loggamma(1 + mu)[:, None]
          - loggamma(1 + mu[:, None] / 2 - ks[None, :] / 2) - loggamma(mu[:, None] / 2 + ks[None, :] / 2 + 1.5))
    Mxi = np.exp(lm) @ C.T  # (ns, nvec)
    z = 0.5 - 1j * s
    # log(2 Gamma(z) cos(pi z/2) (2 pi)^{-z}), stably for large s > 0
    lcos = np.pi * s / 2 + 1j * np.pi / 4 - math.log(2) + np.log1p(np.exp(-1j * np.pi * z))
    pref = np.exp(math.log(2) + loggamma(z) + lcos - z * math.log(2 * math.pi))
    m = np.arange(D.shape[1])
    low = (1.0 / (2 * m[None, :] + 0.5 - 1j * s[:, None])) @ D.T
    return (pref[:, None] * Mxi - low) * norm[None, :]


def tail_masses(nvec=280, S_list=S_LIST, width=0.25, per_panel=8, chunk=4096):
    ks, C, norm = mode_arrays(nvec)
    D = d_coeffs(ks, C)
    xg, wg = np.polynomial.legendre.leggauss(per_panel)
    Smax = max(S_list)
    edges = np.arange(0.0, Smax + 1e-9, width)
    s = (edges[:-1, None] + width / 2 + width / 2 * xg[None, :]).ravel()
    w = np.tile(width / 2 * wg, edges.size - 1)
    acc = {S: np.zeros(nvec) for S in S_list}
    for i0 in range(0, s.size, chunk):
        ss, ww = s[i0 : i0 + chunk], w[i0 : i0 + chunk]
        e = (np.abs(zeta_hat(ss, ks, C, norm, D)) ** 2) * ww[:, None] / math.pi
        for S in S_list:
            sel = ss <= S
            acc[S] += e[sel].sum(axis=0)
    return {S: (1.0 - acc[S]) for S in S_list}


def main():
    t = tail_masses()
    out = {"nvec": 280, "grade": "measured (float64, closed form, Gauss panels 1/4 x 8)",
           "S": {str(S): {"m_z": float(v.sum()), "max_tau": float(v.max()), "min_tau": float(v.min()),
                         "tau_n_sample": {str(n): float(v[n]) for n in (0, 1, 10, 50, 100, 200, 279)}}
                 for S, v in t.items()}}
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
