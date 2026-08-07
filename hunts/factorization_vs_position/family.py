from typing import Sequence
import numpy as np
from mpmath import mp
from scipy.optimize import brentq
from zeta.epstein import chi5, L_chi, dh_theta

# Guard digits
_GUARD = 5

def f_kappa_coefficients(kappa: float, n_max: int) -> list[float]:
    """Dirichlet coefficients for the generalized DH family parameterized by kappa."""
    with mp.workdps(15):
        c = (1 - mp.mpc(0, 1) * kappa) / 2
        a = [0.0]
        for n in range(1, n_max + 1):
            v = 2 * c * chi5(n)
            a.append(float(mp.re(v)))
    return a

def f_kappa(s, kappa: float, dps: int = 15) -> mp.mpc:
    """The function F_kappa(s) evaluated directly via its L-function components."""
    with mp.workdps(dps + _GUARD):
        c = (1 - mp.mpc(0, 1) * kappa) / 2
        L1 = L_chi(s, conjugate=False, dps=dps+_GUARD)
        L2 = L_chi(s, conjugate=True, dps=dps+_GUARD)
        return c * L1 + mp.conj(c) * L2

def Z_kappa(t: float, kappa: float, dps: int = 15) -> float:
    """Hardy Z-function for the F_kappa family."""
    with mp.workdps(dps + _GUARD):
        tv = mp.mpf(t)
        s = mp.mpc(mp.mpf(1)/2, tv)
        val = mp.expjpi(dh_theta(tv, dps + _GUARD) / mp.pi) * f_kappa(s, kappa, dps + _GUARD)
        return float(mp.re(val))

def find_online_zeros_kappa(kappa: float, t_max: float = 60.0, dps: int = 15, step: float = 0.1) -> list[float]:
    """Sign-change hunt for Z_kappa to find on-line zeros up to t_max."""
    zeros = []
    t_vals = np.arange(0.0, t_max + step, step)
    
    # We only care about positive t
    # Skip t=0 if we don't want to double count or hit pole-like behavior if any (none here though)
    Z_vals = np.array([Z_kappa(t, kappa, dps) for t in t_vals])
    
    for i in range(len(t_vals) - 1):
        if Z_vals[i] * Z_vals[i+1] < 0:
            root = brentq(lambda t: Z_kappa(t, kappa, dps), t_vals[i], t_vals[i+1])
            zeros.append(float(root))
        elif Z_vals[i] == 0:
            zeros.append(float(t_vals[i]))
            
    return zeros
