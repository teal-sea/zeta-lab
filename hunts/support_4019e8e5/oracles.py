"""Oracles: every number this arm relies on, checked by a second route."""

from __future__ import annotations

import math
import sys
import os

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
    "hunts", "frontier_math"))

import t1lp  # noqa: E402


def check_f_against_gram_form():
    """f built here vs `hunts/frontier_math/gram_form.py`, independently coded."""
    import gram_form as gf
    ss = np.array([0.3, 1.0, 2.0, math.pi, 6.283185307179586, 13.7, 41.9, 100.5])
    worst_k = max(abs(float(t1lp.kpair(s)) - gf.phi_r(float(s)) ** 2) for s in ss)
    worst_d = max(abs(float(t1lp.damage1(s)) - gf.damage(1.0, float(s))) for s in ss)
    return {"worst_kpair_diff": worst_k, "worst_damage_diff": worst_d}


def check_f_by_quadrature():
    """ghat by direct numerical quadrature of the defining integral."""
    from scipy.integrate import quad
    out = 0.0
    for s in (0.7, 3.3, 9.9, 25.1):
        for re in (0.0, 1.0):
            gr = quad(lambda t: math.cos(math.sqrt(2) * t) * math.exp(re * t)
                      * math.cos(s * t), -0.5, 0.5, limit=200)[0]
            gi = quad(lambda t: math.cos(math.sqrt(2) * t) * math.exp(re * t)
                      * math.sin(s * t), -0.5, 0.5, limit=200)[0]
            ref = complex(*np.real_if_close(
                [float(np.real(t1lp.ghat(re + 1j * s))),
                 float(np.imag(t1lp.ghat(re + 1j * s)))]))
            out = max(out, abs(gr - ref.real), abs(gi - ref.imag))
    return {"worst_ghat_quadrature_diff": out}


def check_asymptotic_envelope(s0=200.0, s1=4000.0, n=400001):
    """C_f with sup_{s>=s0} s |s^2 f(s) - F(s)| <= C_f."""
    s = np.linspace(s0, s1, n)
    err = s * np.abs(t1lp.s2f(s) - t1lp.F_env(s))
    # and further out, to see it settle
    s2 = np.linspace(2e4, 2.4e4, 200001)
    err2 = s2 * np.abs(t1lp.s2f(s2) - t1lp.F_env(s2))
    return {"C_f_sup_on_[%g,%g]" % (s0, s1): float(err.max()),
            "C_f_sup_on_[2e4,2.4e4]": float(err2.max())}


def check_floor():
    """The uniform-lattice gas row, maximised over the gap lam."""
    lams = np.linspace(5.6, 7.0, 141)
    vals = np.array([t1lp.gas_row(float(l), dmax=40000) for l in lams])
    i = int(vals.argmax())
    a, b = lams[max(i - 1, 0)], lams[min(i + 1, len(lams) - 1)]
    gr = (math.sqrt(5) - 1) / 2
    for _ in range(40):
        c, d = b - gr * (b - a), a + gr * (b - a)
        if t1lp.gas_row(c, dmax=40000) < t1lp.gas_row(d, dmax=40000):
            a = c
        else:
            b = d
    lam = (a + b) / 2
    return {"argmax_lambda": lam, "two_pi": 2 * math.pi,
            "gas_row_at_2pi_d1e6": t1lp.gas_row(2 * math.pi, dmax=1000000),
            "gas_row_at_2pi_d1e5": t1lp.gas_row(2 * math.pi, dmax=100000),
            "gas_row_at_argmax": t1lp.gas_row(lam, dmax=200000),
            "brief_floor": t1lp.LATTICE_FLOOR}


def check_G_exact(W=3, K=4, seed=3):
    """s^2 G(s) from the closed form vs numerical quadrature of -int mu cos."""
    from scipy.integrate import quad
    rng = np.random.default_rng(seed)
    kl = t1lp.Klass(W, K)
    x = rng.normal(size=kl.nvar) * 0.3
    # force mu(W) = 0 by shifting mu_0
    e = kl.endval
    x = x - e * (float(e @ x) / float(e @ e))
    mu_k, d_k, psi = kl.mu_of(x)
    h = kl.h

    def mu_fn(w):
        if w <= 0 or w >= kl.W:
            return 0.0
        l = min(int(w / h), kl.N - 1)
        t = w - l * h
        return mu_k[l] + d_k[l] * t + psi[l] * t * t / 2.0

    worst = 0.0
    for s in (0.4, 1.1, 3.7, 12.9, 47.3, 231.0):
        num = -quad(lambda w: mu_fn(w) * math.cos(s * w), 0, kl.W,
                    limit=4000, points=[i * h for i in range(kl.N + 1)])[0]
        ex = float(kl.G(x, np.array([s]))[0])
        worst = max(worst, abs(num - ex))
    return {"worst_G_closedform_vs_quadrature": worst,
            "mu_W_residual": float(kl.endval @ x)}


def run():
    out = {}
    out.update(check_f_against_gram_form())
    out.update(check_f_by_quadrature())
    out.update(check_asymptotic_envelope())
    out.update(check_floor())
    out.update(check_G_exact())
    return out


if __name__ == "__main__":
    import json
    print(json.dumps(run(), indent=2))
