"""Bounded floating-point scout, never a zero-existence proof."""

from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timezone
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.optimize import root


def parameter():
    phi = (1 + mp.sqrt(5)) / 2
    return -phi - mp.sqrt(1 + phi * phi)


def parameter_plus():
    phi = (1 + mp.sqrt(5)) / 2
    return mp.sqrt(1 + phi * phi) - phi


def _resolve_tau(tau):
    return parameter() if tau is None else tau


def dirichlet(s, tau=None):
    tau = _resolve_tau(tau)
    return sum(a * mp.zeta(s, mp.mpf(n) / 5)
               for n, a in enumerate([0, 1, tau, -tau, -1]) if n) / 5**s


def completed(s, tau=None):
    tau = _resolve_tau(tau)
    return (5 / mp.pi)**((s + 1) / 2) * mp.gamma((s + 1) / 2) * dirichlet(s, tau)


def theta(x, nmax=18, tau=None):
    tau = _resolve_tau(tau)
    a = [0, 1, tau, -tau, -1]
    return mp.fsum(n * a[n % 5] * mp.exp(-mp.pi * n*n*x/5)
                   for n in range(1, nmax + 1))


def heat_mp(z, t, nmax=18, upper=4, tau=None, wave='sin'):
    tau = _resolve_tau(tau)
    if wave not in ('sin', 'cos'):
        raise ValueError("wave must be 'sin' or 'cos'")
    a = [0, 1, tau, -tau, -1]
    coeff = [(n, n*a[n % 5]) for n in range(1, nmax + 1) if a[n % 5]]

    def integrand(u):
        q = mp.exp(-mp.pi * mp.exp(2*u) / 5)
        omega = mp.fsum(c * q**(n*n) for n, c in coeff)
        kernel = mp.cos(z*u) if wave == 'cos' else mp.sin(z*u)
        return 4 * mp.exp(t*u*u + 3*u/2) * omega * kernel

    return mp.quad(integrand, [0, mp.mpf('0.5'), 1, 2, upper])


def heat_plus_mp(z, t, nmax=18, upper=4, tau=None):
    """Cosine heat integral for the plus (even-kernel) function."""
    if tau is None:
        tau = parameter_plus()
    return heat_mp(z, t, nmax=nmax, upper=upper, tau=tau, wave='cos')


def heat_grid(order=240):
    nodes, weights = np.polynomial.legendre.leggauss(order)
    u = 2 * (nodes + 1)
    weights = 2 * weights
    with mp.workdps(30):
        tau = float(parameter())
    a = [0., 1., tau, -tau, -1.]
    omega = sum(n*a[n % 5]*np.exp(-np.pi*n*n*np.exp(2*u)/5)
                for n in range(1, 15))
    base = 4 * weights * np.exp(1.5*u) * omega

    def evaluate(z, t):
        return np.sum(base * np.exp(t*u*u) * np.sin(z*u))

    return evaluate


def run():
    started = time.monotonic()
    result = {"grade": "measured", "time": datetime.now(timezone.utc).isoformat(),
              "dps": 40, "zero_solves": [], "continuation": []}
    with mp.workdps(40):
        result['tau_minus'] = mp.nstr(parameter(), 40)
        for seed in [2+9j, 2+18j, 1+7j, 1+13j]:
            before = time.monotonic()
            try:
                def bounded(s):
                    if time.monotonic() - before > 6:
                        raise ValueError('six-second per-solve budget')
                    if not (-1 < s.real < 4 and abs(s.imag) < 30):
                        raise ValueError('iterate left the pilot box')
                    return dirichlet(s)
                s = mp.findroot(bounded, (seed, seed + mp.mpf('0.05')), maxsteps=20)
                row = {"seed": str(seed), "s_re": mp.nstr(s.real, 35),
                       "s_im": mp.nstr(s.imag, 35), "residual": mp.nstr(abs(dirichlet(s)), 8)}
            except (ValueError, ZeroDivisionError) as exc:
                row = {"seed": str(seed), "error": str(exc)}
            row['seconds'] = time.monotonic() - before
            result['zero_solves'].append(row)
            print(json.dumps(row), flush=True)
            if time.monotonic() - started > 30:
                result['stop'] = 'initial solve budget'
                return result
        eligible = [r for r in result['zero_solves']
                    if 's_re' in r and float(r['s_re']) > 0.6 and abs(float(r['s_im'])) < 20]
        if eligible:
            chosen = max(eligible, key=lambda r: float(r['s_re']))
            z = complex(float(chosen['s_im']), float(chosen['s_re']) - .5)
            evaluate = heat_grid()
            for t in [0., .1, .2, .25, .4]:
                def objective(v):
                    w = evaluate(complex(*v), t)
                    return [w.real, w.imag]
                answer = root(objective, [z.real, z.imag], tol=1e-10)
                z = complex(*answer.x)
                result['continuation'].append({"t": t, "z_re": z.real, "z_im": z.imag,
                                               "success": bool(answer.success),
                                               "residual": abs(evaluate(z, t))})
    result['seconds'] = time.monotonic() - started
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('pilot.json'))
    args = parser.parse_args()
    data = run()
    args.output.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(data, indent=2))
