"""Laplace expansion for D_n, and the explicit finite threshold for Turan.

Reduction established numerically in this hunt (journal.md), validated against
the committed zeta/li.py table to 18 digits:

    gamma(n) = 8 n! b_n,   b_n = J_{n-1} - J_n/4,   J_k = I_k/(4^k (2k)!),
    I_k = int_0^inf u^{2k} w(u) du,   w(u) = e^{u/4} omega(e^u) > 0,

    q_n := gamma(n)/gamma(n-1) = n b_n / b_{n-1},   r_n = q_{n+1}/q_{n+2},

and, keeping the exact b_n (no asymptotic shortcut),

    r_n = [(n+1)/(n+2)] * (b_{n+1}b_{n+1} / (b_n b_{n+2})) ...   (exact)
        = [(n+2)/(n+1)] * I_n^2/(I_{n-1} I_{n+1}) * (1 + O(J_n/J_{n-1})).

Define the Cauchy-Schwarz deficit of the positive-weight moments,

    D_n := 1 - I_n^2 / (I_{n-1} I_{n+1})  >= 0   (automatic, w > 0),

so that the Turan inequality r_n >= 1 is, at leading order,

    D_n  <=  1/(n+1).

The single-term regime: for u >= ~1, omega(e^u) = e^{-pi e^u}(1 + O(e^{-3 pi e^u})),
so w(u) = exp(u/4 - pi e^u + o(1)) and

    I_n = int_0^inf exp(Psi(u)) du,   Psi(u) = 2n log u + u/4 - pi e^u,

whose saddle u_* solves  Psi'(u_*) = 0, i.e.  pi e^{u_*} = 1/4 + 2n/u_*.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).parent


def omega_series(x, dps):
    with mp.workdps(dps):
        tot = mp.mpf(0)
        n = 1
        while True:
            t = mp.e ** (-mp.pi * n * n * x)
            tot += t
            if t < mp.mpf(10) ** (-(dps - 5)):
                break
            n += 1
        return tot


def w(u, dps):
    with mp.workdps(dps):
        return mp.e ** (u / 4) * omega_series(mp.e**u, dps)


def lw(u, dps):
    with mp.workdps(dps):
        return mp.log(w(u, dps))


def saddle(n, dps, guess=None):
    """Solve pi e^u = 1/4 + 2n/u in the single-term regime (u >= 1)."""
    with mp.workdps(dps):
        f = lambda u: mp.pi * mp.e**u - mp.mpf(1) / 4 - 2 * n / u
        if guess is None:
            guess = mp.log(mp.mpf(2) * n / mp.pi) - mp.log(mp.log(mp.mpf(2) * n / mp.pi))
        return mp.findroot(f, guess)


def laplace_I(n, dps, orders=1):
    """Laplace approximation to I_n with the sqrt(2 pi / Psi'') prefactor."""
    with mp.workdps(dps):
        us = saddle(n, dps)
        Psi_pp = -(2 * n / us**2 + 2 * n / us + mp.mpf(1) / 4)
        Psi0 = 2 * n * mp.log(us) + us / 4 - mp.pi * mp.e**us
        return mp.e**Psi0 * mp.sqrt(2 * mp.pi / (-Psi_pp))


def exact_D(n, dps):
    """D_n from exact quadrature of the I_k, for cross-checking the expansion."""
    import sys

    sys.path.insert(0, str(HERE))
    from turan_large_n import compute_I

    I = compute_I(n + 1, dps)
    with mp.workdps(dps):
        return 1 - I[n] ** 2 / (I[n - 1] * I[n + 1])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=80)
    ap.add_argument("--n-list", type=str, default="50,100,200,400,800,1600,3200")
    ap.add_argument("--no-exact", action="store_true")
    args = ap.parse_args()
    dps = args.dps
    ns = [int(x) for x in args.n_list.split(",")]

    rows = []
    with mp.workdps(dps):
        for n in ns:
            us = saddle(n, dps)
            I = [laplace_I(m, dps) for m in (n - 1, n, n + 1)]
            D_lap = 1 - I[1] ** 2 / (I[0] * I[2])
            row = {
                "n": n,
                "u_saddle": mp.nstr(us, 12),
                "D_laplace": mp.nstr(D_lap, 12),
                "n*D_laplace": mp.nstr(n * D_lap, 12),
                "1/(n+1)": mp.nstr(mp.mpf(1) / (n + 1), 12),
                "predicted_r_minus_1": mp.nstr(
                    (n + 2) / (n + 1) * I[1] ** 2 / (I[0] * I[2]) - 1, 12
                ),
            }
            if not args.no_exact:
                De = exact_D(n, dps)
                row["D_exact"] = mp.nstr(De, 12)
                row["rel_err_D"] = mp.nstr(abs(D_lap - De) / De, 6)
            rows.append(row)
        print(json.dumps(rows, indent=1))
        (HERE / "laplace_D.json").write_text(json.dumps(rows, indent=1))


if __name__ == "__main__":
    main()