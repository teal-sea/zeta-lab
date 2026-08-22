"""Does the dps=60 magnitude survive a route that does not touch the lattice sums?

`Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s)`, so at `s = 0.8 + 85.7i` the
magnitude is set almost entirely by the gamma factor, whose size Stirling gives
in closed form: `|Gamma(sigma+it)| ~ sqrt(2 pi) |t|^(sigma-1/2) e^(-pi|t|/2)`.
That fixes `|Lambda_Q|` up to the `O(1)` factor `|zeta_Q(0.8+85.7i)|`, which the
Dirichlet series bounds crudely from the convergent region.  It is a sanity
check on the exponent, not on the digits.

    .venv/bin/python hunts/dps_cap/sanity_stirling.py
"""

from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from mpmath import mp  # noqa: E402

SIGMA, T = mp.mpf("0.8"), mp.mpf("85.7")
A, B, C = 2, 1, 3

with mp.workdps(40):
    d = mp.mpf(A) * C - mp.mpf(B) ** 2 / 4
    prefactor = (mp.sqrt(d) / mp.pi) ** SIGMA
    stirling = mp.sqrt(2 * mp.pi) * T ** (SIGMA - mp.mpf(1) / 2) * mp.e ** (-mp.pi * T / 2)
    gamma_exact = abs(mp.gamma(mp.mpc(SIGMA, T)))
    predicted = prefactor * gamma_exact
    print(f"d                       = {mp.nstr(d, 6)}")
    print(f"|(sqrt(d)/pi)^s|        = {mp.nstr(prefactor, 8)}")
    print(f"Stirling |Gamma(s)|     = {mp.nstr(stirling, 8)}")
    print(f"exact    |Gamma(s)|     = {mp.nstr(gamma_exact, 8)}")
    print(f"|Lambda_Q| / |zeta_Q|   = {mp.nstr(predicted, 8)}")
    print(f"=> |zeta_Q(s)| implied by 1.61745263238e-58: "
          f"{mp.nstr(mp.mpf('1.61745263238e-58') / predicted, 8)}")
    print(f"=> |zeta_Q(s)| implied by 4.84638192796e-35: "
          f"{mp.nstr(mp.mpf('4.84638192796e-35') / predicted, 8)}")
