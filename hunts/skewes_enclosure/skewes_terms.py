"""Revers's Lehman-method error terms and zero sums, evaluated as Arb balls.

Source: M. Revers, *New bounds in R.S. Lehman's estimates for the difference
pi(x) - li(x)*, arXiv:2501.04488 v2 (J. Number Theory 2025), Theorem 3.1.
For A with RH verified to height A, 2 pi e < T <= A, omega - eta >= 44.22,
5A/(4 omega) <= alpha <= A^2 and 0 < eta < omega/100:

    I(omega, eta) >= -1 - sum_{0<|gamma|<=T} e^{i gamma omega}
                         (1/rho + 1/(omega rho^2)) e^{-gamma^2/(2 alpha)} - R,
    R = R1 + ... + R6.

(The source writes "+ R" with |R| <= R1 + ... + R6; the lower bound uses -R.)
Pairing gamma with -gamma, the sum is 2 Re of the sum over gamma > 0, with
rho = 1/2 + i gamma, which is valid for gamma <= A under the cited RH-to-A
hypothesis. This module re-derives nothing: it evaluates the cited formulas.

Every number is a python-flint ``arb``/``acb`` ball. Inputs given as decimal
strings are converted exactly by Arb's parser to a ball containing the decimal.
"""

from __future__ import annotations

from dataclasses import dataclass

import flint
from flint import acb, arb

#: Working precision in bits. The sum needs gamma*omega ~ 2^33 reduced mod 2 pi
#: plus ~40 fractional bits (MISSION.md section (b)); 128 leaves headroom.
PREC = 128


def _b(x) -> arb:
    return x if isinstance(x, arb) else arb(str(x))


@dataclass(frozen=True)
class LehmanParams:
    omega: str
    eta: str
    alpha: str
    A: str
    T: str

    def balls(self):
        return tuple(_b(v) for v in (self.omega, self.eta, self.alpha, self.A, self.T))


def check_hypotheses(p: LehmanParams) -> dict:
    """Theorem 3.1's side conditions, each decided on balls (True only if proved)."""
    w, eta, al, A, T = p.balls()
    two_pi_e = 2 * arb.pi() * arb(1).exp()
    return {
        "omega - eta >= 44.22": bool(w - eta >= arb("44.22")),
        "5A/(4 omega) <= alpha": bool(5 * A / (4 * w) <= al),
        "alpha <= A^2": bool(al <= A * A),
        "0 < eta < omega/100": bool(eta > 0) and bool(eta < w / 100),
        "2 pi e < T <= A": bool(T > two_pi_e) and bool(T <= A),
    }


def revers_R(p: LehmanParams) -> dict:
    """R1..R6 of Revers Theorem 3.1 as balls, plus their sum under key 'R'."""
    old = flint.ctx.prec
    flint.ctx.prec = PREC
    try:
        w, eta, al, A, T = p.balls()
        lo, hi = w - eta, w + eta
        log2 = arb(2).log()
        g = (-al / 2 * eta * eta).exp()  # e^{-alpha eta^2 / 2}
        r1 = (2 / lo + 8 / lo**2 + arb("58.56") / lo**3
              + log2 * hi * (-lo / 2).exp() + 2 * hi * (-lo / 6).exp() / log2)
        m = arb("0.082") * al
        inv_eta = 1 / eta
        # min{0.082 alpha, 1/eta}: decided on balls, refuse if they overlap.
        if bool(m <= inv_eta):
            mn = m
        elif bool(inv_eta <= m):
            mn = inv_eta
        else:
            mn = arb.union(m, inv_eta)
        r2 = arb("0.037") / (w * al.sqrt()) * (mn * g + (1 - g) / lo)
        r3 = arb("0.074") * al.sqrt() * g
        r4 = ((-T * T / (2 * al)).exp()
              * (al / (arb.pi() * T * T) * (T / (2 * arb.pi())).log()
                 + 8 * T.log() / T + 4 * al / T**3)
              * (1 + 1 / (w * T)))
        r5 = arb("0.003") / lo**2
        r6 = ((1 + 22 / (A * w)) * A * A.log()
              * (arb("8.283") / A * (-al / 4 * eta * eta + hi / 2).exp()
                 + arb("7.152") * eta * (-A * A / (2 * al) + hi / 2).exp()))
        out = {"R1": r1, "R2": r2, "R3": r3, "R4": r4, "R5": r5, "R6": r6}
        out["R"] = r1 + r2 + r3 + r4 + r5 + r6
        return out
    finally:
        flint.ctx.prec = old


def lehman_sum(gammas, omega, alpha, second_order: bool = True) -> arb:
    """sum_{0<|gamma|<=T} e^{i gamma omega}(1/rho + 1/(omega rho^2)) e^{-gamma^2/2 alpha}.

    ``gammas`` are positive ordinates as arb balls (or exact decimals); the
    caller is responsible for completeness up to T. ``second_order=False`` drops
    Revers's 1/(omega rho^2) term, leaving the classical Lehman sum S1.
    """
    old = flint.ctx.prec
    flint.ctx.prec = PREC
    try:
        w, al = _b(omega), _b(alpha)
        two_al = 2 * al
        total = acb(0)
        half = arb(1) / 2
        for g in gammas:
            g = _b(g)
            rho = acb(half, g)
            inv = 1 / rho
            term = inv + inv * inv / w if second_order else inv
            phase = acb(0, g * w).exp()
            total += phase * term * (-(g * g) / two_al).exp()
        return 2 * total.real
    finally:
        flint.ctx.prec = old


def partial_F(gammas, omega) -> arb:
    """Revers section 8's f_T(omega) = -1 - sum_{0<|gamma|<=T} e^{i omega gamma}/rho."""
    old = flint.ctx.prec
    flint.ctx.prec = PREC
    try:
        w = _b(omega)
        total = acb(0)
        half = arb(1) / 2
        for g in gammas:
            g = _b(g)
            total += acb(0, g * w).exp() / acb(half, g)
        return -1 - 2 * total.real
    finally:
        flint.ctx.prec = old


def lower_bound_I(sum_ball: arb, p: LehmanParams) -> arb:
    """-1 - S - R as a ball; a positive lower endpoint localizes a sign change."""
    return -1 - sum_ball - revers_R(p)["R"]


#: [Rev25] section 4 parameter sets. The paper writes T = gamma_2000000 <
#: 1131944.4718 and T = gamma_22000000 < 10379599.7274, but Arb's Turing count
#: gives N(1131944.4718) = 1999999 and N(10379599.7274) = 21999999: those decimals
#: are lower bounds on the zeros (truncations), not upper bounds. The T used here
#: is the next decimal up, which Arb counts to exactly 2000000 and 22000000.
REVERS_PRINTED_T = {"chao_plymen": "1131944.4718", "saouter_demichel": "10379599.7274"}
CHAO_PLYMEN = LehmanParams("727.952018", "0.00016", "1.34e11", "1.022e7", "1131944.4719")
SAOUTER_DEMICHEL = LehmanParams("727.95134", "0.0000228", "6e12", "6.85e7", "10379600")
N_ZEROS = {"chao_plymen": 2_000_000, "saouter_demichel": 22_000_000}

#: [Rev25]'s printed float sums S* at those parameter sets (Mathematica).
REVERS_S_STAR = {
    "chao_plymen": "-1.006553478788955",
    "saouter_demichel": "-1.002922947193156",
}
