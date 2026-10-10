"""Theorem A, Theorem B and the table D(h), each verified in Arb.

* `cover(...)`: partition [q_from, q_to] into intervals; on each interval
  choose parameters with the float model and verify in Arb a lower bound for
  L(1, chi) valid on the whole interval (the bound is evaluated at the right
  end, where it is weakest, and h at the left end, where sqrt q is smallest).
* `tail_constant(...)`: the monotone family a = 8 log(lambda log q),
  b = (1 + eta) a used for every q >= Q1 (RESULTS.md, proof of Theorem A).
* `d_table(...)`: D(h) = largest |D| not excluded for class number <= h.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

from hunts.qrh_class_number import lbound as lb

HERE = Path(__file__).resolve().parent


def _s(x: arb) -> str:
    return x.str(20, radius=True)


def _lower(x: arb) -> float:
    """A float that is <= every point of the ball (rounded down)."""
    v = float(x.lower())
    return math.nextafter(v, -math.inf)


def interval_bound(q_lo: int, q_hi: int, params, sigma0='7/8', B=None, tab=None):
    """Verified lower bounds on [q_lo, q_hi] for log L(1,chi) and for h."""
    a, b, dx, dy = params
    with ctx.workprec(lb.PREC):
        d = lb.log_L1_lower(q_hi, a, b, dx, dy, sigma0=sigma0, B=B, tab=tab, detail=True)
        logL = d['logL'].lower()
        L = logL.exp()
        h = arb(q_lo).sqrt() * L / arb.pi()
        llq = arb(q_lo).log().log()      # smallest log log q on the interval
        return {
            'q_lo': q_lo, 'q_hi': q_hi,
            'a': str(a), 'b': str(b), 'dx': str(dx), 'dy': str(dy),
            'M': _s(d['M']), 'E': _s(d['E']),
            'logL_lower': _lower(logL),
            'L_lower': _lower(L),
            'h_lower': _lower(h),
            'L_loglogq_lower': _lower(L * llq) if llq > 0 else None,
        }


def cover(q_from: int, q_to: int, ratio: float, sigma0='7/8', log_scale=False,
          progress=None):
    """Intervals [q_i, q_{i+1}] covering [q_from, q_to].

    ratio: q_{i+1} = ceil(q_i * ratio), or with log_scale,
    log q_{i+1} = ratio * log q_i.
    """
    tab = lb.tables()
    B = lb.meissel_mertens()
    fm = lb.FloatModel(sigma0=float(Fraction(sigma0)), tab=tab)
    rows = []
    q = q_from
    start = None
    while q < q_to:
        if log_scale:
            nq = int(math.exp(math.log(q) * ratio)) + 1
        else:
            nq = int(math.ceil(q * ratio))
        nq = min(max(nq, q + 1), q_to)
        best, x = fm.optimise(math.log(nq), start=start)
        start = x
        params = lb.params_from_float(*x)
        try:
            row = interval_bound(q, nq, params, sigma0=sigma0, B=B, tab=tab)
        except ValueError:
            # a prime sits on a boundary ball: nudge a and b
            pa, pb, pdx, pdy = params
            params = (pa + Fraction(1, 997), pb + Fraction(1, 991), pdx, pdy)
            row = interval_bound(q, nq, params, sigma0=sigma0, B=B, tab=tab)
        row['float_logL'] = best
        rows.append(row)
        if progress:
            progress(row)
        q = nq
    return rows


def d_table(rows, h_max: int, tail_h_lower: float):
    """D(h) for h = 1..h_max from a cover.

    If h(D) <= h and |D| lies in an interval whose verified h_lower exceeds h,
    a contradiction; so |D| <= D(h) := the right end of the last interval with
    h_lower <= h.  Requires tail_h_lower (the Theorem A bound at the end of
    the cover, increasing beyond it) to exceed h_max.
    """
    if not tail_h_lower > h_max:
        raise ValueError('tail bound does not exceed h_max')
    if rows[-1]['h_lower'] <= h_max:
        raise ValueError('cover too short for h_max')
    out = []
    for h in range(1, h_max + 1):
        last = None
        for r in rows:
            if r['h_lower'] <= h:
                last = r['q_hi']
        out.append({'h': h, 'D_bound': last if last is not None else rows[0]['q_lo']})
    return out


# ---------------------------------------------------------------------------
# Theorem A: the tail family
# ---------------------------------------------------------------------------


def tail_constant(Q1: int, lam: Fraction, eta: Fraction, dx: Fraction, dy: Fraction,
                  sigma0='7/8'):
    """K1 such that log L(1,chi) >= K1 - log a(q) for all q >= Q1, where
    a(q) = (1/(1-sigma0)) log(lam log q), b = (1+eta) a.

    Every piece is evaluated at Q1 in a form that is nonincreasing in q
    (RESULTS.md, Lemma 6).  Rosser-Schoenfeld is used for all t >= 286.
    """
    tab = lb.tables()
    B = lb.meissel_mertens()
    with ctx.workprec(lb.PREC):
        eps0 = 1 - lb._arb(sigma0)
        lam_a, eta_a = lb._arb(lam), lb._arb(eta)
        logQ = arb(Q1).log()
        a1 = (lam_a * logQ).log() / eps0
        b1 = (1 + eta_a) * a1
        if not (a1 > arb(286).log()):
            raise ValueError('a(Q1) must exceed log 286')
        if not (lam_a <= 1):
            raise ValueError('lambda must be <= 1')
        kappa = ((1 + eta_a) * (1 + eta_a).log()) / eta_a - 1
        # main term pieces
        P2 = lb.p2_lower(a1, tab)
        main = -B - kappa - 1 / (2 * a1 * b1) + P2
        # zero sums with G~ = (1/2) log Q1 + max(0, psi/2 + P)
        half = logQ / 2
        Ry = lb.zero_sum_upper(a1, dy, half, eps0, g_nonneg=True)
        Rx = lb.zero_sum_upper(b1, dx, half, eps0, g_nonneg=True)
        T = lb.trivial_upper(a1) + lb.trivial_upper(b1)
        E = (Rx + Ry + T) / (b1 - a1)
        K1 = main - E
        c = K1.exp() / 8 * (8 * eps0)   # constant in L >= c/(loglog q + log lam)
        return {
            'Q1': Q1, 'lambda': str(lam), 'eta': str(eta), 'dx': str(dx), 'dy': str(dy),
            'sigma0': str(sigma0), 'a1': _s(a1), 'b1': _s(b1), 'kappa': _s(kappa),
            'P2': _s(P2), 'E': _s(E), 'K1': _s(K1),
            'c_lower': _lower(c), 'A': math.log(float(Fraction(lam))),
        }


def save(path: Path, obj) -> None:
    path.write_text(json.dumps(obj, indent=1) + '\n')
