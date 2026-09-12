"""Exact Vasyunin Gram entries and enclosure-checked d_N^2 (Baez-Duarte form).

Everything here computes the L^2(0, infty) quantities

    e_k(t) = {1/(k t)},      b_k = <chi_(0,1), e_k> = (1 - gamma + log k)/k,
    G[j,k] = <e_j, e_k>      (Vasyunin's formula, SOURCES.md section 2),
    d_N^2  = 1 - b^T G^{-1} b.

Two arms:

* arb arm (python-flint): every quantity is a ball; the linear solve is
  `arb_mat.solve`, which proves invertibility and returns enclosures, so the
  reported d_N^2 ball rigorously contains the true value given only that the
  formula implemented is Vasyunin's. Grade: enclosure-checked.
* mpmath arm: an independent reimplementation (floats at chosen dps) of the
  same formula, plus formula-independent quadrature of selected Gram entries
  (piecewise closed form with an exact trigamma tail), used to validate the
  arb arm. Grade: measured.

House rules: no global mpmath state is left modified (mp.workdps only);
the flint global context precision is set explicitly by every entry point.
"""

from __future__ import annotations

import json
import time
from math import gcd
from pathlib import Path

import numpy as np
from flint import arb, arb_mat, ctx, fmpz_mat
from mpmath import mp

HERE = Path(__file__).resolve().parent

#: Conjectured constant C = 2 + gamma - log(4 pi), 30 digits (matches
#: zeta.criteria.BD_CONSTANT).
BD_CONSTANT_STR = "0.046191417932242067628620495813"


# ---------------------------------------------------------------------------
# small number theory helpers
# ---------------------------------------------------------------------------

def mobius_sieve(N: int) -> np.ndarray:
    """mu(1..N) as an int8 array (index 0 unused)."""
    mu = np.ones(N + 1, dtype=np.int8)
    primes_mask = np.ones(N + 1, dtype=bool)
    primes_mask[:2] = False
    for p in range(2, N + 1):
        if primes_mask[p]:
            primes_mask[2 * p :: p] = False
            mu[p::p] *= -1
            mu[p * p :: p * p] = 0
    return mu


def coprime_up_to_half(q: int) -> np.ndarray:
    """All p with 1 <= p <= q//2 and gcd(p, q) = 1, as int64."""
    if q == 1:
        return np.zeros(0, dtype=np.int64)
    ps = np.arange(1, q // 2 + 1, dtype=np.int64)
    g = np.gcd(ps, q)
    return ps[g == 1]


# ---------------------------------------------------------------------------
# arb arm: Vasyunin sums in bulk
# ---------------------------------------------------------------------------

class VTables:
    """Balls for V(p/q) = sum_{m=1}^{q-1} {m p/q} cot(pi m/q), coprime p<q.

    Stored only for p <= q//2 (V((q-p)/q) = -V(p/q), an identity checked in
    the tests below); the reduced sum

        V(p/q) = (1/q) sum_{m=1}^{floor((q-1)/2)} (2 (m p mod q) - q) cot(pi m/q)

    (the m and q-m terms pair up; the m = q/2 term has cot(pi/2) = 0)
    is evaluated as an exact integer matrix times a ball vector, so the
    heavy loop runs inside flint.
    """

    def __init__(self, prec: int):
        self.prec = prec
        self.max_q = 0
        self._ps: dict[int, np.ndarray] = {}
        self._vals: dict[int, list] = {}

    def extend(self, new_max: int, progress_every: float = 30.0) -> float:
        """Build tables for q in (self.max_q, new_max]. Returns seconds."""
        ctx.prec = self.prec
        t0 = time.time()
        last = t0
        for q in range(self.max_q + 1, new_max + 1):
            self._build_q(q)
            now = time.time()
            if now - last > progress_every:
                print(f"    VTables: q = {q}/{new_max} ({now - t0:.0f}s)", flush=True)
                last = now
        self.max_q = new_max
        return time.time() - t0

    def _build_q(self, q: int) -> None:
        ps = coprime_up_to_half(q)
        self._ps[q] = ps
        if q <= 2 or len(ps) == 0:
            self._vals[q] = [arb(0)] * len(ps)
            return
        mhalf = (q - 1) // 2
        ms = np.arange(1, mhalf + 1, dtype=np.int64)
        cots = arb_mat(mhalf, 1, [(arb(int(m)) / q).cot_pi() for m in ms])
        Wint = 2 * (np.outer(ps, ms) % q) - q
        A = arb_mat(fmpz_mat(len(ps), mhalf, Wint.ravel().tolist()))
        prod = A * cots
        self._vals[q] = [prod[i, 0] / q for i in range(len(ps))]

    def V(self, p: int, q: int):
        """V(p/q) for gcd(p, q) = 1, 1 <= p < q (q >= 2); V(anything/1) = 0."""
        if q == 1:
            return arb(0)
        p = p % q
        if 2 * p <= q:
            sign = 1
        else:
            p = q - p
            sign = -1
        idx = int(np.searchsorted(self._ps[q], p))
        return sign * self._vals[q][idx]

    def W(self, p: int, q: int):
        """V(p/q) + V(q/p) for coprime p < q."""
        if p == 1:
            return self.V(1, q)
        return self.V(p, q) + self.V(q, p)


class GramBuilder:
    """Assemble the arb Gram matrix and target vector for any N <= max built."""

    def __init__(self, prec: int):
        self.prec = prec
        self.vt = VTables(prec)
        ctx.prec = prec
        self._logs: list = [None, arb(0)]
        self._gamma = arb.const_euler()
        self._log2pi = (2 * arb.pi()).log()
        self._halfpi = arb.pi() / 2
        self._c1_half = (self._log2pi - self._gamma) / 2

    def extend(self, new_max: int) -> float:
        ctx.prec = self.prec
        for r in range(len(self._logs), new_max + 1):
            self._logs.append(arb(r).log())
        return self.vt.extend(new_max)

    def coprime_entry(self, p: int, q: int):
        """<e_p, e_q> for coprime p < q, as a ball."""
        ctx.prec = self.prec
        pq = p * q
        return (
            self._c1_half * (p + q)
            + (q - p) * (self._logs[p] - self._logs[q]) / 2
            - self._halfpi * self.vt.W(p, q)
        ) / pq

    def entry(self, j: int, k: int):
        """<e_j, e_k> for any j, k >= 1 (diagonal has a closed form)."""
        ctx.prec = self.prec
        if j == k:
            return (self._log2pi - self._gamma) / j
        j, k = min(j, k), max(j, k)
        d = gcd(j, k)
        return self.coprime_entry(j // d, k // d) / d

    def gram(self, N: int, want_float: bool = True):
        """(arb_mat G, float64 midpoint copy or None). O(N^2) ball ops."""
        ctx.prec = self.prec
        if N > self.vt.max_q:
            raise ValueError("extend() first")
        G = arb_mat(N, N)
        Gf = np.zeros((N, N)) if want_float else None
        diag = self._log2pi - self._gamma
        for j in range(1, N + 1):
            v = diag / j
            G[j - 1, j - 1] = v
            if want_float:
                Gf[j - 1, j - 1] = float(v)
        for q in range(2, N + 1):
            ps_all = np.concatenate(
                [self._ps_low(q), q - self._ps_low(q)[::-1]]
            ) if q > 2 else np.array([1], dtype=np.int64)
            for p in ps_all:
                p = int(p)
                if p >= q or gcd(p, q) != 1:
                    continue
                base = self.coprime_entry(p, q)
                for d in range(1, N // q + 1):
                    v = base / d if d > 1 else base
                    G[d * p - 1, d * q - 1] = v
                    G[d * q - 1, d * p - 1] = v
                    if want_float:
                        fv = float(v)
                        Gf[d * p - 1, d * q - 1] = fv
                        Gf[d * q - 1, d * p - 1] = fv
        return G, Gf

    def _ps_low(self, q: int) -> np.ndarray:
        ps = self.vt._ps.get(q)
        if ps is None:
            ps = coprime_up_to_half(q)
        return ps

    def rhs(self, N: int):
        """b_k = (1 - gamma + log k)/k, k = 1..N, as an arb column."""
        ctx.prec = self.prec
        one_minus_gamma = 1 - self._gamma
        return arb_mat(N, 1, [(one_minus_gamma + self._logs[k]) / k for k in range(1, N + 1)])


def dot(u: arb_mat, v: arb_mat):
    """u^T v for two arb columns."""
    return (u.transpose() * v)[0, 0]


def solve_d2(G: arb_mat, b: arb_mat, prec_solve: int):
    """Solve G x = b with balls; return dict of enclosures.

    d2 ball rigorously contains 1 - b^T G^{-1} b because x contains G^{-1} b.
    residual = 1 - 2 b.x + x.G.x is an independent recomputation that must
    overlap d2 (it equals the squared distance at the true minimizer).
    """
    ctx.prec = prec_solve
    t0 = time.time()
    x = G.solve(b)
    t_solve = time.time() - t0
    d2 = 1 - dot(b, x)
    Gx = G * x
    residual = 1 - 2 * dot(b, x) + dot(x, Gx)
    return {
        "x": x,
        "d2": d2,
        "residual": residual,
        "overlap": bool(d2.overlaps(residual)),
        "t_solve": t_solve,
        "x_max_rad": max(float(x[i, 0].rad()) for i in range(x.nrows())),
    }


def bcf_upper_bound(G: arb_mat, b: arb_mat, N: int, prec: int, logs: list):
    """|chi - sum a_k e_k|^2 at the BCF vector a_k = -mu(k)(1 - log k/log N).

    A rigorous upper bound for d_N^2 at every N (any vector gives one);
    BCF's Theorem 1 says this choice already achieves C/log N + O(1/log^2 N)
    under RH plus their discrete-moment hypothesis.
    """
    ctx.prec = prec
    mu = mobius_sieve(N)
    logN = logs[N]
    a = arb_mat(
        N, 1,
        [(-int(mu[k])) * (1 - logs[k] / logN) if mu[k] else arb(0) for k in range(1, N + 1)],
    )
    return 1 - 2 * dot(b, a) + dot(a, G * a)


def ball_str(v: arb, digits: int = 40) -> str:
    return v.str(digits)


def ball_record(v: arb, digits: int = 40) -> dict:
    return {
        "ball": v.str(digits, radius=True),
        "mid": float(v.mid()),
        "rad": float(v.rad()),
    }


# ---------------------------------------------------------------------------
# mpmath arm: independent reimplementation and quadrature
# ---------------------------------------------------------------------------

def gram_entry_mp(n: int, m: int, dps: int = 50):
    """<e_n, e_m> via Vasyunin's formula in mpmath (independent of flint)."""
    with mp.workdps(dps + 10):
        w = gcd(n, m)
        n0, m0 = n // w, m // w

        def V(h, k):
            if k == 1:
                return mp.mpf(0)
            s = mp.mpf(0)
            for j in range(1, k):
                s += mp.frac(mp.mpf(j * h) / k) * mp.cot(mp.pi * j / k)
            return s

        val = (
            (mp.log(2 * mp.pi) - mp.euler) / 2 * (mp.mpf(1) / n + mp.mpf(1) / m)
            + mp.mpf(m - n) / (2 * m * n) * mp.log(mp.mpf(n) / m)
            - mp.pi * w / (2 * n * m) * (V(m0, n0) + V(n0, m0))
        )
        result = +val
    return result


def gram_entry_quad(j: int, k: int, dps: int = 40, M: int = 80, adaptive: bool = False):
    """<e_j, e_k> = int_0^infty {u/j}{u/k} u^-2 du, no Vasyunin anywhere.

    Finite part: breakpoints at multiples of j and k up to U = M*lcm(j,k);
    between consecutive breakpoints {u/j}{u/k} = (u/j - a)(u/k - b) with a, b
    constant integers, so the integral has the closed form

        (beta-alpha)/(jk) - (b/j + a/k) log(beta/alpha) + a b (1/alpha - 1/beta).

    With adaptive=True the finite part uses mp.quad on each piece instead
    (slower, independent of the antiderivative algebra).

    Tail (exact): {u/j}{u/k} has period L = lcm(j,k), and
    sum_{m>=M} (v + mL)^-2 = L^-2 psi_1(M + v/L), so

        tail = L^-2 int_0^L {v/j}{v/k} psi_1(M + v/L) dv,

    a smooth piecewise integral evaluated with mp.quad.
    """
    L = j * k // gcd(j, k)
    U = M * L
    breaks = sorted(set(range(0, U + 1, j)) | set(range(0, U + 1, k)))
    with mp.workdps(dps + 15):
        total = mp.mpf(0)
        for alpha, beta in zip(breaks[:-1], breaks[1:]):
            a = alpha // j
            b = alpha // k
            if adaptive:
                aa, bb = mp.mpf(a), mp.mpf(b)
                piece = mp.quad(
                    lambda u, aa=aa, bb=bb: (u / j - aa) * (u / k - bb) / u**2,
                    [alpha, beta],
                ) if alpha > 0 else mp.mpf(beta - alpha) / (j * k)
            else:
                piece = mp.mpf(beta - alpha) / (j * k)
                if alpha > 0:
                    piece -= (mp.mpf(b) / j + mp.mpf(a) / k) * mp.log(mp.mpf(beta) / alpha)
                    piece += mp.mpf(a) * b * (mp.mpf(1) / alpha - mp.mpf(1) / beta)
            total += piece
        # tail over [U, infty) via periodicity + trigamma
        sub = sorted({0, L} | {t for t in range(0, L + 1) if t % j == 0 or t % k == 0})
        tail = mp.mpf(0)
        for alpha, beta in zip(sub[:-1], sub[1:]):
            tail += mp.quad(
                lambda v: mp.frac(v / j) * mp.frac(v / k) * mp.psi(1, M + v / mp.mpf(L)),
                [alpha, beta],
            )
        tail /= L**2
        result = +(total + tail)
    return result


def rhs_quad(k: int, dps: int = 40):
    """b_k = int_0^1 {1/(k t)} dt by direct quadrature (breakpoints 1/(k n))."""
    with mp.workdps(dps + 10):
        pts = [mp.mpf(1)] + [mp.mpf(1) / (k * n) for n in range(1, 200)]
        pts = sorted(p for p in pts if p <= 1)
        val = mp.mpf(0)
        for a, b in zip(pts[:-1], pts[1:]):
            val += mp.quad(lambda t: mp.frac(1 / (k * t)), [a, b])
        # remaining (0, min): {1/(kt)} on (0, 1/(199k)) oscillates; use
        # substitution u = 1/(kt): int = (1/k) int_{u0}^inf {u}/u^2 du with
        # u0 = 199; {u}/u^2 tail = sum over unit intervals in closed form:
        # int_n^{n+1} (u-n)/u^2 du = log((n+1)/n) - 1/(n+1).
        u0 = 199
        # sum_{n>=u0} [log(1+1/n) - 1/(n+1)] telescopes:
        # partial sums to U give log(U/u0) - (H_U - H_{u0}) -> H_{u0} - log u0 - gamma.
        s = mp.harmonic(u0) - mp.log(u0) - mp.euler
        val += s / k
        result = +val
    return result


def d2_mp(N: int, dps: int = 60):
    """Full pipeline in mpmath: build G, b, lu_solve, d2. Independent arm."""
    with mp.workdps(dps + 10):
        G = mp.zeros(N, N)
        for j in range(1, N + 1):
            for k in range(j, N + 1):
                v = gram_entry_mp(j, k, dps=dps)
                G[j - 1, k - 1] = v
                G[k - 1, j - 1] = v
        b = mp.matrix([(1 - mp.euler + mp.log(k)) / k for k in range(1, N + 1)])
        x = mp.lu_solve(G, b)
        d2 = 1 - mp.fdot(zip(b, x))
        result = +d2
    return result
