"""The Bombieri-Lagarias split of the Li coefficients, for zeta and its rivals.

Hunt #150 (`rh_moonshot`), mechanism `li_arithmetic`.  Nothing here is a
result about the Riemann hypothesis; see `NOTES.md` for what each number is
and how it is graded.

The split (derived here, self-reviewed, and pinned numerically by the tests)
----------------------------------------------------------------------------
Write s = 1/(1 - z), so that lambda_n = n [z^n] log xi(1/(1-z)) (`zeta.li`).
With xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s), put the factor
(s-1) with zeta, since (s-1) zeta(s) is entire and equal to 1 at s = 1:

    lambda_n = A(n) + T(n),
    A(n) = n [z^n] log( s pi^{-s/2} Gamma(s/2) )               (archimedean)
    T(n) = n [z^n] log( (s-1) zeta(s) )                        (arithmetic)

Expanding log Gamma(1/2 + w) at w = (s-1)/2 = z/(2(1-z)), and using
n [z^n] z^k (1-z)^{-k} = k C(n,k),

    A(n) = 1 - (n/2)(gamma + log 4 pi)
             + sum_{k=2}^{n} C(n,k) (-1)^k (1 - 2^{-k}) zeta(k),

and, writing zeta'/zeta(s) + 1/(s-1) = sum_{k>=0} eta_k (s-1)^k,

    T(n) = sum_{j=1}^{n} C(n,j) eta_{j-1}.

That is the Bombieri-Lagarias / Coffey decomposition up to the sign
convention of the eta's (Bombieri-Lagarias 1999; Coffey 2005 calls the two
pieces S_2 and S_1).  T(1) = eta_0 = Euler's gamma, A(1) = 1 - (gamma +
log 4 pi)/2, and A(1) + T(1) = lambda_1 = 1 + gamma/2 - log(4 pi)/2.

A cancellation-free form of A(n), used as the second route: since
(1 - 2^{-k}) zeta(k) = sum over odd m of m^{-k},

    A(n) = -(n/2)(gamma + log pi) + sum_{k>=1} [ n/(2k) - 1 + (1 - 1/(2k+1))^n ].

The Davenport-Heilbronn analogue.  F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s)
has no pole and no (s-1) factor, f(1) != 0, and expanding log Gamma(1 + w):

    A_DH(n) = -(n/2)(log(pi/5) + gamma) + sum_{k=2}^{n} C(n,k)(-1)^k 2^{-k} zeta(k)
            = -(n/2)(log(pi/5) + gamma) + sum_{m>=1} [ (1 - 1/(2m))^n - 1 + n/(2m) ],
    T_DH(n) = n [z^n] log f(1/(1-z)).

Routes implemented (they share no evaluator unless stated):

* A(n), A_DH(n): a binomial transform of zeta(k) at the precision the 2^n
  cancellation needs (mpmath's integer zeta values), and the series above with
  a Hurwitz-zeta tail (elementary powers only).
* T(n): Taylor coefficients of log((s-1) zeta(s)) at s = 1 from mpmath's
  Stieltjes constants (small n), and a Cauchy integral of log((s-1) zeta(s))
  on |z| = r with Arb's zeta (python-flint), any n.
* T_DH(n): generalized Stieltjes constants gamma_k(a/5) (small n), and a Cauchy
  integral of log f with Arb's Hurwitz zeta.
* lambda_n themselves are read from `hunts/li_dh_onset/artifacts` (zeta to
  n = 2000, DH to n = 5000; `zeta.core.xi` and that hunt's DH evaluator), so
  lambda_n - A(n) - T(n) = 0 is a three-evaluator identity check.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import mpmath
from mpmath import mp

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
if str(_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_ROOT))

#: Where this mechanism keeps its committed outputs.
ARTIFACTS = _HERE / "artifacts"
#: The lambda tables computed by hunt #128 (`li_dh_onset`), read-only inputs.
DH_ONSET_ARTIFACTS = _ROOT / "hunts" / "li_dh_onset" / "artifacts"

#: Guard digits carried internally.
GUARD = 10

#: The Davenport-Heilbronn coefficients on residues 1..4 mod 5 are
#: (1, kappa, -kappa, -1); kappa is taken from `zeta.epstein`.


# ---------------------------------------------------------------------------
# lambda tables from hunt #128
# ---------------------------------------------------------------------------


def load_lambda(kind: str) -> list:
    """lambda_1 .. lambda_N as mpf strings' values, from `li_dh_onset`.

    ``kind`` is ``"xi"`` (N = 2000, radius 0.9, dps 30) or ``"dh"``
    (N = 5000, radius 0.95, dps 30).  Those tables were computed by a Cauchy
    route on the completed functions; their own controls are in
    `hunts/li_dh_onset/RESULTS.md`.
    """
    name = {"xi": "lambda_xi_n2000_r0.9.json", "dh": "lambda_dh_n5000_r0.95.json"}[kind]
    blob = json.loads((DH_ONSET_ARTIFACTS / name).read_text())
    with mp.workdps(int(blob["dps"]) + 5):
        return [mp.mpf(v) for v in blob["lambda"]]


# ---------------------------------------------------------------------------
# archimedean parts
# ---------------------------------------------------------------------------


def binomial_transform(values: list, n_max: int) -> list:
    """b_n = sum_{k=0}^{n} C(n,k) values[k] for n = 0..n_max, at ambient precision.

    Computed by n_max rounds of forward sums, d_j <- d_j + d_{j+1}, so no
    binomial coefficient is formed.  The caller must have set the precision:
    intermediate magnitudes reach sum_k C(n,k) |values[k]|.
    """
    d = [mp.mpf(v) for v in values[: n_max + 1]]
    if len(d) < n_max + 1:
        raise ValueError("need values[0..n_max]")
    out = [d[0]]
    for n in range(1, n_max + 1):
        top = n_max - n
        for j in range(top + 1):
            d[j] = d[j] + d[j + 1]
        out.append(d[0])
    return out


def _integer_zeta_values(k_max: int, work: int) -> list:
    """zeta(k) for k = 0..k_max at ``work`` digits (entries 0 and 1 unused).

    mpmath's integer-argument zeta for small k; for large k the direct sum
    sum_{m <= M} m^{-k} with M^{-k} below the working floor (M is at most a
    few dozen once k exceeds work/1.5).
    """
    vals = [mp.mpf(0), mp.mpf(0)]
    floor_digits = work + 5
    with mp.workdps(work):
        for k in range(2, k_max + 1):
            log10_m = floor_digits / k
            if log10_m <= math.log10(64):
                M = int(math.ceil(10**log10_m)) + 1
                vals.append(mp.fsum(mp.power(m, -k) for m in range(1, M + 1)))
            else:
                vals.append(mp.zeta(k))
    return vals


def zeta_archimedean(n_max: int, dps: int = 30) -> list:
    """A(1) .. A(n_max) for zeta, binomial route (see the module docstring).

    The alternating sum cancels about n log10(2) digits, which the working
    precision carries explicitly.
    """
    work = dps + 2 * GUARD + int(math.ceil(n_max * math.log10(2))) + 5
    with mp.workdps(work):
        zk = _integer_zeta_values(n_max, work)
        v = [mp.mpf(0), mp.mpf(0)] + [
            (-1) ** k * (1 - mp.mpf(2) ** (-k)) * zk[k] for k in range(2, n_max + 1)
        ]
        b = binomial_transform(v, n_max)
        lin = (mp.euler + mp.log(4 * mp.pi)) / 2
        out = [1 - n * lin + b[n] for n in range(1, n_max + 1)]
    with mp.workdps(dps):
        return [+x for x in out]


def zeta_archimedean_series(n: int, dps: int = 30) -> mpmath.mpf:
    """A(n) for zeta by the cancellation-free series with a Hurwitz tail.

    A(n) = -(n/2)(gamma + log pi) + sum_{k=1}^{K} g(k) + sum_{j>=2} c_j 2^{-j} zeta(j, K + 3/2),
    g(k) = n/(2k) - 1 + (1 - 1/(2k+1))^n,  c_j = n + (-1)^j C(n,j),
    which is exact: for k > K, g(k) = sum_{j>=2} c_j (2k+1)^{-j}.
    """
    n = int(n)
    work = dps + 2 * GUARD
    with mp.workdps(work):
        K = 4 * n + 64
        head = mp.fsum(
            mp.mpf(n) / (2 * k) - 1 + mp.power(1 - mp.mpf(1) / (2 * k + 1), n)
            for k in range(1, K + 1)
        )
        tail = mp.mpf(0)
        tol = mp.mpf(10) ** (-work)
        for j in range(2, 10 * n + 200):
            cj = n + (-1) ** j * (mp.binomial(n, j) if j <= n else 0)
            term = cj * mp.power(2, -j) * mp.zeta(j, K + mp.mpf(3) / 2)
            tail += term
            if j > 3 and abs(term) < tol:
                break
        value = -n * (mp.euler + mp.log(mp.pi)) / 2 + head + tail
    with mp.workdps(dps):
        return +value


def dh_archimedean(n_max: int, dps: int = 30) -> list:
    """A_DH(1) .. A_DH(n_max), binomial route; cancels about n log10(3/2) digits."""
    work = dps + 2 * GUARD + int(math.ceil(n_max * math.log10(1.5))) + 5
    with mp.workdps(work):
        zk = _integer_zeta_values(n_max, work)
        v = [mp.mpf(0), mp.mpf(0)] + [
            (-1) ** k * mp.mpf(2) ** (-k) * zk[k] for k in range(2, n_max + 1)
        ]
        b = binomial_transform(v, n_max)
        lin = (mp.log(mp.pi / 5) + mp.euler) / 2
        out = [-n * lin + b[n] for n in range(1, n_max + 1)]
    with mp.workdps(dps):
        return [+x for x in out]


def dh_archimedean_series(n: int, dps: int = 30) -> mpmath.mpf:
    """A_DH(n) by the series sum_{m>=1}[(1 - 1/(2m))^n - 1 + n/(2m)] with a Hurwitz tail."""
    n = int(n)
    work = dps + 2 * GUARD
    with mp.workdps(work):
        M = 4 * n + 64
        head = mp.fsum(
            mp.power(1 - mp.mpf(1) / (2 * m), n) - 1 + mp.mpf(n) / (2 * m)
            for m in range(1, M + 1)
        )
        tail = mp.mpf(0)
        tol = mp.mpf(10) ** (-work)
        for j in range(2, n + 1):
            term = (-1) ** j * mp.binomial(n, j) * mp.power(2, -j) * mp.zeta(j, M + 1)
            tail += term
            if j > 3 and abs(term) < tol:
                break
        value = -n * (mp.log(mp.pi / 5) + mp.euler) / 2 + head + tail
    with mp.workdps(dps):
        return +value


# ---------------------------------------------------------------------------
# arithmetic parts from Taylor coefficients at s = 1 (no contour)
# ---------------------------------------------------------------------------


def _log_series(a: list) -> list:
    """Coefficients of log(sum a_j u^j) for a_0 > 0, up to the length of ``a``.

    j c_j = j a_j / a_0 - sum_{i=1}^{j-1} i c_i a_{j-i} / a_0, plus c_0 = log a_0.
    """
    n = len(a) - 1
    c = [mp.log(a[0])] + [mp.mpf(0)] * n
    for j in range(1, n + 1):
        acc = j * a[j] - mp.fsum(i * c[i] * a[j - i] for i in range(1, j))
        c[j] = acc / (j * a[0])
    return c


def _binomial_li(c: list, n_max: int) -> list:
    """sum_{j=1}^{n} j C(n,j) c_j for n = 1..n_max: n [z^n] of sum c_j (s-1)^j."""
    return [
        mp.fsum(j * mp.binomial(n, j) * c[j] for j in range(1, n + 1))
        for n in range(1, n_max + 1)
    ]


def zeta_arithmetic_stieltjes(n_max: int, dps: int = 30) -> list:
    """T(1) .. T(n_max) from the Stieltjes constants (mpmath ``stieltjes``).

    (s-1) zeta(s) = 1 + sum_{k>=0} (-1)^k gamma_k (s-1)^{k+1} / k!, so its
    logarithm is a power series in (s-1) whose coefficients c_j feed
    T(n) = sum_j j C(n,j) c_j.  The binomial sum cancels about n log10 2
    digits, so the precision is raised accordingly.  Cheap for n_max <= 40.
    """
    work = dps + 2 * GUARD + int(math.ceil(n_max * math.log10(2))) + 5
    with mp.workdps(work):
        a = [mp.mpf(1)] + [
            (-1) ** k * mp.stieltjes(k) / mp.factorial(k) for k in range(n_max)
        ]
        c = _log_series(a)
        out = _binomial_li(c, n_max)
    with mp.workdps(dps):
        return [+x for x in out]


def dh_arithmetic_stieltjes(n_max: int, dps: int = 30) -> list:
    """T_DH(1) .. T_DH(n_max) from generalized Stieltjes constants gamma_k(a/5).

    f(s) = 5^{-s} sum_{a=1}^{4} c_a zeta(s, a/5) with c = (1, kappa, -kappa, -1),
    zeta(s, q) = 1/(s-1) + sum_k (-1)^k gamma_k(q) (s-1)^k / k!, and the poles
    cancel because sum c_a = 0.  So f(1+u) = (1/5) e^{-u log 5}
    sum_k (-1)^k G_k u^k / k! with G_k = sum_a c_a gamma_k(a/5).
    """
    from zeta.epstein import kappa

    work = dps + 2 * GUARD + int(math.ceil(n_max * math.log10(2))) + 5
    with mp.workdps(work):
        kap = kappa(work)
        coef = [mp.mpf(1), kap, -kap, mp.mpf(-1)]
        G = [
            mp.fsum(coef[a - 1] * mp.stieltjes(k, mp.mpf(a) / 5) for a in range(1, 5))
            for k in range(n_max + 1)
        ]
        g = [(-1) ** k * G[k] / mp.factorial(k) for k in range(n_max + 1)]
        e = [(-mp.log(5)) ** j / mp.factorial(j) for j in range(n_max + 1)]
        prod = [
            mp.fsum(e[i] * g[j - i] for i in range(j + 1)) / 5 for j in range(n_max + 1)
        ]
        if not prod[0] > 0:
            raise ValueError("f(1) should be positive")
        c = _log_series(prod)
        out = _binomial_li(c, n_max)
    with mp.workdps(dps):
        return [+x for x in out]


# ---------------------------------------------------------------------------
# a generic Cauchy extractor on Arb (python-flint) evaluators
# ---------------------------------------------------------------------------


def _fft(values: list, inverse: bool = False) -> list:
    """Radix-2 decimation-in-time FFT on a list of flint ``acb`` (length 2^m).

    Forward: X_n = sum_j x_j e^{-2 pi i j n / N}.
    """
    from flint import acb, arb

    N = len(values)
    if N & (N - 1):
        raise ValueError("length must be a power of two")
    levels = N.bit_length() - 1
    # bit reversal
    out = [None] * N
    for i in range(N):
        r = int(format(i, f"0{levels}b")[::-1], 2) if levels else 0
        out[r] = values[i]
    sign = 1 if inverse else -1
    size = 2
    while size <= N:
        half = size // 2
        ang = arb.pi() * 2 * sign / size
        w_step = acb(ang.cos(), ang.sin())
        tw = [acb(1)]
        for _ in range(half - 1):
            tw.append(tw[-1] * w_step)
        for start in range(0, N, size):
            for k in range(half):
                a = out[start + k]
                b = out[start + k + half] * tw[k]
                out[start + k] = a + b
                out[start + k + half] = a - b
        size *= 2
    return out


def _mid(x):
    """Drop the radius of an Arb ball (we use Arb as fast multiprecision)."""
    from flint import acb

    return acb(x.real.mid(), x.imag.mid())


def cauchy_log_coefficients(
    evaluator, n_max: int, radius: str, work_digits: int, n_points: int
) -> dict:
    """n [z^n] log g(1/(1-z)) for n = 1..n_max, g given as an Arb evaluator.

    ``evaluator(s)`` takes and returns flint ``acb`` at the ambient flint
    precision.  The branch of log g is built by continuity from node 0
    (z = r, where every g used here is real and positive) with the winding
    number checked, exactly as `zeta.li._unwrapped_log` does; the Taylor
    coefficients come from one FFT, divided by r^n.  Returns the coefficients
    as mpmath values together with the largest imaginary residue measured
    against the r^{-n} round-off floor (a value below 1 is clean).
    """
    from flint import acb, arb, ctx

    if n_points & (n_points - 1):
        raise ValueError("n_points must be a power of two")
    old = ctx.prec
    ctx.prec = int(math.ceil(work_digits * 3.33)) + 16
    try:
        R = arb(radius)
        two_pi = arb.pi() * 2
        logs = []
        prev_arg = None
        args0 = None
        for j in range(n_points):
            ang = two_pi * j / n_points
            z = acb(R * ang.cos(), R * ang.sin())
            s = 1 / (1 - z)
            v = _mid(evaluator(s))
            a = v.arg().mid()
            if prev_arg is None:
                args0 = a
                cand = a
            else:
                k = ((prev_arg - a) / two_pi).mid()
                kk = int(math.floor(float(k) + 0.5))
                cand = a + two_pi * kk
                if abs(float(cand - prev_arg)) >= math.pi / 2:
                    raise ValueError("circle undersampled: arg jump too large")
            prev_arg = cand
            logs.append(acb(abs(v).log().mid(), arb(cand).mid()))
        winding = int(math.floor(float((prev_arg - args0) / two_pi) + 0.5))
        if winding != 0:
            raise ValueError(f"log g winds {winding} times: the disc is not zero-free")
        spec = _fft(logs)
        biggest = max(float(abs(x).mid()) for x in logs)
        out = []
        worst = 0.0
        with mp.workdps(work_digits):
            for n in range(1, n_max + 1):
                c = spec[n] / n_points
                inv = R ** (-n)
                c = c * inv
                re = c.real.mid()
                im = c.imag.mid()
                floor = biggest * float(inv) * 10.0 ** (-work_digits + GUARD + 2)
                if floor > 0:
                    worst = max(worst, abs(float(im)) / floor)
                man, exp = re.man_exp()
                out.append(n * mp.mpf((int(man), int(exp))))
        return {"coefficients": out, "imag_residue_over_floor": worst}
    finally:
        ctx.prec = old


def zeta_arith_evaluator(s):
    """(s - 1) zeta(s) on Arb: entire, 1 at s = 1, the arithmetic factor of xi."""
    return (s - 1) * s.zeta()


def dh_f_evaluator(digits: int):
    """f(s) = 5^{-s} [zeta(s,1/5) + kappa zeta(s,2/5) - kappa zeta(s,3/5) - zeta(s,4/5)] on Arb.

    ``digits`` must cover the working precision of the caller: kappa is taken
    from `zeta.epstein.kappa` at that many digits and handed to Arb as a string.
    """
    from flint import acb, arb, ctx

    from zeta.epstein import kappa

    digits = int(digits) + 10
    with mp.workdps(digits):
        kap_str = mpmath.nstr(kappa(digits), digits)
    cache = {}

    def f(s):
        prec = ctx.prec
        if prec not in cache:
            kap = arb(kap_str)
            cache[prec] = (kap, [acb(arb(a) / 5) for a in range(1, 5)])
        kap, qs = cache[prec]
        h = [s.zeta(q) for q in qs]
        return acb(5) ** (-s) * (h[0] + kap * h[1] - kap * h[2] - h[3])

    return f


def work_digits(n_max: int, dps: int, radius: str) -> int:
    """dps + 2*guard + n_max log10(1/r): `zeta.li`'s rule for the r^{-n} division."""
    return int(math.ceil(dps + 2 * GUARD + n_max * math.log10(1 / float(radius))))


def node_count(n_max: int, work: int, radius: str) -> int:
    """Smallest power of two above work ln10 / ln(1/r) + n_max + 8 (`zeta.li`'s rule)."""
    need = work * math.log(10) / math.log(1 / float(radius)) + n_max + 8
    return 1 << int(math.ceil(math.log2(need)))
