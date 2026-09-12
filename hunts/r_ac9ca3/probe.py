"""Hunt R-AC9CA3 Probe: Truncated Weil Positivity on Davenport-Heilbronn.

Settles whether the first positivity failure of the CvS/CCM truncated Weil form
on Davenport-Heilbronn is at (c, N) = (31, 60), tracking the first off-line pair.

Runs end to end with Arb ball arithmetic (python-flint) and mpmath cross-checks.
Emits findings to hunts/r_ac9ca3/results.json.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from pathlib import Path

from flint import acb, acb_mat, arb, ctx
from mpmath import mp

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
RESULTS_JSON = HERE / "results.json"
DATA_ONLINE_ZEROS = REPO_ROOT / "data" / "dh_zeros_online_T120.json"

GAMMA_OFF_1 = "85.699348485377592171929267708941729037987829423408"
DELTA_OFF_1 = "0.30851718245663738555335196060684412785067026830502"

GAMMA_OFF_2 = "114.1633427307569809041644"
DELTA_OFF_2 = "0.1508300806097370824038"


def _ball_pm(x: arb, eps: arb) -> arb:
    """Add a symmetric radius eps to ball x."""
    eps = abs(eps)
    return x + (arb(0).union(eps).union(-eps))


def arb_to_mpf(x: arb, digits: int = 70) -> mp.mpf:
    """Extract clean decimal string from arb midpoint to mpf."""
    s = x.str(digits).split()[0]
    if s.startswith("["):
        s = s[1:]
    return mp.mpf(s)


# ---------------------------------------------------------------------------
# BallTruncation: rigorous ball-arithmetic Galerkin matrix assembly
# ---------------------------------------------------------------------------


class BallTruncation:
    """Rigorous Arb ball assembly of the CvS/CCM truncated Weil matrix."""

    def __init__(self, c: int, N: int, kind: str = "dh", prec: int = 600):
        ctx.prec = prec
        self.prec = prec
        self.c = c
        self.N = N
        self.kind = kind
        pi = arb.pi()
        L = arb(c).log()
        self.L = L
        z = (-2 * L).exp()
        J = int(math.ceil((prec + 30) * math.log(2) / (2 * float(L)))) + 3

        if kind == "zeta":
            a = arb(1) / 4
            const = -pi.log() + acb(a).digamma().real
            limit = int(c)
            sieve = [True] * (limit + 1)
            coeffs = []
            for p in range(2, limit + 1):
                if sieve[p]:
                    for m in range(2 * p, limit + 1, p):
                        sieve[m] = False
                    q = p
                    while q <= limit:
                        coeffs.append((q, arb(p).log()))
                        q *= p
        elif kind == "dh":
            a = arb(3) / 4
            const = -(pi / 5).log() + acb(a).digamma().real
            coeffs = self._dh_coeffs(int(c))
        else:
            raise ValueError(f"Unknown kind {kind!r}")

        self.a = a
        mus = [2 * (arb(j) + a) for j in range(J)]
        Es = [(-m * L).exp() for m in mus]
        one_minus_z = 1 - z

        tail_int = sum((E / m for m, E in zip(mus, Es)), arb(0))
        tail_int = _ball_pm(tail_int, Es[-1] * z / (mus[-1] * one_minus_z))

        S = [arb(0)] * (N + 1)
        Dg = [arb(0)] * (N + 1)
        for k in range(N + 1):
            om = 2 * pi * k / L
            zz = acb(a, om / 2)
            psi0 = zz.digamma()
            psi1 = acb(2).zeta(zz)
            if k == 0:
                S[0] = arb(0)
                sum_cos1 = arb(0)
            else:
                geo = sum((E * om / (m * m + om * om) for m, E in zip(mus, Es)), arb(0))
                geo = _ball_pm(geo, Es[-1] * z * om / (mus[-1] ** 2 * one_minus_z))
                S[k] = psi0.imag / 2 - geo
                geo1 = sum((E * om * om / (m * (m * m + om * om)) for m, E in zip(mus, Es)), arb(0))
                geo1 = _ball_pm(geo1, Es[-1] * z / (mus[-1] * one_minus_z))
                sum_cos1 = -(psi0.real - acb(a).digamma().real) / 2 + geo1

            geox = sum((E * ((m * m - om * om) / (m * m + om * om) ** 2 + m * L / (m * m + om * om)) for m, E in zip(mus, Es)), arb(0))
            geox = _ball_pm(geox, Es[-1] * z * (1 + mus[-1] * L) / (mus[-1] ** 2 * one_minus_z))
            sum_xcos = psi1.real / 4 - geox
            Dg[k] = 2 * sum_cos1 - (2 / L) * sum_xcos

        self._S = S
        self._archdiag = [const - Dg[k] + 2 * tail_int for k in range(N + 1)]
        P = [arb(0)] * (N + 1)
        R = [arb(0)] * (N + 1)
        for q, lam_val in coeffs:
            y = arb(q).log()
            w = lam_val / arb(q).sqrt()
            for k in range(N + 1):
                om = 2 * pi * k / L
                P[k] += w * (om * y).sin()
                R[k] += w * 2 * (1 - y / L) * (om * y).cos()
        self._P = P
        self._R = R
        self._pi = pi

    def _dh_coeffs(self, cmax: int):
        s5 = arb(5).sqrt()
        kap = ((10 - 2 * s5).sqrt() - 2) / (s5 - 1)
        pat = [arb(1), kap, -kap, arb(-1), arb(0)]

        def a(n):
            return pat[(n - 1) % 5]

        lam = {1: arb(0)}
        out = []
        for n in range(2, cmax + 1):
            s = a(n) * arb(n).log()
            for d in range(2, n):
                if n % d == 0:
                    s -= lam[d] * a(n // d)
            lam[n] = s
            out.append((n, s))
        return out

    def w02(self, n: int, m: int) -> arb:
        if self.kind != "zeta":
            return arb(0)
        L = self.L
        pi2 = self._pi**2
        num = 32 * L * (L / 4).sinh() ** 2 * (L * L - 16 * pi2 * m * n)
        return num / ((L * L + 16 * pi2 * m * m) * (L * L + 16 * pi2 * n * n))

    def _sgn(self, seq, k):
        return seq[k] if k >= 0 else -seq[-k]

    def entry(self, n: int, m: int) -> arb:
        if n == m:
            k = abs(n)
            return self.w02(n, n) + self._archdiag[k] - self._R[k]
        tm = self._sgn(self._S, m) + self._sgn(self._P, m)
        tn = self._sgn(self._S, n) + self._sgn(self._P, n)
        return self.w02(n, m) - (tm - tn) / (self._pi * (n - m))

    def even_matrix(self):
        N = self.N
        s2 = arb(2).sqrt()
        M = [[arb(0)] * (N + 1) for _ in range(N + 1)]
        M[0][0] = self.entry(0, 0)
        for k in range(1, N + 1):
            v = s2 * self.entry(0, k)
            M[0][k] = M[k][0] = v
        for j in range(1, N + 1):
            for k in range(j, N + 1):
                v = self.entry(j, k) + self.entry(j, -k)
                M[j][k] = M[k][j] = v
        return M

    def odd_matrix(self):
        N = self.N
        M = [[arb(0)] * N for _ in range(N)]
        for j in range(1, N + 1):
            for k in range(j, N + 1):
                v = self.entry(j, k) - self.entry(j, -k)
                M[j - 1][k - 1] = M[k - 1][j - 1] = v
        return M


# ---------------------------------------------------------------------------
# Linear algebra helpers: Ball LDL^T and Rayleigh bounds
# ---------------------------------------------------------------------------


def pivot_signs(M, prec: int):
    """Ball LDL^T of M; returns (signs, conclusive)."""
    ctx.prec = prec
    n = len(M)
    A = [[M[i][j] for j in range(n)] for i in range(n)]
    d = []
    Lf = [[arb(0)] * n for _ in range(n)]
    signs = []
    for j in range(n):
        s = A[j][j]
        for k in range(j):
            s -= Lf[j][k] * Lf[j][k] * d[k]
        if s > 0:
            signs.append(1)
        elif s < 0:
            signs.append(-1)
        else:
            signs.append(0)
            return signs, False
        d.append(s)
        for i in range(j + 1, n):
            t = A[i][j]
            for k in range(j):
                t -= Lf[i][k] * Lf[j][k] * d[k]
            Lf[i][j] = t / s
    return signs, True


def first_neg_from_signs(signs, sector: str):
    """Smallest band N whose sector matrix has a negative eigenvalue."""
    for j, s in enumerate(signs):
        if s < 0:
            return j if sector == "even" else j + 1
    return None


def eig_enclosure_min(M, n: int, prec: int):
    """Enclose smallest real eigenvalue of n x n leading submatrix."""
    ctx.prec = prec
    A = acb_mat([[acb(M[i][j]) for j in range(n)] for i in range(n)])
    E = A.eig(nonstop=True, multiple=True)
    lo = min(E, key=lambda e: float(e.real.mid()))
    return lo.real


# ---------------------------------------------------------------------------
# Dictionary functions and transform profiling
# ---------------------------------------------------------------------------


def embed_even_arb(v):
    N = len(v) - 1
    s2 = arb(2).sqrt()
    u = {0: v[0]}
    for k in range(1, N + 1):
        u[k] = v[k] / s2
        u[-k] = v[k] / s2
    return u


def g_even_arb(v, L, prec: int = 300):
    ctx.prec = prec
    N = len(v) - 1
    u = embed_even_arb(v)
    idx = list(range(-N, N + 1))
    pi = arb.pi()

    def g(r):
        is_complex = isinstance(r, acb)
        tot = acb(0) if is_complex else arb(0)
        Ts = {}
        for k in range(-N, N + 1):
            if k == 0:
                Ts[0] = acb(0) if is_complex else arb(0)
            else:
                om = 2 * pi * k / L
                s = ((r - om) * L / 2).sin()
                Ts[k] = 2 * s * s * om / ((om - r) * (om + r))
        for i, n in enumerate(idx):
            for m in idx[i:]:
                w = u[n] * u[m] * (1 if m == n else 2)
                if n == m:
                    om = 2 * pi * n / L
                    sm = ((r - om) * L / 2).sin()
                    sp = ((r + om) * L / 2).sin()
                    val = (2 / L) * (sm * sm / (r - om) ** 2 + sp * sp / (r + om) ** 2)
                else:
                    val = (Ts[m] - Ts[n]) / (pi * (n - m))
                tot += w * val
        return tot

    return g


# ---------------------------------------------------------------------------
# Full Probe Runner
# ---------------------------------------------------------------------------


def run_probe():
    t_start = time.time()
    results = {
        "meta": {
            "hunt_id": "r_ac9ca3",
            "question": "Truncated Weil form: first positivity failure on Davenport-Heilbronn is at (c, N) = (31, 60), tracking the off-line pair",
            "gamma_off": GAMMA_OFF_1,
            "delta_off": DELTA_OFF_1,
            "gamma_off_2": GAMMA_OFF_2,
            "delta_off_2": DELTA_OFF_2,
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        },
        "ladders": {},
        "deep_probes": {},
        "transition_analysis": {},
        "marginal_cell_31_60": {},
        "zeta_control_31_60": {},
        "localization_deep_cell_47_64": {},
        "dictionary_attribution_31_60": {},
        "second_offline_pair_analysis": {},
    }

    print("=" * 78)
    print("STAGE 1: LATTICE SCAN (c in 6..60, Nmax=128)")
    print("=" * 78)

    first_neg_N_even_by_c = {}
    first_neg_N_odd_by_c = {}
    band_edges_at_crossing = []

    for c in range(6, 61):
        t0 = time.time()
        bt = BallTruncation(c, 128, kind="dh", prec=600)
        Me = bt.even_matrix()
        Mo = bt.odd_matrix()
        se, ce = pivot_signs(Me, 600)
        so, co = pivot_signs(Mo, 600)

        neg_e = first_neg_from_signs(se, "even")
        neg_o = first_neg_from_signs(so, "odd")

        first_neg_N_even_by_c[str(c)] = neg_e
        first_neg_N_odd_by_c[str(c)] = neg_o

        n_neg_e = sum(1 for s in se if s < 0)
        n_neg_o = sum(1 for s in so if s < 0)

        elapsed = round(time.time() - t0, 2)
        results["ladders"][str(c)] = {
            "c": c,
            "Nmax": 128,
            "prec": 600,
            "conclusive_even": bool(ce),
            "conclusive_odd": bool(co),
            "first_neg_N_even": neg_e,
            "first_neg_N_odd": neg_o,
            "n_neg_even_at_128": n_neg_e,
            "n_neg_odd_at_128": n_neg_o,
            "elapsed_s": elapsed,
        }

        if c >= 32 and neg_e is not None:
            L_val = math.log(c)
            band_edge = 2 * math.pi * neg_e / L_val
            band_edges_at_crossing.append(band_edge)

        print(
            f"c={c:2d}: first_neg even={neg_e} odd={neg_o} "
            f"n_neg@128=({n_neg_e},{n_neg_o}) concl=({ce},{co}) [{elapsed:.2f}s]"
        )

    # Deep probes at boundary
    print("\nSTAGE 1b: DEEP PROBES (c=29 Nmax=256, c=30 Nmax=256, c=31 Nmax=192)")
    for c, Nmax in ((29, 256), (30, 256), (31, 192)):
        t0 = time.time()
        bt = BallTruncation(c, Nmax, kind="dh", prec=600)
        se, ce = pivot_signs(bt.even_matrix(), 600)
        so, co = pivot_signs(bt.odd_matrix(), 600)
        neg_e = first_neg_from_signs(se, "even")
        neg_o = first_neg_from_signs(so, "odd")
        elapsed = round(time.time() - t0, 2)
        results["deep_probes"][str(c)] = {
            "c": c,
            "Nmax": Nmax,
            "prec": 600,
            "conclusive_even": bool(ce),
            "conclusive_odd": bool(co),
            "first_neg_N_even": neg_e,
            "first_neg_N_odd": neg_o,
            "n_neg_even": sum(1 for s in se if s < 0),
            "n_neg_odd": sum(1 for s in so if s < 0),
            "elapsed_s": elapsed,
        }
        print(
            f"deep c={c:2d} Nmax={Nmax}: first_neg even={neg_e} odd={neg_o} "
            f"concl=({ce},{co}) [{elapsed:.2f}s]"
        )

    # Transition analysis
    mean_band_edge = sum(band_edges_at_crossing) / len(band_edges_at_crossing)
    var_band_edge = sum((x - mean_band_edge) ** 2 for x in band_edges_at_crossing) / len(band_edges_at_crossing)
    std_band_edge = math.sqrt(var_band_edge)

    results["transition_analysis"] = {
        "first_negative_cell": {"c": 31, "N": 60, "sector": "even"},
        "positive_regime_c_le_30": "c <= 30 strictly positive definite for all N <= 128 (and N <= 256 at c=29, 30)",
        "band_edge_mean_c32_60": round(mean_band_edge, 2),
        "band_edge_std_c32_60": round(std_band_edge, 2),
        "band_edge_min_c32_60": round(min(band_edges_at_crossing), 2),
        "band_edge_max_c32_60": round(max(band_edges_at_crossing), 2),
        "target_gamma_off": float(GAMMA_OFF_1),
    }

    print("\n" + "=" * 78)
    print("STAGE 2: PRECISION ENCLOSURES AT MARGINAL CELL (31, 60)")
    print("=" * 78)

    bt31 = BallTruncation(31, 64, kind="dh", prec=700)
    Me31 = bt31.even_matrix()

    # Enclosures for N=58..64
    e_encs = {}
    for N in (58, 59, 60, 61, 64):
        enc = eig_enclosure_min(Me31, N + 1, 700)
        e_encs[str(N)] = {
            "mid": enc.str(30).split()[0].strip("[]"),
            "rad": float(enc.rad()),
            "sign": "positive" if enc > 0 else "negative",
        }
        print(f"N={N}: lam_min enclosure = {e_encs[str(N)]['mid']} (rad ~ {float(enc.rad()):.2e})")

    # Rayleigh upper bound with dps 60 eigenvector
    mp.dps = 60
    bt31_60 = BallTruncation(31, 60, kind="dh", prec=700)
    Me31_60 = bt31_60.even_matrix()

    M_mp = mp.matrix(61, 61)
    for i in range(61):
        for j in range(61):
            M_mp[i, j] = arb_to_mpf(Me31_60[i][j], 70)

    ev_mp, vecs_mp = mp.eigsy(M_mp)
    ord_mp = sorted(range(len(ev_mp)), key=lambda i: ev_mp[i])
    v_dps60 = [vecs_mp[i, ord_mp[0]] for i in range(61)]

    # Convert to exact dyadics in Arb
    ctx.prec = 700
    v_dyadic = []
    for x in v_dps60:
        sign, man, exp, _ = mp.mpf(x)._mpf_
        v_dyadic.append(arb(int(-man if sign else man)) * (arb(2) ** exp))

    num = arb(0)
    for i in range(61):
        for j in range(61):
            num += v_dyadic[i] * Me31_60[i][j] * v_dyadic[j]
    den = sum((x * x for x in v_dyadic), arb(0))
    q_ball = num / den
    q_upper = q_ball.mid() + q_ball.rad()

    so31_60, co31_60 = pivot_signs(bt31_60.odd_matrix(), 700)

    results["marginal_cell_31_60"] = {
        "enclosures": e_encs,
        "lambda_min_59": e_encs["59"]["mid"],
        "lambda_min_60": e_encs["60"]["mid"],
        "mpmath_eig_dps60": mp.nstr(ev_mp[ord_mp[0]], 20),
        "rayleigh_quotient_mid": q_ball.str(30).split()[0].strip("[]"),
        "rayleigh_upper_endpoint": q_upper.str(30).split()[0].strip("[]"),
        "rayleigh_upper_is_strictly_negative": bool(q_upper < 0),
        "odd_sector_inertia": [sum(1 for s in so31_60 if s > 0), sum(1 for s in so31_60 if s < 0), bool(co31_60)],
    }
    print(f"mpmath scout eigenvalue at (31,60): {results['marginal_cell_31_60']['mpmath_eig_dps60']}")
    print(f"Rayleigh upper endpoint at (31,60): {results['marginal_cell_31_60']['rayleigh_upper_endpoint']} (strictly negative: {q_upper < 0})")
    print(f"Odd sector inertia at (31,60):      {results['marginal_cell_31_60']['odd_sector_inertia']}")

    print("\n" + "=" * 78)
    print("STAGE 3: DISCRIMINATION CONTROL (RIEMANN ZETA AT (31, 60))")
    print("=" * 78)

    t0 = time.time()
    bt_zeta = BallTruncation(31, 60, kind="zeta", prec=2400)
    se_z, ce_z = pivot_signs(bt_zeta.even_matrix(), 2400)
    so_z, co_z = pivot_signs(bt_zeta.odd_matrix(), 2400)
    enc_z = eig_enclosure_min(bt_zeta.even_matrix(), 61, 2400)
    elapsed_z = round(time.time() - t0, 2)

    results["zeta_control_31_60"] = {
        "c": 31,
        "N": 60,
        "prec": 2400,
        "even_inertia": [sum(1 for s in se_z if s > 0), sum(1 for s in se_z if s < 0), bool(ce_z)],
        "odd_inertia": [sum(1 for s in so_z if s > 0), sum(1 for s in so_z if s < 0), bool(co_z)],
        "lam_min_mid": enc_z.str(30).split()[0].strip("[]"),
        "lam_min_is_strictly_positive": bool(enc_z > 0),
        "elapsed_s": elapsed_z,
    }
    print(f"Zeta (31, 60) even inertia: {results['zeta_control_31_60']['even_inertia']}")
    print(f"Zeta (31, 60) odd inertia:  {results['zeta_control_31_60']['odd_inertia']}")
    print(f"Zeta (31, 60) lam_min:      {results['zeta_control_31_60']['lam_min_mid']} [{elapsed_z:.2f}s]")

    print("\n" + "=" * 78)
    print("STAGE 4: LOCALIZATION AT DEEP CELL (47, 64)")
    print("=" * 78)

    bt47 = BallTruncation(47, 64, kind="dh", prec=600)
    Me47 = bt47.even_matrix()
    M47_mp = mp.matrix(65, 65)
    for i in range(65):
        for j in range(65):
            M47_mp[i, j] = arb_to_mpf(Me47[i][j], 70)
    ev47, vecs47 = mp.eigsy(M47_mp)
    ord47 = sorted(range(len(ev47)), key=lambda i: ev47[i])
    lam47 = float(ev47[ord47[0]])
    v47 = [float(vecs47[i, ord47[0]]) for i in range(65)]

    L47 = math.log(47)
    gamma_target = float(GAMMA_OFF_1)
    k_target = gamma_target * L47 / (2 * math.pi)

    tot_mass = sum(x * x for x in v47)
    win_mass = sum(v47[k] ** 2 for k in range(65) if abs(2 * math.pi * k / L47 - gamma_target) <= 6.0)
    mass_fraction = win_mass / tot_mass

    k_peak = max(range(65), key=lambda k: abs(v47[k]))
    freq_peak = 2 * math.pi * k_peak / L47

    results["localization_deep_cell_47_64"] = {
        "c": 47,
        "N": 64,
        "lambda_min": lam47,
        "k_peak": k_peak,
        "freq_peak": round(freq_peak, 4),
        "target_freq": gamma_target,
        "k_target": round(k_target, 4),
        "mass_fraction_within_6_of_target": round(mass_fraction, 4),
    }
    print(f"Deep cell (47, 64) lam_min: {lam47:.6f}")
    print(f"Peak mode k={k_peak} (freq={freq_peak:.2f}) vs k_target={k_target:.2f} (freq={gamma_target:.2f})")
    print(f"Mass fraction within +-6 of target: {mass_fraction * 100:.2f}%")

    print("\n" + "=" * 78)
    print("STAGE 5: DICTIONARY DECOMPOSITION AT (31, 60)")
    print("=" * 78)

    t0 = time.time()
    v_arb = [v_dyadic[i] for i in range(61)]
    L_arb = arb(31).log()
    g_arb = g_even_arb(v_arb, L_arb, prec=300)

    g_off = arb(GAMMA_OFF_1)
    d_off = arb(DELTA_OFF_1)

    quad_pos = g_arb(acb(g_off, d_off))
    quad_neg = g_arb(acb(g_off, -d_off))
    quad_tot = 2 * (quad_pos + quad_neg)
    quad_re = quad_tot.real

    # Load on-line zeros
    with open(DATA_ONLINE_ZEROS) as f:
        seeds = json.load(f)["zeros"]

    online_terms = [2 * g_arb(arb(s)) for s in seeds]
    online_sum = sum(online_terms, arb(0))
    all_online_nonneg = all(t >= 0 for t in online_terms)

    lam_min_val = arb(results["marginal_cell_31_60"]["lambda_min_60"])
    lam_minus_quad = lam_min_val - quad_re

    # Tail model
    dens = lambda r: mp.log(5 * r / (2 * mp.pi)) / (2 * mp.pi)
    gv_mp = lambda r: float(g_arb(arb(r)).mid())
    tail_est = mp.quad(lambda r: gv_mp(r) * dens(r), [120, 200, 400, 600])

    elapsed_dict = round(time.time() - t0, 2)
    results["dictionary_attribution_31_60"] = {
        "c": 31,
        "N": 60,
        "lambda_min": lam_min_val.str(30).split()[0].strip("[]"),
        "offline_quadruple": quad_re.str(30).split()[0].strip("[]"),
        "online_partial_sum_T120": online_sum.str(30).split()[0].strip("[]"),
        "all_online_terms_nonnegative": bool(all_online_nonneg),
        "lambda_minus_quad": lam_minus_quad.str(30).split()[0].strip("[]"),
        "lambda_minus_quad_is_positive": bool(lam_minus_quad > 0),
        "tail_model_T_gt_120": str(tail_est),
        "elapsed_s": elapsed_dict,
    }
    print(f"lambda_min:             {results['dictionary_attribution_31_60']['lambda_min']}")
    print(f"offline quadruple:      {results['dictionary_attribution_31_60']['offline_quadruple']}")
    print(f"online partial sum:     {results['dictionary_attribution_31_60']['online_partial_sum_T120']}")
    print(f"lambda - quadruple:     {results['dictionary_attribution_31_60']['lambda_minus_quad']} (strictly positive: {lam_minus_quad > 0})")
    print(f"tail estimate (T > 120):{tail_est}")

    print("\n" + "=" * 78)
    print("STAGE 6: SECOND OFF-LINE PAIR DETECTION (c >= 44)")
    print("=" * 78)
    c44_neg_count = results["ladders"]["44"]["n_neg_even_at_128"]
    c47_neg_count = results["ladders"]["47"]["n_neg_even_at_128"]
    results["second_offline_pair_analysis"] = {
        "second_negative_threshold_c": 44,
        "n_neg_even_at_c44_N128": c44_neg_count,
        "n_neg_even_at_c47_N128": c47_neg_count,
        "second_offline_zero": f"rho_2 = 0.65083 + 114.16334i (delta=0.1508, gamma=114.16)",
        "mechanism": "Second off-line pair enters window at higher bandwidth L=log(c) >= log(44) ~ 3.78",
    }
    print(f"At c=44, N=128: n_neg_even = {c44_neg_count}")
    print(f"At c=47, N=128: n_neg_even = {c47_neg_count}")

    # Total elapsed
    results["meta"]["total_elapsed_s"] = round(time.time() - t_start, 2)

    with open(RESULTS_JSON, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nAll results successfully written to {RESULTS_JSON} in {results['meta']['total_elapsed_s']}s")
    return results


if __name__ == "__main__":
    run_probe()
