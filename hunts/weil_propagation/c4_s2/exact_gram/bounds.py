"""exact_gram/: the a priori bounds P1 to P4 of PREREG s1 (derivations: BOUNDS.md).

Everything here is python-flint ball arithmetic. Two published inequalities
enter as cited assumptions (BOUNDS.md s0), each spot-checked against arb in
test_bounds.py (measured, not proved here):

  (Landau)  |J_nu(x)| <= 0.7858 x^{-1/3},  nu >= 0, x > 0
            (L. J. Landau, J. London Math. Soc. 61 (2000) 197-215: c = 0.7857468704...);
  (Kapteyn) |J_nu(nu t)| <= t^nu exp(nu sqrt(1-t^2)) / (1 + sqrt(1-t^2))^nu,  0 < t <= 1
            (DLMF 10.14.5).

Modes are kernel/'s prolate data read as exact decimals (PREREG s1): the
Legendre coefficients c_r of phi~_n = sum_r c_r P_{k_r} on [0, 1] with
int_0^1 phi~^2 = 1, and zeta_n(w) = norm_n sum_r c_r 2 (-1)^{k_r/2} j_{k_r}(2 pi w)
for w >= 1, norm_n = (1 - lam_n^2)^{-1/2}.
"""

from __future__ import annotations

import math
import os
import sys
from dataclasses import dataclass, field

from flint import acb, arb, arb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
KERNEL = os.path.normpath(os.path.join(HERE, "..", "kernel"))

LANDAU = arb("0.7858")  # upper for 0.7857468704...
#: |j_k(x)| = sqrt(pi/(2x)) |J_{k+1/2}(x)| <= JB x^{-5/6}
JB_STR = "0.98487"  # >= sqrt(pi/2) * 0.7858 = 0.984859...
GAUSS_CONST = arb(64) / 15  # Trefethen, SIAM Rev. 50 (2008), Thm 4.5


def two_pi():
    return 2 * arb.pi()


# --------------------------------------------------------------------------
# modes
# --------------------------------------------------------------------------


@dataclass
class Modes:
    ks: list  # even Legendre orders
    coef: list  # coef[n][r] (arb, exact decimals)
    norm: list  # (1 - lam^2)^{-1/2} (arb)
    l1: list  # sum_r |c_r| (arb)
    _cache: dict = field(default_factory=dict, repr=False)

    @property
    def nvec(self):
        return len(self.coef)

    def C(self, n):
        """|zeta_n(v)| <= C_n v^{-5/6} for v >= 1 (Landau)."""
        return self.norm[n] * 2 * arb(JB_STR) * self.l1[n] * two_pi() ** (-arb(5) / 6)

    def deriv_at_1(self, n, m):
        """phi~_n^{(m)}(1) = sum_r c_r (k+m)! / (2^m m! (k-m)!) (cached)."""
        key = ("d", n, m, ctx.prec)
        if key not in self._cache:
            self._cache[key] = sum((c * _legendre_d1(k, m) for c, k in zip(self.coef[n], self.ks) if k >= m), arb(0))
        return self._cache[key]

    def dl1(self, n, m):
        """An upper bound on ||phi~_n^{(m)}||_{L1[-1,1]} (|P_k^{(m)}| <= P_k^{(m)}(1) on [-1, 1]) (cached)."""
        key = ("l", n, m, ctx.prec)
        if key not in self._cache:
            self._cache[key] = sum((abs(c) * 2 * _legendre_d1(k, m) for c, k in zip(self.coef[n], self.ks) if k >= m), arb(0))
        return self._cache[key]


def _legendre_d1(k, m):
    return arb(math.factorial(k + m)) / (arb(2) ** m * math.factorial(m) * math.factorial(k - m))


def prolate_modes(nvec, dps=40):
    if KERNEL not in sys.path:
        sys.path.insert(0, KERNEL)
    import sonin
    from mpmath import mp

    pv, pd = sonin.prolate_vectors(dps, 0, nvec), sonin.prolate_data(dps, 0)
    with mp.workdps(dps + 25):
        coef = [[arb(mp.nstr(c, dps + 20)) for c in pv["coef"][n]] for n in range(nvec)]
        lam = [arb(mp.nstr(x, dps + 20)) for x in pd["lam"]]
    norm = [(1 / (1 - lam[n] ** 2)).sqrt() if n < len(lam) else _norm_tiny_lam(n, dps) for n in range(nvec)]
    l1 = [sum((abs(c) for c in row), arb(0)) for row in coef]
    return Modes(list(pv["ks"]), coef, norm, l1)


def _norm_tiny_lam(n, dps):
    # beyond prolate_data's n_max, |lam| < 10^-(dps+GUARD) (sonin docstring): norm in [1, 1 + 10^-(2 dps)]
    return arb(1) + arb(0).union(arb(10) ** (-2 * dps))


# --------------------------------------------------------------------------
# spherical Bessel tables in balls
# --------------------------------------------------------------------------


def kapteyn_j(k, x):
    """An upper bound on |j_k(x)| for 0 < x <= k + 1/2 (Kapteyn, nu = k + 1/2)."""
    nu = arb(k) + arb(0.5)
    t = arb(x) / nu
    r = (1 - t * t).sqrt()
    J = t**nu * (nu * r).exp() / (1 + r) ** nu
    return (arb.pi() / (2 * arb(x))).sqrt() * J


_GAUSS = {}


def gauss_rule(n):
    """[(x_j, w_j)] of the n-point Gauss-Legendre rule on (-1, 1) at the current precision (arb, rigorous)."""
    key = (n, ctx.prec)
    if key not in _GAUSS:
        _GAUSS[key] = [arb.legendre_p_root(n, k, weight=True) for k in range(n)]
    return _GAUSS[key]


def point(left, right=None, n=0, j=0):
    """The j-th n-point Gauss node of the panel [left, right] (or the point left if right is None),
    as a function of the working precision. left and right are exact binary floats; midpoint and
    half-width are formed in arb (exact), so adjacent panels share their endpoint exactly."""
    if right is None:
        return lambda: arb(left)
    return lambda: (arb(left) + arb(right)) / 2 + (arb(right) - arb(left)) / 2 * gauss_rule(n)[j][0]


def zeta_values(modes, pts, scale=1):
    """zeta_n(scale * w) for w in pts (functions from point()), as an arb_mat (len(pts) x nvec)."""
    kmax = max(modes.ks)
    sgn = [2 * (-1) ** (k // 2) for k in modes.ks]
    rows = []
    for p in pts:
        tab = bessel_table(lambda: two_pi() * scale * p(), kmax)
        jk = [tab[k] * s for k, s in zip(modes.ks, sgn)]
        rows.append([modes.norm[n] * sum((c * j for c, j in zip(modes.coef[n], jk)), arb(0)) for n in range(modes.nvec)])
    return arb_mat(rows)


def bessel_table(zfun, kmax, extra_bits=64):
    """[j_0(z), .., j_kmax(z)] as balls, z = zfun() > 0 evaluated at the raised precision.
    Upward recurrence while its radius stays below 2^-(prec+8) in absolute terms (stable for
    k < z; past the turning point the balls track the growth); beyond that order,
    [0 +/- Kapteyn bound]. The extra precision doubles until the Kapteyn bound is below
    2^-(prec+8) at the hand-over order. Never silently wide."""
    old = ctx.prec
    while True:
        ctx.prec = old + extra_bits
        try:
            tol = arb(2) ** (-(old + 8))
            z = zfun()
            xf = float(z.mid())
            vals = [z.sin() / z, z.sin() / z**2 - z.cos() / z]
            k = 1
            while k < kmax:
                nxt = (2 * k + 1) / z * vals[k] - vals[k - 1]
                if nxt.rad() > tol:
                    break
                vals.append(nxt)
                k += 1
            ok = True
            for kk in range(len(vals), kmax + 1):
                b = kapteyn_j(kk, z.upper()) if kk + 0.5 >= xf else None
                if b is None or (kk == len(vals) and not b < tol):
                    ok = False
                    break
                vals.append(arb(0).union(b).union(-b))
        finally:
            ctx.prec = old
        if ok:
            return [+v for v in vals[: kmax + 1]]
        if extra_bits > 8192:
            raise ArithmeticError(f"bessel_table: no closure at z = {xf}, kmax = {kmax}")
        extra_bits *= 2


# --------------------------------------------------------------------------
# P1: Gauss panels in w (E3)
# --------------------------------------------------------------------------


def w_panels(Kmax, s_max, per_panel=12):
    """(left, h) of every panel, the same loop as two_adic/ta_mellin.w_nodes."""
    out, left, right_end = [], 1.0, 2.0**Kmax
    while left < right_end:
        freq = 2 * math.pi + s_max / left
        h = min(2 * math.pi / freq, right_end - left)
        nxt = left + h
        p2 = 2.0 ** math.floor(math.log2(left) + 1e-12)
        if left < 2 * p2 < nxt:
            h, nxt = 2 * p2 - left, 2 * p2
        out.append((left, h))
        left = nxt
    return out


def w_panel_ends(Kmax, s_max, per_panel=12):
    """Exact endpoints e_0 = 1 < e_1 < ... = 2^Kmax: each panel ends where the next begins."""
    return [left for left, _ in w_panels(Kmax, s_max, per_panel)] + [2.0**Kmax]


def gauss_panel_error(h, M, rho, n):
    """Error of the n-point Gauss rule on a panel of width h for |f| <= M on the image of E_rho
    (Trefethen 2008, Thm 4.5, scaled by h/2)."""
    rho = arb(rho)
    return arb(h) / 2 * GAUSS_CONST * M * rho ** (-2 * n) / (rho * rho - 1)


def _rho_for(mid, h, rho_max=15.0):
    return max(1.5, min(rho_max, 1.8 * mid / h))


def e3_hat_bound(Kmax, s_max, per_panel=12):
    """P1: sup over |s| <= s_max of |zeta^_n(s) - Gauss sum| / norm_n (the factor 2 ||xi||_1 <= 4
    included), summed over every panel of [1, 2^Kmax]. Multiply by norm_n for mode n.
    For b^ multiply further by 1/(1 - 2^{-1/2}) (BOUNDS.md s1.3)."""
    tot = arb(0)
    S = arb(s_max)
    ends = w_panel_ends(Kmax, s_max, per_panel)
    for left, right in zip(ends[:-1], ends[1:]):
        hh = arb(right) - arb(left)  # the exact width of the panel the rule uses
        h = float(hh.upper())
        mid = (arb(left) + arb(right)) / 2
        rho = _rho_for(float(mid.mid()), h)
        a_semi = hh / 4 * (arb(rho) + 1 / arb(rho))
        beta = hh / 4 * (arb(rho) - 1 / arb(rho))
        xmin = mid - a_semi
        if not xmin > 0:
            raise ArithmeticError("P1: ellipse reaches the branch cut")
        M = 2 * (two_pi() * beta + S * beta / xmin).exp() / xmin.sqrt()
        tot += gauss_panel_error(hh, M, rho, per_panel)
    return tot


# --------------------------------------------------------------------------
# P2: the tail beyond W (E4)
# --------------------------------------------------------------------------


def asym_remainder(beta_re, beta_abs, a, W, J):
    """|remainder| of the J-term series for int_W^inf e^{i a w} w^beta dw (Re beta < -1)."""
    poch = arb(1)
    for j in range(J):
        poch *= arb(beta_abs) + j
    return poch / abs(arb(a)) ** J * arb(W) ** (arb(beta_re) - J + 1) / (J - arb(beta_re) - 1)


def e4_tail_bound(modes, n, W, s_max, M, J):
    """P2: |T_n(W; s) - (M-derivative, J-term expansion)| for |s| <= s_max."""
    W = arb(W)
    rem_ibp = modes.norm[n] * modes.dl1(n, M) * two_pi() ** (-M) * W ** (arb(0.5) - M) / (M - arb(0.5))
    rem_ser = arb(0)
    for m in range(M):
        d = abs(modes.deriv_at_1(n, m))
        if d == 0:
            continue
        b_re = -(m + 1) - arb(0.5)
        b_abs = (b_re * b_re + arb(s_max) ** 2).sqrt()
        rem_ser += d * 2 * two_pi() ** (-(m + 1)) * asym_remainder(b_re, b_abs, two_pi(), W, J)
    return rem_ibp + modes.norm[n] * rem_ser


def b_kseries_tail(modes, n, k_stop):
    """|sum_{k >= k_stop} r^k T(2^k; s)| <= 3 C_n 2^{-5 k_stop/6} / (1 - 2^{-5/6}) (Landau)."""
    q = arb(2) ** (-arb(5) / 6)
    return 3 * modes.C(n) * q**k_stop / (1 - q)


# --------------------------------------------------------------------------
# P3: the trapezoid rule in s (aliasing, discrete tail)
# --------------------------------------------------------------------------


def alias_q(delta):
    return (-(two_pi() / (3 * arb(delta)))).exp()


def alias_weight(Ginv_abs, Cs):
    """sum_ij |G^-1_ij| C_i C_j."""
    n = len(Cs)
    return sum((Ginv_abs[i][j] * Cs[i] * Cs[j] for i in range(n) for j in range(n)), arb(0))


def p3_alias_entry(weight, L, delta):
    """Entrywise bound on the aliasing of one family's window sum M (BOUNDS.md s3.2)."""
    q = alias_q(delta)
    L = arb(L)
    return weight * arb(1.5) * L * (2 * L / 3).exp() * 2 * q / (1 - q)


def p3_alias_rho(weight, delta):
    q = alias_q(delta)
    return weight * arb(1.5) * 2 * q / (1 - q)


def kappa(L, N, S0):
    """sup_{|s| >= S0} sum_{|n| <= N} |V^_n(s)|^2 <= sum 4 / (L (S0 - 2 pi |n| / L)^2) (bound_quad/ Prop 2)."""
    L = arb(L)
    S0 = arb(S0)
    kN = two_pi() * N / L
    if not S0 > kN:
        raise ValueError("S0 must exceed 2 pi N / L")
    return sum((4 / (L * (S0 - two_pi() * abs(n) / L) ** 2) for n in range(-N, N + 1)), arb(0))


def p3_total(Ginv_abs_z, Ginv_abs_b, Cz, Cb, L, N, delta, S_prime):
    """Spectral-norm bound on the s-rule error of Delta_T at (L, N): aliasing of both families
    plus the discrete tail beyond S'."""
    wz, wb = alias_weight(Ginv_abs_z, Cz), alias_weight(Ginv_abs_b, Cb)
    alias = (2 * N + 1) * (p3_alias_entry(wz, L, delta) + p3_alias_entry(wb, L, delta))
    nvec = len(Cz)
    tail = kappa(L, N, S_prime) * (nvec + max(p3_alias_rho(wz, delta), p3_alias_rho(wb, delta)))
    return alias + tail


# --------------------------------------------------------------------------
# P4: Gram matrices in v-space
# --------------------------------------------------------------------------


def quad_pair(modes, a, b, m, per_panel=12, rho_max=15.0):
    """int_a^b zeta_i(u) zeta_j(2^m u) du (all i, j) by Gauss panels of width at most
    1 / (1 + 2^m), with the panel bound added to every entry (BOUNDS.md s4.1). Returns arb_mat.
    Nodes and weights are arb's (legendre_p_root), so the rule is the exact Gauss rule."""
    lam = 2**m
    nv = modes.nvec
    acc = arb_mat(nv, nv)
    err = arb(0)
    rule = gauss_rule(per_panel)
    left = a
    while left < b:
        # width at most one combined oscillation, and small enough near u = 1 that rho_max fits
        right = min(left + min(1.0 / (1 + lam), 1.8 * left / rho_max), b)
        h = right - left  # a float; the rule below uses the exact arb values of left and right
        mid = (left + right) / 2
        half_a = (arb(right) - arb(left)) / 2
        pts = [point(left, right, per_panel, j) for j in range(per_panel)]
        Z1 = zeta_values(modes, pts)
        Z2 = Z1 if m == 0 else zeta_values(modes, pts, scale=lam)
        W = arb_mat([[rule[q][1] * half_a if q == r else arb(0) for r in range(per_panel)] for q in range(per_panel)])
        acc += Z1.transpose() * W * Z2
        rho = max(1.5, min(rho_max, 1.8 * mid / h * 0.999))
        hh = 2 * half_a
        beta = hh / 4 * (arb(rho) - 1 / arb(rho))
        if not (arb(mid) - hh / 4 * (arb(rho) + 1 / arb(rho))) > 0:
            raise ArithmeticError("quad_pair: ellipse reaches u <= 0")
        err += gauss_panel_error(hh, 4 * (two_pi() * beta * (1 + lam)).exp(), rho, per_panel)
        left = right
    return arb_mat([[acc[i, j] + _pm(err * modes.norm[i] * modes.norm[j]) for j in range(nv)] for i in range(nv)])


def _pm(r):
    r = arb(r.upper())
    return arb(0).union(r).union(-r)


def _asym_int(a, beta, W, J):
    """(value, radius bound) of int_W^inf e^{i a w} w^beta dw by the J-term series; a != 0 real, beta real."""
    W = arb(W)
    a = arb(a)
    ia = acb(0, a)
    tot = acb(0)
    fall = arb(1)
    for j in range(J):
        tot += (-1) ** j * fall * W ** (arb(beta) - j) / ia ** (j + 1)
        fall *= arb(beta) - j
    val = -(ia * W).exp() * tot
    return val, asym_remainder(beta, abs(arb(beta)), a, W, J)


def gram_z_tail(modes, W, M, J=40):
    """P4, region C for G_z: int_W^inf zeta_i zeta_j by the product of the two M-term expansions,
    with every remainder bounded (BOUNDS.md s4.2). W must be in the convergent range (kmax_for)."""
    nv = modes.nvec
    W = arb(W)
    tp = two_pi()
    D = [[modes.norm[i] * (-1) ** p * modes.deriv_at_1(i, p) for p in range(M)] for i in range(nv)]
    I = [[acb(0) for _ in range(M)] for _ in range(M)]
    R = [[arb(0) for _ in range(M)] for _ in range(M)]
    for p in range(M):
        for q in range(M):
            e = p + q + 2
            for sg in (1, -1):
                for tg in (1, -1):
                    c = acb(0, sg) ** (-(p + 1)) * acb(0, tg) ** (-(q + 1)) * tp ** (-e)
                    if sg + tg == 0:
                        I[p][q] += c * W ** (-(e - 1)) / (e - 1)
                    else:
                        v, r = _asym_int((sg + tg) * tp, -e, W, J)
                        I[p][q] += c * v
                        R[p][q] += r * tp ** (-e)
    rem = [modes.norm[i] * modes.dl1(i, M) * tp ** (-M) for i in range(nv)]
    out = []
    for i in range(nv):
        row = []
        for j in range(nv):
            val = sum((D[i][p] * I[p][q] * D[j][q] for p in range(M) for q in range(M)), acb(0)).real
            e_ser = sum((abs(D[i][p]) * abs(D[j][q]) * R[p][q] for p in range(M) for q in range(M)), arb(0))
            e_rem = (modes.C(i) * rem[j] + rem[i] * modes.C(j)) * W ** (arb(1) / 6 - M) / (M - arb(1) / 6) \
                + rem[i] * rem[j] * W ** (1 - 2 * arb(M)) / (2 * M - 1)
            r = e_ser + e_rem
            row.append(val + arb(0).union(r).union(-r))
        out.append(row)
    return arb_mat(out)


def gram_z(modes, Kmax, M=None, per_panel=12):
    """P4: G_z = int_1^inf zeta_i zeta_j: Gauss panels on [1, 2^Kmax] plus the region-C expansion."""
    if M is None:
        M = choose_M(modes, 2.0**Kmax)
    return quad_pair(modes, 1.0, 2.0**Kmax, 0, per_panel) + gram_z_tail(modes, 2.0**Kmax, M)


def choose_M(modes, W, target=arb(10) ** -30, Mmax=120):
    """Smallest M with max_n norm_n ||p^{(M)}||_1 (2 pi W)^{-M} below target (P2's convergence rule)."""
    for M in range(2, Mmax):
        if all(float((modes.norm[n] * modes.dl1(n, M) * (two_pi() * W) ** (-M)).upper()) < float(target.mid())
               for n in range(modes.nvec)):
            return M
    raise ArithmeticError(f"P2: no M <= {Mmax} closes at W = {W}")


def gram_b_region_a(modes, Kmax, per_panel=12):
    """P4, region A of G_b: the pieces (m, t) with t + m + 1 <= Kmax, weights w_t = 2 - 2^-t,
    sum_t w_t [A(m, t) + A(m, t)^T (m >= 1)] (BOUNDS.md s4.3). Regions B and C are the next unit."""
    nv = modes.nvec
    acc = arb_mat(nv, nv)
    for t in range(Kmax):
        wt = 2 - arb(2) ** (-t)
        for m in range(0, Kmax - t):
            A = quad_pair(modes, 2.0**t, 2.0 ** (t + 1), m, per_panel)
            acc += A * wt if m == 0 else (A + A.transpose()) * wt
    return acc


def gram_b(modes, Kmax):
    raise NotImplementedError("P4: G_b regions B and C (integration by parts) are not built yet; "
                              "production stays at PREREG row D0 (BOUNDS.md s4.4)")
