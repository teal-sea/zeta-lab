"""referee/: helpers for the falsification tests of the Delta_T error bound.

Written before any code in bound_trunc/, bound_quad/ or assembler/ was read
(BRIEF.md, Independence). Everything here imports two_adic/, kernel/ and
checker/ read-only.

Three things live here.

1. ``delta_T_knobs``: two_adic/'s Delta_T build (``ta_prolate.delta_T_cells``
   as checker/'s ``run_checker_ts.build_unit`` calls it, then symmetrised and
   real as the snapshot stores it) re-assembled from the same two_adic/
   functions, with the knobs the fixed bound interface does not expose made
   explicit: the w Gauss nodes per panel, the s panel width and nodes, the
   term counts of the asymptotic 1/w tail series, the number of derivatives
   of phi~_n at 1, a relative perturbation of the samples, a mode dropped from
   the family, the rho route and the assembly summation. At the defaults it
   must reproduce the snapshot row bit for bit up to platform rounding
   (``test_referee_bounds.py`` pins that).
2. Loaders for the stored matrices (checker/'s snapshot, two_adic/'s s7b
   probe runs) and for the bound modules and JSON files of the two bound
   folders, by path, so that an absent bound is a skip and a malformed one a
   failure.
3. Exact conversions: an arb ball's upper end and a decimal string as fmpq,
   and an exact Frobenius upper bound of a float64 matrix difference.
"""

from __future__ import annotations

import contextlib
import importlib.util
import json
import math
import os
import sys
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
C4 = os.path.normpath(os.path.join(HERE, ".."))
TWO_ADIC = os.path.join(C4, "two_adic")
KERNEL = os.path.join(C4, "kernel")
CHECKER = os.path.join(C4, "checker")
for _p in (TWO_ADIC, KERNEL):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import ta_mellin as TM  # noqa: E402  (two_adic/, read-only)
import ta_prolate as TP  # noqa: E402  (two_adic/, read-only)

TWO_PI = 2.0 * math.pi
CELLS = (2.2, 2.5, 2.9)
PLANTS_JSON = os.path.join(HERE, "referee_plants.json")
SNAPSHOT = os.path.join(CHECKER, "checker_ts_snapshot.json")
GRAM_PROBE = os.path.join(TWO_ADIC, "ta_gram_probe.json")
BOUND_TRUNC_PY = os.path.join(C4, "bound_trunc", "eps_trunc.py")
BOUND_TRUNC_JSON = os.path.join(C4, "bound_trunc", "eps_trunc.json")
BOUND_QUAD_PY = os.path.join(C4, "bound_quad", "eps_quad.py")
BOUND_QUAD_JSON = os.path.join(C4, "bound_quad", "eps_quad.json")

# The eleven stored builds (nvec, S as keyed, N), BRIEF.md "Stored builds".
STORED_BUILDS = [
    (80, 1200, 8),
    (80, 1200, 16), (80, 1600, 16), (120, 1200, 16), (120, 1600, 16), (160, 1600, 16),
    (200, 2400, 32), (240, 2400, 32), (280, 2266, 32), (319, 2633, 32), (364, 3060, 32),
]


# ------------------------------------------------------------------ the build


_PM_CACHE: dict = {}
_HATS_CACHE: dict = {}


def prolate_modes(nvec: int, mderiv: int = 14):
    key = (nvec, mderiv)
    if key not in _PM_CACHE:
        _PM_CACHE[key] = TP.ProlateModes(nvec=nvec, dps=20, mderiv=mderiv)
    return _PM_CACHE[key]


def _tail_modes(pm, W, s, mmax, terms):
    """ta_prolate._tail_modes, restricted to the derivative orders pm carries."""
    return TP._tail_modes(pm, W, s, mmax=min(mmax, pm.derivs.shape[1] - 1), terms=terms)


def hats_knobs(pm, s, Kmax, *, w_per_panel=12, terms=25, far_terms=8, far_mmax=4, chunk=128):
    """ta_prolate.hats_modes (alpha = 1) with its hard-coded counts as arguments.

    Defaults are hats_modes' own: per_panel 12, the tail at 2^Kmax to 25 terms
    and all derivative orders, the dilates beyond Kmax to 8 terms and orders
    up to 4, stopping when a dilate's term falls below 1e-18.
    """
    if (2 * (pm.nvec - 1)) ** 2 / (4 * math.pi * 2.0 ** Kmax) > 2.0:
        raise ValueError(f"Kmax = {Kmax} too small for {pm.nvec} modes (two_adic/'s guard)")
    s = np.asarray(s, dtype=float)
    w, wt, level = TM.w_nodes(Kmax, float(np.abs(s).max()), w_per_panel)
    Fw = pm.zeta(w) * wt[None, :]
    logw = np.log(w)
    idx = [np.where(level == k)[0] for k in range(Kmax)]
    Wmax = 2.0 ** Kmax
    Z = np.zeros((pm.nvec, s.size), dtype=complex)
    B = np.zeros((pm.nvec, s.size), dtype=complex)
    for i0 in range(0, s.size, chunk):
        ss = s[i0 : i0 + chunk]
        ph = np.exp(np.outer(-0.5 - 1j * ss, logw))
        lev = np.stack([ph[:, ik] @ Fw[:, ik].T for ik in idx], axis=2)
        tail = _tail_modes(pm, Wmax, ss, mmax=pm.derivs.shape[1] - 1, terms=terms)
        Tk = np.cumsum(lev[:, :, ::-1], axis=2)[:, :, ::-1] + tail[:, :, None]
        r = 2.0 ** (-0.5 + 1j * ss)
        rk = r[:, None] ** np.arange(Kmax)[None, :]
        bh = np.einsum("sk,snk->sn", rk, Tk)
        k, rpow = Kmax, r ** Kmax
        while k < Kmax + 70:
            term = rpow[:, None] * _tail_modes(pm, 2.0 ** k, ss, mmax=far_mmax, terms=far_terms)
            bh += term
            if np.abs(term).max() < 1e-18:
                break
            k += 1
            rpow = rpow * r
        Z[:, i0 : i0 + chunk] = Tk[:, :, 0].T
        B[:, i0 : i0 + chunk] = bh.T
    return Z, B


def _perturb(x, rel, rng):
    x = np.asarray(x)
    if np.iscomplexobj(x):
        e = rng.uniform(-1, 1, x.shape) + 1j * rng.uniform(-1, 1, x.shape)
    else:
        e = rng.uniform(-1, 1, x.shape)
    return x * (1.0 + rel * e)


def rho_svd(hat_rows, factor):
    """rho by a thin SVD of F (a second stable route; QR is two_adic/'s).

    rho(s) = ||Sigma^-1 V^* conj(w^(s))||^2 with F = U Sigma V^*, G = F^* F.
    """
    _, sig, Vh = np.linalg.svd(np.asarray(factor), full_matrices=False)
    Y = (np.conj(Vh) @ np.conj(hat_rows)) / sig[:, None]
    return np.sum(np.abs(Y) ** 2, axis=0)


def T_from_rho_fsum(rho_s, s, ds_w, L, N):
    """T_from_rho with every entry's sum over s correctly rounded (math.fsum)."""
    V = TM.window_hat(L, N, s)
    wts = rho_s * ds_w
    n = V.shape[0]
    M = np.zeros((n, n), dtype=complex)
    for i in range(n):
        vi = np.conj(V[i]) * wts
        for j in range(i, n):
            p = vi * V[j]
            val = complex(math.fsum(p.real), math.fsum(p.imag)) / TWO_PI
            M[i, j] = val
            M[j, i] = np.conj(val)
    return M


def delta_T_knobs(nvec, S, Kmax=None, Ns=(8, 16, 32), cells=CELLS, *, w_per_panel=12, s_width=1.0,
                  s_per_panel=8, terms=25, far_terms=8, far_mmax=4, mderiv=14, drop=(),
                  perturb=None, perturb_seed=12345, rho_route="qr", assembly="matmul"):
    """{(c, N): Delta_T as the snapshot stores it (real part of the Hermitian part)}, diag.

    perturb: None, or a dict {"what": rel} with what in {"Z", "B", "J", "A",
    "zeta_w"}; a relative uniform perturbation of that many units, fixed seed.
    "zeta_w" perturbs the w-samples zeta_n(w) before the Mellin sums (the mode
    data), the others the Mellin samples and the two tail rows.
    drop: indices of modes removed from the family (a code defect plant).
    rho_route: "qr" (two_adic/'s), "svd" (a second stable route), "inv"
    (two_adic/'s pre-2026-09-24 route, rho_inv of the formed Gram matrix).
    """
    if Kmax is None:
        Kmax = TP.kmax_for(nvec)
    perturb = dict(perturb or {})
    s, sw = TM.s_grid(float(S), width=s_width, per_panel=s_per_panel)
    hkey = (nvec, float(S), Kmax, w_per_panel, s_width, s_per_panel, terms, far_terms, far_mmax, mderiv,
            perturb.get("zeta_w"), perturb_seed if "zeta_w" in perturb else None)
    if hkey not in _HATS_CACHE:
        pm = prolate_modes(nvec, mderiv)
        if "zeta_w" in perturb:
            import copy
            base, prng, rel = pm, np.random.default_rng(perturb_seed + 1), perturb["zeta_w"]
            pm = copy.copy(base)
            pm.zeta = lambda w: _perturb(base.zeta(w), rel, prng)
        Zh, Bh = hats_knobs(pm, s, Kmax, w_per_panel=w_per_panel, terms=terms, far_terms=far_terms,
                            far_mmax=far_mmax)
        jz0, jb0 = TP.jumps(pm, 1.0)
        _HATS_CACHE.clear()  # keep one family in memory
        _HATS_CACHE[hkey] = (Zh, Bh, jz0, jb0, pm.derivs[:, 0] * pm.norm)
    Z, B, jz, jb, A = _HATS_CACHE[hkey]
    keep = [i for i in range(nvec) if i not in set(drop)]
    if drop:  # a mode removed from the family: every per-mode quantity loses that row
        Z, B, jz, jb, A = Z[keep], B[keep], jz[keep], jb[keep], A[keep]
    rng = np.random.default_rng(perturb_seed)
    if "Z" in perturb:
        Z = _perturb(Z, perturb["Z"], rng)
    if "B" in perturb:
        B = _perturb(B, perturb["B"], rng)
    if "J" in perturb:
        jz, jb = _perturb(jz, perturb["J"], rng), _perturb(jb, perturb["J"], rng)
    if "A" in perturb:
        A = _perturb(A, perturb["A"], rng)
    dil_b = 1.0 / (1.0 - 1.0 / 2.0)
    Fz = TP.gram_factor_s(Z, sw, jz, float(S), A, 1.0)
    Fb = TP.gram_factor_s(B, sw, jb, float(S), A, dil_b)
    if rho_route == "qr":
        rz, rb = TM.rho(Z, factor=Fz), TM.rho(B, factor=Fb)
    elif rho_route == "svd":
        rz, rb = rho_svd(Z, Fz), rho_svd(B, Fb)
    elif rho_route == "inv":
        rz = TM.rho_inv(Z, np.conj(Fz.T) @ Fz)
        rb = TM.rho_inv(B, np.conj(Fb.T) @ Fb)
    else:
        raise ValueError(rho_route)
    tfr = TM.T_from_rho if assembly == "matmul" else T_from_rho_fsum
    out = {}
    for c in cells:
        L = math.log(float(c))
        for N in Ns:
            d = tfr(rz, s, sw, L, N) - tfr(rb, s, sw, L, N)
            out[(c, N)] = ((d + d.conj().T) / 2).real
    sz = np.linalg.svd(Fz, compute_uv=False)
    sb = np.linalg.svd(Fb, compute_uv=False)
    diag = {"Kmax": int(Kmax), "n_s": int(s.size), "cond_Fz": float(sz[0] / sz[-1]),
            "cond_Fb": float(sb[0] / sb[-1]), "nvec_family": len(keep)}
    return out, diag


# ------------------------------------------------------------- stored data


def load_json(path):
    with open(path) as fh:
        return json.load(fh)


def unit_key(c, N, dps, nv, S):
    """checker/'s run_checker_ts.unit_key."""
    return f"{c}|{N}|{dps}|{nv}|{S}"


def T_inf(c, N, dps=40):
    """kernel/'s T_inf as the snapshot rows were composed with (KernelProvider)."""
    import ta_ts
    return ta_ts.KernelProvider().T_inf_matrix(c, N, dps)


def stored_TS(snap, c, N, nv, S, dps=40):
    return np.array(snap["T_S"][unit_key(c, N, dps, nv, S)], dtype=float)


def s_exact(snap, nv, S, N):
    """The S the stored build actually used (non-integer for 280, 319, 364 modes)."""
    return snap["units"][f"{nv}|{S}|{N}"]["S_exact"]


# ------------------------------------------------------------ exact numbers


def to_q(x):
    """A float64 as the exact rational it is (python-flint fmpq)."""
    from flint import fmpq
    return fmpq(*float(x).as_integer_ratio())


def dec_to_q(s):
    """A decimal string as the exact rational it denotes."""
    from flint import fmpq
    f = Fraction(str(s))
    return fmpq(f.numerator, f.denominator)


def arb_upper_q(ball):
    """The upper end of an arb ball as an exact fmpq (None if not finite)."""
    from flint import fmpq, fmpz
    if not ball.is_finite():
        return None
    u = ball.upper()
    m, e = u.man_exp()
    m, e = int(m), int(e)
    return fmpq(fmpz(m) * fmpz(2) ** e) if e >= 0 else fmpq(m, 2 ** (-e))


def frob_upper_q(Da, Db):
    """An exact upper bound, as fmpq, of ||Da - Db||_F >= ||Da - Db||_2.

    Every entry difference is formed exactly over the rationals; the square
    root of the exact sum of squares is bounded above by a rational (the
    integer square root of a scaled numerator, plus one).
    """
    from flint import fmpq, fmpz
    tot = fmpq(0)
    for a, b in zip(np.ravel(Da), np.ravel(Db)):
        d = to_q(a) - to_q(b)
        tot += d * d
    # sqrt(p/q) <= (isqrt(p q 4^k) + 1) / (q 2^k)
    p, q = int(tot.p), int(tot.q)
    k = 64
    r = math.isqrt(p * q * 4 ** k) + 1
    return fmpq(fmpz(r), fmpz(q) * fmpz(2) ** k)


def rayleigh_lower_q(Da, Db):
    """An exact lower bound, as fmpq, of ||Da - Db||_2: |v^T D v| / v^T v over the
    rationals, with v the float64 eigenvector of the eigenvalue largest in modulus."""
    from flint import fmpq
    D = np.asarray(Da, dtype=float) - np.asarray(Db, dtype=float)
    w, U = np.linalg.eigh((D + D.T) / 2)
    v = [to_q(x) for x in U[:, int(np.argmax(np.abs(w)))]]
    A, B = np.ravel(Da), np.ravel(Db)
    n = len(v)
    num = fmpq(0)
    for i in range(n):
        if v[i] == 0:
            continue
        row = fmpq(0)
        for j in range(n):
            row += (to_q(A[i * n + j]) - to_q(B[i * n + j])) * v[j]
        num += v[i] * row
    den = sum((x * x for x in v), fmpq(0))
    return abs(num) / den


def spec(D):
    """The spectral norm of a real symmetric matrix (float64, one route)."""
    D = np.asarray(D, dtype=float)
    return float(np.abs(np.linalg.eigvalsh((D + D.T) / 2)).max())


# ------------------------------------------------------------- bound access


def load_module(path, name):
    spec_ = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec_)
    d = os.path.dirname(path)
    if d not in sys.path:
        sys.path.insert(0, d)
    spec_.loader.exec_module(mod)
    return mod


@contextlib.contextmanager
def arb_prec(bits):
    from flint import ctx
    old = ctx.prec
    ctx.prec = bits
    try:
        yield
    finally:
        ctx.prec = old
