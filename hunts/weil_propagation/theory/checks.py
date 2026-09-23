"""Cheap numerical checks for the theory worker's RESULTS.md.

Everything here reuses the replicated Galerkin assembly of
``hunts/rogue_frontier/weil_trunc/galerkin.py`` (CCM arXiv:2511.22755
eq. (3.10)-(3.16), validated there against quadrature and published values).
No new assembly code is written; the checks only read matrices and
eigenvectors.  Total runtime is a few minutes at most.

Checks (numbering follows RESULTS.md section 3):

  A. DH arithmetic across the lattice step c = 30 -> 31.
  B. An atom at n = c has exactly zero weight in the window log c.
  C. The slope kink of lambda_min(L) when a prime-power atom enters,
     against the predicted jump -Lambda(q) q^{-1/2} (2/L) (sum_n u_n)^2.
  D. Perron-Frobenius structure of the pole-free zeta form, and the
     sign structure of the DH ground state, as a function of y on [0, L].
  E. The fixed-window (dilation) formula against zeta/weil.py.
  F. Ground-state transport across the lattice step 30 -> 31.
  G. Relative boundary mass phi_N(0)^2 / lambda_N of the zeta ground state.
  H. The same ratio for DH approaching its crossing.

Run from the repo root:  .venv/bin/python hunts/weil_propagation/theory/checks.py
Writes checks.json beside this file.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "hunts" / "rogue_frontier" / "weil_trunc"))
import galerkin as G  # noqa: E402


def f(x, d=6):
    return mp.nstr(x, d)


# ---------------------------------------------------------------------------
# A. DH arithmetic across 30 -> 31
# ---------------------------------------------------------------------------


def check_A():
    with mp.workdps(40):
        lam = dict(G.dh_lambda_coeffs(40))
        full = {n: lam.get(n, mp.mpf(0)) for n in range(2, 41)}
        mult5 = {n: full[n] for n in range(5, 41, 5)}
        neg = [n for n in range(2, 32) if full[n] < 0]
        out = {
            "Lambda_f(29)": f(full[29], 12),
            "Lambda_f(30)": f(full[30], 12),
            "Lambda_f(31)": f(full[31], 12),
            "log(31)": f(mp.log(31), 12),
            "Lambda_f(31)-log31": f(full[31] - mp.log(31), 3),
            "max|Lambda_f(5m)|, 5m<=40": f(max(abs(v) for v in mult5.values()), 3),
            "n<=31 with Lambda_f(n)<0": neg,
            "Lambda_f(3)": f(full[3], 12),
            "composite n<=31 with Lambda_f(n)!=0 and n not a prime power": [
                n for n in range(2, 32)
                if full[n] != 0 and len({p for p in range(2, n + 1)
                                         if n % p == 0 and all(p % r for r in range(2, p))}) > 1
            ],
        }
    return out


# ---------------------------------------------------------------------------
# B. The atom at n = c sits at y = L and carries zero weight
# ---------------------------------------------------------------------------


def check_B(N=12):
    with mp.workdps(50):
        T = G.Truncation(31, N, kind="dh")
        # rebuild the prime sequences without the n = 31 atom
        L = T.L
        lam31 = dict(G.dh_lambda_coeffs(31))[31]
        w = lam31 / mp.sqrt(31)
        y = mp.log(31)
        dP = max(abs(w * mp.sin(2 * mp.pi * k * y / L)) for k in range(N + 1))
        dR = max(abs(w * 2 * (1 - y / L) * mp.cos(2 * mp.pi * k * y / L)) for k in range(N + 1))
    return {"N": N, "max |P_k contribution of n=31|": f(dP, 3),
            "max |R_k contribution of n=31|": f(dR, 3)}


# ---------------------------------------------------------------------------
# C. The kink at a prime-power entry
# ---------------------------------------------------------------------------


def _ground(c, N, kind="zeta", pole=True):
    T = G.Truncation(c, N, kind=kind)
    E = T.even_matrix()
    if not pole and kind == "zeta":
        # subtract the pole block W02 in even coordinates
        Np = N + 1
        W = mp.matrix(Np)
        W[0, 0] = T.w02(0, 0)
        for k in range(1, Np):
            v = mp.sqrt(2) * T.w02(0, k)
            W[0, k] = v
            W[k, 0] = v
        for j in range(1, Np):
            for k in range(j, Np):
                v = T.w02(j, k) + T.w02(j, -k)
                W[j, k] = v
                W[k, j] = v
        E = E - W
    ev, vec = G.eigsy_sorted(E)
    return T, ev, vec


def check_C(q, Lam, N=16, h=mp.mpf("1e-6")):
    """Left/right slopes of lambda_min in L = log c at L0 = log q."""
    with mp.workdps(45):
        L0 = mp.log(q)
        lam = {}
        for s in (-2, -1, 0, 1, 2):
            c = mp.e ** (L0 + s * h)
            if s == 0:
                c = mp.mpf(q)
            _, ev, vec = _ground(c, N)
            lam[s] = ev[0]
            if s == 0:
                v = vec[0]
        # second-order one-sided differences
        left = (3 * lam[0] - 4 * lam[-1] + lam[-2]) / (2 * h)
        right = (-3 * lam[0] + 4 * lam[1] - lam[2]) / (2 * h)
        S = v[0] + mp.sqrt(2) * mp.fsum(v[1:])
        pred = -Lam / mp.sqrt(q) * (2 / L0) * S * S
        return {"q": q, "N": N, "lambda_min(L0)": f(lam[0], 8),
                "slope_left": f(left, 10), "slope_right": f(right, 10),
                "jump_measured": f(right - left, 10), "jump_predicted": f(pred, 10),
                "rel_dev": f(abs((right - left) - pred) / abs(pred), 3),
                "phi_N(0)^2 = (sum u_n)^2 / L": f(S * S / L0, 8)}


# ---------------------------------------------------------------------------
# D. Perron-Frobenius structure
# ---------------------------------------------------------------------------


def _profile(v, L, npts=400):
    """phi(y) on (0, L) from even coordinates; returns min, max, sign changes."""
    N = len(v) - 1
    vals = []
    for i in range(1, npts):
        y = L * i / npts
        s = v[0] / mp.sqrt(L)
        for k in range(1, N + 1):
            s += v[k] * mp.sqrt(2 / L) * mp.cos(2 * mp.pi * k * y / L)
        vals.append(s)
    if sum(vals) < 0:
        vals = [-x for x in vals]
    changes = sum(1 for a, b in zip(vals, vals[1:]) if a * b < 0)
    return min(vals), max(vals), changes


def check_D(cells):
    out = []
    for kind, c, N, pole, dps in cells:
        with mp.workdps(dps):
            T, ev, vec = _ground(mp.mpf(c), N, kind=kind, pole=pole)
            mn, mx, ch = _profile(vec[0], T.L)
            nneg = sum(1 for e in ev if e < 0)
            out.append({"kind": kind, "c": c, "N": N, "pole": pole,
                        "lambda_1": f(ev[0], 6), "lambda_2": f(ev[1], 6),
                        "n_negative_even": nneg,
                        "ground_min_over_max": f(mn / mx, 4),
                        "ground_sign_changes_on_grid": ch})
    return out


# ---------------------------------------------------------------------------
# E. The dilation identity against zeta/weil.py (constants check)
# ---------------------------------------------------------------------------


def E_dilated_box(a):
    """Q(f_a) for f = 1_{[-1,1]}/sqrt(2), f_a(x) = a^{-1/2} f(x/a), from the
    fixed-window formula of RESULTS.md s2.2 (pole, archimedean, primes)."""
    a = mp.mpf(a)
    g = lambda y: (2 - abs(y)) / 2
    pole = 16 * mp.sinh(a / 2) ** 2 / a
    arch = -(mp.euler + mp.log(mp.pi) + mp.log(1 - mp.e ** (-4 * a)))
    arch += mp.quad(lambda y: 2 * a * (mp.e ** (-2 * a * y) - mp.e ** (-a * y / 2) * g(y))
                    / (1 - mp.e ** (-2 * a * y)), [0, 1, 2])
    primes = mp.mpf(0)
    for q, p in G.prime_powers_upto(float(mp.e ** (2 * a))):
        if mp.log(q) < 2 * a:
            primes -= 2 * mp.log(p) / mp.sqrt(q) * g(mp.log(q) / a)
    return pole + arch + primes


def check_E(avals=("0.3", "0.8", "1.2")):
    sys.path.insert(0, str(ROOT))
    from zeta.weil import fejer_pair, weil_functional
    out = []
    with mp.workdps(30):
        for a in avals:
            mine = E_dilated_box(a)
            h, g = fejer_pair(a)
            lab = 2 * mp.mpf(a) * weil_functional(h, g, dps=30)
            out.append({"a": a, "E(a; box)": f(mine, 15), "2a*W_lab(fejer)": f(lab, 15),
                        "abs_dev": f(abs(mine - lab), 3)})
    return out


# ---------------------------------------------------------------------------
# F. Ground-state transport across the lattice step 30 -> 31
# ---------------------------------------------------------------------------


def check_F():
    """Even coordinates are coordinates of the ground state dilated to [0,1]
    (e_k(y) = sqrt(2/L) cos(2 pi k y / L) -> sqrt2 cos(2 pi k t)), so the
    dilation transport of a ground state is the identity on coordinates."""
    out = []
    for kind, N, dps in (("dh", 60, 60), ("zeta", 32, 110)):
        with mp.workdps(dps):
            T30 = G.Truncation(30, N, kind=kind)
            T31 = G.Truncation(31, N, kind=kind)
            E30, E31 = T30.even_matrix(), T31.even_matrix()
            ev30, V30 = G.eigsy_sorted(E30)
            ev31, V31 = G.eigsy_sorted(E31)
            v30 = mp.matrix(V30[0])
            v31 = mp.matrix(V31[0])
            ov = abs(mp.fsum(v30[i] * v31[i] for i in range(N + 1)))
            sgn = 1 if mp.fsum(v30[i] * v31[i] for i in range(N + 1)) > 0 else -1
            d = v31 - sgn * v30
            rq = (v30.T * E31 * v30)[0]
            out.append({"kind": kind, "N": N,
                        "lambda_1(30)": f(ev30[0], 6), "lambda_1(31)": f(ev31[0], 6),
                        "1-|<v30,v31>|": f(1 - ov, 4),
                        "||v31 - v30||": f(mp.norm(d), 4),
                        "Q_31(v30) (dilated old ground state as trial)": f(rq, 6)})
    return out


# ---------------------------------------------------------------------------
# G. Relative boundary mass phi_N(0)^2 / lambda_N of the zeta ground state
# ---------------------------------------------------------------------------


def check_G(cells=((3, 16), (3, 32), (6, 16), (6, 32), (10, 24), (13, 24), (13, 32), (20, 32))):
    out = []
    for c, N in cells:
        with mp.workdps(40 + 3 * c):
            T, ev, vec = _ground(mp.mpf(c), N)
            v = vec[0]
            S = v[0] + mp.sqrt(2) * mp.fsum(v[1:])
            out.append({"c": c, "N": N, "lambda_1": f(ev[0], 5),
                        "phi_N(0)^2/lambda_1": f(S * S / T.L / ev[0], 5)})
    return out


# ---------------------------------------------------------------------------
# H. Boundary mass ratio for DH approaching the crossing, and for zeta
# ---------------------------------------------------------------------------


def check_H(cells=(("dh", 13, 32, 50), ("dh", 20, 60, 60), ("dh", 25, 60, 60),
                   ("dh", 29, 60, 60), ("dh", 30, 60, 60), ("dh", 31, 60, 60),
                   ("zeta", 25, 32, 110), ("zeta", 29, 32, 110), ("zeta", 31, 32, 110))):
    out = []
    for kind, c, N, dps in cells:
        with mp.workdps(dps):
            T, ev, vec = _ground(mp.mpf(c), N, kind=kind)
            v = vec[0]
            S = v[0] + mp.sqrt(2) * mp.fsum(v[1:])
            out.append({"kind": kind, "c": c, "N": N, "lambda_1": f(ev[0], 5),
                        "phi_N(0)^2": f(S * S / T.L, 5),
                        "phi_N(0)^2/lambda_1": f(S * S / T.L / ev[0], 5)})
    return out


if __name__ == "__main__":
    res = {}
    res["A_dh_arithmetic"] = check_A()
    print("A", res["A_dh_arithmetic"])
    res["B_edge_atom"] = check_B()
    print("B", res["B_edge_atom"])
    res["C_kink"] = []
    for q, p in ((3, 3), (4, 2), (5, 5), (7, 7)):
        with mp.workdps(45):
            Lam = mp.log(p)
        r = check_C(q, Lam)
        print("C", r)
        res["C_kink"].append(r)
    cells = [
        ("zeta", 13, 24, False, 60),
        ("zeta", 13, 24, True, 60),
        ("zeta", 31, 32, False, 110),
        ("zeta", 31, 32, True, 110),
        ("dh", 13, 24, True, 40),
        ("dh", 30, 60, True, 60),
        ("dh", 31, 60, True, 60),
    ]
    res["D_perron_frobenius"] = check_D(cells)
    for r in res["D_perron_frobenius"]:
        print("D", r)
    res["E_dilation_vs_weil_py"] = check_E()
    for r in res["E_dilation_vs_weil_py"]:
        print("E", r)
    res["F_transport_30_31"] = check_F()
    for r in res["F_transport_30_31"]:
        print("F", r)
    res["G_boundary_mass"] = check_G()
    for r in res["G_boundary_mass"]:
        print("G", r)
    res["H_boundary_mass_dh"] = check_H()
    for r in res["H_boundary_mass_dh"]:
        print("H", r)
    (HERE / "checks.json").write_text(json.dumps(res, indent=1))
