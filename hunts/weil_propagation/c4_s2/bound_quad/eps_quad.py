"""bound_quad/: every error of Delta_T_stored except the mode truncation (DERIVATION.md s2).

    eps_quad(c, N, nvec, S, Kmax) -> flint.arb

returns an upper bound on ||Delta_T_nvec,exact - Delta_T_stored||_2 on the
(2N + 1)-dimensional window space. For every stored build it is +inf: source
E2 (the projection taken in the inner product truncated to [-S, S]) has no
bound (DERIVATION s2.3), so no finite number is an upper bound that this
folder can support. The pieces that do close are returned by

    eps_quad_parts(c, N, nvec, S, Kmax) -> {source: arb or None}

with None for a source that does not close on that build and the reason in
eps_quad_reasons. Every number is an arb ball; "upper" strings round the
upper end of the ball up. Assumptions are the numbered A1 .. A9 of
DERIVATION s2.0; each piece lists the ones it uses.

Inputs read (read-only): checker/checker_ts_snapshot.json, `units[..]["diag"]`
(cond_Fz, cond_Fb, gram_z_offI as recorded by two_adic/'s delta_T_cells).
"""

from __future__ import annotations

import json
import math
import os
from decimal import Decimal
from fractions import Fraction

import numpy as np
from flint import arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
C4S2 = os.path.normpath(os.path.join(HERE, ".."))
SNAPSHOT = os.path.join(C4S2, "checker", "checker_ts_snapshot.json")
OUT = os.path.join(HERE, "eps_quad.json")

ctx.prec = 128
U = arb(2) ** -53  # unit roundoff of IEEE binary64, round to nearest
CELLS = ("2.2", "2.5", "2.9")
# the eleven stored builds (BRIEF.md): (N, nvec, S as passed to delta_T_cells)
BUILDS = [
    (8, 80, 1200.0),
    (16, 80, 1200.0), (16, 80, 1600.0), (16, 120, 1200.0), (16, 120, 1600.0), (16, 160, 1600.0),
    (32, 200, 2400.0), (32, 240, 2400.0), (32, 280, 2266.1020257693895),
    (32, 319, 2633.163333456407), (32, 364, 3060.0807085398565),
]
C_QR = 32  # A6: LAPACK Householder QR / SVD backward-error constant (assumption, not proven here)
C_CX = 4  # A7: complex arithmetic, gamma_k -> gamma_{C_CX k}

ASSUMPTIONS = {
    "E1": ["A1", "A2", "A3"],
    "E2": ["A1", "A2", "A6"],
    "E6": ["A1", "A4", "A6", "A7"],
    "E7": ["A1", "A5", "A7", "A8", "A9"],
}


def kmax_for(nvec: int) -> int:
    """two_adic/ta_prolate.kmax_for, restated so this module imports nothing from two_adic/."""
    return max(10, int(math.ceil(math.log2(max(nvec - 1, 1) ** 2 / (2 * math.pi)))))


def gamma(k) -> arb:
    """gamma_k = k u / (1 - k u), as an arb ball (Higham s3.1); requires k u < 1."""
    ku = arb(k) * U
    if not ku < 1:
        raise ValueError("k u >= 1")
    return ku / (1 - ku)


def s_nodes(S: float) -> int:
    """Number of s-nodes of ta_mellin.s_grid(S, width=1, per_panel=8), as delta_T_cells builds it."""
    edges = np.arange(-S, S + 1e-12, 1.0)
    return 8 * (edges.size - 1)


def s_covered(S: float) -> float:
    """Right end of s_grid(S, 1, 8): the grid covers [-S, -S + floor(2S + 1e-12)]."""
    edges = np.arange(-S, S + 1e-12, 1.0)
    return float(edges[-1])


def _diag(nvec: int, S: float, N: int):
    """two_adic/'s recorded diagnostics for a stored build, or None."""
    with open(SNAPSHOT) as fh:
        units = json.load(fh)["units"]
    key = f"{nvec}|{int(S)}|{16 if N == 8 else N}" if f"{nvec}|{int(S)}|{N}" not in units else f"{nvec}|{int(S)}|{N}"
    u = units.get(key)
    return None if u is None else u["diag"]


# ------------------------------------------------------------------ E1


def kappa(c, N: int, S0) -> arb:
    """kappa(S0) >= sup_{|s| >= S0} sum_{|n| <= N} |V^_n(s)|^2 (DERIVATION s2.2, Prop 2).

    |V^_n(s)| <= 2 / (sqrt(L) |s - 2 pi n / L|) and |s - 2 pi n / L| >= S0 - 2 pi |n| / L,
    valid when S0 > 2 pi N / L.
    """
    L = arb(c).log() if isinstance(c, str) else arb(str(c)).log()
    S0 = arb(S0)
    edge = 2 * arb.pi() * N / L
    if not S0 > edge:
        raise ValueError("S0 must exceed 2 pi N / L")
    tot = arb(0)
    for n in range(-N, N + 1):
        tot += 4 / (L * (S0 - 2 * arb.pi() * abs(n) / L) ** 2)
    return tot


def e1(c, N: int, nvec: int, S: float) -> arb:
    """E1 <= kappa(S0) * nvec with S0 = min(S, right end of the grid) (Prop 2)."""
    S0 = min(float(S), s_covered(S))
    return kappa(c, N, S0) * nvec


# ------------------------------------------------------------------ E2


def cond_enclosure(cond_rec: float, m: int, n: int):
    """(lower, upper) for the true cond(F) from a recorded float64 value (A6, Weyl; Prop 3, Prop 5).

    A backward-stable SVD returns the singular values of F + dF with ||dF||_2 <= g ||F||_2,
    g = gamma_{C_QR m n} sqrt(n), so |s~_i - s_i| <= g s_max. Upper is None when
    1 / cond_rec <= g (the recorded smallest singular value is inside the error).
    """
    g = gamma(C_QR * m * n) * arb(n).sqrt()
    inv = 1 / arb(cond_rec)
    lower = (1 - g) / (inv + g)
    upper = (1 + g) / (inv - g) if inv > g else None
    return lower, upper


def _gram_measured(nvec: int, S: float):
    path = os.path.join(HERE, "bound_quad_gram.json")
    if not os.path.exists(path):
        return None
    with open(path) as fh:
        rows = json.load(fh)["rows"]
    for r in rows:
        if r["nvec"] == nvec and abs(r["S"] - S) < 1e-9:
            return r
    return None


def e2_obstruction(nvec: int, S: float, N: int, d: float = 0.1):
    """Lower bound on ||X||, X = G_S^{-1/2} G_exact G_S^{-1/2} - I, the quantity a perturbation
    bound through the Gram needs below 1 (Prop 3). ||X|| >= (1 - d) / lambda_min(G_S) - 1 (A2).

    lambda_min(G_S): measured (bound_quad_gram.json, float64 singular values of F) where
    run_bound_quad.py ran it; otherwise lambda_min <= lambda_max / cond(G_S) with
    lambda_max <= 1 + nvec offI (offI the recorded max |G_S - I| entry) and cond(G_S) = cond(F_z)^2
    at the lower end of cond_enclosure (A6).
    """
    meas = _gram_measured(nvec, S)
    if meas is not None:
        return (1 - arb(d)) / arb(meas["Gz_eig_min"]) - 1
    dg = _diag(nvec, S, N)
    if dg is None:
        return None
    lo, _ = cond_enclosure(dg["cond_Fz"], s_nodes(S) + 2, nvec)
    lam_max = 1 + nvec * arb(dg["gram_z_offI"]) * (1 + arb(1e-6))
    return (1 - arb(d)) * lo**2 / lam_max - 1


# ------------------------------------------------------------------ E6


def rho_rel_error(m: int, n: int, cond_rec) -> arb | None:
    """Relative error bound on rho~(s) from the Householder QR and the triangular solve (Prop 5), or None."""
    _, condF = cond_enclosure(cond_rec, m, n)
    if condF is None:
        return None
    g_qr = gamma(C_QR * m * n)
    eta = g_qr * arb(n).sqrt() * condF
    if not (2 * eta + eta**2) < 1:
        return None
    g_tri = gamma(C_CX * n)
    eta2 = g_tri * arb(n).sqrt() * condF * (1 + eta) / (1 - eta)
    if not eta2 < 1:
        return None
    g_nrm = gamma(C_CX * 2 * n)
    hi = (1 + g_nrm) / ((1 - 2 * eta - eta**2) * (1 - eta2) ** 2) - 1
    lo = 1 - (1 - g_nrm) / ((1 + eta) ** 2 * (1 + eta2) ** 2)
    return hi if hi > lo else lo


def e6(c, N: int, nvec: int, S: float) -> arb | None:
    """E6 <= (delta_z + delta_b) L nvec (Prop 5); None where the QR bound does not close."""
    dg = _diag(nvec, S, N)
    if dg is None:
        return None
    m = s_nodes(S) + 2
    dz = rho_rel_error(m, nvec, dg["cond_Fz"])
    db = rho_rel_error(m, nvec, dg["cond_Fb"])
    if dz is None or db is None:
        return None
    L = arb(str(c)).log()
    return (dz + db) * L * nvec


# ------------------------------------------------------------------ E7


def min_k_distance(c, N: int, S: float) -> float:
    """min over the stored s-nodes and |n| <= N of |2 pi n / L - s| (float64, as the code forms k)."""
    xg, _ = np.polynomial.legendre.leggauss(8)
    edges = np.arange(-S, S + 1e-12, 1.0)
    s = (edges[:-1, None] + 0.5 + 0.5 * xg[None, :]).ravel()
    L = math.log(float(c))
    k = 2.0 * math.pi * np.arange(-N, N + 1)[:, None] / L - s[None, :]
    return float(np.abs(k).min())


def _ts_max_abs(c, N: int, nvec: int, S: float) -> float | None:
    """max |entry| of the stored T_S row (checker/ snapshot, dps 40), or None if not stored."""
    with open(SNAPSHOT) as fh:
        ts = json.load(fh)["T_S"]
    row = ts.get(f"{c}|{N}|40|{nvec}|{int(S)}")
    return None if row is None else float(np.abs(np.array(row)).max())


def e7(c, N: int, nvec: int, S: float) -> arb | None:
    """E7: float64 rounding of the assembly, given the leverage bound A5 (Prop 6)."""
    L = arb(str(c)).log()
    ns = s_nodes(S)
    lev = arb(nvec + 2)  # A5
    # V^ evaluation (A8): absolute error per entry <= (5 u / kmin + L^2 u (2 pi N / L + S) / 2) / sqrt(L)
    kmin = arb(min_k_distance(c, N, S)) * (1 - arb(1e-12))
    if not kmin > 1e-12:
        raise ValueError("an s-node falls within 1e-12 of 2 pi n / L")
    dv = (5 * U / kmin + L**2 * U * (2 * arb.pi() * N / L + arb(S)) / 2) / L.sqrt()
    vmax = L.sqrt()
    term = vmax**2 + 2 * vmax * dv + dv**2  # bound on |conj(V~_m) V~_n| per unit leverage
    # entrywise: products, the GEMM sum over ns nodes, the scalings (ns + 8 operations, A7), and the
    # perturbation of the V^ entries; for each of M_inf and M_S
    per_entry = lev * (gamma(C_CX * (ns + 8)) * term + 2 * vmax * dv + dv**2)
    spectral = 2 * (2 * N + 1) * per_entry
    # symmetrization (X + X^*)/2 of Delta_T: relative u on entries of size <= 2 L lev
    spectral += (2 * N + 1) * 2 * U * 2 * L * lev
    # T_S = T_inf + Delta_T in float64: u |T_S entry|
    tmax = _ts_max_abs(c, N, nvec, S)
    if tmax is None:
        return None  # not a stored build: the T_S entry size is not known here
    spectral += (2 * N + 1) * U * arb(tmax) * (1 + 4 * U)
    return spectral


# ------------------------------------------------------------------ assembly


def eps_quad_parts(c, N: int, nvec: int, S: float, Kmax: int | None = None) -> dict:
    """{E1, E2, E3, E4, E5, E6, E7}: arb upper bounds, or None where the source does not close."""
    return {"E1": e1(c, N, nvec, S), "E2": None, "E3": None, "E4": None, "E5": None,
            "E6": e6(c, N, nvec, S), "E7": e7(c, N, nvec, S)}


def eps_quad_reasons(c, N: int, nvec: int, S: float) -> dict:
    ob = e2_obstruction(nvec, S, N)
    ob_s = "n/a" if ob is None else upper_str(ob, lower=True)
    r = {
        "E2": "no bound: the stored projection is taken in the inner product truncated to [-S, S]; a "
              "perturbation bound through the Gram needs ||G_S^{-1} G_exact - I|| < 1, and the recorded "
              f"diagnostics give it >= {ob_s} on this build (DERIVATION s2.3, Prop 3); only a recomputation "
              "with the exact Gram closes it (s2.8), not run",
        "E3": "not bounded in the box: Gauss panels in w need Bernstein-ellipse bounds evaluated per panel "
              "and a propagation through the discretized projection (s2.4, s2.7)",
        "E4": "not bounded in the box: the 1/w series is truncated at 14 derivatives and 25 terms with no "
              "remainder bound in the code (s2.4)",
        "E5": "not bounded in the box: needs eigenvector residuals of kernel/'s Slepian solve (s2.4)",
    }
    parts = eps_quad_parts(c, N, nvec, S)
    if parts["E7"] is None:
        r["E7"] = "not a stored build: no stored T_S row to size the last rounding step"
    if parts["E6"] is None:
        dg = _diag(nvec, S, N)
        r["E6"] = ("no bound: 2 eta + eta^2 >= 1 at cond(F_z) = %.3g, cond(F_b) = %.3g (s2.5, Prop 5)"
                   % (dg["cond_Fz"], dg["cond_Fb"]) if dg else "no recorded cond(F) for this build")
    return r


def eps_quad(c, N: int, nvec: int, S: float, Kmax: int | None = None) -> arb:
    """Upper bound on ||Delta_T_nvec,exact - Delta_T_stored||_2 from every source but mode truncation.

    +inf on every build: E2 does not close (DERIVATION s2.3). The closing pieces are in eps_quad_parts.
    """
    parts = eps_quad_parts(c, N, nvec, S, Kmax)
    if any(v is None for v in parts.values()):
        return arb.pos_inf()
    tot = arb(0)
    for v in parts.values():
        tot += v
    return tot


def upper_str(x: arb, digits: int = 4, lower: bool = False) -> str:
    """Decimal string >= the upper end of x (or <= the lower end if lower=True), `digits` significant."""
    end = x.lower() if lower else x.upper()
    f = float(end)
    for _ in range(2):
        f = math.nextafter(f, -math.inf if lower else math.inf)
    s = f"{f:.{digits - 1}e}"
    q, target = Fraction(Decimal(s)), Fraction(f)
    step = Fraction(Decimal(f"1e{int(s.split('e')[1]) - (digits - 1)}"))
    while (q > target) if lower else (q < target):
        q = q - step if lower else q + step
        s = f"{float(q):.{digits - 1}e}"
        q = Fraction(Decimal(s))
    return s


def build_json() -> list[dict]:
    rows = []
    for N, nvec, S in BUILDS:
        Kmax = kmax_for(nvec)
        for c in CELLS:
            parts = eps_quad_parts(c, N, nvec, S, Kmax)
            reasons = eps_quad_reasons(c, N, nvec, S)
            ob = e2_obstruction(nvec, S, N)
            rows.append({
                "c": c, "N": N, "nvec": nvec, "S": S, "Kmax": Kmax,
                "eps_upper": None,
                "grade": "no bound (outcome 4 for this folder): E2 does not close; the pieces below are "
                         "ordinary arguments with arb arithmetic, unreviewed, under the listed assumptions",
                "why": reasons["E2"],
                "assumptions": sorted({a for k in ("E1", "E6", "E7") for a in ASSUMPTIONS[k]}),
                "parts_upper": {k: (None if v is None else upper_str(v)) for k, v in parts.items()},
                "parts_reasons": {k: reasons[k] for k in reasons if parts.get(k) is None},
                "parts_assumptions": ASSUMPTIONS,
                "e2_obstruction_lower": None if ob is None else upper_str(ob, lower=True),
                "s_nodes": s_nodes(S),
            })
    return rows


def main() -> None:
    rows = build_json()
    with open(OUT, "w") as fh:
        json.dump(rows, fh, indent=1)
    for r in rows:
        if r["c"] == "2.9":
            print(r["N"], r["nvec"], int(r["S"]), r["parts_upper"], "E2 obstruction >=", r["e2_obstruction_lower"])


if __name__ == "__main__":
    main()
