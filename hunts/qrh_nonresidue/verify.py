"""Reproduce every number in RESULTS.md and write verification.json.

Run from the repository root:

    PYTHONPATH=. .venv/bin/python hunts/qrh_nonresidue/verify.py [--table-limit N]

Sections: constants (Arb, cross-checked with mpmath), Theorem 1 closed-form
margins, small moduli by exact subgroup generation, per-modulus bounds,
weakened-abscissa ablation, exhaustive tables (least nonresidue, least and
least prime primitive root, least strong witness), literature record values,
Theorem 3 closed-form margin, and a planted lesion.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp
import numpy as np
from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from hunts.qrh_nonresidue import explicit as E  # noqa: E402
from hunts.qrh_nonresidue import tables as T  # noqa: E402

HERE = Path(__file__).resolve().parent
OEIS = HERE / "oeis"

THETA = F(7, 8)
C_MAIN = F(1, 4)
L0 = F(5, 2)  # Theorem 1 and 3 closed form proved for log q >= L0
C_ASYM = F(1, 8)
KAPPA = F(7, 10)
L1 = F(6)  # Theorem 1(b): n(chi) <= (0.7 log q)^8 for log q >= L1


def lo(b: arb) -> float:
    return float(b.lower())


def ball(b: arb) -> str:
    return b.str(12, radius=True)


def section_constants(out: dict) -> E.Constants:
    C = E.constants(THETA, C_MAIN)
    with mp.workdps(40):
        c = mp.mpf(1) / 4
        s0 = mp.mpf(7) / 4 + c
        lz = mp.zeta(s0, derivative=1) / mp.zeta(s0)
        ref = {
            "A_chi": -lz - mp.log(mp.pi) / 2 + mp.digamma((s0 + 1) / 2) / 2,
            "A_zeta": 1 / s0 + 1 / (s0 - 1) - mp.log(mp.pi) / 2 + mp.digamma(s0 / 2) / 2 + lz,
            "Fz": -mp.zeta(-c, derivative=1) / mp.zeta(-c),
        }
        z0, z1, z2 = (mp.zeta(-c, derivative=k) for k in range(3))
        ref["Fz1"] = -(z2 / z0 - (z1 / z0) ** 2)
        # functional-equation route for zeta'/zeta(-c), shares no code with Arb
        lz1 = mp.zeta(1 + c, derivative=1) / mp.zeta(1 + c)
        fe = -lz1 + mp.log(mp.pi) - mp.digamma(-c / 2) / 2 - mp.digamma((1 + c) / 2) / 2
        ref["Fz_functional_equation"] = -fe
    agree = {}
    for k in ("A_chi", "A_zeta", "Fz", "Fz1"):
        mid = float(getattr(C, k).mid())
        agree[k] = abs(mid - float(ref[k])) < 1e-12
    agree["Fz_functional_equation"] = abs(float(C.Fz.mid()) - float(ref["Fz_functional_equation"])) < 1e-12
    out["constants"] = {
        "theta": str(THETA), "c": str(C_MAIN),
        **{k: ball(getattr(C, k)) for k in ("W1", "sigma0", "A_chi", "A_zeta", "K_inf", "L_star",
                                             "R1", "R2", "Fz", "Fz1", "w_max")},
        "mpmath_agrees": agree,
    }
    assert all(agree.values()), agree
    return C


def section_theorem1(out: dict, C: E.Constants) -> None:
    Lb = E._q(L0)
    m0 = E.margin_closed(C, Lb)
    # K(x) = K_inf needs log x = 8 log L0 >= L_star
    kfix = (8 * Lb.log()) >= C.L_star
    grid = {}
    worst = None
    for L in [2.5, 2.6, 2.8, 3, 3.5, 4, 5, 6, 8, 10, 15, 20, 30, 50, 100, 300, 1000, 10000]:
        m = E.margin_closed(C, arb(repr(L)))
        grid[str(L)] = round(lo(m), 6)
        worst = lo(m) if worst is None else min(worst, lo(m))
    # Theorem 1(b): x = (0.7 L)^8 with c = 1/8 for log q >= L1
    Cb = E.constants(THETA, C_ASYM)
    mb = E.margin_closed(Cb, E._q(L1), E._q(KAPPA))
    kfixb = (8 * (E._q(KAPPA) * E._q(L1)).log()) >= Cb.L_star
    gridb = {str(L): round(lo(E.margin_closed(Cb, arb(L), E._q(KAPPA))), 6)
             for L in [6, 7, 8, 10, 20, 50, 100, 1000, 10 ** 5]}
    c1 = (1 + E._q(C_MAIN)) ** 2 / (2 * (E._q(THETA) + E._q(C_MAIN)))
    c1b = (1 + E._q(C_ASYM)) ** 2 / (2 * (E._q(THETA) + E._q(C_ASYM)))
    # Theorem 1(d): Oct 5 Thm 1.1 alone (theta = 11/12), x = L^12, L >= 2
    Cd = E.constants(F(11, 12), C_MAIN)
    md = E.margin_closed(Cd, arb(2))
    kfixd = (12 * arb(2).log()) >= Cd.L_star
    out["theorem1_part_d_eleven_twelfths"] = {
        "L0": "2", "normalised_margin": ball(md), "margin_positive": lo(md) > 0,
        "K_constant_at_L0": bool(kfixd), "A_chi_plus_A_zeta": ball(Cd.A_chi + Cd.A_zeta),
        "grid": {str(L): round(lo(E.margin_closed(Cd, arb(L))), 6) for L in (2, 3, 5, 10, 100)}}
    assert lo(md) > 0 and kfixd and lo(Cd.A_chi + Cd.A_zeta) > 0
    q4, q4C = E.quartic_kernel_c1(THETA, F(0))
    q4b, q4bC = E.quartic_kernel_c1(THETA, F(1, 50))
    out["theorem1_part_c_quartic"] = {"c1_limit_96sqrt3_over_343": ball(q4), "C_limit": ball(q4C),
                                      "c1_at_c_1_50": ball(q4b), "C_at_c_1_50": ball(q4bC)}
    out["theorem1"] = {
        "L0": str(L0),
        "normalised_margin_at_L0": ball(m0),
        "margin_positive": lo(m0) > 0,
        "K_constant_at_L0": bool(kfix),
        "control_grid_lower_endpoints": grid,
        "control_grid_min": worst,
        "asymptotic_c1_at_c_1_4": ball(c1),
        "asymptotic_C_at_c_1_4": ball(c1 ** 8),
        "limit_c1": "4/7",
        "limit_C": ball(E._q(F(4, 7)) ** 8),
        "part_b": {"c": str(C_ASYM), "kappa": str(KAPPA), "L1": str(L1),
                   "normalised_margin_at_L1": ball(mb), "margin_positive": lo(mb) > 0,
                   "K_constant_at_L1": bool(kfixb), "control_grid": gridb,
                   "c1_at_c_1_8": ball(c1b), "kappa_pow_8": ball(E._q(KAPPA) ** 8)},
    }
    assert lo(m0) > 0 and kfix and lo(mb) > 0 and kfixb


def section_small_moduli(out: dict, qmax: int) -> None:
    primes = [int(p) for p in np.nonzero(T.prime_sieve(5000))[0]]
    t = time.time()
    rows = []
    worst_ratio, worst_q = 0.0, None
    proof_part = {}
    for q in range(3, qmax + 1):
        N = T.generation_bound(q, primes)
        r = N / T.log8(q)
        if q <= 12:
            proof_part[q] = {"N": N, "log_q_pow_8": round(T.log8(q), 4), "ok": N <= T.log8(q)}
        if r > worst_ratio:
            worst_ratio, worst_q = r, q
        rows.append(N)
    rows = np.array(rows)
    big = int(np.argmax(rows)) + 3
    # Theorem 1(b) below log q = 6: largest q <= e^6 violating N(q) <= (0.7 log q)^8
    kap = float(KAPPA)
    with mp.workdps(30):
        bad = [q for q in range(3, 404)
               if mp.mpf(int(rows[q - 3])) > (mp.mpf(kap) * mp.log(q)) ** 8]
    q_b = (max(bad) + 1) if bad else 3
    out["small_moduli"] = {
        "qmax": qmax,
        "seconds": round(time.time() - t, 2),
        "proof_part_q_3_to_12": proof_part,
        "max_N_over_log8": round(worst_ratio, 6), "at_q": worst_q,
        "largest_N": int(rows.max()), "largest_N_at_q": big,
        "all_within_log8": bool(worst_ratio <= 1),
        "theorem1b_q_b": q_b,
        "theorem1b_violations_below_q_b": bad,
    }
    assert all(v["ok"] for v in proof_part.values())
    assert worst_ratio <= 1


def least_x_for(C, L, omega, exponent=None):
    def pred(x):
        return lo(E.margin(C, arb(repr(x)), arb(repr(L)), arb(repr(omega)))) > 0
    return E.least_x(pred, lo=2.0, hi=1e300)


def section_per_modulus(out: dict, C: E.Constants) -> None:
    rows = {}
    for k in [2, 3, 5, 10, 20, 50, 100, 1000]:
        L = k * math.log(10)
        x0 = least_x_for(C, L, L / math.log(2))
        rows[f"1e{k}"] = {"x0": f"{x0:.4e}", "x0_over_log8": round(x0 / L ** 8, 6),
                          "x0_pow_1_8_over_logq": round(x0 ** 0.125 / L, 6)}
    out["per_modulus_bound"] = {"c": str(C.c), "rows": rows,
                                "note": "x0 is a point where the margin was verified positive; "
                                        "x0^(1/8)/log q tends to c1 = 0.6944 for c = 1/4"}


def section_ablation(out: dict) -> None:
    res = {}
    for th in [F(7, 8), F(11, 12), F(15, 16)]:
        C = E.constants(th, C_MAIN)
        e = 1 / (1 - th)
        Ls = [10.0, 100.0, 1000.0, 10000.0]
        xs = [least_x_for(C, L, L / math.log(2)) for L in Ls]
        slopes = [math.log(xs[i + 1] / xs[i]) / math.log(10) for i in range(len(Ls) - 1)]
        res[str(th)] = {"predicted_exponent": float(e),
                        "x0": [f"{x:.4e}" for x in xs],
                        "local_slopes": [round(s, 4) for s in slopes]}
        assert abs(slopes[-1] - float(e)) < 0.05 * float(e)
    out["ablation"] = res


def section_tables(out: dict, N: int) -> dict:
    t = time.time()
    isp = T.prime_sieve(N)
    spf = T.spf_sieve(N)
    ps = np.nonzero(isp)[0].astype(np.int64)
    odd = ps[ps > 2]
    nr = T.least_nonresidues(odd, ps[:300])
    Fm = T.distinct_prime_factors(odd - 1, spf)
    g = T.least_primitive_roots(odd, Fm, range(2, 2000))
    gs = T.least_primitive_roots(odd, Fm, [int(x) for x in ps[:400]])
    oddn = np.arange(9, N + 1, 2)
    comp = oddn[~isp[oddn]]
    w = T.least_strong_witness(comp)
    secs = round(time.time() - t, 2)
    logp8 = np.log(odd.astype(float)) ** 8
    logn8 = np.log(comp.astype(float)) ** 8
    # Theorem 3 sieve factor, vectorised: factors are ascending, zero padded
    omega = (Fm > 0).sum(axis=1)
    rec = np.where(Fm > 0, 1.0 / np.where(Fm > 0, Fm, 1), 0.0)
    suffix = np.cumsum(rec[:, ::-1], axis=1)[:, ::-1]
    lam = np.full(len(odd), np.inf)
    for j in range(Fm.shape[1] + 1):
        valid = j <= omega
        Om = 2.0 ** j
        s = omega - j
        delta = 1 - (suffix[:, j] if j < Fm.shape[1] else 0.0)
        val = np.where(s == 0, Om - 1, (2 * Om - 1) + (s - 1) * (3 * Om - 2) / np.where(delta > 0, delta, np.nan))
        ok = valid & ((s == 0) | (delta > 0))
        lam = np.where(ok & (val < lam), val, lam)
    lam = np.maximum(lam, 1.0)
    bound3 = (lam * np.log(odd.astype(float))) ** 8
    ratio1 = logp8 / nr
    ratio3 = bound3 / gs
    ratio2 = logn8 / w
    # lesion: the exponent-1 bound n(p) <= log p is refuted by the same table
    lesion_hits = int((nr > np.log(odd.astype(float))).sum())
    out["tables"] = {
        "limit": N, "seconds": secs,
        "primes": int(len(odd)),
        "least_nonresidue_max": int(nr.max()), "at_p": int(odd[nr.argmax()]),
        "min_margin_log8_over_n": round(float(ratio1.min()), 4), "at": int(odd[ratio1.argmin()]),
        "bach_2log2_holds": bool((nr <= 2 * np.log(odd.astype(float)) ** 2).all()),
        "least_primitive_root_max": int(g.max()), "at_p_g": int(odd[g.argmax()]),
        "least_prime_primitive_root_max": int(gs.max()), "at_p_gs": int(odd[gs.argmax()]),
        "theorem3_min_margin": round(float(ratio3.min()), 4), "at_p3": int(odd[ratio3.argmin()]),
        "theorem3_lambda_max": round(float(lam.max()), 4),
        "odd_composites": int(len(comp)),
        "least_witness_max": int(w.max()), "at_n": int(comp[w.argmax()]),
        "witness_histogram": {int(k): int(v) for k, v in enumerate(np.bincount(w)) if v},
        "theorem2_min_margin": round(float(ratio2.min()), 4), "at_n2": int(comp[ratio2.argmin()]),
        "lesion_log_p_bound_refuted_by": lesion_hits,
    }
    assert ratio1.min() > 1 and ratio2.min() > 1 and ratio3.min() > 1 and lesion_hits > 0
    return {"odd": odd, "nr": nr}


def _bfile(name: str) -> list[tuple[int, int]]:
    rows = []
    for line in (OEIS / name).read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        a, b = line.split()
        rows.append((int(a), int(b)))
    return rows


def section_records(out: dict) -> None:
    small = [int(p) for p in np.nonzero(T.prime_sieve(2000))[0]]
    rec = {}
    # A000229: least prime p whose least quadratic nonresidue is prime(k)
    rows = []
    for k, p in _bfile("b000229.txt"):
        n = T.legendre_nonresidue_int(p)
        assert n == small[k - 1], (k, p, n)
        rows.append({"p": p, "n_p": n, "margin": round(math.log(p) ** 8 / n, 1)})
    rec["A000229"] = {"count": len(rows), "all_verified": True,
                      "min_margin": min(r["margin"] for r in rows), "last": rows[-1]}
    # A002229 / A002230: record least primitive roots
    roots = dict(_bfile("b002229.txt"))
    primes = dict(_bfile("b002230.txt"))
    rows = []
    for k in sorted(primes):
        p, gp = primes[k], roots[k]
        if p == 2:  # g(2) = 1; the bounds concern odd primes
            continue
        assert T.least_primitive_root_int(p) == gp, (p, gp)
        qs = T.factor_small(p - 1)
        lam = float(min(v for j in range(len(qs) + 1)
                        if (v := E.sieve_factor(qs, j)) is not None))
        gstar = T.least_primitive_root_int(p, prime_only=True)
        rows.append({"p": p, "g": gp, "g_star": gstar, "Lambda_p": round(max(lam, 1.0), 4),
                     "margin": f"{(max(lam, 1.0) * math.log(p)) ** 8 / gstar:.3e}"})
    rec["A002229_A002230"] = {"count": len(rows), "all_verified": True, "last": rows[-1],
                              "min_margin": min(float(r["margin"]) for r in rows)}
    # A014233: least odd n failing Miller-Rabin to the first k prime bases
    rows = []
    for k, n in _bfile("b014233.txt"):
        wv = T.least_strong_witness_int(n)
        assert all(T.is_strong_liar(a, n) for a in small[:k])
        rows.append({"k": k, "n": n, "least_witness": wv,
                     "margin": f"{math.log(n) ** 8 / wv:.3e}"})
    rec["A014233"] = {"count": len(rows), "all_verified": True, "rows": rows}
    out["records"] = rec


def section_theorem3(out: dict, C: E.Constants) -> None:
    small = {}
    for p in (3, 5, 7, 11):
        qs = T.factor_small(p - 1)
        lam = max(min(v for j in range(len(qs) + 1)
                      if (v := E.sieve_factor(qs, j)) is not None), F(1))
        gs = T.least_primitive_root_int(p, True)
        small[p] = {"g_star": gs, "Lambda_p": str(lam),
                    "bound": round((float(lam) * math.log(p)) ** 8, 3),
                    "ok": gs <= (float(lam) * math.log(p)) ** 8}
    L = E._q(L0)
    m = E.primroot_margin(C, (8 * L.log()).exp(), L, arb(1), True) / (8 * L.log()).exp()
    grid = {}
    for Lv in [2.5, 3, 5, 10, 100]:
        for lam in [1, 3, 15, 1000]:
            x = (8 * (arb(lam) * arb(Lv)).log()).exp()
            grid[f"L={Lv},Lambda={lam}"] = round(lo(E.primroot_margin(C, x, arb(Lv), arb(lam), True) / x), 6)
    out["theorem3"] = {"L0": str(L0), "normalised_margin_at_L0_lambda_1": ball(m),
                       "margin_positive": lo(m) > 0, "control_grid": grid,
                       "small_p": small}
    assert lo(m) > 0 and min(grid.values()) > 0
    assert all(v["ok"] for v in small.values())


def section_lesion(out: dict, C: E.Constants) -> None:
    """Planted fault: drop every log q contribution (the zero sum).

    The resulting q-independent 'bound' must be refuted by the record table,
    otherwise the controls could not have detected a missing zero term.
    """
    x_bad = least_x_for(C, 0.0, 0.0)
    small = [int(p) for p in np.nonzero(T.prime_sieve(2000))[0]]
    refuting = [(p, small[k - 1]) for k, p in _bfile("b000229.txt") if small[k - 1] > x_bad]
    thg = F(8749570195, 10 ** 10)
    Cg = E.constants(thg, C_MAIN)
    xs = [least_x_for(Cg, L, L / math.log(2)) for L in (1e3, 1e4)]
    out["lesion"] = {"zero_sum_dropped_bound": round(x_bad, 3),
                     "refuted_by_A000229_count": len(refuting),
                     "first_refutation": refuting[0] if refuting else None,
                     "guo_abscissa_theta": str(thg),
                     "guo_predicted_exponent": round(1 / (1 - float(thg)), 6),
                     "guo_measured_slope": round(math.log(xs[1] / xs[0]) / math.log(10), 6)}
    assert refuting


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--table-limit", type=int, default=10 ** 7)
    ap.add_argument("--qmax", type=int, default=10 ** 4)
    ap.add_argument("--out", default=str(HERE / "verification.json"))
    args = ap.parse_args()
    ctx.prec = E.PREC
    out: dict = {"base_commit": "ef4e0564", "backend": "python-flint " + __import__("flint").__version__}
    t0 = time.time()
    C = section_constants(out)
    section_theorem1(out, C)
    section_small_moduli(out, args.qmax)
    section_per_modulus(out, C)
    section_ablation(out)
    section_theorem3(out, C)
    section_records(out)
    section_lesion(out, C)
    section_tables(out, args.table_limit)
    out["total_seconds"] = round(time.time() - t0, 1)
    import resource
    ru = resource.getrusage(resource.RUSAGE_SELF)
    out["cpu_seconds"] = round(ru.ru_utime + ru.ru_stime, 1)
    out["peak_rss_mb"] = round(ru.ru_maxrss / 1024, 1)
    Path(args.out).write_text(json.dumps(out, indent=1, default=str) + "\n")
    print(json.dumps(out, indent=1, default=str))


if __name__ == "__main__":
    main()
