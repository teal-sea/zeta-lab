"""Hunt #148: the cross-check run.

Every exact number in this hunt's documents is recomputed by the second implementation,
``ffprobe_pari.py`` (PARI/GP through cypari2, which imports nothing from ``ffprobe.py``).
Where an element-by-element comparison means something, the PARI value is compared with
the ``ffprobe.py`` value as an exact element of Q(zeta_N); where the documents quote a count
of checks, PARI recomputes the count on its own.  ``ffprobe`` is imported here only to be
compared against.  Each item is checkpointed to ``results_second.partial.json``; the run
ends by writing ``results_second.json``.

    .venv/bin/python hunts/ff_probe/crosscheck.py              # every item
    .venv/bin/python hunts/ff_probe/crosscheck.py --item probe # one item
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
import sys
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import ffprobe as F  # noqa: E402  (the primary, read only to compare)
import ffprobe_pari as PC  # noqa: E402  (the second implementation)

pari = PC.pari


def co(f) -> list:
    """Coefficient list (constant first) of an ffprobe polynomial."""
    c = [int(x) for x in f.coeffs()]
    return c if c else [0]


def same(pv, cyc) -> bool:
    return PC.equal(pv, PC.to_pari(cyc))


def from_record(rec):
    """The exact value stored by ``ffprobe.cyc_record``, as a PARI polmod."""
    s = rec["poly"].replace("x", "z")
    return pari(f"Mod({s}, polcyclo({rec['N']}, z))")


def norm2(pv, N) -> Fraction:
    """|a|^2 as a rational number (asserted rational)."""
    v = pv * PC.conj(pv, N)
    lifted = pari.lift(v)
    assert int(pari.poldegree(lifted)) <= 0, "not rational"
    x = pari.polcoef(lifted, 0)
    return Fraction(int(pari.numerator(x)), int(pari.denominator(x)))


def gcd_trivial(a, b, q) -> bool:
    return int(pari.poldegree(pari.gcd(PC.poly(a, q), PC.poly(b, q)))) == 0


def results(name: str) -> dict:
    return json.loads((HERE / f"results_{name}.json").read_text())


# ---------------------------------------------------------------------------
# Step 1 (SOURCES.md)
# ---------------------------------------------------------------------------


def item_symbols(full: bool) -> dict:
    """Both PARI symbol routes and ffprobe's table, for every monic modulus in step 1's range."""
    out = {}
    for (q, n, md) in ((7, 3, 3), (7, 6, 3), (13, 4, 2)):
        S = F.Setup(q, n)
        md = md if full else 2
        tot = agree = 0
        for d in range(1, md + 1):
            for c in PC.monic_polys(q, d):
                tot += 1
                a = PC.symbol_vector(c, d, q, n, "res")
                b = PC.symbol_vector(c, d, q, n, "frob")
                mine = F.symbol_table_res(S, S.P(c))
                agree += int((a == b).all() and (a == mine).all())
        out[f"q{q}_n{n}"] = {"max_deg": md, "moduli": tot, "all_routes_agree": agree}
    return out


def item_davenport_hasse(full: bool) -> dict:
    """PARI's own count: enumerated Gauss sums against the Davenport-Hasse closed form."""
    out = {}
    for (q, n, md) in ((7, 3, 3), (7, 6, 3), (13, 4, 2)):
        md = md if full else min(md, 2)
        N = math.lcm(n, q, 4)
        cnt = {"2014": 0, "2007_own_character": 0, "2007_with_2014_character": 0}
        tot = nsf_tot = nsf_zero = 0
        for d in range(1, md + 1):
            for c in PC.monic_polys(q, d):
                cp = PC.poly(c, q)
                sf = PC.mobius(c, q) != 0
                for rd in range(0, 3):
                    for r in PC.monic_polys(q, rd):
                        if not gcd_trivial(r, c, q):
                            continue
                        if not sf:
                            if rd <= 1:
                                nsf_tot += 1
                                nsf_zero += int(PC.is_zero(PC.gauss(r, c, q, n, 1, N)))
                            continue
                        rp = PC.poly(r, q)
                        Hp = PC._FUN["ffgausshall"](rp, cp, q, n, N)
                        Hm = PC._FUN["ffgausshall"](-rp, cp, q, n, N)
                        for j in range(1, n):
                            g = PC._FUN["ffh2pm"](Hp[j - 1], N)
                            gm = PC._FUN["ffh2pm"](Hm[j - 1], N)
                            d14 = PC.gauss_dh(r, c, q, n, j, N)
                            d07 = PC.gauss_dh(r, c, q, n, j, N, v2007=True)
                            tot += 1
                            cnt["2014"] += int(not PC.equal(d14, g))
                            cnt["2007_own_character"] += int(not PC.equal(d07, gm))
                            cnt["2007_with_2014_character"] += int(not PC.equal(d07, g))
        out[f"q{q}_n{n}"] = {"max_deg": md, "checked": tot, "mismatches": cnt,
                             "nonsquarefree_checked": nsf_tot, "nonsquarefree_zero": nsf_zero}
    return out


def item_structural(full: bool) -> dict:
    """PARI's enumerated Gauss sums against ffprobe's structural route (CRT, prime powers, DH)."""
    q, n, N = 7, 3, 84
    S = F.Setup(q, n)
    md = 3 if full else 2
    tot = agree = 0
    for d in range(1, md + 1):
        for c in PC.monic_polys(q, d):
            cp = PC.poly(c, q)
            for rd in range(0, md + 1):
                for r in PC.monic_polys(q, rd):
                    H = PC._FUN["ffgausshall"](PC.poly(r, q), cp, q, n, N)
                    for j in (1, 2):
                        tot += 1
                        agree += int(same(PC._FUN["ffh2pm"](H[j - 1], N), F.gauss_struct(S, S.P(r), j, S.P(c))))
    return {"max_deg_c": md, "max_deg_r": md, "checked": tot, "agree": agree}


def item_pari_internal(full: bool) -> dict:
    """The identities PARI uses beyond the definitions, checked inside PARI against enumeration:
    its CRT/Davenport-Hasse route for g(r, eps^j, c), and Gamma(c) = gamma_3(c) for squarefree
    c (used for the probe weights at degree 5)."""
    q, n, N = 7, 6, 84
    tot = ok = 0
    for d in range(1, (3 if full else 2) + 1):
        for c in PC.monic_polys(q, d):
            cp = PC.poly(c, q)
            for r in ([1], [3], [0, 1], [2, 1], [1, 0, 1]):
                H = PC._FUN["ffgausshall"](PC.poly(r, q), cp, q, n, N)
                for j in range(1, n):
                    tot += 1
                    ok += int(PC.equal(PC.gauss_struct(r, c, q, n, j, N), PC._FUN["ffh2pm"](H[j - 1], N)))
    P = PC.PariProbe()
    gtot = gok = 0
    for d in range(1, (4 if full else 3) + 1):
        for c in PC.monic_polys(q, d):
            if PC.mobius(c, q) == 0:
                continue
            gtot += 1
            gok += int(PC.equal(P.Gamma(c), P.gamma_j(c, 3)))
    return {"structural_eq_enumeration": [ok, tot], "Gamma_eq_gamma3_squarefree": [gok, gtot]}


def item_C_routes(full: bool) -> dict:
    q, n, N = 7, 3, 84
    S = F.Setup(q, n)
    T, L = [0, 1], (lambda a: [(-a) % q, 1])
    rs = [[1], T, PC._pmul(T, L(1), q), PC._pmul(T, T, q), [1, 0, 1], PC._pmul(PC._pmul(T, L(1), q), L(3), q),
          [1, 1, 0, 1]]
    tot = agree = 0
    for r in rs:
        for j in (1, 2):
            for i in range(0, (3 if full else 2) + 1):
                tot += 1
                agree += int(same(PC.C(r, q, n, j, i, N), F.C_fast(S, S.P(r), j, i)))
    return {"checked": tot, "agree": agree}


class RhoBook:
    """PARI's rho_0 values (C by enumeration up to degree 2, by CRT/DH above), cached, and
    the count of them that equal ffprobe's."""

    def __init__(self, q, n):
        self.q, self.n, self.N = q, n, math.lcm(n, q, 4)
        self.S = F.Setup(q, n)
        self.cache: dict = {}
        self.compared = self.agree = 0

    def __call__(self, r, j, i):
        r = [x % self.q for x in r]
        while len(r) > 1 and r[-1] == 0:
            r.pop()
        key = (tuple(r), j, i % self.n)
        if key not in self.cache:
            v = PC.rho0(r, self.q, self.n, j, i % self.n, self.N, 2)
            self.cache[key] = v
            self.compared += 1
            self.agree += int(same(v, F.rho0(self.S, self.S.P(r), j, i % self.n)[0]))
        return self.cache[key]


def item_rho0_relations(full: bool) -> dict:
    """theta base values, Psi's degree, the Hecke relations, periodicity, the affine rule and the
    cubic theta against gamma_2, all from PARI's rho_0 (step 1, items e to j)."""
    q, n, N = 7, 3, 84
    rho = RhoBook(q, n)
    T, L = [0, 1], (lambda a: [(-a) % q, 1])
    mul = lambda *fs: _mul(q, *fs)
    one = [1]
    out = {}
    out["theta_base"] = {f"j{j}": {"rho0_1_0_is_1": PC.equal(rho(one, j, 0), 1),
                                   "rho0_1_1_is_q_tau": PC.equal(rho(one, j, 1), PC.tau(q, n, j, N) * q),
                                   "rho0_1_2_is_0": PC.is_zero(rho(one, j, 2))} for j in (1, 2)}
    ok = tot = 0
    for r in [one, T, L(1), mul(T, L(1)), [1, 0, 1], mul(T, T)]:
        for j in (1, 2):
            for i in range(3):
                R = (1 + len(r) - 1 - i) // n
                D = PC.psi_coeffs(r, q, n, j, i, N, max(R, -1) + 1, 2)
                tot += 1
                ok += int(all(PC.is_zero(x) for x in D[max(R, -1) + 1:]))
    out["psi_polynomial"] = {"checked": tot, "vanish_above_R": ok}
    rlist = [one, T, L(1), mul(T, L(1)), [1, 0, 1], mul(T, L(1), L(3)), [1, 1, 0, 1], mul(T, [1, 0, 1]),
             mul(T, T, T), mul([0, 1, 0, 1], L(2))]
    hinf = {"printed_2014": [0, 0], "printed_2007": [0, 0], "corrected": [0, 0]}
    for r in rlist:
        for j in (1, 2):
            rr = {i: rho(r, j, i) for i in range(n)}
            for form in hinf:
                rec = PC.hecke_infinity_records(q, n, j, len(r) - 1, rr, N, form)
                hinf[form][0] += sum(rec)
                hinf[form][1] += len(rec)
    out["hecke_infinity"] = {k: {"hold": v[0], "checked": v[1]} for k, v in hinf.items()}
    both = {}
    for (qq, nn) in ((7, 3), (7, 6)):
        rb = rho if nn == 3 else RhoBook(qq, nn)
        NN = math.lcm(nn, qq, 4)
        Lx = lambda a: [(-a) % qq, 1]
        tot2 = {"2007_character": [0, 0], "2014_character": [0, 0]}
        for r in [[1], Lx(1), _mul(qq, Lx(1), Lx(2)), [1, 0, 1], _mul(qq, Lx(1), Lx(2), Lx(3))]:
            for jj in ((1, 2) if nn == 3 else (1,)):
                rr = {i: rb(r, jj, i) for i in range(nn)}
                rm = {i: rb([(-x) % qq for x in r], jj, i) for i in range(nn)}
                a = PC.hecke_infinity_records(qq, nn, jj, len(r) - 1, rm, NN, "corrected", 0)
                b = PC.hecke_infinity_records(qq, nn, jj, len(r) - 1, rr, NN, "corrected", 1)
                tot2["2007_character"][0] += sum(a)
                tot2["2007_character"][1] += len(a)
                tot2["2014_character"][0] += sum(b)
                tot2["2014_character"][1] += len(b)
        both[f"q{qq}_n{nn}"] = {k: {"hold": v[0], "checked": v[1]} for k, v in tot2.items()}
        if nn == 6:
            out["rho0_agree_q7_n6"] = {"compared": rb.compared, "agree": rb.agree}
    out["hecke_infinity_both"] = both
    fh_ok = fh_tot = van_ok = van_tot = 0
    for ro, P in [(one, T), (one, L(1)), (L(1), T), (one, [1, 0, 1]), (L(2), [1, 0, 1]), (mul(T, L(1)), L(3))]:
        for jj in range(0, 2):
            for j in (1, 2):
                for i in range(3):
                    lhs = rho(mul(ro, *([P] * jj)) if jj else ro, j, i)
                    rhs = PC.finite_hecke_rhs(q, n, j, ro, P, jj, i, lambda a, b, j=j: rho(a, j, b), N)
                    fh_tot += 1
                    fh_ok += int(PC.equal(lhs, rhs))
        for j in (1, 2):
            for i in range(3):
                van_tot += 1
                van_ok += int(PC.is_zero(rho(mul(ro, P, P), j, i)))
    out["finite_hecke"] = {"hold": fh_ok, "checked": fh_tot, "vanish_at_r_o_P^(n-1)": [van_ok, van_tot]}
    per_ok = per_tot = 0
    for r, b in [(T, L(1)), (L(2), T), (one, T), ([1, 0, 1], L(4))]:
        for j in (1, 2):
            for i in range(3):
                per_tot += 1
                per_ok += int(PC.equal(rho(mul(r, b, b, b), j, i), rho(r, j, i)))
    out["periodicity"] = {"hold": per_ok, "checked": per_tot}
    lg = PC.logtab(q)
    aff_ok = aff_tot = 0
    for r in [T, mul(T, L(1)), [1, 0, 1], mul(T, L(1), L(3))]:
        k = len(r) - 1
        for a in (2, 3):
            for b in (0, 1, 5):
                rt = PC.affine_image(r, a, b, q)
                for j in (1, 2):
                    for i in range(3):
                        aff_tot += 1
                        pred = rho(r, j, i) * PC.zeta((N // n) * j * i * (k + 1 - i) * lg[a], N)
                        aff_ok += int(PC.equal(rho(rt, j, i), pred))
    out["affine_invariance"] = {"hold": aff_ok, "checked": aff_tot}
    # the cubic theta against gamma_2 (sextic symbol squared), every squarefree c of degree <= 3
    sq = PC.sqrtq(q, N)
    fam = {}
    for b in (0, 1, 2):
        rec = {}
        for d in range(0, (3 if full else 2) + 1):
            vals = {}
            for c in PC.monic_polys(q, d):
                if PC.mobius(c, q) == 0:
                    continue
                g2 = PC.gauss_struct([1], c, q, 6, 2, N) / sq ** d
                ratio = rho(c, 2, (b - d) % 3) / g2
                vals[str(pari.lift(ratio))] = ratio
            first = next(iter(vals.values()))
            rec[str(d)] = {"distinct_ratios": len(vals), "ratio_abs": abs(PC.to_complex(first, N)),
                           "ratio_lift": str(pari.lift(first))}
        fam[f"b{b}"] = rec
    out["cubic_theta_vs_gamma2"] = fam
    out["rho0_agree_q7_n3"] = {"compared": rho.compared, "agree": rho.agree}
    return out


def _mul(q, *fs):
    out = [1]
    for f in fs:
        out = PC._pmul(out, f, q)
    return out


# ---------------------------------------------------------------------------
# Step 2 (LOCAL_IDENTITY.md)
# ---------------------------------------------------------------------------


def item_phase_identities(full: bool) -> dict:
    q, n, N = 7, 6, 84
    S = F.Setup(q, n)
    Pr = F.Probe(S)
    P = PC.PariProbe()
    sg = P.sgn
    mon = lambda d: list(PC.monic_polys(q, d))
    rec_bad = rec_tot = 0
    for da in (1, 2):
        for db in (1, 2):
            for a in mon(da):
                for b in mon(db):
                    if not gcd_trivial(a, b, q):
                        continue
                    rec_tot += 1
                    rec_bad += int((P.sym(a, b) - (sg * da * db + P.sym(b, a))) % n != 0)
    gam_bad = gam_tot = 0
    for d in range(0, 4):
        for c in mon(d):
            gam_tot += 1
            gam_bad += int(not same(P.Gamma(c), Pr.Gamma(S.P(c), "closed")))
    sig = {"gamma2_cubed": 0, "gamma1_gamma2": 0, "G_squarefree": 0}
    sig_tot = 0
    for d in range(1, 4):
        for c in mon(d):
            m = PC.mobius(c, q)
            if m == 0:
                continue
            sig_tot += 1
            H = PC._FUN["ffgausshall"](PC.poly([1], q), PC.poly(c, q), q, n, N)
            g1, g2, g3 = (PC._FUN["ffh2pm"](H[j - 1], N) / P.sq ** d for j in (1, 2, 3))
            alpha = P.lam ** d
            G = P.zn(-P.sym([4], c)) * P.Gamma(c)
            sig["gamma2_cubed"] += int(not PC.equal(g2 ** 3, alpha * m))
            sig["gamma1_gamma2"] += int(not PC.equal(g1 * g2, alpha * G * m))
            sig["G_squarefree"] += int(not PC.equal(G, P.zn(-P.sym([4], c)) * g3))
    Gf = lambda c: P.zn(-P.sym([4], c)) * P.Gamma(c)
    ref_bad = ref_tot = 0
    for dv in range(0, 3):
        for dw in range(0, 3):
            for v in mon(dv):
                for w in mon(dw):
                    ref_tot += 1
                    ref_bad += int(not PC.equal(Gf(PC._pmul(v, w, q)), Gf(v) * Gf(w) * P.R(dv, dw)))
    pp_bad = pp_tot = 0
    for Pp in PC.primes_list(q, 2):
        pp_tot += 1
        g3 = P.gamma_j(Pp, 3)
        ok = (PC.equal(Gf(PC._pmul(Pp, Pp, q)), P.zn(P.sym([4], Pp))) and PC.equal(Gf(_mul(q, Pp, Pp, Pp)), g3)
              and PC.equal(P.R(len(Pp) - 1, len(Pp) - 1), g3 ** 2)
              and PC.equal(P.R(len(Pp) - 1, len(Pp) - 1), P.zn(P.sym([6], Pp))))
        pp_bad += int(not ok)
    return {"reciprocity": {"checked": rec_tot, "mismatches": rec_bad},
            "Gamma_closed_form": {"checked": gam_tot, "mismatches": gam_bad},
            "signal": {"checked": sig_tot, "mismatches": sig},
            "G_refinement_all_pairs": {"checked": ref_tot, "mismatches": ref_bad},
            "prime_phases": {"checked": pp_tot, "mismatches": pp_bad},
            "lambda_alpha_equal": same(P.lam, Pr.lam_alpha)}


def item_F_routes(full: bool) -> dict:
    q, n, N = 7, 6, 84
    S = F.Setup(q, n)
    Pr = F.Probe(S)
    tot = agree = crt_agree = 0
    for ds in range(0, 3):
        for dA in range(0, 3):
            if ds + dA > (3 if full else 2):
                continue
            for s in F.monic_coprime_T(S, ds):
                for A in F.monic_coprime_T(S, dA):
                    for H in S.residues(2):
                        if H.is_zero():
                            continue
                        brute = PC.F_poisson(co(s), co(A), co(H), q, n, N)
                        tot += 1
                        agree += int(same(brute, Pr.F_local(s, A, H)))
                        crt_agree += int(PC.equal(PC.F_crt(co(s), co(A), co(H), q, n, N), brute))
    return {"checked": tot, "pari_definition_eq_ffprobe_factorization": agree, "pari_crt_eq_pari_definition": crt_agree}


def item_C_p(full: bool) -> dict:
    q, n, N = 7, 6, 84
    S = F.Setup(q, n)
    Pr = F.Probe(S)
    tot = agree = 0
    for key in [(1, 1), (3, 1), (1, 0, 1), (3, 1, 1)]:
        Pp = S.P(list(key))
        for t in range(0, 8 if full else 4):
            for k in range(0, 3 if Pp.degree() == 1 else 2):
                for jp in range(0, 9):
                    tot += 1
                    agree += int(same(PC.C_p(list(key), t, k, jp, q, n, N), Pr.C_p_closed(Pp, t, k, jp)))
    # the prime-power reduction inside PARI against enumeration, every residue y modulo p^t
    red_tot = red_ok = 0
    for key, tmax in (((1, 1), 3), ((1, 0, 1), 1)):
        for t in range(1, tmax + 1):
            Pt = PC.poly(list(key), q) ** t
            dt = int(pari.poldegree(Pt))
            for code in range(q ** dt):
                y = PC._FUN["ffpoly"](code, dt, q)
                red_tot += 1
                a = PC._FUN["ffgpp"](y, 1, PC.poly(list(key), q), t, q, n, N, 1)
                b = PC._FUN["ffgauss"](y, Pt, q, n, 1, N)
                red_ok += int(PC.equal(a, b))
    return {"checked": tot, "agree": agree, "reduction_eq_enumeration": [red_ok, red_tot]}


def item_K(full: bool) -> dict:
    """PARI's K(c, n, s, a; u) by its definition against ffprobe's product of local summands."""
    q, n, N = 7, 6, 84
    S = F.Setup(q, n)
    Pr = F.Probe(S)
    P = PC.PariProbe()
    rows = [S.P([1]), S.P([3]), S.P([1, 1]), S.P([2, 1]) ** 2, S.P([1, 0, 1]), S.P([1, 1]) * S.P([2, 1])]
    if full:
        rows += [S.P([5, 1]) ** 3, S.P([1, 1]) ** 5 * S.P([2])]
        specs = [(rows, 3, 1, 1), (rows[:3], 2, 2, 1)]
    else:
        specs = [(rows, 2, 1, 1)]
    out = []
    for (rws, maxA, maxs, maxa) in specs:
        tot = nz = agree = 0
        for u in rws:
            for D in range(0, maxA + 1):
                for (c, n_) in F.theta_indices(S, D):
                    for ds in range(0, maxs + 1):
                        for s in F.monic_coprime_T(S, ds):
                            for da in range(0, maxa + 1):
                                for a in F.monic_coprime_T(S, da):
                                    kp = P.K_def(co(c), co(n_), co(s), co(a), co(u))
                                    tot += 1
                                    nz += int(not PC.is_zero(kp))
                                    agree += int(same(kp, F.K_product(Pr, c, n_, s, a, u)))
        out.append({"max_deg_A": maxA, "max_deg_s": maxs, "max_deg_a": maxa, "checked": tot, "nonzero": nz,
                    "agree": agree})
    return {"specs": out}


def item_lemma(full: bool) -> dict:
    """Every coefficient of P_p by its definition (PARI) against the closed form (ffprobe)."""
    q, n, N = 7, 6, 84
    S = F.Setup(q, n)
    Pr = F.Probe(S)
    P = PC.PariProbe()
    cases = coeffs = agree = 0
    keys = [(1, 1), (4, 1), (1, 0, 1)] if full else [(1, 1)]
    for key in keys:
        Pp = S.P(list(key))
        Xm, Wm, Vm = (13, 3, 2) if Pp.degree() == 1 else (13, 2, 2)
        if not full:
            Xm, Wm, Vm = 7, 1, 1
        B = F.Bound(Xm, Wm, Vm)
        for j in range(0, 6):
            for w in [S.P([1]), S.P([2]), S.P([3, 1]) if key != (4, 1) else S.P([5, 1]), S.P([1, 1, 1])]:
                if (w % Pp).is_zero():
                    continue
                u = Pp ** j * w
                cases += 1
                closed = Pr.P_local_closed(Pp, u, B)
                for ex in range(0, Xm + 1):
                    for k in range(0, Wm + 1):
                        for m in range(0, Vm + 1):
                            coeffs += 1
                            if ex % 3 == 2:
                                agree += int(closed.coeff((ex, k, m)).is_zero())
                                continue
                            e0, l = (0, ex // 3) if ex % 3 == 0 else (1, ex // 3)
                            v = PC.local_coefficient(P, list(key), co(u), e0, l, k, m)
                            agree += int(same(v, closed.coeff((ex, k, m))))
    return {"cases": cases, "coefficients": coeffs, "agree": agree}


def item_probe(full: bool) -> dict:
    """The probe's values: PARI's direct sum (or, for (4,0,5), its Poisson side for D_s = 0)
    against the exact values stored by the primary run."""
    r2 = results("step2")
    r2b = results("step2b") if (HERE / "results_step2b.json").is_file() else {}
    P = PC.PariProbe()
    out = {}
    stored = {tuple(rec["triple"]): rec["value"] for rec in r2["probe_representations"]}
    for k, rec in r2b.items():
        if k.startswith("s0_"):
            stored[tuple(rec["triple"])] = rec["value"]
    trips = sorted(stored) if full else [(0, 2, 1), (0, 1, 1), (1, 1, 2)]
    for t in trips:
        t0 = time.time()
        DX, Ds, DA = t
        if t == (4, 0, 5):
            val = PC.probe_poisson_s1(P, DX, DA, gamma_route="gamma3")
            route = "poisson_s1"
        else:
            val = PC.probe_direct(P, DX, Ds, DA, gamma_route="gamma3")
            route = "direct"
        out["_".join(map(str, t))] = {"triple": list(t), "route": route, "equal_to_stored": PC.equal(val, from_record(stored[t])),
                                      "zero": PC.is_zero(val), "abs": abs(PC.to_complex(val, P.N)),
                                      "seconds": round(time.time() - t0, 1)}
    for k, rec in r2b.items():
        if k.startswith("empty_") and full:
            t = tuple(rec["triple"])
            val = PC.probe_direct(P, *t)
            out["_".join(map(str, t))] = {"triple": list(t), "route": "direct", "zero": PC.is_zero(val),
                                          "frequency_box_empty": t[2] - t[0] <= 0}
    # the balanced probes of the ledger, in the paper's normalization
    led = results("ledger")
    bal = []
    for b in led["balanced_probe"] if full else led["balanced_probe"][:1]:
        Pb = PC.PariProbe(xi_j=b["xi_j"])
        D = b["D_X"]
        val = PC.probe_direct(Pb, D, D, 2 * D)
        norm = 7 ** (-2 * D - (1 + D) / 2)
        bal.append({"xi_j": b["xi_j"], "D": D, "abs_I_paper_normalization": abs(PC.to_complex(val, 84)) * norm,
                    "stored": b["abs_I_paper_normalization"]})
    out["balanced"] = bal
    return out


def item_ledger(full: bool) -> dict:
    q, n, N = 7, 6, 84
    out = {}
    T = [0, 1]
    mct = lambda d: [c for c in PC.monic_polys(q, d) if d == 0 or c[0] % q != 0]
    ok = tot = 0
    for s in mct(1):
        for A in mct(2):
            if PC.mobius(A, q) == 0 or not gcd_trivial(A, s, q):
                continue
            for H in ([1], [2, 1], [3, 0, 1]):
                if not gcd_trivial(H, _mul(q, s, A), q) or H[0] % q == 0:
                    continue
                tot += 1
                ok += int(norm2(PC.F_poisson(s, A, H, q, n, N), N) == q * q ** 2)
    out["F_abs2_generic"] = {"checked": tot, "equal_q_times_qA": ok}
    worst, at, nz = 0.0, None, 0
    for ds in range(0, 3 if full else 2):
        for dA in range(0, 3 if full else 2):
            for s in mct(ds):
                for A in mct(dA):
                    for code in range(1, q ** 2):
                        H = [code % q, code // q]
                        f = PC.F_poisson(s, A, H, q, n, N)
                        if PC.is_zero(f):
                            continue
                        nz += 1
                        ratio = abs(PC.to_complex(f, N)) / (q ** ds * q ** (1 + dA))
                        if ratio > worst + 1e-12:
                            worst, at = ratio, (ds, dA, s, A, H)
    out["F_vs_elementary_bound"] = {"max_ratio": worst, "at": at, "nonzero_cases": nz}
    P = PC.PariProbe()
    L = []
    for d in range(0, 4):
        h = P.one * 0
        for a in PC.monic_polys(q, d):
            h = h + P.eta(a)
        L.append(h)
    out["target_L"] = {"degree_one": all(PC.is_zero(c) for c in L[2:]), "abs2_c1": str(norm2(L[1], N))}
    # the principal correction on the circles, from PARI's prime classes (closed form, floats)
    classes = Counter()
    for Pp in PC.primes_list(q, 6 if full else 4):
        classes[(len(Pp) - 1, P.eta_exp(Pp))] += 1
    lam = PC.to_complex(P.lam, N)
    circ = {}
    for sigma in (Fraction(7, 8), Fraction(5, 6), Fraction(3, 4), Fraction(17, 24)):
        rr = q ** (-float(sigma))
        vals = []
        for t in range(360):
            X = rr * cmath.exp(2j * math.pi * t / 360)
            logH = 0j
            for (dP, k), cnt in classes.items():
                Q = q ** dP
                eta_p = cmath.exp(2j * math.pi * k / N)
                x = X ** dP
                V = W = 1.0 / Q
                Dd = eta_p * x
                a_p = (lam.conjugate() ** dP) ** 3 * eta_p ** 3
                R = a_p ** 2 * Q ** 4 * x ** 6 * V
                J = -eta_p * x + W * R
                Pst = ((R * (1 - 1.0 / Q) - eta_p * (Q - 1) * x * W * V) / (1 - V) + J) / (1 - R)
                Pp_ = 1 / (1 - V) + W / (1 - W) + Pst
                logH += cnt * cmath.log(Pp_ * (1 - V) * (1 - W) / (1 - Dd))
            vals.append(cmath.exp(logH))
        circ[str(sigma)] = {"max_abs_H_minus_1": max(abs(v - 1) for v in vals), "min_abs_H": min(abs(v) for v in vals)}
    out["principal_correction"] = circ
    # the five leading terms of H_p - 1 at p = T + 1, u = 1, from the local factor by definition
    maxes = (6, 1, 1)
    loc = {}
    for e0 in (0, 1):
        for l in range(0, 3):
            if e0 + 3 * l > 6:
                continue
            for k in (0, 1):
                for m in (0, 1):
                    v = PC.local_coefficient(P, [1, 1], [1], e0, l, k, m)
                    if not PC.is_zero(v):
                        loc[(e0 + 3 * l, k, m)] = v
    Pser = PC.PSeries(maxes, loc)
    eta_p = P.eta([1, 1])
    rho = P.zn(P.sym([1], [1, 1]))
    fac = PC.PSeries(maxes, {(0, 0, 0): P.one, (0, 0, 1): -P.one})
    fac = fac * PC.PSeries(maxes, {(0, 0, 0): P.one, (0, 1, 0): -rho})
    geo = {(k, 0, 0): (eta_p * PC.conj(rho, N)) ** k for k in range(0, 7)}
    Hs = Pser * fac * PC.PSeries(maxes, geo)
    t = {e: c for e, c in Hs.terms.items() if e != (0, 0, 0)}
    a2 = {str(e): str(norm2(c, N)) for e, c in t.items()}
    low = min(sum(e) for e in t)
    out["leading_terms"] = {"abs2": a2, "lowest": sorted(str(e) for e in t if sum(e) == low)}
    return out


def item_rival(full: bool) -> dict:
    q, n, N = 7, 6, 84
    lg = PC.logtab(q)
    scan = []
    for e in range(1, 6):
        for al in range(0, 7):
            for be in range(1, 7):
                Lc = PC.L_coefficients(q, n, N, e, al, be, 4)
                Lb = PC.L_coefficients(q, n, N, -e, -al, -be, 2)
                eps = Lc[2] / q
                fe = (all(PC.is_zero(x) for x in Lc[3:]) and PC.equal(Lc[1], eps * PC.conj(Lc[1], N))
                      and PC.equal(eps * PC.conj(eps, N), 1))
                d = [Lc[k] + eps * Lb[k] for k in range(3)]
                bet = d[1] / d[0]
                disc = bet * bet - 4 * q
                dv = PC.to_complex(disc, N).real
                roots = pari.polroots(pari.Pol([pari(f"subst(lift({x}), 'z, exp(2*Pi*I/{N}))") for x in (d[2], d[1], d[0])]))
                mods = [abs(complex(r)) for r in roots]
                sig = [-math.log(m) / math.log(q) for m in mods]
                scan.append({"e": e, "alpha": al, "beta": be, "fe": fe, "beta_real": PC.equal(bet, PC.conj(bet, N)),
                             "disc": dv, "disc_zero": PC.is_zero(disc),
                             "off": [abs(m * math.sqrt(q) - 1) > 1e-12 for m in mods], "sigma": sig,
                             "root_abs_times_sqrtq": [m * math.sqrt(q) for m in mods]})
    off = [r for r in scan if any(r["off"])]
    out = {"characters": len(scan), "functional_equation_holds": sum(r["fe"] for r in scan),
           "beta_real": sum(r["beta_real"] for r in scan), "with_zeros_off_circle": len(off),
           "off_iff_disc_positive": all((r["disc"] > 0) == any(r["off"]) for r in scan),
           "any_disc_zero": any(r["disc_zero"] for r in scan),
           "sigma_distribution": {f"{k:.4f}": v for k, v in sorted(Counter(round(max(r["sigma"]), 4) for r in off).items())},
           "beyond_one": sum(1 for r in off if max(r["sigma"]) > 1),
           "largest_sigma_not_above_1": max(max(r["sigma"]) for r in off if max(r["sigma"]) <= 1)}
    ex = next(r for r in scan if (r["e"], r["alpha"], r["beta"]) == (2, 2, 2))
    out["example"] = {"sigma": sorted(ex["sigma"]), "root_abs_times_sqrtq": sorted(ex["root_abs_times_sqrtq"]),
                      "off": ex["off"]}
    # the local identity: definition of the principal row against the product of local factors
    e, al, be = 2, 2, 2
    Lc = PC.L_coefficients(q, n, N, e, al, be, 2)
    eps = Lc[2] / q
    chi_pm = lambda a, ee, aa, bb: (lambda k: 0 * PC._FUN["ffone"](N) if k is None else PC.zeta(k, N))(
        PC.char_T3_exp(a, q, n, N, lg, ee, aa, bb))
    chi = lambda a: chi_pm(a, e, al, be)
    chib = lambda a: chi_pm(a, -e, -al, -be)
    dfun = lambda a: (chi(a) + eps * chib(a)) / (1 + eps)
    maxes = (3, 1, 0) if full else (2, 0, 0)
    li = {}
    for name, fun in (("rival", dfun), ("chi", chi)):
        Pq = PC.PariProbe(eta_fun=fun)
        lhs = PC.high_series_def(Pq, [1], maxes)
        rhs = PC.euler_product_def(Pq, [1], maxes)
        keys = sorted(set(lhs.terms) | set(rhs.terms))
        diff = [k for k in keys if not PC.equal(lhs.coeff(k, N), rhs.coeff(k, N))]
        li[name] = {"mismatched": [list(k) for k in diff],
                    "lhs_abs_at_first": abs(PC.to_complex(lhs.coeff(diff[0], N), N)) if diff else None,
                    "rhs_abs_at_first": abs(PC.to_complex(rhs.coeff(diff[0], N), N)) if diff else None}
    out["local_identity"] = li
    P1, P2 = [6, 1], [5, 1]  # T - 1, T - 2
    out["non_multiplicative_at"] = {"d_P1P2": abs(PC.to_complex(dfun(PC._pmul(P1, P2, q)), N)),
                                    "d_P1_d_P2": abs(PC.to_complex(dfun(P1) * dfun(P2), N))}
    return out


# ---------------------------------------------------------------------------
# Step 3 (S4.md)
# ---------------------------------------------------------------------------


def item_s4(full: bool) -> dict:
    q, n, N = 13, 4, 52
    rho = RhoBook(q, n)
    j = 1
    L = lambda a: [(-a) % q, 1]
    mul = lambda *fs: _mul(q, *fs)
    one = [1]
    tau = lambda m: PC.tau(q, n, m, N)
    out = {}
    out["base_values"] = {
        "rho0_1_0_is_1": PC.equal(rho(one, j, 0), 1),
        "rho0_1_1_is_q_tau": PC.equal(rho(one, j, 1), tau(j) * q),
        "rho0_1_2_is_0": PC.is_zero(rho(one, j, 2)),
        "rho0_1_3_is_0": PC.is_zero(rho(one, j, 3)),
        "deg1_rho0_0_is_1": all(PC.equal(rho(L(a), j, 0), 1) for a in (1, 5)),
        "deg1_rho0_2_is_tau2_q2": all(PC.equal(rho(L(a), j, 2), tau(2 * j) * q * q) for a in (1, 5)),
        "deg1_rho0_1_3_zero": all(PC.is_zero(rho(L(a), j, i)) for a in (1, 5) for i in (1, 3)),
    }
    hc = [0, 0]
    rl = [one, L(1), mul(L(1), L(2)), [2, 0, 1], mul(L(1), L(2), L(3))]
    for r in rl:
        rec = PC.hecke_infinity_records(q, n, j, len(r) - 1, {i: rho(r, j, i) for i in range(n)}, N, "corrected")
        hc[0] += sum(rec)
        hc[1] += len(rec)
    fh = [0, 0]
    for ro, Pp in [(one, L(1)), (L(2), L(1)), (one, [2, 0, 1])]:
        for jj in range(0, n - 1):
            for i in range(n):
                fh[1] += 1
                lhs = rho(mul(ro, *([Pp] * jj)) if jj else ro, j, i)
                fh[0] += int(PC.equal(lhs, PC.finite_hecke_rhs(q, n, j, ro, Pp, jj, i, lambda a, b: rho(a, j, b), N)))
    out["relations"] = {"hecke_infinity_corrected": {"hold": hc[0], "checked": hc[1]},
                        "finite_hecke": {"hold": fh[0], "checked": fh[1]},
                        "periodicity_r_b4": all(PC.equal(rho(mul(L(2), L(1), L(1), L(1), L(1)), j, i), rho(L(2), j, i))
                                                for i in range(n))}
    tot = {"2007_character": [0, 0], "2014_character": [0, 0]}
    for r in rl:
        rr = {i: rho(r, j, i) for i in range(n)}
        rm = {i: rho([(-x) % q for x in r], j, i) for i in range(n)}
        a = PC.hecke_infinity_records(q, n, j, len(r) - 1, rm, N, "corrected", 0)
        b = PC.hecke_infinity_records(q, n, j, len(r) - 1, rr, N, "corrected", 1)
        tot["2007_character"][0] += sum(a)
        tot["2007_character"][1] += len(a)
        tot["2014_character"][0] += sum(b)
        tot["2014_character"][1] += len(b)
    out["hecke_infinity_both"] = {k: {"hold": v[0], "checked": v[1]} for k, v in tot.items()}
    lgq = PC.logtab(q)
    sgn = PC.zeta((N // n) * (lgq[q - 1] % n), N)
    rel = {}
    for conv, sign in (("e_o(a_-1)", 1), ("e_o(-a_-1)", -1)):
        Cf = lambda r, i: PC.C_struct([(sign * x) % q for x in r], q, n, j, i, N)
        rr = {"deg2_C2_eq_tau_q_C1_epschi(-1)": [], "deg2_C3_eq_tau3_q3": [], "deg3_C3_eq_tau2_q2_C1": [],
              "deg4_C3_eq_tau_q2_C2": []}
        for r in (mul(L(1), L(2)), [2, 0, 1], mul(L(3), L(7))):
            rr["deg2_C2_eq_tau_q_C1_epschi(-1)"].append(PC.equal(Cf(r, 2), tau(j) * q * Cf(r, 1) * sgn))
            rr["deg2_C3_eq_tau3_q3"].append(PC.equal(Cf(r, 3), tau(3 * j) * q ** 3))
        for r in (mul(L(1), L(2), L(3)), mul(L(1), [2, 0, 1])):
            rr["deg3_C3_eq_tau2_q2_C1"].append(PC.equal(Cf(r, 3), tau(2 * j) * q ** 2 * Cf(r, 1)))
        r4 = mul(L(1), L(2), L(3), L(4))
        rr["deg4_C3_eq_tau_q2_C2"].append(PC.equal(Cf(r4, 3), tau(j) * q ** 2 * Cf(r4, 2)))
        rr["deg4_C3_eq_tau_q_C2"] = [PC.equal(Cf(r4, 3), tau(j) * q * Cf(r4, 2))]
        rel[conv] = rr
    out["patterson_n4_relations"] = rel
    samples = {0: [one], 1: [L(1), L(5)], 2: [mul(L(1), L(2)), mul(L(3), L(7)), [2, 0, 1]],
               3: [mul(L(1), L(2), L(3)), mul(L(1), L(2), L(5)), mul(L(1), [2, 0, 1])]}
    if full:
        samples[4] = [mul(L(1), L(2), L(3), L(4)), mul([2, 0, 1], L(3), L(5))]
    table = {}
    for d, rs in samples.items():
        for i in range(n):
            vals = [rho(r, j, i) for r in rs]
            table[f"{d},{i}"] = {"all_zero": all(PC.is_zero(v) for v in vals),
                                 "abs": [round(abs(PC.to_complex(v, N)), 6) for v in vals]}
    out["component_table"] = table
    lams = list(range(3, q))
    defects = {}
    import itertools
    for (i0, i1, i2, i3) in itertools.product((0, 1), (0, 2), (0, 1, 2, 3), (1, 3)):
        vals = []
        for lam in lams:
            P1, P2, P3 = L(1), L(2), L(lam)
            f = {"1": rho(one, j, i0)}
            for k, Pp in (("1", P1), ("2", P2), ("3", P3)):
                f["p" + k] = rho(Pp, j, i1)
            for k, (A_, B_) in (("12", (P1, P2)), ("13", (P1, P3)), ("23", (P2, P3))):
                f["p" + k] = rho(mul(A_, B_), j, i2)
            f["p123"] = rho(mul(P1, P2, P3), j, i3)
            if any(PC.is_zero(v) for v in f.values()):
                vals.append(None)
                continue
            num = norm2(f["p123"], N) * norm2(f["p1"], N) * norm2(f["p2"], N) * norm2(f["p3"], N)
            den = norm2(f["p12"], N) * norm2(f["p13"], N) * norm2(f["p23"], N) * norm2(f["1"], N)
            vals.append(num / den)
        good = [v for v in vals if v is not None]
        defects[f"{i0}{i1}{i2}{i3}"] = {"defect": [None if v is None else round(float(v), 9) for v in vals],
                                        "distinct_exact_values": len(set(good)),
                                        "all_equal_one": all(v == 1 for v in good) if good else None}
    out["three_body"] = defects
    mod = {"single": {}, "pair": {}, "triple": {}}
    for i in range(n):
        mod["single"][str(i)] = sorted({str(norm2(rho(L(a), j, i), N)) for a in [1, 2] + lams})
        mod["pair"][str(i)] = sorted({str(norm2(rho(mul(A_, B_), j, i), N)) for lam in lams
                                      for (A_, B_) in ((L(1), L(lam)), (L(2), L(lam)))}
                                     | {str(norm2(rho(mul(L(1), L(2)), j, i), N))})
        mod["triple"][str(i)] = {str(lam): str(norm2(rho(mul(L(1), L(2), L(lam)), j, i), N)) for lam in lams}
    out["moduli_by_lambda"] = mod
    hyp = []
    for lam in lams:
        r = mul(L(1), L(2), L(lam))
        H = PC.from_hist(PC.hypergeometric_hist(r, q, n, j, N), N)
        C1 = PC.C_struct(r, q, n, j, 1, N)
        hyp.append({"lambda": lam, "abs2_exact": str(norm2(H, N)), "C1_equals_tau_times_H": PC.equal(C1, tau(j) * H),
                    "rho0_i1_equals_C1": PC.equal(rho(r, j, 1), C1)})
    out["hypergeometric"] = hyp
    # the reduction of K to theta: |F(1, A, 1)|^2 = q^(1 + deg A) at the ten A of the verdict,
    # F by enumeration of the residues modulo T A (quartic symbols, xi = chi_T)
    fab = []
    for lam in lams:
        A = mul(L(1), L(2), L(lam))
        fab.append(norm2(PC.F_poisson([1], A, [1], q, n, N, 1), N) == q ** 4)
    out["F_abs2_q_to_1_plus_degA"] = {"checked": len(fab), "hold": sum(fab)}
    census = Counter()
    tot3 = 0
    for r in PC.monic_polys(q, 3):
        if PC.mobius(r, q) == 0:
            continue
        tot3 += 1
        H = PC.from_hist(PC.hypergeometric_hist(r, q, n, j, N), N)
        ftype = "+".join(str(d) for d in sorted(len(Pp) - 1 for Pp, _ in PC.factor(r, q)))
        census[f"{ftype}: {norm2(H, N)}"] += 1
    out["degree3_census"] = {"squarefree_monic_degree_3": tot3, "abs2_H_counts_by_factorization_type": dict(census)}
    out["rho0_agree_q13_n4"] = {"compared": rho.compared, "agree": rho.agree}
    return out


ITEMS = {"symbols": item_symbols, "davenport_hasse": item_davenport_hasse, "structural": item_structural,
         "pari_internal": item_pari_internal, "C_routes": item_C_routes, "rho0_relations": item_rho0_relations, "phase_identities": item_phase_identities,
         "F_routes": item_F_routes, "C_p": item_C_p, "K": item_K, "lemma": item_lemma, "probe": item_probe,
         "ledger": item_ledger, "rival": item_rival, "s4": item_s4}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--item", choices=sorted(ITEMS), action="append")
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args(argv)
    suffix = "_quick" if args.quick else ""
    partial = HERE / f"results_second{suffix}.partial.json"
    final = HERE / f"results_second{suffix}.json"
    out = json.loads(partial.read_text()) if partial.is_file() else (
        json.loads(final.read_text()) if final.is_file() else {})
    for name in (args.item or list(ITEMS)):
        if name in out and not args.item:
            continue
        t0 = time.time()
        res = ITEMS[name](not args.quick)
        res["seconds"] = round(time.time() - t0, 1)
        out[name] = F._jsonable(res)
        partial.write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
        print(f"{name}: {res['seconds']} s", flush=True)
    final.write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    if partial.is_file():
        partial.unlink()
    return 0


if __name__ == "__main__":
    sys.exit(main())
