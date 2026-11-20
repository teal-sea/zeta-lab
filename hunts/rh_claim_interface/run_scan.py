"""Stages `zeros`, `explicit` and `scan` of hunt #161.

Usage (from the repo root, one core):

    .venv/bin/python -m hunts.rh_claim_interface.run_scan zeros    SCRATCH [N]
    .venv/bin/python -m hunts.rh_claim_interface.run_scan explicit SCRATCH
    .venv/bin/python -m hunts.rh_claim_interface.run_scan scan     SCRATCH Y_MAX
    .venv/bin/python -m hunts.rh_claim_interface.run_scan enclose  SCRATCH Y_MAX
    .venv/bin/python -m hunts.rh_claim_interface.run_scan frontier SCRATCH

SCRATCH holds caches and checkpoints and is not committed.  The small JSON
files written next to this module are.
"""

from __future__ import annotations

import hashlib
import json
import math
import sys
import time
from pathlib import Path

import numpy as np

from . import instrument as I
from . import zero_side as Z

HERE = Path(__file__).resolve().parent
N_ZEROS_DEFAULT = 20000


def _dump(name: str, obj) -> None:
    (HERE / name).write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n")


def _load_zeros(scratch: str, n: int = N_ZEROS_DEFAULT):
    return Z.zeta_zero_ordinates(n, prec=64, cache_dir=scratch)


# ---------------------------------------------------------------------------
# zeros
# ---------------------------------------------------------------------------


def stage_zeros(scratch: str, n: int = N_ZEROS_DEFAULT) -> None:
    t0 = time.time()
    g, max_rad = _load_zeros(scratch, n)
    elapsed = time.time() - t0
    repo = HERE.parents[1]
    lab = json.loads((repo / "data" / "zeros_1000.json").read_text())
    lab_g = np.array([float(x) for x in lab["zeros"]])
    k = min(len(lab_g), len(g))
    ladder = []
    for m in (100, 1000, 5000, 10000, n):
        if m <= n:
            gm = g[:m]
            t = float(gm[-1])
            ladder.append(
                {
                    "n_zeros": m,
                    "height": t,
                    "partial": Z.zeta_partial(gm),
                    "tail_budget": Z.zeta_tail_budget(gm),
                    "density_prediction": (math.log(t / (2 * math.pi)) + 1) / (math.pi * t),
                }
            )
    _dump(
        "zeros.json",
        {
            "source": "python-flint acb.zeta_zeros at 64 bits (Arb isolates the k-th zero by index)",
            "n_zeros": int(n),
            "height": float(g[-1]),
            "max_ball_radius": max_rad,
            "sha256_float64_le": hashlib.sha256(g.astype("<f8").tobytes()).hexdigest(),
            "first": [float(x) for x in g[:3]],
            "max_abs_diff_vs_data_zeros_1000": float(np.max(np.abs(g[:k] - lab_g[:k]))),
            "c0": I.C0,
            "ladder": ladder,
            "elapsed_s": round(elapsed, 1),
        },
    )
    print(json.dumps(ladder[-1]), "elapsed", round(elapsed, 1))


# ---------------------------------------------------------------------------
# explicit formula for G, as a measured defect
# ---------------------------------------------------------------------------


def explicit_grid() -> list[float]:
    fixed = [1.0, 1.25, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0, 7.0, 7.5, 8.0, 9.0, 10.5, 16.0, 30.5, 100.5, 1000.5]
    rng = np.random.default_rng(161)
    rnd = np.exp(rng.uniform(0.0, math.log(1e8), size=240))
    # exact dyadic points: round to 1/64
    rnd = np.round(rnd * 64.0) / 64.0
    rnd = rnd[rnd >= 1.0]
    return sorted(set(fixed) | set(float(x) for x in rnd))


def stage_explicit(scratch: str) -> None:
    t0 = time.time()
    g, _ = _load_zeros(scratch)
    ys = explicit_grid()
    prime_side = I.G_arb(ys, prec=128)
    ps = np.array([float(x.mid()) for x in prime_side])
    ps_rad = max(float(x.rad()) for x in prime_side)
    ya = np.array(ys)
    rows = []
    ladder = {}
    for m in (100, 1000, 5000, len(g)):
        gm = g[:m]
        tail = Z.zeta_tail_budget(gm)
        zs = Z.zeta_zero_side(ya, gm)
        defect = ps - zs
        ratio = defect / (np.sqrt(ya) * tail)
        ladder[str(m)] = {
            "tail_budget": tail,
            "max_abs_ratio_y_gt_1": float(np.max(np.abs(ratio[ya > 1.0]))),
            "max_abs_defect_over_sqrt_y": float(np.max(np.abs(defect / np.sqrt(ya)))),
            "ratio_at_y_1": float(ratio[0]),
        }
        if m == len(g):
            for y, p, z, d, r in zip(ys, ps, zs, defect, ratio):
                rows.append({"y": y, "prime_side": float(p), "zero_side": float(z), "defect": float(d), "ratio_to_budget": float(r)})
    # enclosure-carrying spot checks: both sides and the budget in Arb
    spots = []
    n_arb = 2000
    for y in (1, 2.5, 100.5, 10007.25, 1000003.5):
        ps_a = I.G_arb([y], prec=128)[0]
        zs_a, tail_a = Z.zeta_zero_side_arb(y, n_arb, prec=128)
        from flint import ctx

        old = ctx.prec
        ctx.prec = 128
        try:
            d = ps_a - zs_a
            budget = tail_a * I._as_arb(y).sqrt()
            inside = bool(abs(d) <= budget)
            touches = bool(abs(d).overlaps(budget))
            spots.append(
                {
                    "y": float(y),
                    "n_zeros": n_arb,
                    "prime_side": ps_a.str(25),
                    "zero_side_truncated": zs_a.str(25),
                    "defect": d.str(12),
                    "budget": budget.str(12),
                    "abs_defect_le_budget_decided_by_arb": inside,
                    "abs_defect_ball_overlaps_budget_ball": touches,
                }
            )
        finally:
            ctx.prec = old
    _dump(
        "explicit_zeta.json",
        {
            "identity": "G(y) = sum_rho y^rho/(rho(1-rho)) + log(2 pi) + T(y), y >= 1",
            "prime_side": "Arb, 128 bits; max radius %.3g" % ps_rad,
            "zero_side": "float64 sum over the first N zeros; budget = (c0 - partial sum) sqrt(y)",
            "n_points": len(ys),
            "y_max": max(ys),
            "ladder": ladder,
            "rows": rows,
            "arb_spots": spots,
            "elapsed_s": round(time.time() - t0, 1),
        },
    )
    print(json.dumps(ladder, indent=1))
    for s in spots:
        print(s)


# ---------------------------------------------------------------------------
# the scan
# ---------------------------------------------------------------------------

BINS_PER_DECADE = 10


def stage_scan(scratch: str, y_max: int, seg: int = 1 << 24) -> None:
    y_max = int(y_max)
    nb = int(round(math.log10(y_max) * BINS_PER_DECADE))
    edges = np.array([10 ** (k / BINS_PER_DECADE) for k in range(nb + 1)])
    edges[-1] = y_max + 0.5
    ck = Path(scratch) / f"scan_{y_max}.npz"
    bmax = np.full(nb, -np.inf)
    bmin = np.full(nb, np.inf)
    bargmax = np.zeros(nb)
    bargmin = np.zeros(nb)
    gmax = np.full(nb, -np.inf)  # sup of G(n)/sqrt(n)
    gargmax = np.zeros(nb)
    state = None
    spent = 0.0
    if ck.exists():
        d = np.load(ck, allow_pickle=False)
        bmax, bmin, bargmax, bargmin = d["bmax"], d["bmin"], d["bargmax"], d["bargmin"]
        gmax, gargmax = d["gmax"], d["gargmax"]
        state = (int(d["lo"]), np.longdouble(d["e_hi"]) + np.longdouble(d["e_lo"]), np.longdouble(d["r_hi"]) + np.longdouble(d["r_lo"]))
        spent = float(d["spent"])
        print("resuming at", state[0], "after", round(spent, 1), "s")
    t0 = time.time()
    base = I.small_primes(math.isqrt(y_max) + 2)
    lo = 2 if state is None else state[0]
    e_run = np.longdouble(I.EULER_GAMMA) if state is None else state[1]
    r_run = np.longdouble(-1.0) if state is None else state[2]
    while lo <= y_max:
        hi = min(lo + seg, y_max + 1)
        lam = I.lambda_segment(lo, hi, base)
        n = np.arange(lo, hi, dtype=np.float64)
        ce = np.cumsum(lam / n + np.log1p(-1.0 / n), dtype=np.longdouble)
        cr = np.cumsum(lam - 1.0, dtype=np.longdouble)
        e_arr = (e_run + ce).astype(np.float64)
        r_arr = (r_run + cr).astype(np.float64)
        e_run = e_run + ce[-1]
        r_run = r_run + cr[-1]
        del ce, cr, lam
        sq = np.sqrt(n)
        corr = (I.LOG_2PI + I.T_float(n)) / sq
        f = (n * e_arr - r_arr) / sq - corr
        cut = np.searchsorted(n, edges)
        for b in range(nb):
            a, c = cut[b], cut[b + 1]
            if c <= a:
                continue
            fs = f[a:c]
            i = int(np.argmax(fs))
            if fs[i] > bmax[b]:
                bmax[b], bargmax[b] = fs[i], n[a + i]
            i = int(np.argmin(fs))
            if fs[i] < bmin[b]:
                bmin[b], bargmin[b] = fs[i], n[a + i]
            gs = fs + corr[a:c]
            i = int(np.argmax(gs))
            if gs[i] > gmax[b]:
                gmax[b], gargmax[b] = gs[i], n[a + i]
        lo = hi
        e_hi = np.float64(e_run)
        r_hi = np.float64(r_run)
        np.savez(
            ck,
            bmax=bmax, bmin=bmin, bargmax=bargmax, bargmin=bargmin, gmax=gmax, gargmax=gargmax,
            lo=lo, e_hi=e_hi, e_lo=np.float64(e_run - np.longdouble(e_hi)),
            r_hi=r_hi, r_lo=np.float64(r_run - np.longdouble(r_hi)),
            spent=spent + time.time() - t0,
        )
    spent += time.time() - t0
    out = {
        "y_max": y_max,
        "route": "float64 increments, extended-precision running sums; F(n) at every integer 2 <= n <= y_max",
        "bins_per_decade": BINS_PER_DECADE,
        "bin_lo": [float(x) for x in edges[:-1]],
        "bin_max_F": [float(x) for x in bmax],
        "bin_argmax_n": [int(x) for x in bargmax],
        "bin_min_F": [float(x) for x in bmin],
        "bin_argmin_n": [int(x) for x in bargmin],
        "bin_max_G_over_sqrt": [float(x) for x in gmax],
        "bin_argmax_G_over_sqrt_n": [int(x) for x in gargmax],
        "final_E": float(e_run),
        "final_R": float(r_run),
        "c0": I.C0,
        "elapsed_s": round(spent, 1),
    }
    _dump(f"scan_{_tag(y_max)}.json", out)
    print("scan to", y_max, "in", round(spent, 1), "s")
    print("max F over n>=2:", max(bmax), "min:", min(bmin))


def _tag(y_max: int) -> str:
    e = round(math.log10(y_max))
    return f"1e{e}" if 10**e == y_max else str(y_max)


# ---------------------------------------------------------------------------
# enclosures at the extremal points
# ---------------------------------------------------------------------------


def stage_enclose(scratch: str, y_max: int, precs=(128, 192)) -> None:
    """Arb enclosures at the per-decade extremes found by the scan."""
    t0 = time.time()
    scan = json.loads((HERE / f"scan_{_tag(y_max)}.json").read_text())
    bpd = scan["bins_per_decade"]
    nb = len(scan["bin_max_F"])
    decades = []
    for k in range(nb // bpd):
        sl = slice(k * bpd, (k + 1) * bpd)
        fm = scan["bin_max_F"][sl]
        fn = scan["bin_min_F"][sl]
        gm = scan["bin_max_G_over_sqrt"][sl]
        i = int(np.argmax(fm))
        j = int(np.argmin(fn))
        h = int(np.argmax(gm))
        decades.append(
            {
                "decade": k,
                "n_max": scan["bin_argmax_n"][sl][i],
                "F_max_float": fm[i],
                "n_min": scan["bin_argmin_n"][sl][j],
                "F_min_float": fn[j],
                "n_gmax": scan["bin_argmax_G_over_sqrt_n"][sl][h],
                "G_over_sqrt_max_float": gm[h],
            }
        )
    # integer points needed: n_max - 1, n_max, n_min, n_gmax
    pts = set()
    for d in decades:
        pts.update([max(d["n_max"] - 1, 1), d["n_max"], d["n_min"], d["n_gmax"]])
    pts = sorted(pts)
    from flint import arb, ctx

    by_prec = {}
    for prec in precs:
        sums = I.arb_prefix_sums(pts, prec=prec)
        by_prec[prec] = sums
    prec = precs[0]
    sums = by_prec[prec]
    ctx.prec = prec
    try:
        g = arb.const_euler()
        log2pi = (2 * arb.pi()).log()

        def er(n):
            psi, a = sums[n]
            return a - arb(n).log() + g, psi - n

        consts = {prec: (g, log2pi)}
        for other in precs[1:]:  # the constants at each precision, not the 128-bit balls reused
            ctx.prec = other
            consts[other] = (arb.const_euler(), (2 * arb.pi()).log())
        ctx.prec = prec

        def f_at(y, n, which=prec):
            """(G(y), F(y)) from the prefix sums at `which` bits; the caller sets ctx.prec to match."""
            psi, a = by_prec[which][n]
            g_w, log2pi_w = consts[which]
            ya = I._as_arb(y)
            gg = ya * a - psi - ya * ya.log() + (1 + g_w) * ya
            return gg, (gg - log2pi_w - I.T_arb(ya)) / ya.sqrt()

        for d in decades:
            # the minimum: an integer (a prime power)
            n = d["n_min"]
            gg, ff = f_at(n, n)
            d["F_min_arb"] = ff.str(25)
            d["F_min_float_minus_arb"] = d["F_min_float"] - float(ff.mid())
            d["F_min_over_c0"] = float((ff / I.c0_arb(prec)).mid())
            c0_1 = I.c0_arb(prec)
            inside1 = [bool(ff > -c0_1) and bool(ff < c0_1)]
            # the integer maximum, then the interior critical point next to it
            n = d["n_max"]
            gg, ff = f_at(n, n)
            d["F_max_int_arb"] = ff.str(25)
            d["F_max_float_minus_arb"] = d["F_max_float"] - float(ff.mid())
            inside1.append(bool(ff > -c0_1) and bool(ff < c0_1))
            best = None
            for m in (n - 1, n):
                if m < 1:
                    continue
                e_m, r_m = er(m)
                cp = I.interior_critical_point(m, float(e_m.mid()), float(r_m.mid()))
                if cp is None:
                    continue
                y_c = cp[0]
                _, fc = f_at(y_c, m)
                if best is None or float(fc.mid()) > float(best[1].mid()):
                    best = (y_c, fc, m)
            if best is not None:
                y_c, fc, m = best
                d["y_crit"] = y_c
                d["y_crit_hex"] = float(y_c).hex()
                d["n_crit_floor"] = int(m)
                d["F_crit_arb"] = fc.str(25)
                d["F_crit_minus_F_int"] = float((fc - ff).mid())
                inside1.append(bool(fc > -c0_1) and bool(fc < c0_1))
                d["F_crit_over_c0"] = float((fc / I.c0_arb(prec)).mid())
                # derivative at the float critical point, same prefix sums
                psi, a = sums[m]
                ya = I._as_arb(y_c)
                tt = I.T_arb(ya)
                gval = ya * a - psi - ya * ya.log() + (1 + g) * ya - log2pi - tt
                t_prime = tt / ya - (1 - 1 / (ya * ya)).log() / (2 * ya)
                fp = ((a - ya.log() + g - t_prime) - gval / (2 * ya)) / ya.sqrt()
                d["F_prime_at_y_crit_arb"] = fp.str(8)
            else:
                d["y_crit"] = None
                d["F_crit_over_c0"] = float((ff / I.c0_arb(prec)).mid())
            n = d["n_gmax"]
            gg, ff = f_at(n, n)
            ratio = gg / arb(n).sqrt()
            d["G_over_sqrt_max_arb"] = ratio.str(25)
            d["inside_envelope_decided_by_arb"] = all(inside1)
            # precision response: every extreme of the decade again at the second
            # precision (the first version of this stage repeated only the minimum)
            if len(precs) > 1:
                ctx.prec = precs[1]
                c0_2 = I.c0_arb(precs[1])
                _, f2 = f_at(d["n_min"], d["n_min"], precs[1])
                d["F_min_arb_prec2"] = f2.str(25)
                inside = [bool(f2 > -c0_2) and bool(f2 < c0_2)]
                _, f2 = f_at(d["n_max"], d["n_max"], precs[1])
                d["F_max_int_arb_prec2"] = f2.str(25)
                inside.append(bool(f2 > -c0_2) and bool(f2 < c0_2))
                if d.get("y_crit") is not None:
                    _, f2 = f_at(d["y_crit"], d["n_crit_floor"], precs[1])
                    d["F_crit_arb_prec2"] = f2.str(25)
                    inside.append(bool(f2 > -c0_2) and bool(f2 < c0_2))
                g2, _ = f_at(d["n_gmax"], d["n_gmax"], precs[1])
                d["G_over_sqrt_max_arb_prec2"] = (g2 / arb(d["n_gmax"]).sqrt()).str(25)
                d["inside_envelope_decided_by_arb_prec2"] = all(inside)
                ctx.prec = prec
    finally:
        ctx.prec = 53
    out = {
        "y_max": scan["y_max"],
        "precisions_bits": list(precs),
        "c0": I.c0_arb(128).str(30),
        "decades": decades,
        "elapsed_s": round(time.time() - t0, 1),
    }
    _dump(f"scan_{_tag(y_max)}_enclosed.json", out)
    for d in decades:
        print(d["decade"], d["n_min"], d["F_min_arb"], "|", d.get("y_crit"), d.get("F_crit_arb"), d.get("F_prime_at_y_crit_arb"))
    print("elapsed", out["elapsed_s"])


# ---------------------------------------------------------------------------
# the unconditional frontier: what is known without RH
# ---------------------------------------------------------------------------

#: Heights below which every zero is known to lie on the line (quoted, not recomputed).
H_RAMARE_2013 = 2.44e12  # the T0 used in Ramare, Acta Arith. 159 (2013), section 4
H_PLATT_TRUDGIAN = 3.0e12  # Platt and Trudgian 2021
#: Constants of Theorem 1.1 of the 2013 paper, in this hunt's units:
#: |G(x)| <= RAMARE_SQRT_CONST sqrt(x) + RAMARE_LINEAR_CONST x for x >= RAMARE_X_MIN.
#: Author copies read in the review round (sha256 of the PDF as fetched on 2026-11-20).
RAMARE_2013_AUTHOR_COPY_SHA256 = "a4de9b736c7d942563a15b8141c3244add6878d1730482a518e1cdc0cba9d2a9"
RAMARE_2023_CORRIGENDUM_AUTHOR_COPY_SHA256 = "ec315280a24bd5b5d2170aeb145b29a7abae6d00ea1304f78b4a2f3fbd9a6b5e"
RAMARE_SQRT_CONST = 0.5
RAMARE_LINEAR_CONST = 1.75e-12
RAMARE_X_MIN = 8950


def one_sided_density_weight(height: float) -> float:
    """Leading term of sum over zeros with gamma > height of 1/gamma^2.

    From dN(t) = (1/2pi) log(t/2pi) dt: the integral of t^-2 dN(t) from
    `height` to infinity.  An estimate, not an enclosure.
    """
    return (math.log(height / (2 * math.pi)) + 1) / (2 * math.pi * height)


def ramare_lemma_4_2_as_printed(t: float) -> float:
    """Right-hand side of Lemma 4.2 of the 2013 paper as the author copy prints it."""
    lg = math.log(t / (2 * math.pi))
    return lg / (2 * math.pi * t) + 0.67 * (2 * lg + 0.5) / (t * t)


def unconditional_reach(w1: float) -> dict:
    """Where the bound |G - log 2pi - T| <= c0 sqrt(y) + w1 (y + 3 sqrt(y)) stops giving each statement.

    Derivation in RESULTS.md section 6.  `w1` is the one-sided weight of the
    zeros above the verified height.
    """
    c0 = I.C0
    a = 1.0 - c0 - 3.0 * w1
    root = (a + math.sqrt(a * a - 4.0 * w1 * I.LOG_2PI)) / (2.0 * w1)
    return {
        "w1": w1,
        "y_where_excess_over_envelope_reaches_c0": (c0 / w1 - 3.0) ** 2,
        "y_up_to_which_G_le_sqrt_y_is_guaranteed": root * root,
        "excess_over_c0_at_y_1e9": w1 * (math.sqrt(1e9) + 3.0),
        "crude_y_where_2w1_y_reaches_c0_sqrt_y": (c0 / (2 * w1)) ** 2,
        "crude_y_where_2w1_y_reaches_sqrt_y": (1.0 / (2 * w1)) ** 2,
    }


def stage_frontier(scratch: str) -> None:
    """What is known about G without RH, and one printed lemma checked against the zero table."""
    t0 = time.time()
    g, _ = _load_zeros(scratch)
    top = float(g[-1])
    # the weight of the zeros above the table, read off the closed form c0 (on-line zeros: known to 3e12)
    tail_one_sided = Z.zeta_tail_budget(g) / 2.0
    checks = []
    for t in (1000.0, 5000.0, 10000.0):
        listed = g[g >= t]
        partial = math.fsum((1.0 / (listed * listed)).tolist())
        checks.append(
            {
                "T": t,
                "n_listed_zeros_from_T": int(len(listed)),
                "listed_sum_of_inverse_squares": partial,
                "listed_sum_plus_tail_from_c0": partial + tail_one_sided,
                "lemma_4_2_as_printed": ramare_lemma_4_2_as_printed(t),
                "density_leading_term": one_sided_density_weight(t),
                "listed_sum_alone_exceeds_printed_bound": bool(partial > ramare_lemma_4_2_as_printed(t)),
            }
        )
    out = {
        "what": "what is known about G(y) without RH, in this hunt's units; float grade, nothing here is an enclosure",
        "bound": "|G(y) - log 2pi - T(y)| <= c0 sqrt(y) + w1 (y + 3 sqrt(y)), w1 = sum over zeros with gamma > H of 1/gamma^2, H a height below which every zero is on the line",
        "sources": {
            "ramare_2013": "O. Ramare, Explicit estimates for the summatory function of Lambda(n)/n from the one of Lambda(n), Acta Arith. 159 (2013), 113-122",
            "ramare_2013_author_copy_sha256": RAMARE_2013_AUTHOR_COPY_SHA256,
            "ramare_2023": "O. Ramare, Corrigendum to the above, Acta Arith. 211 (2023), 93-96, DOI 10.4064/aa220605-11-10 (journal reference from the publisher's listing)",
            "ramare_2023_author_copy_sha256": RAMARE_2023_CORRIGENDUM_AUTHOR_COPY_SHA256,
            "note": "author copies read; the journal versions were not consulted",
        },
        "zero_table_height": top,
        "tail_one_sided_from_c0_above_table": tail_one_sided,
        "ramare_theorem_1_1": {
            "source": "O. Ramare, Acta Arith. 159 (2013), 113-122, Theorem 1.1 (the 2023 corrigendum says it needs no change); read, not re-proved",
            "in_these_units": "|G(x)| <= sqrt(x)/2 + 1.75e-12 x for x >= 8950",
            "sqrt_const": RAMARE_SQRT_CONST,
            "linear_const": RAMARE_LINEAR_CONST,
            "x_min": RAMARE_X_MIN,
            "y_up_to_which_G_le_sqrt_y_follows": (RAMARE_SQRT_CONST / RAMARE_LINEAR_CONST) ** 2,
            "bound_on_abs_F_at_y_1e9_from_its_proof": 0.047 + RAMARE_LINEAR_CONST * math.sqrt(1e9),
        },
        "ramare_lemma_4_2_check": {
            "printed": "sum_{gamma >= T} 1/gamma^2 <= log(T/2pi)/(2 pi T) + 0.67 (2 log(T/2pi) + 1/2)/T^2 for T >= 1000 (author copy)",
            "rows": checks,
            "printed_bound_at_T0": ramare_lemma_4_2_as_printed(H_RAMARE_2013),
            "density_leading_term_at_T0": one_sided_density_weight(H_RAMARE_2013),
        },
        "reach": {
            "H_2.44e12": unconditional_reach(one_sided_density_weight(H_RAMARE_2013)),
            "H_3e12": unconditional_reach(one_sided_density_weight(H_PLATT_TRUDGIAN)),
        },
        "single_quadruple_onsets_at_3e12_for_comparison": "RESULTS.md section 6: 10^46.6 (envelope) and 10^49.3 (G <= sqrt(y)); a single planted quadruple, not this bound",
        "elapsed_s": round(time.time() - t0, 1),
    }
    _dump("frontier.json", out)
    print(json.dumps(out, indent=1))


def main(argv: list[str]) -> None:
    stage, scratch = argv[1], argv[2]
    Path(scratch).mkdir(parents=True, exist_ok=True)
    if stage == "zeros":
        stage_zeros(scratch, int(argv[3]) if len(argv) > 3 else N_ZEROS_DEFAULT)
    elif stage == "explicit":
        stage_explicit(scratch)
    elif stage == "scan":
        stage_scan(scratch, int(float(argv[3])))
    elif stage == "enclose":
        stage_enclose(scratch, int(float(argv[3])))
    elif stage == "frontier":
        stage_frontier(scratch)
    else:
        raise SystemExit(f"unknown stage {stage}")


if __name__ == "__main__":
    main(sys.argv)
