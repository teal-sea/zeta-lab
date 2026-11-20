"""Character stages of hunt #161.

    .venv/bin/python -m hunts.rh_claim_interface.run_characters lseries  QMAX
    .venv/bin/python -m hunts.rh_claim_interface.run_characters explicit QMAX_ZEROS T_MAX
    .venv/bin/python -m hunts.rh_claim_interface.run_characters levels   QMAX Y_MAX

`lseries`: L'/L(1, chi) for every primitive chi of conductor <= QMAX by two
Arb routes and one mpmath route, and the s = 0 constant by a direct route
against its derived closed form.

`explicit`: the character explicit formula as a measured defect, prime side
against a zero sum, with the exact tail budget c_chi - partial sum.

`levels`: Gm for `Level.cyc psi`, every primitive psi of conductor <= QMAX,
against the envelope the character formula gives under GRH.
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np

from . import instrument as I
from . import zero_side as Z

HERE = Path(__file__).resolve().parent


def _dump(name: str, obj) -> None:
    (HERE / name).write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n")


def _c(x) -> complex:
    return complex(float(x.real.mid()), float(x.imag.mid()))


def _abs_diff_mp(a, cm) -> float:
    """|a - cm| for an acb a and an mpmath number cm, subtracted at 40 digits."""
    from mpmath import mp

    with mp.workdps(40):
        am = mp.mpc(mp.mpf(a.real.mid().str(40, radius=False)), mp.mpf(a.imag.mid().str(40, radius=False)))
        return float(abs(am - cm))


def all_primitive(qmax: int) -> list[I.Char]:
    out = []
    for q in range(3, qmax + 1):
        out.extend(I.primitive_characters(q))
    return out


# ---------------------------------------------------------------------------
# L'/L(1, chi): three routes
# ---------------------------------------------------------------------------


def stage_lseries(qmax: int) -> None:
    from flint import ctx

    t0 = time.time()
    rows = []
    worst_ab = 0.0
    worst_ac = 0.0
    worst_0 = 0.0
    for chi in all_primitive(qmax):
        a = I.logderiv_at_one_arb(chi, 128)
        b = I.logderiv_at_one_stieltjes(chi, 128)
        cm = I.logderiv_at_one_mpmath(chi, 30)
        k = I.char_constants(chi, 128)
        ctx.prec = 128
        try:
            overlap = bool(a.overlaps(b))
            d_ab = float(abs(a - b).upper())
            d0 = float(abs(k["direct0"] - k["derived0"]).upper())
            overlap0 = bool(k["direct0"].overlaps(k["derived0"]))
            row = {
                "q": chi.q,
                "conrey": chi.conrey,
                "order": chi.order(),
                "parity": chi.parity(),
                "l1_re": a.real.str(30),
                "l1_im": a.imag.str(30),
                "routes_overlap": overlap,
                "abs_jet_minus_stieltjes_upper": d_ab,
                "abs_jet_minus_mpmath": _abs_diff_mp(a, cm),
                "c_chi": k["c"].str(30),
                "const0_re": k["direct0"].real.str(30),
                "const0_im": k["direct0"].imag.str(30),
                "const0_direct_overlaps_derived": overlap0,
                "abs_const0_direct_minus_derived_upper": d0,
            }
        finally:
            ctx.prec = 53
        worst_ab = max(worst_ab, d_ab)
        worst_ac = max(worst_ac, row["abs_jet_minus_mpmath"])
        worst_0 = max(worst_0, d0)
        rows.append(row)
    _dump(
        "lseries.json",
        {
            "qmax": qmax,
            "n_characters": len(rows),
            "routes": [
                "A: Arb Taylor jet of L(s, chi) at s = 1 (acb_series.dirichlet_l), 128 bits",
                "B: Arb generalized Stieltjes constants of the Hurwitz zeta function, 128 bits",
                "C: mpmath Stieltjes constants at 30 digits, converted to float",
            ],
            "all_A_B_overlap": all(r["routes_overlap"] for r in rows),
            "worst_abs_A_minus_B_upper": worst_ab,
            "worst_abs_A_minus_C": worst_ac,
            "all_const0_overlap": all(r["const0_direct_overlaps_derived"] for r in rows),
            "worst_abs_const0_direct_minus_derived_upper": worst_0,
            "rows": rows,
            "elapsed_s": round(time.time() - t0, 1),
        },
    )
    print(len(rows), "characters; worst A-B", worst_ab, "worst A-C", worst_ac, "worst const0", worst_0, "in", round(time.time() - t0, 1), "s")


# ---------------------------------------------------------------------------
# explicit formula for Gchi, as a measured defect
# ---------------------------------------------------------------------------


def _prime_power_arrays(n: int):
    pp = I.prime_powers_upto(n)
    return np.array([a for a, _ in pp], dtype=np.int64), np.log(np.array([b for _, b in pp], dtype=np.float64))


def gchi_grid(chi: I.Char, ys: np.ndarray, l1: complex, pk: np.ndarray, lp: np.ndarray) -> np.ndarray:
    vals = chi.values()[pk % chi.q]
    out = np.empty(len(ys), dtype=np.complex128)
    pkf = pk.astype(np.float64)
    for i, y in enumerate(ys):
        m = int(np.searchsorted(pk, y, side="right"))
        w = lp[:m] * (y / pkf[:m] - 1.0)
        out[i] = complex(math.fsum((w * vals[:m].real).tolist()), math.fsum((w * vals[:m].imag).tolist())) + y * l1
    return out


def stage_explicit(qmax: int, t_max: float, y_top: float = 1e6) -> None:
    t0 = time.time()
    rng = np.random.default_rng(1611)
    ys = np.concatenate([[1.0, 1.5, 2.5, 10.5, 100.5, 1000.5], np.round(np.exp(rng.uniform(0, math.log(y_top), 54)) * 64) / 64])
    ys = np.unique(ys[ys >= 1.0])
    pk, lp = _prime_power_arrays(int(y_top) + 1)
    rows = []
    for chi in all_primitive(qmax):
        k = I.char_constants(chi, 128)
        l1 = _c(k["l1"])
        const0 = _c(k["direct0"])
        c = float(k["c"].mid())
        zs = Z.l_zero_ordinates(chi, t_max, step=0.04)
        part = Z.l_partial(zs)
        tail = c - part
        lhs = gchi_grid(chi, ys, l1, pk, lp)
        rhs = Z.l_zero_side(chi, ys, zs, const0)
        ratio = np.abs(lhs - rhs) / (np.sqrt(ys) * tail)
        rows.append(
            {
                "q": chi.q,
                "conrey": chi.conrey,
                "order": chi.order(),
                "parity": chi.parity(),
                "n_zeros": int(len(zs)),
                "count_main_term": Z.riemann_von_mangoldt_main(chi.q, t_max),
                "c_chi": c,
                "partial": part,
                "tail_budget": tail,
                "density_prediction": (math.log(chi.q * t_max / (2 * math.pi)) + 1) / (math.pi * t_max),
                "ratio_at_y_1": float(ratio[0]),
                "max_ratio_y_gt_1": float(np.max(ratio[1:])),
                "argmax_y": float(ys[1:][int(np.argmax(ratio[1:]))]),
            }
        )
        print(rows[-1]["q"], rows[-1]["conrey"], rows[-1]["parity"], rows[-1]["n_zeros"], round(rows[-1]["count_main_term"], 1), round(tail, 5), round(rows[-1]["max_ratio_y_gt_1"], 4), flush=True)
    _dump(
        "explicit_chi.json",
        {
            "identity_odd": "Gchi(y) = sum_rho y^rho/(rho(1-rho)) + L'/L(0,chi) + T_odd(y)",
            "identity_even": "Gchi(y) = sum_rho y^rho/(rho(1-rho)) + log y + 1 + b(chi) + T(y)",
            "qmax": qmax,
            "t_max": t_max,
            "y_top": y_top,
            "n_points": int(len(ys)),
            "prime_side": "float64, exactly rounded sums",
            "zeros": "sign changes of the Hardy Z function on a 0.04 grid, bisected; a lower bound on the count",
            "worst_ratio_y_gt_1": max(r["max_ratio_y_gt_1"] for r in rows),
            "all_tails_positive": all(r["tail_budget"] > 0 for r in rows),
            "worst_tail_vs_density": max(abs(r["tail_budget"] / r["density_prediction"] - 1) for r in rows),
            "rows": rows,
            "elapsed_s": round(time.time() - t0, 1),
        },
    )
    print("worst ratio", max(r["max_ratio_y_gt_1"] for r in rows), "elapsed", round(time.time() - t0, 1))


# ---------------------------------------------------------------------------
# levels
# ---------------------------------------------------------------------------


def build_levels(qmax: int) -> list[dict]:
    seen: dict = {}
    for psi in all_primitive(qmax):
        lev = I.cyc_level(psi)
        if lev["key"] in seen:
            seen[lev["key"]]["generators"].append((psi.q, psi.conrey))
        else:
            lev["generators"] = [(psi.q, psi.conrey)]
            seen[lev["key"]] = lev
    return list(seen.values())


def _combo_from_level(lev: dict) -> dict:
    mod = I.level_model(lev, 128)
    return {
        "kind": "level",
        "q": lev["q"],
        "o": lev["o"],
        "generators": lev["generators"],
        "zeta": 1.0,
        "v": I.level_weights(lev),
        "ell": float(mod["ell"].mid()),
        "C": float(mod["C"].mid()),
        "m0": float(mod["m0"].mid()),
        "m1": float(mod["m1"].mid()),
        "wT": float(mod["wT"].mid()),
        "wTo": float(mod["wTo"].mid()),
        "level": lev,
        "model": mod,
    }


def _combo_from_char(chi: I.Char) -> dict:
    k = I.char_constants(chi, 128)
    odd = k["parity"] == 1
    return {
        "kind": "char",
        "q": chi.q,
        "o": chi.order(),
        "generators": [(chi.q, chi.conrey)],
        "zeta": 0.0,
        "v": np.real(chi.values()),
        "ell": float(k["l1"].real.mid()),
        "C": float(k["c"].mid()),
        "m0": float(k["direct0"].real.mid()) + (0.0 if odd else 1.0),
        "m1": 0.0 if odd else 1.0,
        "wT": 0.0 if odd else 1.0,
        "wTo": 1.0 if odd else 0.0,
    }


def stage_levels(qmax: int, y_max: int, seg: int = 1 << 22, write: bool = True) -> dict:
    t0 = time.time()
    levels = build_levels(qmax)
    combos = [_combo_from_level(lev) for lev in levels] + [_combo_from_char(chi) for chi in all_primitive(qmax)]
    t_setup = time.time() - t0
    nd = int(math.ceil(math.log10(y_max)))
    for cb in combos:
        cb["e_run"] = np.longdouble(cb["ell"])
        cb["r_run"] = np.longdouble(0.0)
        cb["dmax"] = np.full(nd, -np.inf)
        cb["dmin"] = np.full(nd, np.inf)
        cb["dargmax"] = np.zeros(nd)
        cb["dargmin"] = np.zeros(nd)
        cb["gsup"] = -np.inf  # sup of value/sqrt(n) over n >= 100
        cb["gsup_n"] = 0
        cb["last_above_sqrt"] = 0  # last n with value > sqrt(n)
    edges = np.array([10.0**k for k in range(nd + 1)])
    edges[0] = 2.0
    edges[-1] = y_max + 0.5
    for n, e_arr, r_arr, lam in I.scan_integers(y_max, seg=seg):
        g = n * e_arr - r_arr
        sq = np.sqrt(n)
        logn = np.log(n)
        tt = I.T_float(n)
        to = I.T_odd_float(n)
        ni = n.astype(np.int64)
        res_cache: dict[int, np.ndarray] = {}
        cut = np.searchsorted(n, edges)
        lam_over_n = lam / n
        for cb in combos:
            q = cb["q"]
            if q not in res_cache:
                res_cache[q] = ni % q
            vn = cb["v"][res_cache[q]]
            ce = np.cumsum(lam_over_n * vn, dtype=np.longdouble)
            cr = np.cumsum(lam * vn, dtype=np.longdouble)
            ew = (cb["e_run"] + ce).astype(np.float64)
            rw = (cb["r_run"] + cr).astype(np.float64)
            cb["e_run"] = cb["e_run"] + ce[-1]
            cb["r_run"] = cb["r_run"] + cr[-1]
            val = cb["zeta"] * g + n * ew - rw
            m = cb["m0"] + cb["m1"] * logn + cb["wT"] * tt + cb["wTo"] * to
            r = (val - m) / (cb["C"] * sq)
            for d in range(nd):
                a, c = cut[d], cut[d + 1]
                if c <= a:
                    continue
                rs = r[a:c]
                i = int(np.argmax(rs))
                if rs[i] > cb["dmax"][d]:
                    cb["dmax"][d], cb["dargmax"][d] = rs[i], n[a + i]
                i = int(np.argmin(rs))
                if rs[i] < cb["dmin"][d]:
                    cb["dmin"][d], cb["dargmin"][d] = rs[i], n[a + i]
            ratio = val / sq
            big = n >= 100
            if big.any():
                rr = np.where(big, ratio, -np.inf)
                i = int(np.argmax(rr))
                if rr[i] > cb["gsup"]:
                    cb["gsup"], cb["gsup_n"] = float(rr[i]), int(n[i])
            above = np.nonzero(ratio > 1.0)[0]
            if len(above):
                cb["last_above_sqrt"] = int(n[above[-1]])
    t_scan = time.time() - t0 - t_setup

    def summarize(cb):
        dmax, dmin = cb["dmax"], cb["dmin"]
        # decade 0 is [2, 10); "from 100" means decades 2 and up
        worst_all = max(float(np.max(dmax)), float(-np.min(dmin)))
        worst_100 = max(float(np.max(dmax[2:])), float(-np.min(dmin[2:])))
        i = int(np.argmax(np.maximum(dmax[2:], -dmin[2:]))) + 2
        n_w = int(cb["dargmax"][i]) if dmax[i] >= -dmin[i] else int(cb["dargmin"][i])
        return {
            "kind": cb["kind"],
            "q": cb["q"],
            "order": cb["o"],
            "generators": [list(x) for x in cb["generators"]],
            "C": cb["C"],
            "ell": cb["ell"],
            "m0": cb["m0"],
            "m1": cb["m1"],
            "decade_max_ratio": [float(x) for x in dmax],
            "decade_argmax_n": [int(x) for x in cb["dargmax"]],
            "decade_min_ratio": [float(x) for x in dmin],
            "decade_argmin_n": [int(x) for x in cb["dargmin"]],
            "worst_abs_ratio_n_ge_2": worst_all,
            "worst_abs_ratio_n_ge_100": worst_100,
            "worst_n_ge_100_at": n_w,
            "sup_value_over_sqrt_n_ge_100": cb["gsup"],
            "sup_value_over_sqrt_at": cb["gsup_n"],
            "last_n_with_value_above_sqrt": cb["last_above_sqrt"],
        }

    rows = [summarize(cb) for cb in combos]
    lev_rows = [r for r in rows if r["kind"] == "level"]
    chr_rows = [r for r in rows if r["kind"] == "char"]

    # the identity at y = 1, in Arb, for every level
    from flint import ctx

    ident = []
    for cb in combos:
        if cb["kind"] != "level":
            continue
        gm1 = I.Gm_arb(cb["level"], 1, 128)
        m1 = I.M_arb(cb["model"], 1, 128)
        ctx.prec = 128
        try:
            ident.append(bool((gm1 - m1).overlaps(cb["model"]["C"])) and float(abs(gm1 - m1 - cb["model"]["C"]).upper()) < 1e-25)
        finally:
            ctx.prec = 53

    # Arb confirmation of the worst level points (n >= 100)
    order = sorted(range(len(lev_rows)), key=lambda i: -lev_rows[i]["worst_abs_ratio_n_ge_100"])
    level_combos = [cb for cb in combos if cb["kind"] == "level"]
    arb_checks = []
    for i in order[:3]:
        row, cb = lev_rows[i], level_combos[i]
        nw = row["worst_n_ge_100_at"]
        gm = I.Gm_arb(cb["level"], nw, 128)
        mm = I.M_arb(cb["model"], nw, 128)
        ctx.prec = 128
        try:
            from flint import arb

            ratio = (gm - mm) / (cb["model"]["C"] * arb(nw).sqrt())
            arb_checks.append(
                {
                    "q": row["q"],
                    "order": row["order"],
                    "generators": row["generators"],
                    "n": nw,
                    "ratio_arb": ratio.str(20),
                    "abs_ratio_float": row["worst_abs_ratio_n_ge_100"],
                    "abs_float_minus_arb": abs(row["worst_abs_ratio_n_ge_100"] - abs(float(ratio.mid()))),
                    "abs_ratio_below_one_decided_by_arb": bool(abs(ratio) < 1),
                }
            )
        finally:
            ctx.prec = 53

    out = {
        "qmax": qmax,
        "y_max": y_max,
        "route": "float64 scan at every integer; ratio = (value - M(n)) / (C sqrt(n))",
        "n_levels": len(lev_rows),
        "n_characters": len(chr_rows),
        "identity_at_y_1_holds_for_every_level": all(ident),
        "worst_level_ratio_n_ge_100": max(r["worst_abs_ratio_n_ge_100"] for r in lev_rows),
        "worst_level_ratio_n_ge_2": max(r["worst_abs_ratio_n_ge_2"] for r in lev_rows),
        "worst_char_ratio_n_ge_100": max(r["worst_abs_ratio_n_ge_100"] for r in chr_rows),
        "worst_char_ratio_n_ge_2": max(r["worst_abs_ratio_n_ge_2"] for r in chr_rows),
        "max_level_C": max(r["C"] for r in lev_rows),
        "max_level_sup_Gm_over_sqrt_n_ge_100": max(r["sup_value_over_sqrt_n_ge_100"] for r in lev_rows),
        "max_level_last_n_with_Gm_above_sqrt": max(r["last_n_with_value_above_sqrt"] for r in lev_rows),
        "arb_checks": arb_checks,
        "levels": lev_rows,
        "characters": chr_rows,
        "setup_s": round(t_setup, 1),
        "scan_s": round(t_scan, 1),
        "elapsed_s": round(time.time() - t0, 1),
    }
    if not write:
        return out
    _dump(f"levels_q{qmax}_y{int(round(math.log10(y_max)))}.json", out)
    for key in ("n_levels", "n_characters", "identity_at_y_1_holds_for_every_level", "worst_level_ratio_n_ge_100", "worst_level_ratio_n_ge_2", "worst_char_ratio_n_ge_100", "worst_char_ratio_n_ge_2", "max_level_C", "max_level_sup_Gm_over_sqrt_n_ge_100", "max_level_last_n_with_Gm_above_sqrt", "setup_s", "scan_s"):
        print(key, out[key])
    for a in arb_checks:
        print(a)
    return out


def main(argv: list[str]) -> None:
    stage = argv[1]
    if stage == "lseries":
        stage_lseries(int(argv[2]))
    elif stage == "explicit":
        stage_explicit(int(argv[2]), float(argv[3]))
    elif stage == "levels":
        stage_levels(int(argv[2]), int(float(argv[3])))
    else:
        raise SystemExit(f"unknown stage {stage}")


if __name__ == "__main__":
    main(sys.argv)
