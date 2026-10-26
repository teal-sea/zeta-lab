"""Milestones 2 and 3 for Polymath 15 Table 1, row 2, written to row2_check.json.

Row 2 (arXiv:1904.12438v2, debruijn.tex line 1950):
X = 5e12 + 194858, t0 = 0.186, y0 = 0.16733, Lambda = 0.20, winding number 0,
N0 = 630783, "|f_t(x+iy)| lower bound" 0.0376.

What this script computes (every number an Arb ball unless marked as a time):

1. N0 = floor(sqrt(X/(4 pi) + t0/16)) and the interval [x_{N0}, x_{N0+1}).
2. The Lemma (trib2) quantities at N0 for y0 = 0.16733 and y0 = sqrt(0.028)
   (t0 + y0^2/2 = 0.2 exactly for the latter), in four variants:
   - "point": sigma = Re s_* and |gamma| exact at x = X;
   - "uniform": sigma a ball over [x_{N0}, x_{N0+1}] and |gamma| replaced by its
     (gamma-bound) majorant at x_{N0}, valid for every x with N = N0;
   - "polymath_moll2_analytic": the formula of the project's PARI function
     abbeff_moll2_analytic_bound (|gamma| ~ N^-y, tail sums as integrals), read
     from the repository as data and re-implemented here;
   each reported both as the trib2 numerator, which bounds |E_2 f| with
   E_2 = 1 - b_2 2^{-s_*}, and divided by 1 + |b_2 2^{-s_*}|, which bounds |f|.
3. One direct evaluation of f_t, C_t/B_t, e_A, e_B, e_C, e_{C,0} at X + i y0, t0.
4. One rectangle [X, X+1] x [y0, 1] of the barrier at t = t0 and, unless
   --skip-t0-rect / --skip-zero-rect, at t = 0: Rouche check and winding number.

Usage:  .venv/bin/python hunts/dbn_pt_height/evaluator/row2_check.py [--skip-zero-rect]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from flint import acb, arb  # noqa: E402

import effective as ef  # noqa: E402

X_INT = 5000000194858
T0 = "0.186"
Y0_PRINTED = "0.16733"
N0_PRINTED = 630783
PRINTED_BOUND = "0.0376"
DBN_CACHE = Path(os.environ.get("DBN_CACHE_ROOT", os.path.expanduser("~/.cache/zeta-lab/dbn")))
POLYMATH_WINDNUM = (
    DBN_CACHE / "chain-github-dbn_upper_bound/repo/output/"
    "windingnumbers/windnum_nolemma_x5000000194858_y_0.16733_1_t_0_0.186.txt"
)


def ball(v: arb, digits: int = 20) -> dict[str, str]:
    return {"str": v.str(digits), "lower": repr(ef._lower_float(v)), "upper": repr(ef._upper_float(v))}


def cball(v: acb, digits: int = 20) -> dict[str, dict[str, str]]:
    return {"re": ball(v.real, digits), "im": ball(v.imag, digits), "abs": ball(abs(v), digits)}


def _tailint(llim: arb, ulim: arb, a: arb, b: arb) -> arb:
    """int_llim^ulim u^{-a + b log u} du, the project's tailint (erfi form)."""
    pi = arb.pi()
    sb = b.sqrt()
    pref = pi.sqrt() / sb / 2 * (-(a - 1) ** 2 / (4 * b)).exp()
    return pref * (((2 * b * ulim.log() - a + 1) / sb / 2).erfi() - ((2 * b * llim.log() - a + 1) / sb / 2).erfi())


def polymath_moll2_analytic(N: int, y: arb, t: arb, N0: int = 1000) -> arb:
    """Re-implementation of abbeff_moll2_analytic_bound (abbeff_largex_bounds.txt,
    lines 138-145 of the project's pari/ directory, read as data)."""
    Na = arb(N)
    S1_main = arb(0)
    for n in range(1, N0 + 1):
        na = arb(n)
        S1_main += (1 + (y * na.log()).exp() / (y * Na.log()).exp()) * (
            -((1 + y) / 2 + (t / 4) * (Na * Na / na).log()) * na.log()
        ).exp()
    Ny = (y * Na.log()).exp()
    S1_tail = _tailint(arb(N0), Na, (1 + y) / 2 + (t / 2) * Na.log(), t / 4) + _tailint(
        arb(N0), Na, (1 - y) / 2 + (t / 2) * Na.log(), t / 4
    ) / Ny
    S1 = S1_main + S1_tail
    modb2 = (-((1 + y) / 2 + (t / 4) * (Na * Na / 2).log()) * arb(2).log()).exp()
    hi = _tailint(Na / 2, Na, (1 + y) / 2 + (t / 2) * Na.log(), t / 4) + _tailint(
        Na / 2, Na, (1 - y) / 2 + (t / 2) * Na.log(), t / 4
    ) / Ny
    return 2 - (1 - modb2) * S1 - 2 * modb2 * hi, modb2


def euler2_section(y_label: str) -> dict:
    out: dict = {"y0_label": y_label}
    with ef.workprec(ef.PREC):
        X = arb(X_INT)
        t0 = arb(T0)
        y0 = arb("0.028").sqrt() if y_label == "sqrt(0.028)" else arb(y_label)
        N0 = ef.N_of(X, t0)
        xN = ef.x_of_N(N0, t0)
        xN1 = ef.x_of_N(N0 + 1, t0)
        out["N0"] = N0
        out["X_in_N0_interval"] = bool(X >= xN and X < xN1)
        out["x_N0"] = ball(xN, 18)
        out["x_N0_plus_1"] = ball(xN1, 18)
        sp = acb(1 + y0, -X) / 2
        sm = acb(1 - y0, X) / 2
        sig_pt = (sp + (t0 / 2) * ef.alpha(sp)).real
        g_pt = abs((ef.log_Mt(sm, t0) - ef.log_Mt(sp, t0)).exp())
        k_pt = abs((t0 / 2) * (ef.alpha(sm) - ef.alpha(acb(1 + y0, X) / 2)))
        xs = xN.union(xN1)
        spr = acb(1 + y0, -xs) / 2
        sig_rng = (spr + (t0 / 2) * ef.alpha(spr)).real
        g_thm = (arb("0.02") * y0).exp() * (-(y0 / 2) * (xN / (4 * arb.pi())).log()).exp()
        k_thm = t0 * y0 / (2 * (xN - 6))
    variants = {}
    for name, sig, g, k in (("point", sig_pt, g_pt, k_pt), ("uniform", sig_rng, g_thm, k_thm)):
        t1 = time.perf_counter()
        r = ef.euler2_lower_bound(N0, T0, y0, sig, g, k)
        with ef.workprec(ef.PREC):
            numer = r["LB_beta"] - g * r["UB_alpha"] - (1 + r["r"]) * r["Z"]
        variants[name] = {
            "sigma": ball(sig, 18), "gamma_abs": ball(g, 18), "kappa_abs": ball(k, 6),
            "r_abs_b2_2pow_minus_sigma": ball(r["r"], 12),
            "S_b": ball(r["S_b"], 14), "S_b_hi": ball(r["S_b_hi"], 14),
            "S_a": ball(r["S_a"], 14), "S_a_hi": ball(r["S_a_hi"], 14),
            "LB_beta": ball(r["LB_beta"], 14), "UB_alpha": ball(r["UB_alpha"], 14), "Z": ball(r["Z"], 6),
            "trib2_numerator_bounds_abs_E2_f": ball(numer, 12),
            "bound_abs_f_joint": ball(r["joint"], 12),
            "bound_abs_f_separate": ball(r["separate"], 12),
            "bound_abs_f_unmollified": ball(r["trivial"], 12),
            "seconds": round(time.perf_counter() - t1, 2),
        }
    with ef.workprec(ef.PREC):
        t1 = time.perf_counter()
        pm, modb2 = polymath_moll2_analytic(N0, y0, t0)
        variants["polymath_moll2_analytic"] = {
            "value_bounds_abs_E2_f_approximately": ball(pm, 12),
            "modb2": ball(modb2, 12),
            "divided_by_1_plus_modb2": ball(pm / (1 + modb2), 12),
            "seconds": round(time.perf_counter() - t1, 2),
            "note": "uses N^-y for |gamma| and integral majorants of the tails; not a rigorous bound as written",
        }
    out["variants"] = variants
    return out


def point_section() -> dict:
    t1 = time.perf_counter()
    P = ef.point(str(X_INT), Y0_PRINTED, T0, error_mode="exact")
    sec = time.perf_counter() - t1
    tb = ef.theorem_bounds(P)
    with ef.workprec(P.prec):
        b2 = ((P.t / 4) * arb(2).log() ** 2).exp()
        E2 = 1 - b2 * (-P.s_star * arb(2).log()).exp()
        abs_E2f = abs(E2 * P.f)
        ratio = P.ratio_ABC()
    return {
        "x": str(X_INT), "y": Y0_PRINTED, "t": T0, "N": P.N, "prec_bits": P.prec,
        "f": cball(P.f), "C_over_B": cball(P.CB),
        "e_A": ball(P.e_A, 8), "e_B": ball(P.e_B, 8), "e_C": ball(P.e_C, 8), "e_C0": ball(P.e_C0, 8),
        "gamma_abs": ball(abs(P.gamma), 15), "Re_s_star": ball(P.s_star.real, 15), "kappa_abs": ball(abs(P.kappa), 6),
        "theorem_eAB_upper": ball(tb["eAB_upper"], 6), "theorem_eC0_upper": ball(tb["eC0_upper_thm"], 6),
        "abs_E2_times_f": ball(abs_E2f, 12),
        "ratio_ABC_enclosure_of_Ht_over_Bt": cball(ratio, 12),
        "seconds_direct_evaluation": round(sec, 2),
    }


def rect_section(t: str, initial: int) -> dict:
    t1 = time.perf_counter()
    r = ef.barrier_rectangle(str(X_INT), str(X_INT + 1), Y0_PRINTED, "1", t, initial_per_edge=initial)
    sec = time.perf_counter() - t1
    return {
        "rectangle": [str(X_INT), str(X_INT + 1), Y0_PRINTED, "1"], "t": t, "N": r["N"],
        "winding": r["winding"],
        "winding_ball": ball(r["winding_ball"], 6) if r["winding_ball"] is not None else None,
        "n_evaluations": r["n_evaluations"], "n_segments": r["n_segments"], "n_failed": r["n_failed"],
        "E_upper": ball(r["E_upper"], 6), "eAB_upper": ball(r["eAB_upper"], 6), "eC0_upper": ball(r["eC0_upper"], 6),
        "Dz_bottom": ball(r["Dz_bottom"], 8), "Dz_top": ball(r["Dz_top"], 8), "Dt_bottom": ball(r["Dt_bottom"], 8),
        "min_abs_f_lower": ball(r["min_abs_f_lower"], 10), "min_margin": ball(r["min_margin"], 10),
        "blocks": r["blocks"], "n_head": r["n_head"], "K": r["K"], "prec_bits": r["prec"],
        "timings": {k: round(v, 2) for k, v in r["timings"].items()},
        "seconds_total": round(sec, 2),
    }


def polymath_reference() -> dict:
    """First and last rectangle lines of the project's own row-2 barrier log, as data."""
    if not POLYMATH_WINDNUM.exists():
        return {"available": False}
    raw = POLYMATH_WINDNUM.read_bytes()
    lines = raw.decode("utf-8", "replace").splitlines()
    rect = [ln for ln in lines if ln.startswith("Rectangle(")]
    return {
        "available": True,
        "path": "<cache>/dbn/" + str(POLYMATH_WINDNUM.relative_to(DBN_CACHE)),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "columns": "t, ceiling(ddt bound), ceiling(ddz bound), winding number, min mesh |(A+B)/B0|, mesh points",
        "n_rectangles": len(rect),
        "first": rect[0] if rect else None,
        "last": rect[-1] if rect else None,
        "summary_lines": [ln for ln in lines if "winding" in ln.lower() or "cpu" in ln.lower()],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(HERE / "row2_check.json"))
    ap.add_argument("--skip-zero-rect", action="store_true")
    ap.add_argument("--skip-t0-rect", action="store_true")
    args = ap.parse_args()
    t_start = time.perf_counter()
    out: dict = {
        "source": "arXiv:1904.12438v2 debruijn.tex line 1950 (Table 1 row 2)",
        "printed": {"X": "5e12 + 194858", "t0": T0, "y0": Y0_PRINTED, "Lambda": "0.20",
                    "winding": 0, "N0": N0_PRINTED, "lower_bound_column": PRINTED_BOUND},
        "grade": "Arb enclosures of the stated formulas (python-flint); the analytic inputs are the paper's "
                 "Theorem 1.3, Corollary 6.4 and Lemma 10.1 as published",
        "environment": {"python": sys.version.split()[0], "platform": platform.platform()},
    }
    try:
        out["loadavg_at_start"] = Path("/proc/loadavg").read_text().split()[:3]
    except OSError:
        pass
    out["euler2"] = [euler2_section(Y0_PRINTED), euler2_section("sqrt(0.028)")]
    print("euler2 done", flush=True)
    out["point"] = point_section()
    print("point done", flush=True)
    if not args.skip_t0_rect:
        out["rectangle_t0"] = rect_section(T0, initial=16)
        print("t0 rectangle done", flush=True)
    if not args.skip_zero_rect:
        out["rectangle_t_zero"] = rect_section("0", initial=64)
        print("t=0 rectangle done", flush=True)
    out["polymath_row2_barrier_log"] = polymath_reference()
    out["seconds_total"] = round(time.perf_counter() - t_start, 2)
    Path(args.out).write_text(json.dumps(out, indent=1) + "\n")
    print("wrote", args.out, flush=True)


if __name__ == "__main__":
    main()
