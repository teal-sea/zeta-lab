"""Approach-curve, conditioning and comparison analysis of the ladder run.

Reads results/ladder.json (+ coeffs files), writes results/analysis.json and
results/approach_curve.png. Grade: measured; the d_N^2 inputs carry balls,
every fit here is a least-squares fit to midpoints (radii ~1e-50, far below
fit residuals, so they play no role).

Run: .venv/bin/python analyze.py
"""

from __future__ import annotations

import json
import sys
from math import log, sqrt
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
REPO = HERE.parents[2]

C = 0.046191417932242067628620495813


def fit_curve(Ns, es, order: int, fix_C: bool):
    """Fit e = A + B/logN (+ D/log^2 N); optionally fix A = C."""
    x = 1.0 / np.log(Ns)
    if fix_C:
        y = es - C
        cols = [x] if order == 1 else [x, x**2]
        M = np.vstack(cols).T
        coef, res, *_ = np.linalg.lstsq(M, y, rcond=None)
        pred = C + M @ coef
        return {"A": C, "fixed": True, "coef": coef.tolist(),
                "rms": float(np.sqrt(np.mean((pred - es) ** 2)))}
    cols = [np.ones_like(x), x] if order == 1 else [np.ones_like(x), x, x**2]
    M = np.vstack(cols).T
    coef, res, *_ = np.linalg.lstsq(M, y := es, rcond=None)
    pred = M @ coef
    return {"A": float(coef[0]), "fixed": False, "coef": coef[1:].tolist(),
            "rms": float(np.sqrt(np.mean((pred - es) ** 2)))}


def main() -> None:
    data = json.loads((HERE / "results" / "ladder.json").read_text())
    recs = [r for r in data["records"] if "d2" in r]
    supp_path = HERE / "results" / "ladder_supplement.json"
    if supp_path.exists():
        supp = json.loads(supp_path.read_text())["records"]
        have = {r["N"] for r in recs}
        recs += [r for r in supp if r["N"] not in have]
        recs.sort(key=lambda r: r["N"])
    out: dict = {"C": C}

    # main table
    table = []
    for r in recs:
        N = r["N"]
        row = {
            "N": N,
            "d2_ball": r["d2"]["ball"],
            "d2_mid": r["d2"]["mid"],
            "d2_rad": r["d2"]["rad"],
            "headline_prec": r["headline_prec"],
            "cond_float64": r.get("cond_float64"),
        }
        if N > 1:
            row["d2_logN"] = r["d2_logN"]["mid"]
            row["ratio_to_C"] = r["d2_logN_over_C"]["mid"]
            row["dN_sqrt_logN"] = sqrt(r["d2"]["mid"] * log(N))
            if "bcf_upper" in r:
                row["bcf_upper_logN"] = r["bcf_upper_logN"]["mid"]
                row["bcf_over_d2"] = r["bcf_upper"]["mid"] / r["d2"]["mid"]
        table.append(row)
    out["table"] = table

    # approach-curve fits on every point with N > 1 (powers of two plus
    # the supplement; least squares needs no even spacing)
    pts = [(r["N"], r["d2_logN"]["mid"]) for r in recs if r["N"] > 1]
    Ns = np.array([p[0] for p in pts], dtype=float)
    es = np.array([p[1] for p in pts])
    fits = {}
    for tail_from in (64, 256):
        m = Ns >= tail_from
        if m.sum() >= 3:
            fits[f"free_linear_N>={tail_from}"] = fit_curve(Ns[m], es[m], 1, False)
            fits[f"fixedC_linear_N>={tail_from}"] = fit_curve(Ns[m], es[m], 1, True)
        if m.sum() >= 4:
            fits[f"free_quadratic_N>={tail_from}"] = fit_curve(Ns[m], es[m], 2, False)
            fits[f"fixedC_quadratic_N>={tail_from}"] = fit_curve(Ns[m], es[m], 2, True)
    out["fits"] = fits

    # conditioning power law
    cN = [(r["N"], r["cond_float64"]) for r in recs
          if r.get("cond_float64") and r["N"] >= 8]
    lN = np.log([c[0] for c in cN])
    lc = np.log([c[1] for c in cN])
    slope, intercept = np.polyfit(lN, lc, 1)
    out["conditioning"] = {
        "pairs": cN,
        "power_law_exponent": float(slope),
        "prefactor": float(np.exp(intercept)),
    }

    # solve-precision curve: radius of d2 vs solve precision
    prec_curve = []
    for r in recs:
        for s in r.get("solves", []):
            if s.get("ok"):
                prec_curve.append({"N": r["N"], "prec": s["prec"],
                                   "d2_rad": s["d2_rad"], "t_solve": s["t_solve"]})
    out["solve_precision_curve"] = prec_curve

    # coefficient shape vs -mu(k)(1 - log k/log N) at the largest N
    from vasyunin import mobius_sieve
    largest = max(r["N"] for r in recs)
    cf = HERE / "results" / f"coeffs_N{largest}.json"
    if cf.exists():
        xm = np.array(json.loads(cf.read_text())["x_mid"])
        N = largest
        mu = mobius_sieve(N)[1:].astype(float)
        ks = np.arange(1, N + 1, dtype=float)
        model = -mu * (1 - np.log(ks) / np.log(N))
        denom = float(np.linalg.norm(xm) * np.linalg.norm(model))
        out["coeff_shape"] = {
            "N": N,
            "x1": float(xm[0]),
            "model_x1": float(model[0]),
            "cosine_similarity": float(xm @ model / denom) if denom else None,
            "max_abs_x": float(np.abs(xm).max()),
            "rms_diff": float(np.sqrt(np.mean((xm - model) ** 2))),
        }

    # repo comparison: the BBLS L^2(0,1) basis (different quadratic form)
    try:
        sys.path.insert(0, str(REPO))
        from zeta.criteria import baez_duarte_d2
        repo_cmp = []
        for N in (40, 50):
            mine = next((r for r in recs if r["N"] == N), None)
            if mine is None:
                continue
            rr = baez_duarte_d2(N, dps=50, use_cache=True, with_condition=False)
            repo_cmp.append({
                "N": N,
                "repo_L2_01_d2": float(rr["d2"]),
                "repo_ratio_to_C": float(rr["d2"]) * log(N) / C,
                "mine_L2_0inf_d2": mine["d2"]["mid"],
                "mine_ratio_to_C": mine["d2_logN_over_C"]["mid"],
            })
        out["repo_comparison"] = repo_cmp
    except Exception as exc:  # pragma: no cover
        out["repo_comparison_error"] = repr(exc)

    # external anchors (Landreau-Richard)
    anchors = {}
    for N in (2048, 4096):
        r = next((x for x in recs if x["N"] == N), None)
        if r:
            dN = sqrt(r["d2"]["mid"])
            anchors[str(N)] = {
                "d_N": dN,
                "in_LR_window_0.07_0.08": bool(0.07 <= dN <= 0.08),
                "dN_sqrt_logN": dN * sqrt(log(N)),
            }
    anchors["LR_fit_aN_20000"] = 0.21377
    anchors["sqrt_C"] = sqrt(C)
    out["external_anchors"] = anchors

    (HERE / "results" / "analysis.json").write_text(json.dumps(out, indent=1))

    # figure
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        fig, axes = plt.subplots(1, 2, figsize=(11, 4.2))
        ax = axes[0]
        x = 1.0 / np.log(Ns)
        ax.plot(x, es, "o-", label=r"$d_N^2 \log N$ (enclosure-checked)")
        bcf = [(r["N"], r["bcf_upper_logN"]["mid"]) for r in recs
               if r["N"] > 1 and "bcf_upper_logN" in r
               and (r["N"] & (r["N"] - 1)) == 0]
        ax.plot([1 / log(n) for n, _ in bcf], [v for _, v in bcf], "s--",
                label=r"BCF vector $\times \log N$ (upper bound)")
        ax.axhline(C, color="k", lw=1, ls=":", label=f"C = {C:.10f}")
        fk = fits.get("fixedC_linear_N>=64")
        if fk:
            xs = np.linspace(0, x.max(), 100)
            ax.plot(xs, C + fk["coef"][0] * xs, "-", lw=0.8, alpha=0.7,
                    label=f"C + {fk['coef'][0]:.3f}/log N")
        ax.set_xlabel(r"$1/\log N$")
        ax.set_ylabel(r"$d_N^2 \log N$")
        ax.set_ylim(0, max(es.max(), 0.3) * 1.1)
        ax.legend(fontsize=8)
        ax.set_title("Approach to the BCF constant")

        ax = axes[1]
        cn = np.array([c[0] for c in cN])
        cv = np.array([c[1] for c in cN])
        ax.loglog(cn, cv, "o-")
        ax.loglog(cn, np.exp(intercept) * cn ** slope, "--",
                  label=f"~ N^{slope:.2f}")
        ax.set_xlabel("N")
        ax.set_ylabel("cond(G), float64 estimate")
        ax.legend(fontsize=8)
        ax.set_title("Gram conditioning")
        fig.tight_layout()
        fig.savefig(HERE / "results" / "approach_curve.png", dpi=140)
    except Exception as exc:  # pragma: no cover
        out["figure_error"] = repr(exc)

    # console summary
    print(json.dumps({k: out[k] for k in ("fits", "conditioning",
                                          "coeff_shape", "external_anchors",
                                          "repo_comparison") if k in out},
                     indent=1))
    print("written results/analysis.json")


if __name__ == "__main__":
    main()
