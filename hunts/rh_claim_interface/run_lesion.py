"""Lesion and decoy stages of hunt #161.

    .venv/bin/python -m hunts.rh_claim_interface.run_lesion lesion SCRATCH
    .venv/bin/python -m hunts.rh_claim_interface.run_lesion decoy

Lesion.  A synthetic quadruple beta + i gamma0, beta - i gamma0,
1 - beta + i gamma0, 1 - beta - i gamma0 is added to G through the zero-side
formula:

    Delta(y) = 2 Re[ y^rho / (rho (1 - rho)) ] + 2 Re[ y^rho' / (rho' (1 - rho')) ],
    rho = beta + i gamma0,  rho' = 1 - beta + i gamma0.

Two detectors are read: the RH envelope |G - log 2pi - T| <= c0 sqrt(y), and
the archive's interface inequality G(y) <= y^theta.  The base G is the prime
side on the integers up to Y_PRIME and the truncated zero side on a log grid
beyond.  This is a model computation.  It is not a proof of the windowed
lemma and says nothing about whether the archive's proof of it is sound.

Decoy.  The primes are replaced by a Cramer random set of the same density
and the same statistic is read.
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

BETAS = (0.6, 0.75, 0.9, 1.0)
GAMMAS = (10.0, 30.0, 100.0, 1000.0)
Y_PRIME = 10**7
LOG_Y_MODEL = math.log(1e30)
N_MODEL_ZEROS = 2000
WINDOW = 1.5


def _dump(name: str, obj) -> None:
    (HERE / name).write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n")


def lesion_delta(u: np.ndarray, beta: float, gamma0: float) -> np.ndarray:
    """Delta as a function of u = log y."""
    rho = complex(beta, gamma0)
    rho2 = complex(1.0 - beta, gamma0)
    c = 1.0 / (rho * (1.0 - rho))
    c2 = 1.0 / (rho2 * (1.0 - rho2))
    ph = np.exp(1j * gamma0 * u)
    return 2.0 * np.real(c * ph) * np.exp(beta * u) + 2.0 * np.real(c2 * ph) * np.exp((1.0 - beta) * u)


def thetas_for(beta: float) -> list[float]:
    return [0.5, round(0.5 + (beta - 0.5) / 2, 6), round(beta - 0.02, 6)]


def predicted_onset(beta: float, gamma0: float, theta: float) -> float:
    """Envelope crossing 2 y^beta / |rho(1-rho)| = y^theta, ignoring G itself."""
    rho = complex(beta, gamma0)
    return (abs(rho * (1 - rho)) / 2.0) ** (1.0 / (beta - theta))


def predicted_envelope_onset(beta: float, gamma0: float) -> float:
    """Envelope crossing 2 y^beta / |rho(1-rho)| = c0 sqrt(y)."""
    rho = complex(beta, gamma0)
    return (I.C0 * abs(rho * (1 - rho)) / 2.0) ** (1.0 / (beta - 0.5))


def first_true(mask: np.ndarray, x: np.ndarray):
    idx = np.nonzero(mask)[0]
    return None if len(idx) == 0 else float(x[idx[0]])


def window_report(viol: np.ndarray, u: np.ndarray, u_start: float) -> dict:
    """Which windows [Y, Y^1.5] with log Y >= u_start contain a violation."""
    cum = np.concatenate([[0], np.cumsum(viol.astype(np.int64))])
    top = u[-1] / WINDOW
    i_lo = int(np.searchsorted(u, u_start))
    i_hi = int(np.searchsorted(u, top, side="right"))
    if i_hi <= i_lo:
        return {"n_windows": 0}
    idx = np.arange(i_lo, i_hi)
    j = np.searchsorted(u, WINDOW * u[idx], side="right")
    has = (cum[j] - cum[idx]) > 0
    clean = np.nonzero(~has)[0]
    rep = {
        "n_windows": int(len(idx)),
        "n_windows_with_violation": int(has.sum()),
        "log10_Y_first_window": float(u[idx[0]] / math.log(10)),
        "log10_Y_last_window": float(u[idx[-1]] / math.log(10)),
    }
    if len(clean):
        rep["log10_last_clean_window_start"] = float(u[idx[clean[-1]]] / math.log(10))
        rep["every_window_has_violation"] = False
    else:
        rep["log10_last_clean_window_start"] = None
        rep["every_window_has_violation"] = True
    return rep


def stage_lesion(scratch: str) -> None:
    t0 = time.time()
    lesions = [(b, g) for b in BETAS for g in GAMMAS]

    # ---- (A) prime side on the integers, 2 <= n <= Y_PRIME -----------------
    first_env = {k: None for k in lesions}
    first_int = {(b, g, th): None for (b, g) in lesions for th in thetas_for(b)}
    control_env = None
    control_int_last = {0.5: 0, 0.6: 0, 0.75: 0}
    for n, e_arr, r_arr, _ in I.scan_integers(Y_PRIME, seg=1 << 21):
        gval = n * e_arr - r_arr
        u = np.log(n)
        sq = np.sqrt(n)
        base = gval - I.LOG_2PI - I.T_float(n)
        if control_env is None:
            control_env = first_true(np.abs(base) > I.C0 * sq, n)  # the control is read from n = 2
        for th in control_int_last:
            above = np.nonzero(gval > np.exp(th * u))[0]
            if len(above):
                control_int_last[th] = int(n[above[-1]])
        for b, g in lesions:
            need_env = first_env[(b, g)] is None
            need_int = [th for th in thetas_for(b) if first_int[(b, g, th)] is None]
            if not need_env and not need_int:
                continue
            d = lesion_delta(u, b, g)
            if need_env:
                first_env[(b, g)] = first_true((np.abs(base + d) > I.C0 * sq) & (n >= 10), n)
            for th in need_int:
                first_int[(b, g, th)] = first_true((gval + d > np.exp(th * u)) & (n >= 10), n)
    t_prime = time.time() - t0

    # ---- (B) zero-side model on a log grid up to 1e30 ----------------------
    gam, _ = Z.zeta_zero_ordinates(20000, prec=64, cache_dir=scratch)
    gam = gam[:N_MODEL_ZEROS]
    tail = Z.zeta_tail_budget(gam)
    du = 2e-4
    u = np.arange(math.log(10.0), LOG_Y_MODEL, du)
    w = Z.zeta_weights(gam)
    osc = np.empty_like(u)
    for i in range(0, len(u), 2048):
        osc[i : i + 2048] = np.cos(np.outer(u[i : i + 2048], gam)) @ w
    sq = np.exp(0.5 * u)
    y = np.exp(u)
    t_term = I.T_float(np.minimum(y, 1e150))
    g_model = sq * osc + I.LOG_2PI + t_term
    control_model = {
        "max_abs_F_model": float(np.max(np.abs(osc))),
        "any_envelope_violation": bool(np.any(np.abs(osc) > I.C0)),
        "any_interface_violation_theta_half": bool(np.any(g_model > sq)),
    }
    rows = []
    for b, g in lesions:
        d = lesion_delta(u, b, g)
        env_first_model = first_true(np.abs(sq * osc + d) > I.C0 * sq, y)
        row = {
            "beta": b,
            "gamma0": g,
            "envelope_first_y_prime_side": first_env[(b, g)],
            "envelope_first_y_model": env_first_model,
            "envelope_predicted_onset": predicted_envelope_onset(b, g),
            "thetas": [],
        }
        for th in thetas_for(b):
            viol = g_model + d > np.exp(th * u)
            y_first = first_true(viol, y)
            pred = predicted_onset(b, g, th)
            ent = {
                "theta": th,
                "first_y_prime_side": first_int[(b, g, th)],
                "first_y_model": y_first,
                "predicted_onset": pred,
            }
            if y_first is not None:
                u_first = math.log(y_first)
                after = np.nonzero(viol)[0]
                gaps = np.diff(u[after])
                ent["max_gap_between_violations_in_log_y"] = float(gaps.max()) if len(gaps) else None
                ent["period_2pi_over_gamma0"] = 2 * math.pi / g
                ent["windows_from_10"] = window_report(viol, u, math.log(10.0))
                ent["windows_from_onset_two_thirds"] = window_report(viol, u, u_first / WINDOW)
                ent["log10_first_y"] = u_first / math.log(10)
                ent["log10_onset_to_the_two_thirds"] = u_first / WINDOW / math.log(10)
            row["thetas"].append(ent)
        rows.append(row)

    # extrapolation by the closed form only (not a measurement)
    extrap = []
    for g in (1e6, 3e12):
        for b, th in ((1.0, 0.5), (0.75, 0.5), (0.6, 0.55), (0.51, 0.505)):
            extrap.append({"beta": b, "gamma0": g, "theta": th, "log10_predicted_onset": math.log10(abs(complex(b, g) * (1 - complex(b, g))) / 2.0) / (b - th)})

    out = {
        "lesion": "quadruple beta +- i gamma0, 1 - beta +- i gamma0 added through the zero-side formula",
        "detectors": {
            "envelope": "|G - log 2pi - T| > c0 sqrt(y), read from y >= 10",
            "interface": "G(y) > y^theta (the archive's form with C = 1), read from y >= 10",
        },
        "prime_side_reach": Y_PRIME,
        "model": {"n_zeros": N_MODEL_ZEROS, "tail_budget": tail, "log10_y_max": LOG_Y_MODEL / math.log(10), "du": du, "window_exponent": WINDOW},
        "control_no_lesion": {
            "prime_side_first_envelope_violation_n_ge_2": control_env,
            "prime_side_last_n_with_G_above_n_pow_theta": {str(k): v for k, v in control_int_last.items()},
            "model": control_model,
        },
        "rows": rows,
        "closed_form_extrapolation": extrap,
        "prime_side_s": round(t_prime, 1),
        "elapsed_s": round(time.time() - t0, 1),
    }
    _dump("lesion.json", out)
    print("control", out["control_no_lesion"])
    for r in rows:
        print(r["beta"], r["gamma0"], "env prime", r["envelope_first_y_prime_side"], "env model", r["envelope_first_y_model"], "pred", round(r["envelope_predicted_onset"], 1))
        for e in r["thetas"]:
            w10 = e.get("windows_from_10", {})
            w23 = e.get("windows_from_onset_two_thirds", {})
            print("    theta", e["theta"], "first prime", e["first_y_prime_side"], "model", e["first_y_model"], "pred %.3g" % e["predicted_onset"], "| clean-until log10 Y", w10.get("log10_last_clean_window_start"), "| from onset^(2/3):", w23.get("every_window_has_violation"), w23.get("n_windows"))
    print("elapsed", out["elapsed_s"])


# ---------------------------------------------------------------------------
# decoy
# ---------------------------------------------------------------------------


def stage_decoy(n_max: int = 10**6, n_seeds: int = 8) -> None:
    """Cramer random 'primes': each n >= 3 kept with probability 1/log n."""
    t0 = time.time()
    n = np.arange(2, n_max + 1, dtype=np.float64)
    logn = np.log(n)
    sq = np.sqrt(n)
    corr = I.LOG_2PI + I.T_float(n)
    rows = []
    for seed in range(n_seeds):
        rng = np.random.default_rng(1000 + seed)
        keep = rng.random(len(n)) < 1.0 / np.maximum(logn, 1.0)
        lam = np.where(keep, logn, 0.0)
        e = I.EULER_GAMMA + np.cumsum(lam / n + np.log1p(-1.0 / n))
        r = -1.0 + np.cumsum(lam - 1.0)
        gval = n * e - r
        f_raw = (gval - corr) / sq
        big = n >= 100
        # refit: remove the best linear term a*y + b by least squares on n >= 100
        A = np.vstack([n[big], np.ones(big.sum())]).T
        coef, *_ = np.linalg.lstsq(A, gval[big], rcond=None)
        f_fit = (gval[big] - A @ coef) / sq[big]
        rows.append(
            {
                "seed": 1000 + seed,
                "n_kept": int(keep.sum()),
                "sup_abs_F_raw_n_ge_100": float(np.max(np.abs(f_raw[big]))),
                "sup_abs_F_after_linear_refit_n_ge_100": float(np.max(np.abs(f_fit))),
                "fraction_n_ge_100_inside_c0_after_refit": float(np.mean(np.abs(f_fit) <= I.C0)),
            }
        )
    # the true primes through the same code path
    tr = []
    for nn, e_arr, r_arr, _ in I.scan_integers(n_max, seg=1 << 21):
        tr.append(np.abs(I.F_from_ER(nn, e_arr, r_arr))[nn >= 100])
    true_sup = float(np.max(np.concatenate(tr)))
    out = {
        "null": "Cramer set: each integer n >= 3 kept independently with probability 1/log n, weight log n",
        "n_max": n_max,
        "c0": I.C0,
        "true_primes_sup_abs_F_n_ge_100": true_sup,
        "decoy_min_sup_abs_F_raw": min(r["sup_abs_F_raw_n_ge_100"] for r in rows),
        "decoy_min_sup_abs_F_after_refit": min(r["sup_abs_F_after_linear_refit_n_ge_100"] for r in rows),
        "decoy_max_fraction_inside_after_refit": max(r["fraction_n_ge_100_inside_c0_after_refit"] for r in rows),
        "rows": rows,
        "elapsed_s": round(time.time() - t0, 1),
    }
    _dump("decoy.json", out)
    print(json.dumps({k: v for k, v in out.items() if k != "rows"}, indent=1))


def main(argv: list[str]) -> None:
    if argv[1] == "lesion":
        stage_lesion(argv[2])
    elif argv[1] == "decoy":
        stage_decoy()
    else:
        raise SystemExit("unknown stage")


if __name__ == "__main__":
    main(sys.argv)
