"""Rival stage of hunt #161: the standing counterexample battery.

    .venv/bin/python -m hunts.rh_claim_interface.run_rivals N_MAX

For the Davenport-Heilbronn function f_DH and for f_E = zeta_Q / 2 with
Q = (1, 1, 6) (discriminant -23, class number 3), this computes the Dirichlet
coefficients Lambda_f(n) of -f'/f by the convolution recursion

    a_n log n = sum_{d | n} Lambda_f(d) a_{n/d},       a_1 = 1,

forms the same smoothed sum as the interface,

    DH:       G_f(y) = sum_{n<=y} Lambda_f(n) (y/n - 1) + y f'/f(1)
    Epstein:  G_f(y) = sum_{n<=y} Lambda_f(n) (y/n - 1) - y log y + (1 + g0) y

(g0 is the constant in -f'/f(s) = 1/(s-1) - g0 + O(s-1); for zeta g0 = gamma),
and measures how it grows against the off-line zeros this lab already has on
record: 0.808517... + 85.699348...i for DH (`zeta.epstein.OFFLINE_ZERO_*`) and
0.953260... + 16.290215...i for the Epstein form
(`hunts/weil_propagation/numerics/epstein_offline.json`).

Everything here is float grade ("measured").
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np

from . import instrument as I

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]

DH_ZERO = (0.80851718245663738555, 85.699348485377592172)
EPSTEIN_FORM = (1, 1, 6)
EPSTEIN_ZERO = (0.953260474794661, 16.2902157203904)


def _dump(name: str, obj) -> None:
    (HERE / name).write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n")


# ---------------------------------------------------------------------------
# coefficients
# ---------------------------------------------------------------------------


def dh_kappa() -> float:
    from zeta.epstein import kappa

    return float(kappa(dps=30))


def dh_coefficients(n_max: int, kap: float | None = None) -> np.ndarray:
    """a_n of the Davenport-Heilbronn function: period 5, values 1, k, -k, -1, 0."""
    if kap is None:
        kap = dh_kappa()
    pattern = np.array([0.0, 1.0, kap, -kap, -1.0])
    return pattern[np.arange(n_max + 1) % 5]


def epstein_coefficients(n_max: int, form=EPSTEIN_FORM) -> np.ndarray:
    """a_n = r_Q(n) / r_Q(1) for a positive definite form with r_Q(1) != 0."""
    a, b, c = form
    disc = 4 * a * c - b * b
    kmax = math.isqrt(4 * a * n_max // disc) + 1
    vals = []
    for k in range(-kmax, kmax + 1):
        # a m^2 + b k m + c k^2 <= n_max
        dd = b * b * k * k - 4 * a * (c * k * k - n_max)
        if dd < 0:
            continue
        root = math.sqrt(dd)
        m_lo = math.ceil((-b * k - root) / (2 * a)) - 1
        m_hi = math.floor((-b * k + root) / (2 * a)) + 1
        m = np.arange(m_lo, m_hi + 1, dtype=np.int64)
        v = a * m * m + b * k * m + c * k * k
        v = v[(v >= 1) & (v <= n_max)]
        vals.append(v)
    r = np.bincount(np.concatenate(vals), minlength=n_max + 1).astype(np.float64)
    if r[1] == 0:
        raise ValueError("the form does not represent 1: no log-derivative series with a_1 = 1")
    return r / r[1]


def log_derivative_coefficients(a: np.ndarray) -> np.ndarray:
    """Lambda_f(n) for n <= len(a) - 1 by the convolution recursion (float64)."""
    n_max = len(a) - 1
    if a[1] != 1.0:
        raise ValueError("normalise a_1 = 1 first")
    n = np.arange(n_max + 1, dtype=np.float64)
    n[0] = 1.0
    lam = a * np.log(n)
    lam[0] = 0.0
    lam[1] = 0.0
    for d in range(2, n_max // 2 + 1):
        ld = lam[d]
        if ld != 0.0:
            m = n_max // d
            lam[2 * d : m * d + 1 : d] -= ld * a[2 : m + 1]
    return lam


def prime_power_mask(n_max: int) -> np.ndarray:
    mask = np.zeros(n_max + 1, dtype=bool)
    for pk, _ in I.prime_powers_upto(n_max):
        mask[pk] = True
    return mask


# ---------------------------------------------------------------------------
# constants of the rivals
# ---------------------------------------------------------------------------


def dh_logderiv_at_one(dps: int = 30) -> dict:
    """f'/f(1) for DH: mpmath on the lab's dh_f, and python-flint on the L-function combination."""
    from mpmath import mp

    from zeta.epstein import dh_f, kappa

    with mp.workdps(dps + 10):
        h = mp.mpf(10) ** (-6)

        def fm(s):
            return dh_f(s, dps=dps + 10)

        f1 = fm(mp.mpf(1))
        d1 = (-fm(1 + 2 * h) + 8 * fm(1 + h) - 8 * fm(1 - h) + fm(1 - 2 * h)) / (12 * h)
        val_mp = d1 / f1
        kap = kappa(dps=dps + 10)
        kap_s = mp.nstr(kap, dps + 5)
    from flint import acb, acb_series, arb, ctx, dirichlet_char

    old_p, old_c = ctx.prec, ctx.cap
    ctx.prec = 160
    ctx.cap = 3
    try:
        k = arb(kap_s)
        c1 = acb(arb(1) / 2, -k / 2)
        c2 = acb(arb(1) / 2, k / 2)
        s1 = acb_series.dirichlet_l(acb_series([1, 1]), dirichlet_char(5, 2))
        s2 = acb_series.dirichlet_l(acb_series([1, 1]), dirichlet_char(5, 3))
        f = c1 * s1[0] + c2 * s2[0]
        fp = c1 * s1[1] + c2 * s2[1]
        val_fl = fp / f
        out = {
            "mpmath_re": float(mp.re(val_mp)),
            "mpmath_im": float(mp.im(val_mp)),
            "flint_re": float(val_fl.real.mid()),
            "flint_im": float(val_fl.imag.mid()),
            "f_at_1": float(f.real.mid()),
        }
    finally:
        ctx.prec, ctx.cap = old_p, old_c
    out["abs_diff"] = abs(complex(out["mpmath_re"], out["mpmath_im"]) - complex(out["flint_re"], out["flint_im"]))
    return out


def epstein_g0(form=EPSTEIN_FORM, dps: int = 30) -> dict:
    """g0 = R'(1)/R(1) for R(s) = (s-1) zeta_Q(s): finite differences and the Kronecker limit formula."""
    from mpmath import mp

    from zeta.epstein import epstein_zeta

    a, b, c = form
    disc = 4 * a * c - b * b
    with mp.workdps(dps + 15):
        h = mp.mpf(10) ** (-6)

        def big_r(s):
            return (s - 1) * epstein_zeta(s, form, dps=dps + 15)

        rp2, rp1, rm1, rm2 = big_r(1 + 2 * h), big_r(1 + h), big_r(1 - h), big_r(1 - 2 * h)
        deriv = (-rp2 + 8 * rp1 - 8 * rm1 + rm2) / (12 * h)
        r1 = (-rp2 + 4 * rp1 + 4 * rm1 - rm2) / 6
        g0_fd = mp.re(deriv / r1)
        # Kronecker: g0 = 2 gamma - log(2 sqrt|D|) - log(y) - 4 log|eta(tau)|, tau = (-b + i sqrt|D|)/(2a), y = Im tau
        tau = mp.mpc(-b, mp.sqrt(disc)) / (2 * a)
        y = mp.im(tau)
        q = mp.exp(2j * mp.pi * tau)
        eta = mp.exp(2j * mp.pi * tau / 24) * mp.qp(q)
        g0_k = 2 * mp.euler - mp.log(2 * mp.sqrt(disc)) - mp.log(y) - 4 * mp.log(abs(eta))
        res = mp.re(r1)
        return {
            "g0_finite_difference": float(g0_fd),
            "g0_kronecker": float(g0_k),
            "abs_diff": float(abs(g0_fd - g0_k)),
            "residue": float(res),
            "residue_expected_2pi_over_sqrt_disc_times_w": float(2 * mp.pi / mp.sqrt(disc)),
        }


# ---------------------------------------------------------------------------
# analysis
# ---------------------------------------------------------------------------


def smoothed_sum(lam: np.ndarray, lin: float, with_pole: bool) -> np.ndarray:
    """G_f(n) for n = 0..N (entries 0 and 1 set by the formula at y = 1).

    DH (no pole):  G_f(n) = n (A_f(n) + lin) - psi_f(n),  lin = f'/f(1).
    Pole at 1:     G_f(n) = n (A_f(n) - log n + lin) - (psi_f(n) - n),  lin = g0.
    """
    n_max = len(lam) - 1
    n = np.arange(n_max + 1, dtype=np.float64)
    n[0] = 1.0
    if with_pole:
        d_e = lam / n + np.concatenate([[0.0, 0.0], np.log1p(-1.0 / n[2:])])
        e = lin + np.cumsum(d_e, dtype=np.longdouble)
        r = np.cumsum(lam - 1.0, dtype=np.longdouble) + 1.0  # psi(n) - n, with the n = 0 slot undone
        g = (n * e - r).astype(np.float64)
    else:
        e = lin + np.cumsum(lam / n, dtype=np.longdouble)
        r = np.cumsum(lam, dtype=np.longdouble)
        g = (n * e - r).astype(np.float64)
    g[0] = 0.0
    return g


def _hann_decade(k: int, n_top: int):
    """n and the weight h(n)/n on [10^k, 10^(k+1)), h a Hann window in log n."""
    a, b = 10**k, min(10 ** (k + 1), n_top)
    n = np.arange(a, b, dtype=np.float64)
    x = (np.log(n) - math.log(a)) / math.log(10.0)
    return a, b, n, (0.5 - 0.5 * np.cos(2 * math.pi * x)) / n


def demodulate(resid: np.ndarray, gamma: float, k_lo: int, k_hi: int) -> list[float]:
    """|sum resid(n) n^(-i gamma) w(n)| / sum w(n) per decade, w = Hann in log n over n.

    A term c n^(beta + i gamma) in `resid` gives |c| times a weighted mean of
    n^beta, which scales by exactly 10^beta from one decade to the next.  The
    Hann window has spectral half-width 4 pi / log 10 = 5.5 in gamma.
    """
    out = []
    for k in range(k_lo, k_hi):
        a, b, n, w = _hann_decade(k, len(resid))
        ph = np.exp(-1j * gamma * np.log(n))
        out.append(float(abs(np.sum(resid[a:b] * ph * w)) / np.sum(w)))
    return out


def amplitude_from_demod(value: float, beta: float, k: int, n_top: int) -> float:
    """Invert `demodulate` for |c| in the decade k, given beta."""
    a, b, n, w = _hann_decade(k, n_top)
    return value * float(np.sum(w)) / float(np.sum(n**beta * w))


def decade_sup(values: np.ndarray, k_lo: int, k_hi: int) -> list[float]:
    return [float(np.max(np.abs(values[10**k : min(10 ** (k + 1), len(values))]))) for k in range(k_lo, k_hi)]


def slopes(vals: list[float]) -> list[float]:
    return [math.log10(vals[i + 1] / vals[i]) for i in range(len(vals) - 1)]


def coefficient_report(lam: np.ndarray, ppm: np.ndarray) -> dict:
    n_max = len(lam) - 1
    nz = np.abs(lam) > 1e-9
    off = nz & ~ppm
    off[:2] = False
    first_off = int(np.nonzero(off)[0][0]) if off.any() else None
    cum = np.cumsum(np.abs(lam))
    ks = list(range(2, int(round(math.log10(n_max))) + 1))
    growth = [math.log10(cum[10**k] / cum[10 ** (k - 1)]) for k in ks[1:]]
    logn = np.log(np.maximum(np.arange(n_max + 1), 2))
    return {
        "n_max": n_max,
        "count_nonzero": int(nz.sum()),
        "count_nonzero_off_prime_powers": int(off.sum()),
        "first_n_off_prime_powers": first_off,
        "lambda_at_first_off": float(lam[first_off]) if first_off else None,
        "count_negative": int((lam < -1e-9).sum()),
        "min_lambda": float(lam.min()),
        "argmin_lambda": int(lam.argmin()),
        "max_abs_lambda_over_log_n": float(np.max(np.abs(lam[2:]) / logn[2:])),
        "argmax_abs_lambda_over_log_n": int(np.argmax(np.abs(lam[2:]) / logn[2:]) + 2),
        "decade_slopes_of_sum_abs_lambda": growth,
    }


def interface_windows(g: np.ndarray, theta: float, y_lo: int = 10, window: float = 1.5) -> dict:
    """Where G_f(n) > n^theta, and which windows [Y, Y^1.5] inside the range contain such an n."""
    n_max = len(g) - 1
    n = np.arange(n_max + 1, dtype=np.float64)
    viol = np.zeros(n_max + 1, dtype=bool)
    viol[y_lo:] = g[y_lo:] > n[y_lo:] ** theta
    idx = np.nonzero(viol)[0]
    cum = np.concatenate([[0], np.cumsum(viol.astype(np.int64))])
    top = int(math.floor(n_max ** (1.0 / window)))
    ys = np.arange(y_lo, top + 1)
    hi = np.minimum(np.floor(ys.astype(np.float64) ** window).astype(np.int64), n_max)
    has = (cum[hi + 1] - cum[ys]) > 0
    clean = np.nonzero(~has)[0]
    return {
        "theta": theta,
        "n_violations": int(len(idx)),
        "first_violation": int(idx[0]) if len(idx) else None,
        "last_violation": int(idx[-1]) if len(idx) else None,
        "n_windows": int(len(ys)),
        "n_windows_with_violation": int(has.sum()),
        "last_clean_window_start": int(ys[clean[-1]]) if len(clean) else None,
        "largest_window_start": int(top),
    }


def stage_rivals(n_max: int) -> None:
    t0 = time.time()
    ppm = prime_power_mask(n_max)
    kmax = int(round(math.log10(n_max)))
    out: dict = {"n_max": n_max}

    # ---- zeta through the same code path (control) -------------------------
    lam_z = I.lambda_segment(0, n_max + 1, I.small_primes(math.isqrt(n_max) + 2))
    a_z = np.ones(n_max + 1)
    a_z[0] = 0.0
    n_ctrl = min(n_max, 10**6)
    lam_rec = log_derivative_coefficients(a_z[: n_ctrl + 1])
    g_z = smoothed_sum(lam_z, I.EULER_GAMMA, with_pole=True)
    sup_z = decade_sup(g_z, 2, kmax)
    out["zeta_control"] = {
        "recursion_reproduces_von_mangoldt_max_abs_diff": float(np.max(np.abs(lam_rec - lam_z[: n_ctrl + 1]))),
        "recursion_checked_to": n_ctrl,
        "coefficients": coefficient_report(lam_z, ppm),
        "decade_sup_abs_G": sup_z,
        "decade_slopes_of_sup": slopes(sup_z),
        "demod_at_gamma1": demodulate(g_z, 14.134725141734693, 2, kmax),
    }
    out["zeta_control"]["demod_slopes_at_gamma1"] = slopes(out["zeta_control"]["demod_at_gamma1"])

    # ---- Davenport-Heilbronn ------------------------------------------------
    kap = dh_kappa()
    a_dh = dh_coefficients(n_max, kap)
    lam_dh = log_derivative_coefficients(a_dh)
    ld = dh_logderiv_at_one()
    g_dh = smoothed_sum(lam_dh, ld["flint_re"], with_pole=False)
    on = json.loads((REPO / "data" / "dh_zeros_online_T120.json").read_text())
    gam_on = np.array(on["zeros"], dtype=np.float64)
    n = np.arange(n_max + 1, dtype=np.float64)
    n[0] = 1.0
    logn = np.log(n)
    model_on = np.zeros(n_max + 1)
    for gj in gam_on:
        model_on += 2.0 * np.cos(gj * logn) / (0.25 + gj * gj)
    model_on *= np.sqrt(n)
    resid_dh = g_dh - model_on
    beta, gamma = DH_ZERO
    rho = complex(beta, gamma)
    amp_true = 1.0 / abs(rho * (1 - rho))
    dem = demodulate(resid_dh, gamma, 3, kmax)
    dem_raw = demodulate(g_dh, gamma, 3, kmax)
    dem_lo = demodulate(resid_dh, gamma - 8.0, 3, kmax)
    dem_hi = demodulate(resid_dh, gamma + 8.0, 3, kmax)
    k_top = kmax - 1
    amp_hat = amplitude_from_demod(dem[-1], beta, k_top, n_max + 1)
    sup_dh = decade_sup(g_dh, 2, kmax)
    # mpmath cross-check of the recursion on a short prefix
    from mpmath import mp

    from zeta.epstein import dh_coefficient, log_derivative_coefficients as lab_ldc

    lab = lab_ldc(lambda m: dh_coefficient(m, dps=25), 240, dps=25)
    rec_diff = max(abs(float(lab[m]) - lam_dh[m]) for m in range(1, 241))
    out["davenport_heilbronn"] = {
        "kappa": kap,
        "logderiv_at_1": ld,
        "lambda_6": float(lam_dh[6]),
        "lambda_6_closed_form_(1+kappa^2)log6": (1 + kap * kap) * math.log(6),
        "recursion_vs_lab_mpmath_max_abs_diff_n_le_240": rec_diff,
        "coefficients": coefficient_report(lam_dh, ppm),
        "known_zero": {"beta": beta, "gamma": gamma, "source": "zeta.epstein.OFFLINE_ZERO_RE/IM"},
        "n_online_zeros_subtracted": int(len(gam_on)),
        "decade_sup_abs_G": sup_dh,
        "decade_slopes_of_sup": slopes(sup_dh),
        "demod_at_known_zero": dem,
        "demod_slopes_at_known_zero": slopes(dem),
        "demod_without_subtracting_line_zeros": dem_raw,
        "demod_at_gamma_minus_8": dem_lo,
        "demod_at_gamma_plus_8": dem_hi,
        "amplitude_hat_top_decade": amp_hat,
        "amplitude_from_residue_1_over_abs_rho_1_minus_rho": amp_true,
        "interface": [interface_windows(g_dh, th) for th in (0.5, 0.6, 0.75)],
        "predicted_first_violation_theta_0.6": (abs(rho * (1 - rho)) / 2) ** (1 / (beta - 0.6)),
    }
    del model_on, resid_dh, a_dh

    # ---- Epstein (1, 1, 6) --------------------------------------------------
    from zeta.epstein import epstein_representation_count

    a_e = epstein_coefficients(n_max)
    r_check = max(abs(2 * a_e[m] - epstein_representation_count(m, EPSTEIN_FORM)) for m in range(1, 301))
    lam_e = log_derivative_coefficients(a_e)
    g0 = epstein_g0()
    g_e = smoothed_sum(lam_e, g0["g0_kronecker"], with_pole=True)
    beta, gamma = EPSTEIN_ZERO
    rho = complex(beta, gamma)
    amp_true = 1.0 / abs(rho * (1 - rho))
    dem = demodulate(g_e, gamma, 3, kmax)
    dem_lo = demodulate(g_e, gamma - 8.0, 3, kmax)
    dem_hi = demodulate(g_e, gamma + 8.0, 3, kmax)
    amp_hat = amplitude_from_demod(dem[-1], beta, k_top, n_max + 1)
    sup_e = decade_sup(g_e, 2, kmax)
    out["epstein_1_1_6"] = {
        "discriminant": -23,
        "class_number": 3,
        "representation_counts_vs_lab_max_abs_diff_n_le_300": float(r_check),
        "a_2_a_3_a_6": [float(a_e[2]), float(a_e[3]), float(a_e[6])],
        "lambda_6": float(lam_e[6]),
        "lambda_6_closed_form_2log6": 2 * math.log(6),
        "g0": g0,
        "coefficients": coefficient_report(lam_e, ppm),
        "known_zero": {"beta": beta, "gamma": gamma, "source": "hunts/weil_propagation/numerics/epstein_offline.json (measured, dps 20)"},
        "decade_sup_abs_G": sup_e,
        "decade_slopes_of_sup": slopes(sup_e),
        "demod_at_known_zero": dem,
        "demod_slopes_at_known_zero": slopes(dem),
        "demod_at_gamma_minus_8": dem_lo,
        "demod_at_gamma_plus_8": dem_hi,
        "amplitude_hat_top_decade": amp_hat,
        "amplitude_from_residue_1_over_abs_rho_1_minus_rho": amp_true,
        "interface": [interface_windows(g_e, th) for th in (0.5, 0.55, 0.6, 0.75)],
        "predicted_first_violation": {str(th): (abs(rho * (1 - rho)) / 2) ** (1 / (beta - th)) for th in (0.5, 0.55, 0.6, 0.75)},
    }
    out["zeta_control"]["interface"] = [interface_windows(g_z, th) for th in (0.5, 0.55, 0.6, 0.75)]
    out["elapsed_s"] = round(time.time() - t0, 1)
    _dump("rivals.json", out)
    z, d, e = out["zeta_control"], out["davenport_heilbronn"], out["epstein_1_1_6"]
    print("zeta  recursion diff", z["recursion_reproduces_von_mangoldt_max_abs_diff"], "sup slopes", [round(x, 3) for x in z["decade_slopes_of_sup"]], "demod slopes", [round(x, 3) for x in z["demod_slopes_at_gamma1"]])
    print("DH    lam6", d["lambda_6"], d["lambda_6_closed_form_(1+kappa^2)log6"], "rec diff", d["recursion_vs_lab_mpmath_max_abs_diff_n_le_240"], "ld", ld)
    print("DH    coeff", d["coefficients"])
    print("DH    sup slopes", [round(x, 3) for x in d["decade_slopes_of_sup"]], "demod", d["demod_at_known_zero"], "slopes", [round(x, 3) for x in d["demod_slopes_at_known_zero"]])
    print("DH    decoy freq", d["demod_at_gamma_minus_8"], d["demod_at_gamma_plus_8"], "amp", d["amplitude_hat_top_decade"], d["amplitude_from_residue_1_over_abs_rho_1_minus_rho"])
    print("DH    interface", d["interface"])
    print("EPS   r check", e["representation_counts_vs_lab_max_abs_diff_n_le_300"], "lam6", e["lambda_6"], "g0", g0)
    print("EPS   coeff", e["coefficients"])
    print("EPS   sup slopes", [round(x, 3) for x in e["decade_slopes_of_sup"]], "demod", e["demod_at_known_zero"], "slopes", [round(x, 3) for x in e["demod_slopes_at_known_zero"]])
    print("EPS   decoy freq", e["demod_at_gamma_minus_8"], e["demod_at_gamma_plus_8"], "amp", e["amplitude_hat_top_decade"], e["amplitude_from_residue_1_over_abs_rho_1_minus_rho"])
    print("EPS   interface", e["interface"], e["predicted_first_violation"])
    print("zeta  interface", z["interface"])
    print("elapsed", out["elapsed_s"])


if __name__ == "__main__":
    stage_rivals(int(float(sys.argv[1])))
