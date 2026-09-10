"""Issue 58 section 8: the control and sensitivity instrument.

At each cutoff N this computes both:

  * the original error E(N), reusing probe.py's FFT-autocorrelation route
    without reimplementing it;
  * the corrected error
        E_corr(N) := 2 sum_{h=1}^N |r_N(h) - C_N(h)|^2
    exactly as CORRECTED_RH_BRIDGE.md equation (1) defines it, where
    r_N(h) = psi_2(N,h) - (N-h) S(h) is probe.py's e(N,h), and C_N(h) is
    SIEGEL_UNIFORMITY.md equation (5), evaluated for whichever exceptional
    data (q, chi, beta) TT Definition 2.1 -- as read into that document --
    assigns at that N, or C_N == 0 when it assigns none.

Which case holds at a given N is not assumed: Z(N) = exp((log N)^0.1) is
computed, every primitive real character with conductor q < Z(N) is taken
from artifacts/siegel_uniformity/check.py's local_characters(), and each
one's Dirichlet L-function is scanned on the real axis near s=1 for a zero
in the window TT Definition 2.1 requires. L(s,chi) is evaluated exactly via
the Hurwitz-zeta identity L(s,chi) = q^-s sum_a chi(a) zeta(s, a/q) (entire,
since sum_a chi(a) = 0 cancels the pole shared by every zeta(s, a/q) term),
using mpmath's Hurwitz zeta. For every N in the required set, Z(N) < 3.6
(see below), so the only candidate conductor is q = 3.

E_corr at N=2000 is cross-checked against a direct, no-numpy pair count
(reusing probe.py's psi2_python and singular_series_python), the same way
probe.py cross-checks E.

The sensitivity half plants a synthetic off-line-zero term in Lambda: the
real density that a zero pair rho = beta + i*gamma, conj(rho) contributes
to psi'(x) via the explicit formula psi(x) = x - sum_rho x^rho/rho - ...,
namely -2 n^(beta-1) cos(gamma log n) at each integer n (the -1/rho factor
present in the formula cancels on differentiation). Section 8 treats such
perturbations as diagnostics, not alternative prime sequences: the results
record which arithmetic hypotheses the perturbed sequence keeps (real
values, by construction) and which it breaks (a functional equation, since
only one zero pair is planted, not its mirror 1-rho, conj(1-rho); and prime
support, since the perturbation is a smooth term on every integer).

Run: /opt/zeta-venv/bin/python hunts/prime_pair_error/s8_control.py
Writes hunts/prime_pair_error/results_s8_control.json.
"""
from __future__ import annotations

import importlib.util
import json
import math
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from mpmath import mp

HERE = Path(__file__).resolve().parent


def _load(name: str, relpath: str):
    spec = importlib.util.spec_from_file_location(name, HERE / relpath)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


probe = _load("probe", "probe.py")
siegel = _load("siegel_helpers", "artifacts/siegel_uniformity/check.py")

CUTOFFS = [2000, 5000, 10000, 30000, 100000]

# TT Definition 2.1's threshold constant c_0 is "sufficiently small" and not
# pinned to a number in SIEGEL_UNIFORMITY.md or CORRECTED_RH_BRIDGE.md. C0
# below is a representative stand-in used only to draw the scan window; the
# scan additionally pads 0.3 below that window, so shrinking C0 (which only
# shrinks the true window towards s=1) cannot turn a "no exceptional data"
# verdict here into a missed zero.
C0 = 0.05
SCAN_GRID = 1500
SCAN_UPPER = mp.mpf("0.9995")  # stays clear of the removable pole at s=1
SCAN_DPS = 40

# (beta, gamma, amplitude) triples for the planted off-line zero.
PLANT_PARAMS = [
    (0.6, 14.134725, 1.0),
    (0.75, 14.134725, 1.0),
    (0.9, 14.134725, 1.0),
    (0.9, 50.0, 1.0),
    (0.9, 14.134725, 5.0),
]


def hurwitz_L(chi, q: int, s):
    total = mp.mpf(0)
    for a in range(1, q + 1):
        c = chi(a)
        if c:
            total += c * mp.zeta(s, mp.mpf(a) / q)
    return total * mp.power(q, -s)


def scan_for_real_zero(chi, q: int, lo, hi, grid: int = SCAN_GRID):
    """Return a real s in [lo, hi] with L(s, chi) == 0, or None if the scan
    finds neither a sign change nor a near-zero value on the grid."""
    pts = [lo + (hi - lo) * i / grid for i in range(grid + 1)]
    vals = [hurwitz_L(chi, q, p) for p in pts]
    for i in range(grid):
        a, b = vals[i], vals[i + 1]
        if a == 0:
            return pts[i]
        if a * b < 0:
            return mp.findroot(lambda s: hurwitz_L(chi, q, s), (pts[i], pts[i + 1]),
                                solver="bisect")
    j = min(range(grid + 1), key=lambda i: abs(vals[i]))
    if abs(vals[j]) < mp.mpf("1e-6"):
        return pts[j]
    return None


def find_exceptional(N: int):
    """Decide which case CORRECTED_RH_BRIDGE.md/SIEGEL_UNIFORMITY.md assign
    at this N: return (metadata_dict, (q, chi, beta) or None)."""
    with mp.workdps(SCAN_DPS):
        Z = mp.e ** (mp.log(N) ** mp.mpf("0.1"))
        window_lower = 1 - mp.mpf(C0) / mp.log(Z)
        candidates = [(q, name, chi) for q, name, chi in siegel.local_characters() if q < Z]
        scan_lo = max(mp.mpf("0.05"), window_lower - mp.mpf("0.3"))
        for q, name, chi in candidates:
            beta = scan_for_real_zero(chi, q, scan_lo, SCAN_UPPER)
            if beta is not None:
                meta = {
                    "case": "exceptional", "N": N, "q": q, "character": name,
                    "beta": str(beta), "Z": str(Z), "window_lower": str(window_lower),
                    "scan_range": [str(scan_lo), str(SCAN_UPPER)],
                }
                return meta, (q, chi, beta)
        meta = {
            "case": "no_exception", "N": N, "Z": str(Z), "window_lower": str(window_lower),
            "checked_conductors": [q for q, _, _ in candidates],
            "scan_range": [str(scan_lo), str(SCAN_UPPER)],
        }
        return meta, None


def correction_vector(N: int, exc) -> list:
    """C_N(h) for h = 1..N, SIEGEL_UNIFORMITY.md equation (5). The zero
    vector when exc is None, i.e. no exceptional data assigned at this N."""
    if exc is None:
        return [mp.mpf(0)] * N
    q, chi, beta = exc
    with mp.workdps(SCAN_DPS):
        delta = 1 - beta
        Zval = mp.e ** (mp.log(N) ** mp.mpf("0.1"))
        sieve_primes = [p for p in range(2, int(Zval) + 2)
                         if siegel.factors(p) == {p: 1} and p < Zval]
        ph = siegel.phi(q)

        def alpha(p, h):
            rho = 1 if h % p == 0 else 2
            return Fraction(p * (p - rho), (p - 1) ** 2)

        def as_mp(x: Fraction):
            return mp.mpf(x.numerator) / x.denominator

        out = []
        for h in range(1, N + 1):
            T = N - h
            if h % 2 or T == 0:
                out.append(mp.mpf(0))
                continue
            S_star = math.prod((alpha(p, h) for p in sieve_primes if q % p),
                                start=Fraction(1))
            J1 = 1 + (mp.power(T, beta) - 1) / beta
            J2 = (mp.power(N, beta) - mp.power(h, beta)) / beta
            f = lambda t: mp.power(max(mp.mpf(1), t), -delta)
            g = lambda t: mp.power(t + h, -delta)
            J12 = mp.quad(lambda t: f(t) * g(t), [0, 1, T] if T > 1 else [0, T])
            units = [r for r in range(q) if math.gcd(r * (r + h), q) == 1]
            u = Fraction(sum(chi(r) for r in units), q)
            v = Fraction(sum(chi(r + h) for r in units), q)
            scale = as_mp(Fraction(q, ph) ** 2 * S_star)
            c_qh = siegel.ramanujan(q, h)
            out.append(scale * (-as_mp(u) * J1 - as_mp(v) * J2
                                 + as_mp(Fraction(c_qh, q)) * J12))
        return out


def e_vector(lam: np.ndarray, S: np.ndarray, N: int) -> np.ndarray:
    """r_N(h) = psi_2(N,h) - (N-h) S(h) for h = 1..N; probe.py's e(N,k)."""
    psi2 = probe.psi2_fft(lam, N)
    k = np.arange(1, N + 1)
    pred = S[1:N + 1] * (N - k)
    return psi2[1:] - pred


def E_and_Ecorr(e: np.ndarray, corr_arr: np.ndarray) -> tuple[float, float]:
    E = 2.0 * float(np.dot(e, e))
    d = e - corr_arr
    E_corr = 2.0 * float(np.dot(d, d))
    return E, E_corr


def planted_zero_perturbation(lam: np.ndarray, N: int, beta: float, gamma: float,
                               amplitude: float) -> np.ndarray:
    n = np.arange(1, N + 1, dtype=np.float64)
    density = -2.0 * amplitude * np.power(n, beta - 1.0) * np.cos(gamma * np.log(n))
    lam_pert = lam.copy()
    lam_pert[1:N + 1] = lam_pert[1:N + 1] + density
    return lam_pert


def cross_check_2000(exc) -> dict:
    """E_corr(2000) by a direct, no-numpy pair count, cross-checking the
    FFT route the same way probe.py cross-checks E."""
    N = 2000
    psi2 = probe.psi2_python(N)  # length N+1, index by shift
    corr_vec = correction_vector(N, exc)  # length N, index h-1 -> shift h
    total = 0.0
    for h in range(1, N + 1):
        S_h = probe.singular_series_python(h)
        r = psi2[h] - S_h * (N - h)
        total += (r - float(corr_vec[h - 1])) ** 2
    return 2.0 * total


def main() -> int:
    t0 = time.time()
    Nmax = max(CUTOFFS)
    lam, _lam_p = probe.von_mangoldt(Nmax)
    S = probe.singular_series(Nmax)

    rows = []
    for N in CUTOFFS:
        exc_meta, exc_data = find_exceptional(N)
        corr_vec = correction_vector(N, exc_data)
        corr_arr = np.array([float(x) for x in corr_vec], dtype=np.float64)
        e = e_vector(lam, S, N)
        E, E_corr = E_and_Ecorr(e, corr_arr)

        responses = []
        for beta_p, gamma_p, amp in PLANT_PARAMS:
            lam_pert = planted_zero_perturbation(lam, N, beta_p, gamma_p, amp)
            e_pert = e_vector(lam_pert, S, N)
            _, E_corr_pert = E_and_Ecorr(e_pert, corr_arr)
            responses.append({
                "beta": beta_p, "gamma": gamma_p, "amplitude": amp,
                "E_corr_perturbed": E_corr_pert,
                "ratio_to_unperturbed": (E_corr_pert / E_corr) if E_corr else None,
            })

        row = {
            "N": N, "E": E, "E_corr": E_corr,
            "ratio_Ecorr_over_E": (E_corr / E) if E else None,
            "exceptional_case": exc_meta,
            "planted_zero_response": responses,
        }
        rows.append(row)
        print(f"N={N:>7}: E={E:14.4f}  E_corr={E_corr:14.4f}  "
              f"ratio={row['ratio_Ecorr_over_E']:.6f}  case={exc_meta['case']}")

    exc_meta_2000, exc_data_2000 = find_exceptional(2000)
    corr_arr_2000 = np.array([float(x) for x in correction_vector(2000, exc_data_2000)])
    e_2000 = e_vector(lam, S, 2000)
    _, E_corr_fft_2000 = E_and_Ecorr(e_2000, corr_arr_2000)
    E_corr_python_2000 = cross_check_2000(exc_data_2000)
    cross_check = {
        "N": 2000, "case": exc_meta_2000["case"],
        "E_corr_fft": E_corr_fft_2000, "E_corr_pure_python": E_corr_python_2000,
        "absdiff": abs(E_corr_fft_2000 - E_corr_python_2000),
    }
    print(f"\ncross-check N=2000: FFT={E_corr_fft_2000:.6f}  "
          f"pure-Python={E_corr_python_2000:.6f}  |diff|={cross_check['absdiff']:.2e}")
    assert cross_check["absdiff"] < 1e-4

    out = {
        "definitions": {
            "E": "probe.py's E(N) = 2 sum_h e(N,h)^2, e(N,h) = psi_2(N,h) - (N-h) S(h)",
            "E_corr": "CORRECTED_RH_BRIDGE.md eq (1): 2 sum_h (r_N(h) - C_N(h))^2, "
                      "r_N == probe.py's e(N,h)",
            "C_N": "SIEGEL_UNIFORMITY.md eq (5); 0 when no exceptional data is assigned",
            "planted_zero_density": "-2 amplitude n^(beta-1) cos(gamma log n), the psi'(x) "
                                     "density of a zero pair rho=beta+i*gamma, conj(rho) "
                                     "in the explicit formula",
        },
        "planted_zero_hypotheses": {
            "preserved": ["real coefficients (conjugate pair keeps the density real)"],
            "broken": [
                "functional equation (only rho, conj(rho) are planted, not the "
                "reflected pair 1-rho, conj(1-rho))",
                "prime support (the density is a smooth term on every integer n, "
                "not one supported on primes and their powers)",
            ],
            "note": "Section 8: such perturbations are diagnostics, not alternative "
                    "prime sequences.",
        },
        "c0_used_for_scan_window": C0,
        "cutoffs": CUTOFFS,
        "rows": rows,
        "cross_check_N2000": cross_check,
        "planted_zero_params": [
            {"beta": b, "gamma": g, "amplitude": a} for b, g, a in PLANT_PARAMS
        ],
        "seconds_total": time.time() - t0,
    }
    out_path = HERE / "results_s8_control.json"
    out_path.write_text(json.dumps(out, indent=1))
    print(f"\nwrote {out_path}  ({out['seconds_total']:.1f}s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
