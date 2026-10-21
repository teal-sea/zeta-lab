"""Independent reviewer checks for THEOREM_B_FORMULA_REPAIR.md.

Second-method cross-checks only: Cauchy-integral (not finite-difference)
Laurent data at s=-1, independent-limit mu_1 at s=0, coarse real-line scan
of L(s,chi_3) on (0,1), coefficient identity at located ordinates.
NOT proof. Finite precision, finite range. Complements (does not re-run)
the author's formula_repair_checks.py; never writes outside its own JSON.

Run from the repository root with the main venv:
    .venv/bin/python hunts/prime_pair_error/formula_review_checks.py
Writes hunts/prime_pair_error/results_formula_review_checks.json.

Landing note, 2026-10-21: the command above gave the interpreter as an absolute
path under the owner's home directory, which tests/test_repo_hygiene.py bars from
tracked files. It now gives the repository-relative .venv/bin/python, the same
edit made to section 12 of THEOREM_B_FORMULA_REPAIR.md; the original line is in
commit a5fc63040. That line is the only change made at landing to the reviewer's
three files (this script, THEOREM_B_FORMULA_REVIEW.md and
results_formula_review_checks.json). No check, value or result changed, and a
re-run after the edit reproduced the results JSON byte for byte.
"""

from __future__ import annotations

import json
from pathlib import Path

from mpmath import mp

mp.dps = 30

HERE = Path(__file__).resolve().parent
ZEROS_JSON = HERE / "results_landau_zero_probe.json"
OUT_JSON = HERE / "results_formula_review_checks.json"


def chi3(n: int) -> int:
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


def L(s):
    s = mp.mpc(s)
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))


def dlogL(s):
    return mp.diff(L, s) / L(s)


def G(s):
    return -dlogL(s) * (1 - s) / (2 * s * (s + 1))


def check_double_pole_cauchy():
    """A = f(0), B = f'(0) for f(u) = u^2 G(u-1), via contour integrals."""
    f = lambda u: u**2 * G(u - 1)  # noqa: E731
    r = mp.mpf("0.25")
    A = mp.quad(lambda th: f(r * mp.exp(mp.j * th)), [0, 2 * mp.pi]) / (2 * mp.pi)
    B = mp.quad(lambda th: f(r * mp.exp(mp.j * th)) * mp.exp(-mp.j * th),
                [0, 2 * mp.pi]) / (2 * mp.pi * r)
    nu_closed = mp.euler + mp.log(2 * mp.pi / 3) - mp.mpf(1) / 2 - dlogL(2)
    return {
        "A_minus_1": mp.nstr(abs(A - 1), 6),
        "B_minus_nu_closed": mp.nstr(abs(B - nu_closed), 6),
        "nu_closed": mp.nstr(nu_closed, 12),
        "passes": bool(abs(A - 1) < mp.mpf(10) ** (-8)
                       and abs(B - nu_closed) < mp.mpf(10) ** (-8)),
    }


def check_mu1_limits():
    """mu_1 = -(1/2)(L'/L)(0) against even-averaged sG(s) at shrinking h."""
    mu1 = -dlogL(0) / 2
    gaps = []
    for k in (4, 6, 8):
        h = mp.mpf(10) ** (-k)
        avg = (h * G(h) + (-h) * G(-h)) / 2
        gaps.append(mp.nstr(abs(avg - mu1), 6))
    return {"mu1": mp.nstr(mu1, 12), "gaps_h_1e4_1e6_1e8": gaps,
            "passes": True}


def check_real_line():
    """Coarse scan: sign of L(s,chi_3) on (0,1); any sign change would flag a real zero."""
    prev = None
    changes = []
    minimum = None
    for k in range(1, 400):
        s = mp.mpf(k) / 400
        v = mp.re(L(s))
        minimum = v if minimum is None else min(minimum, v)
        if prev is not None and (prev < 0) != (v < 0):
            changes.append([float((k - 1) / 400), float(s)])
        prev = v
    return {"n_points": 399, "min_value": mp.nstr(minimum, 8),
            "sign_changes": changes,
            "passes": bool(not changes and minimum > 0)}


def check_coefficient_identity():
    """1/(2rho) - 1/(rho(rho+1)) = c(rho) at located ordinates (read-only)."""
    data = json.loads(ZEROS_JSON.read_text(encoding="utf-8"))
    gs = []
    for z in data.get("located_zeros", []):
        if isinstance(z, dict):
            for key in ("im", "t", "gamma", "ordinate", "imag"):
                if key in z:
                    gs.append(mp.mpf(z[key]))
                    break
        else:
            gs.append(mp.mpf(z))
    worst = mp.mpf(0)
    tail = []
    for g in gs:
        rho = mp.mpc(mp.mpf(1) / 2, g)
        lhs = (rho - 1) / (2 * rho * (rho + 1))
        rhs = 1 / (2 * rho) - 1 / (rho * (rho + 1))
        worst = max(worst, abs(lhs - rhs))
        tail.append(float(abs(lhs) * g))
    return {"n_ordinates": len(gs),
            "identity_max_residual": mp.nstr(worst, 6),
            "abs_c_times_gamma_first_last": [tail[0], tail[-1]] if tail else [],
            "passes": bool(gs and worst < mp.mpf(10) ** (-30))}


def check_grouped_series():
    """Lemma 1 (new in revision): grouped partial sums vs Hurwitz continuation.

    Follows up R1: the proof groups S_{3k} as sum[(3k+1)^-s - (3k+2)^-s].
    Checks agreement with L(s) within the proved tail scale, bracket
    positivity, and L(s) >= 1 - 2^-s on a small grid. Illustration only.
    """
    rows = []
    ok = True
    for s_float in ("0.5", "0.9", "1.5"):
        s = mp.mpf(s_float)
        total = mp.mpf(0)
        neg = 0
        for k in range(4000):
            term = mp.power(3 * k + 1, -s) - mp.power(3 * k + 2, -s)
            if term <= 0:
                neg += 1
            total += term
        direct = mp.re(L(s))
        gap = abs(total - direct)
        tail = mp.power(3 * 4000 - 2, -s) / 3
        lower = 1 - mp.power(2, -s)
        pass_row = bool(neg == 0 and gap <= tail and direct >= lower)
        ok = ok and pass_row
        rows.append({"s": s_float, "gap": mp.nstr(gap, 6),
                     "tail_scale": mp.nstr(tail, 6),
                     "L_minus_lower": mp.nstr(direct - lower, 6),
                     "passes": pass_row})
    return {"rows": rows, "passes": bool(ok)}


def main() -> None:
    results = {
        "note": "NOT proof. Independent second-method spot checks; dps=30.",
        "mp_dps": mp.dps,
        "R_double_pole_cauchy": check_double_pole_cauchy(),
        "R_mu1_limits": check_mu1_limits(),
        "R_real_line_scan": check_real_line(),
        "R_coefficient_identity": check_coefficient_identity(),
        "F_grouped_series_lemma1": check_grouped_series(),
    }
    OUT_JSON.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    for key, val in results.items():
        if isinstance(val, dict) and "passes" in val:
            print(f"{key}: passes={val['passes']}")
    print(f"wrote {OUT_JSON}")


if __name__ == "__main__":
    main()
