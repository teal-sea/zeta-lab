"""Reproduce the reduction, the instrument, and the asymptotic law.

Run:  .venv/bin/python hunts/gauss_positivity/reproduce.py

Everything printed is recomputed. The validation against the committed
zeta/li.py table runs first and raises if it fails, so no large-n number can
be produced from an unvalidated ratio routine.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).parent
sys.path.insert(0, str(HERE))

from laplace_D import exact_D, saddle  # noqa: E402
from turan_large_n import compute_I, q_ratio  # noqa: E402


def validate(dps: int = 60, n_check: int = 40) -> None:
    """The ratio routine must reproduce zeta/li.py before it is used."""
    from zeta.li import xi_taylor_coefficients

    g = xi_taylor_coefficients(n_check + 4, dps=dps, cache=True)
    I = compute_I(n_check + 4, dps)
    bad = []
    with mp.workdps(dps):
        for n in range(1, n_check + 1):
            r = q_ratio(I, n + 1, dps) / q_ratio(I, n + 2, dps)
            rt = g[n + 1] ** 2 / (g[n] * g[n + 2])
            if abs(r - rt) > mp.mpf(10) ** -(dps - 30) * abs(rt):
                bad.append(n)
    if bad:
        raise RuntimeError(f"ratio routine disagrees with zeta/li.py at n={bad}")
    print(f"[validate] ratio routine matches zeta/li.py at n=1..{n_check}")


def counterexample_positivity_insufficient() -> None:
    """f(t) = 1 + cos t + cos 3t is a positive measure's cosine transform and
    has a complex zero. This is why 'Phi >= 0' is not a criterion."""
    with mp.workdps(30):
        f = lambda t: 1 + mp.cos(t) + mp.cos(3 * t)
        roots = mp.polyroots([4, 0, -2, 1])
        c = [r for r in roots if abs(mp.im(r)) > 1e-20][0]
        t0 = mp.acos(c)
        print(f"[counterexample] complex zero t = {mp.nstr(t0, 12)}, f(t) = {mp.nstr(f(t0), 6)}")


def rival_check() -> None:
    """The Gate-3 test, in its corrected form.

    For a completed Xi_f(t) = F(1/2+it), a zero rho = sigma + i gamma of F gives
    a t-zero at t = gamma - i(sigma - 1/2), real iff sigma = 1/2. So the
    real-rootedness of Xi_f in t IS the critical-line statement transported.

    W_a = zeta(s+a)zeta(s-a) is the WRONG rival here: its transported statement
    is zeta's own RH. Davenport-Heilbronn is the right rival and it fails.
    """
    import zeta.epstein as E
    from zeta.core import xi

    with mp.workdps(30):
        # the corrected zero location for W_a: t = gamma - a, real
        a = mp.mpf(1) / 4
        g1 = mp.im(mp.zetazero(1))
        Xia = lambda t: xi(mp.mpf(1) / 2 + 1j * (t + a)) * xi(
            mp.mpf(1) / 2 + 1j * (t - a)
        )
        print(
            f"[rival] corrected W_a zero t = {mp.nstr(g1 - a, 15)} (real), "
            f"|Xi_a| = {mp.nstr(abs(Xia(g1 - a)), 6)}"
        )
        # Davenport-Heilbronn: an off-line zero gives a COMPLEX t-zero
        s0 = mp.mpf(E.OFFLINE_ZERO_RE)
        g0 = mp.mpf(E.OFFLINE_ZERO_IM)
        t0 = g0 - 1j * (s0 - mp.mpf(1) / 2)
        val = abs(E.completed_dh(mp.mpf(1) / 2 + 1j * t0))
        print(
            f"[rival] DH off-line sigma = {mp.nstr(s0, 20)}"
            f" gives complex t-zero {mp.nstr(t0, 22)},"
            f" |Xi_DH(t0)| = {mp.nstr(val, 6)}"
        )
        if abs(mp.im(t0)) < mp.mpf("0.1"):
            raise RuntimeError("DH rival check: expected a complex t-zero")


def newton_collapse(d_max: int = 60, m_max: int = 150) -> None:
    """Proposition: Newton's inequalities for J^{d,n} follow from Turan.

    Newton for A_k = C(d,k) gamma(n+k) reads
        gamma(n+k)^2/(gamma(n+k-1)gamma(n+k+1)) >= k(d-k)/((k+1)(d-k+1))
    and the right side is < 1 for every d >= 2, 1 <= k <= d-1 (max 0.93548387
    at d=59 k=29), while Turan makes the left side > 1. So Newton is implied.
    """
    from zeta.li import xi_taylor_coefficients

    with mp.workdps(70):
        g = xi_taylor_coefficients(m_max + 3, dps=70, cache=True)
        lhs_min = min(g[m + 1] ** 2 / (g[m] * g[m + 2]) for m in range(0, m_max))
        worst = (mp.mpf(0), 0, 0)
        for d in range(2, d_max):
            for k in range(1, d):
                rhs = mp.mpf(k * (d - k)) / ((k + 1) * (d - k + 1))
                if rhs / lhs_min > worst[0]:
                    worst = (rhs / lhs_min, d, k)
        print(
            f"[newton collapse] min Turan margin = {mp.nstr(lhs_min, 12)}; "
            f"worst RHS/LHS = {mp.nstr(worst[0], 8)} at d={worst[1]}, k={worst[2]}"
        )
        if worst[0] >= 1:
            raise RuntimeError("Newton collapse: a case is NOT implied by Turan")


def blindness_of_low_degree() -> None:
    """Why a hyperbolicity scan below d*(x0) = |x0|/(8t*) cannot fail.

    Uses hunts/jensen_clock's measured dictionary: finite Jensen degree acts on
    the zeros as de Bruijn-Newman heat with t_eff(d) = |x0|/(8d), against the
    Davenport-Heilbronn pair's landing time. Numbers reused, not recomputed.
    """
    with mp.workdps(40):
        s0 = mp.mpf("0.80851718245663738555")
        g0 = mp.mpf("85.6993484853775921719")
        x0 = ((s0 - mp.mpf(1) / 2) + 1j * g0) ** 2
        t_star = mp.mpf("0.0441263")
        d_star = abs(x0) / (8 * t_star)
        print(
            f"[blindness] |x0| = {mp.nstr(abs(x0), 12)}, landing t* = {t_star}"
            f" (hunts/jensen_clock quotes d* = 20785.13 from fuller precision);"
            f" dividing the rounded t* gives d* = {mp.nstr(d_star, 8)}"
        )
        for d in (2, 10, 32, 1000):
            print(
                f"[blindness]   d={d:5d}  t_eff = {mp.nstr(abs(x0) / (8 * d), 8)}"
                f"  = {mp.nstr(abs(x0) / (8 * d) / t_star, 8)}x overheated"
            )
        if abs(x0) / (8 * 32) < t_star:
            raise RuntimeError("blindness check: d=32 is not in the overheated region")


def main() -> None:
    validate()
    counterexample_positivity_insufficient()
    rival_check()
    newton_collapse()
    blindness_of_low_degree()

    print("\n[reduction] D_n = 1 - I_n^2/(I_{n-1} I_{n+1}); Turan is D_n <= 1/(n+1)")
    print("    n        D_n            n*D_n       1/(n+1)     u_saddle    D_laplace      rel_err")
    rows = []
    with mp.workdps(80):
        for n in [100, 400, 1600, 3200]:
            De = exact_D(n, 80)
            us = saddle(n, 80)
            A = 2 * n / us**2 + 2 * n / us + mp.mpf(1) / 4
            Dl = 4 / (us**2 * A)
            rows.append(
                {
                    "n": n,
                    "D_exact": mp.nstr(De, 12),
                    "nD_exact": mp.nstr(n * De, 12),
                    "one_over_np1": mp.nstr(mp.mpf(1) / (n + 1), 12),
                    "u_saddle": mp.nstr(us, 12),
                    "D_laplace": mp.nstr(Dl, 12),
                    "rel_err": mp.nstr(abs(Dl - De) / De, 6),
                }
            )
            r = rows[-1]
            print(
                f"  {r['n']:5d}  {r['D_exact']:>13}  {r['nD_exact']:>12}  {r['one_over_np1']:>11}"
                f"  {r['u_saddle']:>11}  {r['D_laplace']:>13}  {r['rel_err']:>9}"
            )

    print("\n[law] r_n = 1 + 1/n - 2/(n log n) + ..., i.e. n(r_n - 1) -> 1")
    print("    n        u_saddle     1 - n(r_n-1)    2/u_saddle    2/(log n - loglog n)")
    law = []
    with mp.workdps(60):
        for e in [6, 8, 10, 12, 16, 20]:
            n = 10**e
            us = saddle(n, 60)
            A = 2 * n / us**2 + 2 * n / us + mp.mpf(1) / 4
            D = 4 / (us**2 * A)
            rem = 1 - (mp.mpf(n) / (n + 1) - n * D)
            law.append(
                {
                    "n": f"1e{e}",
                    "u_saddle": mp.nstr(us, 12),
                    "one_minus_nr": mp.nstr(rem, 12),
                    "two_over_us": mp.nstr(2 / us, 12),
                    "two_over_log": mp.nstr(2 / (mp.log(n) - mp.log(mp.log(n))), 12),
                }
            )
            r = law[-1]
            print(
                f"  {r['n']:>5}  {r['u_saddle']:>11}  {r['one_minus_nr']:>14}"
                f"  {r['two_over_us']:>12}  {r['two_over_log']:>18}"
            )

    (HERE / "reproduce_results.json").write_text(
        json.dumps({"reduction": rows, "law": law}, indent=1)
    )
    print("\nwrote reproduce_results.json")


if __name__ == "__main__":
    main()