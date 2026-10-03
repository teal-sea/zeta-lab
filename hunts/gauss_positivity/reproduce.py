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


def main() -> None:
    validate()
    counterexample_positivity_insufficient()

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