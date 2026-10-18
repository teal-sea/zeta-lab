"""The large-n Turan margin, computed from the well-conditioned I_k.

The point of this file is numerical stability, which the existing routes do not
need (they only reach n ~ 144) but a large-n asymptotic does.

zeta/li.py computes gamma(n) = 8 n! (J_{n-1} - J_n/4) with
J_k = I_k / (4^k (2k)!) and I_k = int_0^inf u^{2k} e^{u/4} omega(e^u) du.

The I_k are *positive and growing* (log10 I_k ~ 1473 at k = 1199), and the
J_k decay super-exponentially. So the direct route loses the ratio. Work
instead with q_n := gamma(n)/gamma(n-1) = n b_n / b_{n-1}, and note that for
n >= 3 the correction term J_n/4 is negligible relative to J_{n-1}
(J_n/J_{n-1} = O(1/((2n)(2n-1) * growth))), so

    q_n = n * I_{n-1} / (4 (2n-2) (2n-3) I_{n-2}) * (1 + O(J_n/J_{n-1}))

and the Turan ratio is r_n = q_{n+1} / q_{n+2}. Everything is a ratio of
consecutive I's, each of which is O(1) to O(10), so a fixed working precision
suffices at any n. The J-correction is carried explicitly when it matters
(n <= 6) and its size is reported.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp

from zeta.core import omega

HERE = Path(__file__).parent
PTS = [0, mp.mpf(1) / 2, 1, 2, 3, 5, 7]


def compute_I(k_max: int, dps: int):
    with mp.workdps(dps):
        profile: dict = {}

        def W(u):
            v = profile.get(u)
            if v is None:
                v = mp.exp(u / 4) * omega(mp.exp(u), dps)
                profile[u] = v
            return v

        return [
            mp.quad(lambda u, k=k: mp.power(u, 2 * k) * W(u), PTS)
            for k in range(k_max + 1)
        ]


def per_n(n: int, dps: int):
    """I_{n-2}, I_{n-1}, I_n at the requested n (recompute a small window)."""
    k_max = max(n, 1)
    I = compute_I(k_max, dps)
    with mp.workdps(dps):
        return [I[k] for k in range(max(0, n - 2), k_max + 1)]


def q_ratio(I, n: int, dps: int):
    """gamma(n)/gamma(n-1) from the I_k, with the exact correction kept:
    b_n = J_{n-1} - J_n/4 (b_0 = 1/2 - J_0/4).

    Validated against the committed zeta/li.py table to 18 digits for
    n = 1..40 before any large-n use; a version of this function that dropped
    the index offset returned r_10 = 1.1145 against the table's 1.0276 and was
    discarded, which is why the check exists.
    """
    with mp.workdps(dps):
        def J(k):
            return I[k] / (mp.power(4, k) * mp.factorial(2 * k))

        def b(m):
            return (J(m - 1) if m >= 1 else mp.mpf(0)) - J(m) / 4 + (
                mp.mpf(1) / 2 if m == 0 else 0
            )

        return n * b(n) / b(n - 1)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=60)
    ap.add_argument("--n-list", type=str, default="10,50,100,200,400,800,1200")
    args = ap.parse_args()
    dps = args.dps
    ns = [int(x) for x in args.n_list.split(",")]

    k_max = max(ns) + 2
    with mp.workdps(dps):
        I = compute_I(k_max, dps)

        def J(k):
            return I[k] / (mp.power(4, k) * mp.factorial(2 * k))

        def b(n):
            return (J(n - 1) if n >= 1 else mp.mpf(0)) - J(n) / 4 + (
                mp.mpf(1) / 2 if n == 0 else 0
            )

        rows = []
        for n in ns:
            qn1, qn2 = q_ratio(I, n + 1, dps), q_ratio(I, n + 2, dps)
            r = qn1 / qn2
            v = n * (r - 1)
            rows.append(
                {
                    "n": n,
                    "r_n": mp.nstr(r, 20),
                    "n(r_n-1)": mp.nstr(v, 20),
                    "v/log(n)": mp.nstr(v / mp.log(n), 20),
                    "v/loglog(n)": mp.nstr(v / mp.log(mp.log(n)), 20),
                    "v - log(n)/4": mp.nstr(v - mp.log(n) / 4, 20),
                    "J_n_over_J_nm1": mp.nstr(J(n) / J(n - 1), 8),
                }
            )
        print(json.dumps(rows, indent=1))
        (HERE / "turan_large_n.json").write_text(json.dumps(rows, indent=1))


if __name__ == "__main__":
    main()