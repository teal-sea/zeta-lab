"""Prime-side checks and the bounds a prime-side proof of lambda_n >= 0 could use.

Run from the repository root (after ``run_li_arith_split.py``):

    .venv/bin/python hunts/rh_moonshot/li_arithmetic/run_li_arith_prime.py [--x0 100000000] [--n-max 5000]

Writes ``artifacts/prime_side.json`` with

* the Bombieri-Lagarias prime sum, with and without the boundary term,
  against T(n) from the split, for n <= 6 and X up to x0;
* for n = 1..n_max: the margin M(n) = A(n) + 1 - L_n^{(1)}(log 2), the exact
  prime integral P_n = M(n) - lambda_n, the pointwise bound B(n) (exact |E|
  below x0, Schoenfeld's RH-conditional envelope above), the mean-square
  bound sqrt(D2 K2) + tail (exact below x0, Cramer's RH mean square above),
  and an unconditional-shape envelope bound for small n.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from hunts.rh_moonshot.li_arithmetic import li_arith_prime as P  # noqa: E402

#: Mossinghoff-Trudgian (2015) zero-free region constant; used only to give an
#: unconditional-shape envelope exp(-sqrt(log x / R)) a realistic scale.
DLVP_R = 5.573412


def unconditional_shape_bound(n_max: int, m, lam, X0: int) -> list:
    """int_{log 2}^oo e_unc(u) |e^{-u} L_{n-1}^{(2)}(u)| du with e_unc = |E| (x <= X0), x exp(-sqrt(log x/R)) beyond.

    Not a theorem's constants (the prefactor is set to 1); it shows the growth
    rate exp(2n - O(sqrt n)) that any envelope of this shape forces.
    """
    u_lo, u_mid = math.log(2.0), math.log(float(X0))
    fine = np.arange(u_lo, u_mid, 1e-3)
    v = np.arange(math.sqrt(u_mid), math.sqrt(4.0 * n_max + 12 * n_max ** (1 / 3) + 400.0), 0.22 / math.sqrt(n_max))
    u = np.concatenate([fine, v * v])
    xs = np.exp(u[u <= u_mid])
    eps = np.empty_like(u)
    eps[u <= u_mid] = np.abs(P.psi_at(xs, m, lam) - xs) * np.exp(-u[u <= u_mid])
    eps[u > u_mid] = np.exp(-np.sqrt(u[u > u_mid] / DLVP_R))
    w = np.zeros_like(u)
    du = np.diff(u)
    w[:-1] += du / 2
    w[1:] += du / 2
    out = []
    # integrand eps(u) e^{u/2} |ell_{n-1}(u)| with ell_k = e^{-u/2} L_k^{(2)}(u)
    scale = np.exp(u / 2.0)
    for cur in P.scaled_laguerre(u, n_max - 1, 2.0):
        out.append(float(np.sum(w * eps * scale * np.abs(cur))))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--x0", type=int, default=10**8)
    ap.add_argument("--n-max", type=int, default=5000)
    ap.add_argument("--out-dir", default=str(_HERE / "artifacts"))
    args = ap.parse_args()
    split = json.loads((_HERE / "artifacts" / "split_zeta.json").read_text())
    A = np.array([float(v) for v in split["A"]])
    T = np.array([float(v) for v in split["T"]])
    L = np.array([float(v) for v in split["lambda"]])
    n_max = min(args.n_max, len(A))
    out = {"x0": args.x0, "n_max": n_max}
    t0 = time.time()
    m, lam = P.von_mangoldt_table(args.x0)
    out["seconds_sieve"] = round(time.time() - t0, 1)
    out["prime_powers_below_x0"] = int(len(m))
    # 1. the regularized prime sum against T(n)
    conv = {}
    for X in [10**5, 10**6, 10**7, args.x0]:
        r = P.prime_side_T(range(1, 7), X, m, lam)
        conv[str(X)] = {
            str(n): {"sharp_minus_T": r[n]["sharp"] - T[n - 1], "integrated_minus_T": r[n]["integrated"] - T[n - 1]}
            for n in range(1, 7)
        }
    out["prime_sum_convergence"] = conv
    # 2. margins, exact P_n, and the bounds
    L1 = np.array(P.laguerre1_at_log2(n_max))
    M = A[:n_max] + 1.0 - L1
    Pn = M - L[:n_max]
    t0 = time.time()
    kb = P.kernel_bounds(n_max, m, lam, args.x0)
    out["seconds_kernel"] = round(time.time() - t0, 1)
    B = np.array(kb["B_pointwise"])
    K2 = np.array(kb["K2"])
    D2 = np.array(kb["D2"])
    tail = np.array(kb["tail"])
    BL2 = np.sqrt(D2 * K2) + tail
    out["u_grid_points"] = kb["u_grid_points"]
    out["margin_M"] = M.tolist()
    out["P_exact"] = Pn.tolist()
    out["B_pointwise"] = B.tolist()
    out["K2"] = K2.tolist()
    out["D2"] = D2.tolist()
    out["tail"] = tail.tolist()
    out["B_meansquare"] = BL2.tolist()
    n = np.arange(1, n_max + 1)
    ok_pw = B <= M
    ok_l2 = BL2 <= M
    out["pointwise_route_succeeds_at"] = n[ok_pw].tolist()
    out["meansquare_route_succeeds_at_count"] = int(ok_l2.sum())
    out["meansquare_route_succeeds_range"] = [int(n[ok_l2].min()), int(n[ok_l2].max())] if ok_l2.any() else None
    out["margin_negative_up_to"] = int(n[M < 0].max()) if (M < 0).any() else 0
    out["min_ratio_B_over_M_where_M_positive"] = float((B[M > 0] / M[M > 0]).min())
    out["ratio_B_over_absP_median"] = float(np.median(B / np.maximum(np.abs(Pn), 1e-300)))
    # 3. unconditional-shape envelope (small n only)
    t0 = time.time()
    out["B_unconditional_shape"] = unconditional_shape_bound(200, m, lam, args.x0)
    out["seconds_unconditional"] = round(time.time() - t0, 1)
    out["generated"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    od = Path(args.out_dir)
    od.mkdir(parents=True, exist_ok=True)
    (od / "prime_side.json").write_text(json.dumps(out))
    print({k: v for k, v in out.items() if not isinstance(v, (list, dict))})
    print("pointwise succeeds at", out["pointwise_route_succeeds_at"][:20])
    print("meansquare succeeds range", out["meansquare_route_succeeds_range"], out["meansquare_route_succeeds_at_count"])


if __name__ == "__main__":
    main()
