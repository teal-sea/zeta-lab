"""The certificate the out-of-band information supports, read off the LP's dual.

Hunt #110 measured what the BGSTB positivity is worth and showed the Gram-kernel argument
cannot spend it. It never looked at the dual solution, which is the certificate in the
LP's own model: the multiplier profile on the data rows is a kernel Khat(alpha), signed in
band and nonpositive out of band, and the multipliers on tau >= -1 are its x-space partner.
Whatever argument eventually spends the information has to produce a kernel of this shape,
so its shape is the specification.

Same LP as ../frontier_math/configuration_lp.py, rebuilt here only because that module
does not return the duals. Everything printed is verified by strong duality first: if the
dual objective does not match the primal value to 1e-7 the run says so and stops.

    .venv/bin/python hunts/outband_certificate/dual.py [--X 40] [--J 200] [--A 1.5]
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent


def build(J, X, h, eps, M, A_out, strip_floor=0.0):
    n = int(round(X / h))
    x = h * (np.arange(1, n + 1) - 0.5)
    a = np.arange(J + 1) / J
    nv = n + M + 1
    row_m = np.array([m * m for m in range(1, M + 1)], float)
    Cin = 2.0 * h * np.cos(2.0 * np.pi * np.outer(a, x))
    rows, rhs, sgns = [Cin, -Cin], [a + eps, -(a - eps)], [1.0, -1.0]
    aout = None
    if A_out is not None:
        aout = 1.0 + np.arange(1, int((A_out - 1) * J) + 1) / J
        Cout = 2.0 * h * np.cos(2.0 * np.pi * np.outer(aout, x))
        rows.append(-Cout); rhs.append(np.full(len(aout), strip_floor)); sgns.append(-1.0)
    nrows = sum(r.shape[0] for r in rows)
    Aub = np.zeros((nrows, nv)); bub = np.concatenate(rhs); at = 0
    for blk, sgn in zip(rows, sgns):
        m_ = blk.shape[0]
        Aub[at:at + m_, :n] = blk
        Aub[at:at + m_, n:n + M] = sgn * row_m
        Aub[at:at + m_, n + M] = sgn * 4.0
        at += m_
    Aeq = np.zeros((1, nv)); beq = np.array([1.0])
    Aeq[0, n:n + M] = np.arange(1, M + 1); Aeq[0, n + M] = 2.0
    c = np.zeros(nv); c[n] = 1.0
    bounds = [(-1.0, None)] * n + [(0.0, None)] * (M + 1)
    return dict(n=n, x=x, a=a, aout=aout, M=M, Aub=Aub, bub=bub, Aeq=Aeq, beq=beq, c=c,
                bounds=bounds, row_m=row_m, h=h, J=J)


def solve_with_duals(J, X, h=1 / 16, eps=None, M=6, A_out=None, strip_floor=0.0):
    eps = 0.4 / X if eps is None else eps
    L = build(J, X, h, eps, M, A_out, strip_floor)
    t0 = time.time()
    res = linprog(L["c"], A_ub=L["Aub"], b_ub=L["bub"], A_eq=L["Aeq"], b_eq=L["beq"],
                  bounds=L["bounds"], method="highs")
    L["seconds"] = time.time() - t0
    if not res.success:
        return L, None, res
    n, M, J1 = L["n"], L["M"], J + 1
    lam = res.ineqlin.marginals          # d(min p1)/d b_ub, <= 0
    y_hi = -lam[:J1]                     # multiplier on D + tauhat <= a + eps
    y_lo = -lam[J1:2 * J1]               # multiplier on D + tauhat >= a - eps
    z = -lam[2 * J1:] if A_out is not None else np.zeros(0)   # on D + tauhat >= floor
    mu = res.lower.marginals[:n]         # d(min p1)/d(lower bound of tau_i), >= 0
    lam_eq = res.eqlin.marginals[0]
    # Strong duality, in scipy's own convention: value = b_ub . lam + b_eq . lam_eq + lb . mu_lb
    dual_obj = float(L["bub"] @ lam + L["beq"] @ res.eqlin.marginals
                     + np.sum(-1.0 * res.lower.marginals[:n]))
    # The signed data kernel and the x-space kernel it induces on the tau variables.
    khat_in = y_hi - y_lo                # net multiplier at each in-band alpha_j (signed)
    khat_out = -z                        # <= 0 on the strip
    g_x = (L["Aub"][:2 * J1, :n].T @ (-lam[:2 * J1])
           + (L["Aub"][2 * J1:, :n].T @ (-lam[2 * J1:]) if A_out is not None else 0.0))
    out = dict(value=float(res.fun), dual_obj=dual_obj, seconds=L["seconds"],
               D=float(L["row_m"] @ res.x[n:n + M] + 4 * res.x[n + M]),
               p=[float(v) for v in res.x[n:n + M]], q=float(res.x[n + M]),
               khat_in=khat_in, khat_out=khat_out, z=z, mu=mu, g_x=g_x, lam_eq=float(lam_eq))
    return L, out, res


def describe(L, out, label):
    a, aout, x = L["a"], L["aout"], L["x"]
    print(f"\n== {label}: X={L['n'] * L['h']:.0f} J={L['J']} ({out['seconds']:.1f}s)")
    gap = abs(out["value"] - out["dual_obj"])
    print(f"   primal value {out['value']:.7f}   dual objective {out['dual_obj']:.7f}   gap {gap:.1e}")
    if gap > 1e-6:
        print("   STRONG DUALITY FAILED: the kernel below is not a certificate; stopping this case")
        return
    print(f"   adversary: D={out['D']:.5f}  p={['%.4f' % v for v in out['p']]}  q(off-line pairs)={out['q']:.5f}")
    kin = out["khat_in"]
    neg_in = kin < -1e-9
    print(f"   Khat in band [0,1]: min {kin.min():+.4e} at alpha={a[kin.argmin()]:.3f}, "
          f"max {kin.max():+.4e} at alpha={a[kin.argmax()]:.3f}, negative at {neg_in.sum()} of {len(kin)} nodes")
    if aout is not None:
        z = out["z"]; act = z > 1e-9
        print(f"   Khat on the strip (1,{aout[-1]:.2f}]: nonpositive by construction; active (z>0) at {act.sum()} of {len(z)} nodes, "
              f"mass sum z = {z.sum():.4e}, peak {z.max():.4e} at alpha={aout[z.argmax()]:.3f}"
              if act.any() else f"   Khat on the strip: z is identically zero, the positivity is NOT used at this grid")
        if act.any():
            first, last = aout[act][0], aout[act][-1]
            print(f"   active strip support: alpha in [{first:.3f}, {last:.3f}]")
    g = out["g_x"]; mu = out["mu"]
    print(f"   x-space kernel g on the tau grid: min {g.min():+.4e} at x={x[g.argmin()]:.2f}, max {g.max():+.4e}; "
          f"tau>=-1 active (mu>0) at {int((mu > 1e-9).sum())} of {len(mu)} nodes")
    return dict(label=label, X=L["n"] * L["h"], J=L["J"], value=out["value"], dual_obj=out["dual_obj"],
                D=out["D"], p=out["p"], q=out["q"], seconds=out["seconds"],
                khat_in_min=float(kin.min()), khat_in_neg_nodes=int(neg_in.sum()),
                strip=None if aout is None else dict(A=float(aout[-1]), active_nodes=int((out['z'] > 1e-9).sum()),
                                                     nodes=int(len(out['z'])), mass=float(out['z'].sum()),
                                                     peak=float(out['z'].max()), peak_alpha=float(aout[out['z'].argmax()]),
                                                     support=[float(aout[out['z'] > 1e-9][0]), float(aout[out['z'] > 1e-9][-1])] if (out['z'] > 1e-9).any() else None),
                g_min=float(g.min()), g_max=float(g.max()), mu_active=int((mu > 1e-9).sum()),
                khat_in=[float(v) for v in kin], alpha=[float(v) for v in a],
                z=[float(v) for v in out["z"]], aout=None if aout is None else [float(v) for v in aout],
                g_x=[float(v) for v in g], x=[float(v) for v in x])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--X", type=float, default=40.0)
    ap.add_argument("--J", type=int, default=200)
    ap.add_argument("--A", type=float, nargs="*", default=[1.5])
    ap.add_argument("--out", default=str(HERE / "artifacts" / "dual.json"))
    args = ap.parse_args()
    Path(args.out).parent.mkdir(exist_ok=True)
    records = []
    L, out, res = solve_with_duals(args.J, args.X, A_out=None)
    if out is None: print("in-band control infeasible", res.message); sys.exit(2)
    records.append(describe(L, out, "control, in-band only"))
    for A in args.A:
        L, out, res = solve_with_duals(args.J, args.X, A_out=A)
        if out is None: print(f"A_out={A} infeasible", res.message); continue
        records.append(describe(L, out, f"out-of-band positivity to {A}"))
    Path(args.out).write_text(json.dumps([r for r in records if r], indent=1) + "\n")
    print(f"\nartifact: {args.out}")


if __name__ == "__main__":
    main()
