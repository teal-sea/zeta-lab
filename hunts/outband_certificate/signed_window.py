"""The difference-of-squares candidate, priced in the paper's own functional.

SUPERSEDED, kept as the record of the attempt. Every strip start this optimiser tried was
rejected on the sign condition, and RESULTS.md section 5 proves why: for a real even profile
the autocorrelation is strictly positive just inside the edge of its support (Laplace and
Titchmarsh), so the strip condition cannot hold, and the price below is never reached. The
class that can hold it has an odd or complex spectral factor, which is not a Gram kernel.

The stable rank-trace inequality (lean/bridge/Zeta23Ext/StableRankTrace.lean) takes any
Hermitian Q with a bounded positive index. For a signed spectral profile u = v_plus - v_minus
the compression is P_plus - P_minus + Q_offline; apply the theorem to V_plus and
Q' = Q_offline - P_minus (subtracting a positive semidefinite matrix cannot raise the positive
index, Weyl). The Frobenius side becomes the pair sum with weight |FT u|^2, whose transform
u * u is signed and may be nonpositive outside the band, where BGSTB's positivity (every
alpha) drops it. The price sits on the trace side: 4 tr P_minus, four times the negative
mass, per zero.

In the normalisation of hunts/frontier_math/paper_pin.py (int v = 1, so H = 2 - D with
D <= (v*v)(0) + int |alpha| (v*v)), the candidate's value is

    H_u = 2 - min_u [ (u*u)(0) + int_{-1}^{1} |alpha| (u*u)(alpha) + 4 int u_minus ]

over even u with int u_plus = 1 and u*u <= 0 on |alpha| > 1.

Why u cannot be compactly supported. For u supported in [-s, s], near the outer edge
alpha -> 2s the autocorrelation is int_{-d}^{d} f(x) f(-x) dx with f the edge profile,
which is int f_even^2 - int f_odd^2 and is strictly positive for every power-law edge
(f ~ (x - d)^k gives (-1)^k int (x^2 - d^2)^k > 0). So the sign condition can only hold on
the whole strip if u has no edge: the window is not bandlimited, and the pair sum is bounded,
not evaluated, outside the band. The domain below is a wide truncation of that.

Controls: (i) u >= 0 on [-1/2, 1/2] must reproduce Theorem D's 1.3274993; (ii) the unpriced
signed minimum is what the strip is worth to this certificate shape, to be compared with the
LP's class value, which is an upper bound on it.

    .venv/bin/python hunts/outband_certificate/signed_window.py [--S 3] [--h 0.005]
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent
THEOREM_D = 0.6725007036794116
MT_MIN = 2.0 - THEOREM_D


class Model:
    def __init__(self, S: float, h: float, edge: float | None = None):
        # even u on [-S, S]; free variables are its values on [0, S]
        self.S, self.h = S, h
        self.t = np.arange(0.0, S + h / 2, h)
        self.full = np.concatenate([-self.t[:0:-1], self.t])
        m = len(self.full)
        self.alpha = h * np.arange(-(m - 1), m)
        self.inband = np.abs(self.alpha) <= 1.0 + 1e-12
        self.strip = np.abs(self.alpha) > 1.0 + 1e-12
        self.abs_alpha = np.abs(self.alpha)
        # variables may be forced to zero beyond `edge` (the compact controls)
        self.mask = np.ones_like(self.t) if edge is None else (self.t <= edge + 1e-12).astype(float)

    def expand(self, half):
        half = half * self.mask
        return np.concatenate([half[:0:-1], half])

    def terms(self, half):
        u = self.expand(half)
        pos = np.trapezoid(np.maximum(u, 0.0), self.full)
        if pos <= 1e-12:
            return None
        u = u / pos
        ac = np.convolve(u, u[::-1]) * self.h
        zero = ac[len(ac) // 2]
        band = np.trapezoid((self.abs_alpha * ac)[self.inband], self.alpha[self.inband])
        neg = np.trapezoid(np.maximum(-u, 0.0), self.full)
        strip_pos = np.maximum(ac[self.strip], 0.0)
        has_strip = strip_pos.size > 0
        return dict(u=u, ac=ac, J=zero + band, neg=neg,
                    viol=float(np.sum(strip_pos ** 2) * self.h) if has_strip else 0.0,
                    viol_max=float(strip_pos.max()) if has_strip else 0.0,
                    strip_mass=float(-np.trapezoid(np.minimum(ac[self.strip], 0.0), self.alpha[self.strip])) if has_strip else 0.0)

    def objective(self, half, price, penalty):
        r = self.terms(half)
        if r is None:
            return 1e6
        return r["J"] + price * r["neg"] + penalty * r["viol"]


def optimise(model, price, starts, penalty, iters, tol_max):
    best = None
    for x0 in starts:
        res = minimize(model.objective, x0, args=(price, penalty), method="L-BFGS-B",
                       options=dict(maxiter=iters, maxfun=iters * 6))
        r = model.terms(res.x)
        if r is None or r["viol_max"] > tol_max:
            continue
        val = r["J"] + price * r["neg"]
        if best is None or val < best["val"]:
            best = dict(val=val, x=res.x, **{k: r[k] for k in ("J", "neg", "viol_max", "strip_mass", "u", "ac")})
    return best


def starts_for(model, rng, k):
    t = model.t
    core = np.where(t <= 0.5, np.cos(np.sqrt(2.0) * t), 0.0)
    out = [core]
    for _ in range(k):
        a = rng.uniform(0.55, 1.6); eps = rng.uniform(0.02, 0.3); w = rng.uniform(0.05, 0.3)
        out.append(core - eps * np.exp(-((t - a) / w) ** 2) + rng.normal(0.0, 0.01, t.shape))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--S", type=float, default=3.0)
    ap.add_argument("--h", type=float, default=0.005)
    ap.add_argument("--starts", type=int, default=10)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--iters", type=int, default=4000)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    tol_max = 1e-6

    # control (i): the square class on [-1/2, 1/2]
    m0 = Model(0.5, args.h, edge=0.5)
    c = optimise(m0, 0.0, [starts_for(m0, rng, 0)[0]], penalty=0.0, iters=args.iters, tol_max=np.inf)
    print(f"control: compact [-1/2,1/2], no strip, no price: J = {c['J']:.7f} -> H = {2 - c['J']:.7f}"
          f"   (Theorem D {THEOREM_D:.7f}); negative mass {c['neg']:.1e}")

    # the candidate: wide domain, sign condition on the whole strip
    m = Model(args.S, args.h)
    st = starts_for(m, rng, args.starts)
    free = optimise(m, 0.0, st, penalty=1e5, iters=args.iters, tol_max=tol_max)
    priced = optimise(m, 4.0, st + ([free["x"]] if free else []), penalty=1e5, iters=args.iters, tol_max=tol_max)
    out = dict(control=dict(J=c["J"], H=2 - c["J"]))
    for name, b in (("unpriced", free), ("priced", priced)):
        if b is None:
            print(f"{name}: no start satisfied u*u <= 0 on the strip to {tol_max:.0e}")
            out[name] = None
            continue
        print(f"{name}: J = {b['J']:.7f}  neg mass = {b['neg']:.5f}  price 4*neg = {4 * b['neg']:.5f}  "
              f"strip mass = {b['strip_mass']:.3e}  worst strip value = {b['viol_max']:.1e}")
        print(f"         value = {b['val']:.7f} -> H = {2 - b['val']:.7f}   "
              f"{'BEATS Theorem D by %.2e' % (2 - b['val'] - THEOREM_D) if 2 - b['val'] > THEOREM_D else 'below Theorem D by %.2e' % (THEOREM_D - (2 - b['val']))}")
        out[name] = dict(J=b["J"], neg=b["neg"], val=b["val"], H=2 - b["val"], strip_mass=b["strip_mass"],
                         t=[float(v) for v in m.t], u_half=[float(v) for v in b["u"][len(m.t) - 1:]])
    (HERE / "artifacts").mkdir(exist_ok=True)
    (HERE / "artifacts" / "signed-window.json").write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
