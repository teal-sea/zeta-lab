"""Modal app: the exact moment table b_n = int_0^inf Phi(u) u^{2n} du.

Run with:  .venv/bin/python -m modal run hunts/gauss_positivity/modal_moments.py

Design notes, so the cost is bounded before anything is launched:

* Phi is recomputed from its series at every quadrature node, and the node
  count grows with the exponent argument. That is what makes the local run
  time out. Here each shard computes a *contiguous block* of n on one
  container, so the container start-up is amortised and the block is
  checkpointed as it completes.
* Two independent routes per n are computed on purpose (the mandate's
  error budget): a tanh-sinh transform of the whole half-line, and a
  panel-split Gauss-Legendre on [0, 2] plus the analytic tail. They share
  only mpmath's exp/sin, so agreement is a genuine cross-check.
* Nothing here imports zeta; Phi's series is re-implemented from its
  definition so the Modal image needs only mpmath and so the cross-check
  against zeta/li.py is between independent implementations.
"""

from __future__ import annotations

import json

import modal

app = modal.App("zeta-gauss-positivity")

image = (
    modal.Image.debian_slim(python_version="3.11")
    .pip_install("mpmath==1.3.0")
    .add_local_python_source("moments_lib")
)


@app.function(image=image, cpu=1, memory=2048, timeout=3600)
def moment_block(n_lo: int, n_hi: int, dps: int = 40) -> list[dict]:
    """Moments b_n for n_lo <= n <= n_hi, by two independent routes."""
    import mpmath as mp

    mp.mp.dps = dps + 15

    def phi(u):
        """Phi(u) = sum_{n>=1} (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u})."""
        u = mp.mpf(u)
        e4, e5, e9 = mp.exp(4 * u), mp.exp(5 * u), mp.exp(9 * u)
        total = mp.mpf(0)
        n = 1
        while True:
            n2 = mp.mpf(n) ** 2
            term = (2 * mp.pi**2 * n2**2 * e9 - 3 * mp.pi * n2 * e5) * mp.exp(
                -mp.pi * n2 * e4
            )
            total += term
            if abs(term) < mp.mpf(10) ** (-(dps + 20)) * (1 + abs(total)):
                break
            n += 1
            if n > 4000:
                raise RuntimeError("Phi series did not converge")
        return total

    def route_tanhsinh(n: int):
        # x = exp(t), u = x/(1-x) ... use mp.quadosc-free tanh-sinh on (0, inf)
        # substitute u = -log(s), s in (0,1); u^{2n} du = (-log s)^{2n} ds/s
        def f(s):
            if s <= 0 or s >= 1:
                return mp.mpf(0)
            return phi(-mp.log(s)) * (-mp.log(s)) ** (2 * n) / s

        return mp.quad(f, [0, mp.mpf("0.5"), 1])

    def route_panels(n: int):
        # Phi is even; on (0, inf) split at u=2 and use the exp(-pi e^{4u}) tail.
        g = lambda u: phi(u) * u ** (2 * n)
        main = mp.quad(g, [0, mp.mpf("0.25"), mp.mpf("0.5"), 1, mp.mpf("1.5"), 2])
        # tail: u > 2, phi ~ 2 pi^2 e^{9u} exp(-pi e^{4u}); substitute v = pi e^{4u}
        def h(u):
            return phi(u) * u ** (2 * n)

        tail = mp.quad(h, [2, mp.mpf("2.25"), mp.mpf("2.6"), 3, mp.inf])
        return main + tail

    out = []
    for n in range(n_lo, n_hi + 1):
        a = route_tanhsinh(n)
        b = route_panels(n)
        out.append(
            {
                "n": n,
                "tanhsinh": mp.nstr(a, dps),
                "panels": mp.nstr(b, dps),
                "rel_diff": mp.nstr(abs(a - b) / abs(a), 6),
            }
        )
    return out


@app.local_entrypoint()
def main(n_max: int = 24, block: int = 8, dps: int = 40):
    """DEFAULT IS A SINGLE SMALL BLOCK: measure before spending.

    Run `--n-max 8 --block 8` first, time it, then multiply.
    """
    jobs = [(lo, min(lo + block - 1, n_max), dps) for lo in range(0, n_max + 1, block)]
    results = list(moment_block.starmap(jobs))
    flat = sorted([r for block_out in results for r in block_out], key=lambda d: d["n"])
    print(json.dumps(flat, indent=1))
    print("worst rel_diff:", max(float(r["rel_diff"]) for r in flat))