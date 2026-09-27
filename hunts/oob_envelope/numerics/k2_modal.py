"""K2 on Modal: the reduction applied to the Davenport-Heilbronn function.

DH has an off-line zero at 0.8085 + 85.699i and its truncated Weil form is
negative (lambda ~ -0.3, even sector) at CCM cutoff c = 47
(hunts/rogue_frontier/weil_trunc/dhneg_log.md), i.e. Zhu window
L = (log 47)/2. Symbol in Zhu's normalization (conventions pinned from
weil_trunc/galerkin.py and SOURCE.md s4):

    Psi_DH(t) = Re digamma(3/4 + it/2) - log(pi/5) - sum_{log n < 2L} 2 Lambda_f(n)/sqrt(n) cos(t log n),

no pole term, Lambda_f from -f'/f with a_n = (1, kappa, -kappa, -1, 0) mod 5.
DH has no Euler product, so the envelope is H = 0 and S_DH = sum 2|Lambda_f(n)|/sqrt n.

Reports: (1) S_DH and the least T# at which beta* > 0 could hold,
beta*(T) <= log(5T/2pi) + 1/T - S_DH (an upper bound on any valid beta*,
from Re digamma(3/4 + it/2) <= log(t/2) + 1/t for large t... used only to
show infeasibility); (2) lambda_min and LDL inertia of R(T#) at T# = 100, 150
with beta* FORCED to 0.05, 0.5, 2 (invalid envelopes, lesion-style): an
unsound pipeline would be one that reports positivity here. Measured grade.
"""
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
L_STR = "log47/2"
N, Q, PREC, H = 150, 32, 256, Fraction(1, 2)
CHECKS = [100, 150]
BETAS = ["0.05", "0.5", "2"]


def run():
    sys.path.insert(0, str(HERE))
    sys.path.insert(0, "/root")
    from flint import acb, arb, arb_mat, ctx
    from assemble import lam_min_inverse, ldl_inertia, sph_j_all
    ctx.prec = PREC
    t_start = time.time()
    La = arb(47).log() / 2
    twoL = 2 * La
    s5 = arb(5).sqrt()
    kappa = ((10 - 2 * s5).sqrt() - 2) / (s5 - 1)
    pat = [arb(1), kappa, -kappa, arb(-1), arb(0)]
    lam = {}
    for n in range(2, 47):
        s = pat[(n - 1) % 5] * arb(n).log()
        for d in range(2, n):
            if n % d == 0:
                s -= lam[d] * pat[(n // d - 1) % 5]
        lam[n] = s
    comb = []
    for n in range(2, 47):
        ln = arb(n).log()
        if not bool(ln < twoL):
            raise RuntimeError(n)
        comb.append((2 * lam[n] / arb(n).sqrt(), ln))
    S_DH = sum((abs(c) for c, _ in comb), arb(0))
    logqpi = (arb.pi() / 5).log()

    def psi(t):
        v = acb(arb(3) / 4, t / 2).digamma().real - logqpi
        for c, ln in comb:
            v -= c * (t * ln).cos()
        return v

    K = 2 * N - 1
    nus = [arb(2 * i) + arb(1) / 2 for i in range(N)]
    scale = [(-1) ** i * 2 * (La * nu).sqrt() for i, nu in enumerate(nus)]
    gl = [arb.legendre_p_root(Q, k, weight=True) for k in range(Q)]
    ha = arb(H.numerator) / H.denominator
    G, C = arb_mat(N, N), arb_mat(N, N)
    I = arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])
    out = {"L": L_STR, "N": N, "q": Q, "prec": PREC, "S_DH": float(S_DH.mid()),
           "log_threshold_T": float((S_DH + (2 * arb.pi() / 5).log()).mid()), "rows": []}
    npan = int(max(CHECKS) / H)
    for k in range(npan):
        V, wg, wc = [], [], []
        for x, w in gl:
            t_gl = ha * k + ha * (1 + x) / 2
            xl = arb((t_gl * La).mid())
            t = xl / La
            ww = w * ha / 2 / arb.pi()
            j = sph_j_all(K, xl)
            V.append([scale[i] * j[2 * i] for i in range(N)])
            wg.append(ww)
            wc.append(ww * psi(t))
        VtT = arb_mat(Q, N, [V[c][r] for c in range(Q) for r in range(N)])
        G += arb_mat(N, Q, [V[c][r] * wg[c] for r in range(N) for c in range(Q)]) * VtT
        C += arb_mat(N, Q, [V[c][r] * wc[c] for r in range(N) for c in range(Q)]) * VtT
        T = (k + 1) * H
        if T in CHECKS:
            for b in BETAS:
                beta = arb(b)
                R = C + beta * (I - G)
                neg, pos, und, _ = ldl_inertia([[R[i, j] for j in range(N)] for i in range(N)])
                try:
                    lm = float(lam_min_inverse(R).mid())
                except ZeroDivisionError:
                    lm = None
                row = {"T": float(T), "beta_forced": b, "n_neg": neg, "undecided": und,
                       "lam_near0": lm, "elapsed": time.time() - t_start}
                out["rows"].append(row)
                print(json.dumps(row), flush=True)
    return out


try:
    import modal

    app = modal.App("oob-envelope-k2")
    image = (modal.Image.debian_slim(python_version="3.12")
             .pip_install("python-flint==0.9.0")
             .add_local_file(str(HERE / "assemble.py"), "/root/assemble.py"))
    vol = modal.Volume.from_name("oob-envelope-stages", create_if_missing=True)

    @app.function(image=image, cpu=1.0, memory=2048, timeout=3600, volumes={"/out": vol}, retries=1)
    def k2():
        res = run()
        Path("/out/k2_dh.json").write_text(json.dumps(res, indent=1))
        vol.commit()
        return res

    @app.local_entrypoint()
    def main():
        res = k2.remote()
        (HERE / "k2_dh.json").write_text(json.dumps(res, indent=1))
        print(json.dumps({k: v for k, v in res.items() if k != "rows"}))
except ImportError:
    pass
