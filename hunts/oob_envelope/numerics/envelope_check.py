"""Sign gate for the envelope as the matrix code uses it.

K3 cannot see the sign of H (int |F|^2 H = 0 either way), and the H = 0
calibration cannot see it either. The step Q >= R_H needs, for t >= T#,

    Psi_L(t) + H(t) >= log(t / 2 pi) - 1/t - S,

which holds because P_L - H <= S (envelope.py) and Zhu's Lemma 3.1. This
checks it through assemble.Symbol (the code path that builds the matrix) at
sampled points in Arb, then on a fine float64 grid built from the same
envelope.json data, and reports max (P_L - H) on the grid against S.
Lesions: flip the sign of H; replace S by the comb-operator floor S_opt
(Zhu section 7's retraction mechanism, on purpose). Both must show violations.
Measured grade (a finite grid is not a proof; envelope.py is the proof of
P_L - H <= S).
"""
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parent))
from assemble import Symbol, load_envelope, to_arb  # noqa: E402

S_OPT = {"4/5": 1.2190, "119/100": 2.6677}   # probes/comb_operator.out, M = 1600


def main():
    ctx.prec = 128
    out = {}
    for Ls, env, T in (("4/5", "sine:16", 100), ("119/100", "sine:16", 500)):
        L = Fraction(Ls)
        kind, D = env.split(":")
        S, terms = load_envelope(L, kind, int(D))
        sym = Symbol(L, {env: (S, terms)})
        Sa = to_arb(S)
        # (a) Arb, through Symbol, at 4000 points of [15/4, 5 T]
        worst = None
        for t in np.linspace(3.75, 5 * T, 4000):
            ta = arb(float(t))
            v = sym.psi(ta) + sym.H(env, ta) - ((ta / (2 * arb.pi())).log() - 1 / ta - Sa)
            worst = v if worst is None or bool(v < worst) else worst
            if not bool(v > 0):
                raise SystemExit(f"envelope violated at t={t}: {v}")
        # (b) float64 fine grid of P_L - H from the same data
        t = np.arange(3.75, 5 * T, 0.002)
        PL = np.zeros_like(t)
        for n, c, ln in sym.pp:
            PL += float(c.mid()) * np.cos(t * float(ln.mid()))
        H = np.zeros_like(t)
        for p, bs in terms:
            for k, b in bs:
                H += float(b) * np.cos(k * t * math.log(p))
        from scipy.special import digamma
        base = np.real(digamma(0.25 + 0.5j * t)) - math.log(math.pi)
        env_lb = np.log(t / (2 * math.pi)) - 1 / t
        good = base - (PL - H) - (env_lb - float(S))
        flip = base - (PL + H) - (env_lb - float(S))
        opt = base - (PL - H) - (env_lb - S_OPT[Ls])
        rec = {
            "T": T, "S": float(S), "arb_min_margin": float(worst.mid()),
            "grid_points": int(t.size), "max_PL_minus_H": float((PL - H).max()),
            "grid_min_margin": float(good.min()),
            "lesion_flip_violations": int((flip < 0).sum()), "lesion_flip_min": float(flip.min()),
            "lesion_Sopt_violations": int((opt < 0).sum()), "lesion_Sopt_min": float(opt.min()),
        }
        print(Ls, rec)
        out[Ls] = rec
    Path(__file__).with_name("envelope_check.json").write_text(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
