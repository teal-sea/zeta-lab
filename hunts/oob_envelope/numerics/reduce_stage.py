"""Sum stage units in Arb and read lambda_min(R_H) at every unit boundary.

R(T#) = 2 p p^T + C_Psi + C_H + beta*(T#) (I - G), beta* = log(T#/2pi) - 1/T# - S.
Measured grade (no quadrature/tail/coupling bound). Also reports inertia by
Arb LDL, so a negative eigenvalue is detected, not just the one nearest 0.
"""
import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, arb_mat, ctx

sys.path.insert(0, str(Path(__file__).resolve().parent))
from assemble import decode_mats, lam_min_inverse, ldl_inertia, load_envelope, to_arb  # noqa: E402


def ldl_mid_inertia(A):
    """LDL^T without pivoting on exact midpoints (radii dropped at every step,
    i.e. plain 384-bit floating point). Measured grade: LDL of a symmetric
    matrix is backward stable, error ~ 2^-prec * cond. Returns (n_neg, min |pivot|)."""
    n = len(A)
    a = [[arb(x.mid()) for x in row] for row in A]
    neg, minabs = 0, None
    for k in range(n):
        d = a[k][k]
        if d.is_zero():
            return None, 0.0
        if d < 0:
            neg += 1
        ad = float(abs(d).mid())
        minabs = ad if minabs is None else min(minabs, ad)
        inv = arb((1 / d).mid())
        for i in range(k + 1, n):
            li = arb((a[i][k] * inv).mid())
            ai = a[i]
            for j in range(k + 1, i + 1):
                ai[j] = arb((ai[j] - li * a[j][k]).mid())
    return neg, minabs


def reduce_units(directory, tag, out=None):
    def is_unit(p):  # tag_t0_t1.json; skips e.g. tag_reduced.json
        parts = p.stem.split("_")
        return parts[-1].isdigit() and parts[-2].isdigit()

    files = sorted((p for p in Path(directory).glob(f"{tag}_*.json") if is_unit(p)),
                   key=lambda p: int(p.stem.split("_")[-2]))
    acc, rows, t_prev = None, [], 0
    for f in files:
        d = json.loads(f.read_text())
        ctx.prec = d["prec"]
        assert d["t0"] == t_prev, f"gap before {f.name}"
        t_prev = d["t1"]
        mats = decode_mats(d["mats"])
        acc = mats if acc is None else {k: acc[k] + mats[k] for k in acc}
        L = Fraction(d["L"])
        La = to_arb(L)
        N = d["N"]
        env = d["env"]
        S = to_arb(load_envelope(L, env.split(":")[0], int(env.split(":")[1]))[0])
        T = arb(d["t1"])
        beta = (T / (2 * arb.pi())).log() - 1 / T - S
        rec = {"T": d["t1"], "beta": float(beta.mid()), "unit_seconds": d["seconds"]}
        if bool(beta > 0):
            nus = [arb(2 * i) + arb(1) / 2 for i in range(N)]
            h2 = La / 2
            p = [2 * (La * nu).sqrt() * h2.bessel_i(nu) * (arb.pi() / (2 * h2)).sqrt() for nu in nus]
            I = arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])
            P2 = arb_mat(N, N, [2 * p[i] * p[j] for i in range(N) for j in range(N)])
            R = P2 + acc["Psi"] + acc[f"H:{env}"] + beta * (I - acc["G"])
            try:
                lam = lam_min_inverse(R)
                rec.update(lam=float(lam.mid()), lam_rad=float(lam.rad()))
            except ZeroDivisionError:
                rec.update(lam=None)
            rowsR = [[R[i, j] for j in range(N)] for i in range(N)]
            neg, pos, und, _ = ldl_inertia(rowsR)
            mneg, mmin = ldl_mid_inertia(rowsR)
            rec.update(n_neg=neg, undecided=und, mid_n_neg=mneg, mid_min_abs_pivot=mmin,
                       max_entry_rad=max(float(R[i, j].rad()) for i in range(N) for j in range(N)))
        rows.append(rec)
        print(json.dumps(rec), flush=True)
    if out:
        Path(out).write_text(json.dumps({"tag": tag, "rows": rows}, indent=1))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--tag", required=True)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    reduce_units(a.dir, a.tag, a.out)


if __name__ == "__main__":
    main()
