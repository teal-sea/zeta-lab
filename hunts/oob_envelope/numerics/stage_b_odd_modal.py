"""Odd stage B on Modal: enclosure-carrying lower bound for lambda_min(R_H(T#)).

Derivation: odd_derivation.md. Configurations:

  zhu : L = 4/5, T# = 150, H = 0, N = 200, GL-64, 256 bits.
  val : L = 4/5, T# = 100, sine:16, N = 96, GL-64, 256 bits. Validation of
        odd pipeline with the same envelope as even validation.
        Units store C_Psi-beta and C_H separately for H lesions.
  B   : L = 119/100, T# = 500, sine:16, N = 500, GL-96, 384 bits, 50 units.

One unit = a contiguous block of panels. It computes the Arb GL partial sum
    C_nm = (1/pi) sum_panels sum_nodes w (Psi_L + H - beta*) That_n That_m
(odd Fourier columns, with shared Arb arithmetic from assemble.py), writes it to
the volume as soon as it finishes (exact dyadic midpoints plus radii), and
also records its largest node shift. A unit whose file exists is skipped.

The reducer (one container) sums the units in Arb and runs the positivity
step of RUNS.md:
 1. A~ = C - 2 s s^T + beta* I as Arb balls; eps_Q per entry (harden.py's
    Bernstein-ellipse bound, node-shift term included), so
    |A_ij - mid(A~_ij)| <= rad(A~_ij) + eps_Q,ij =: E_ij.
 2. lambda_meas: inverse iteration on mid(A~) (measured only).
 3. lambda0 = 0.99 lambda_meas as an exact dyadic; Lt = Cholesky of
    mid(A~) - lambda0 I with every entry snapped to an exact dyadic.
 4. Rres = mid(A~) - lambda0 I - Lt Lt^T in arb_mat (exact operands);
    r = max_i sum_j |Rres_ij| (upper). lambda_min(mid - lambda0 I) >= -r.
 5. e = max_i sum_j E_ij (upper); lambda_min(A) >= lambda0 - r - e (Weyl).
 6. Zhu (13): lambda_min(R_H) >= min(lambda0 - r - e, beta* - eps_D) - eps_B.
 7. Only the Arb lower endpoint of 6 is reported, as an exact dyadic and a
    decimal rounded down.
The modified Lemma 3.1 condition (T# >= 15/4, beta* > 0 decided in Arb,
S a global bound for P_L - H from envelope.json, or A_L when H=0) is asserted in code.

    modal run stage_b_odd_modal.py --cfg val               # units + reducer
    modal run stage_b_odd_modal.py --cfg B --only 49        # measure one unit
    modal run stage_b_odd_modal.py --cfg B --units-only     # all units
    modal run stage_b_odd_modal.py --cfg B --reduce-only    # positivity step
"""
import hashlib
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
CFGS = {
    "zhu": {"L": "4/5", "T": "150", "env": "none", "N": 200, "q": 64, "prec": 256, "h": "1/2",
            "split": True, "units": 6, "tag": "odd_zhu_L08_v1"},
    "val": {"L": "4/5", "T": "100", "env": "sine:16", "N": 96, "q": 64, "prec": 256, "h": "1/2",
            "split": True, "units": 2, "tag": "odd_val_L08_v1"},
    "val40": {"L": "4/5", "T": "40", "env": "sine:16", "N": 96, "q": 64, "prec": 256, "h": "1/2",
              "split": True, "units": 2, "tag": "odd_val40_L08_v1"},
    "B": {"L": "119/100", "T": "500", "env": "sine:16", "N": 500, "q": 96, "prec": 384, "h": "1/2",
          "split": False, "units": 50, "tag": "odd_stageB_L119_v1"},
}


def input_hashes():
    """Bind each checkpoint to the exact runner and three read-only inputs."""
    result = {}
    for name in ("stage_b_odd_modal.py", "assemble.py", "harden.py", "envelope.json"):
        path = HERE / name
        if not path.exists():
            path = Path("/root") / ("odd_source.py" if name == "stage_b_odd_modal.py" else name)
        result[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def _setup():
    sys.path.insert(0, str(HERE))
    sys.path.insert(0, "/root")


def unit_ranges(cfg):
    npan = int(Fraction(cfg["T"]) / Fraction(cfg["h"]))
    assert npan * Fraction(cfg["h"]) == Fraction(cfg["T"])
    u = cfg["units"]
    assert npan % u == 0
    s = npan // u
    return [(i * s, (i + 1) * s) for i in range(u)]


def common(cfg):
    """Symbol, S, beta*, odd sinh vector; modified Lemma 3.1 gate."""
    _setup()
    from flint import arb, ctx
    from assemble import Symbol, load_envelope, to_arb
    ctx.prec = cfg["prec"]
    L, T = Fraction(cfg["L"]), Fraction(cfg["T"])
    La, Ta = to_arb(L), to_arb(T)
    env = cfg["env"]
    if env == "none":
        sym = Symbol(L, {})
        # The exact finite positive prime sum is the H=0 envelope.
        sym.envs[env] = (sym.A_L, [])
    else:
        kind, D = env.split(":")
        sym = Symbol(L, {env: load_envelope(L, kind, int(D))})
    S = sym.envs[env][0]
    beta = (Ta / (2 * arb.pi())).log() - 1 / Ta - S
    # modified Zhu Lemma 3.1: for t >= T# >= 15/4, Psi_L + H >= log(t/2pi) - 1/t - S
    # (P_L - H <= S for ALL real t, envelope.py), and the right side is
    # increasing in t, so Psi_L + H >= beta* on [T#, inf) once beta* > 0.
    assert T >= Fraction(15, 4)
    assert bool(beta > 0), f"beta* not positive: {beta}"
    N = cfg["N"]
    # Rodrigues + Fourier integral: order n=2i+1, nu=n+1/2=2i+3/2.
    # Zhu (6), restricted to odd orders; see odd_derivation.md section 2.
    nus = [arb(2 * i) + arb(3) / 2 for i in range(N)]
    a = La / 2
    # Integral of normalized P_(2i+1) times sinh equals its exp moment:
    # s_i = 2 sqrt(L nu) sqrt(pi/(2a)) I_nu(a), a=L/2. No (-1)^i here.
    # Rodrigues derivation in odd_derivation.md; pole sign is Zhu Lemma 6.1.
    pvec = [2 * (La * nu).sqrt() * a.bessel_i(nu) * (arb.pi() / (2 * a)).sqrt() for nu in nus]
    return sym, S, beta, nus, pvec, La, Ta


def run_unit(cfg, k0, k1, outdir):
    _setup()
    from flint import arb, arb_mat
    from assemble import encode_mats, sph_j_all, to_arb
    path = Path(outdir) / f"{cfg['tag']}_{k0}_{k1}.json"
    if path.exists():
        previous = json.loads(path.read_text())
        assert previous["cfg"] == cfg and previous["input_hashes"] == input_hashes(), "stale unit"
        return {"unit": [k0, k1], "skipped": True}
    start = time.time()
    sym, S, beta, nus, pvec, La, Ta = common(cfg)
    env, N, q = cfg["env"], cfg["N"], cfg["q"]
    ha = to_arb(Fraction(cfg["h"]))
    # Highest retained odd order is 2N-1. K=2N supplies both recurrence seeds.
    K = 2 * N
    # F_i(t)=i*v_i(t), v_i=(-1)^i 2 sqrt(L nu_i) j_(2i+1)(Lt).
    # F_i conj(F_j)=v_i*v_j, not F_i*F_j: the i phase cancels.
    sc = [(-1) ** i * 2 * (La * nu).sqrt() for i, nu in enumerate(nus)]
    gl = [arb.legendre_p_root(q, k, weight=True) for k in range(q)]
    names = ["PsiB", "H"] if cfg["split"] else ["C"]
    acc = {nm: arb_mat(N, N) for nm in names}
    shift = arb(0)
    for k in range(k0, k1):
        a0 = ha * k
        cols, wts = [], {nm: [] for nm in names}
        for x, w in gl:
            t_gl = a0 + ha * (1 + x) / 2
            xl = arb((t_gl * La).mid())          # exact dyadic Bessel argument
            t = xl / La
            shift = shift.max(abs(t - t_gl))
            j = sph_j_all(K, xl)
            cols.append([sc[i] * j[2 * i + 1] for i in range(N)])
            ww = w * ha / 2 / arb.pi()
            sp, sh = sym.psi(t) - beta, sym.H(env, t)
            if cfg["split"]:
                wts["PsiB"].append(ww * sp)
                wts["H"].append(ww * sh)
            else:
                wts["C"].append(ww * (sp + sh))
        VT = arb_mat(q, N, [cols[c][r] for c in range(q) for r in range(N)])
        for nm in names:
            Vw = arb_mat(N, q, [cols[c][r] * wts[nm][c] for r in range(N) for c in range(q)])
            acc[nm] += Vw * VT
    secs = time.time() - start
    m, e = shift.upper().man_exp() if not shift.is_zero() else (0, 0)
    rec = {"cfg": cfg, "input_hashes": input_hashes(), "k0": k0, "k1": k1, "seconds": secs, "shift_upper": [str(m), int(e)],
           "mats": encode_mats(acc)}
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(rec))
    tmp.rename(path)
    return {"unit": [k0, k1], "seconds": secs}


# ------------------------------------------------------------------ reducer

def error_terms(cfg, sym, beta, nus, pvec, La, Ta, shift):
    """Odd quadrature and tail bounds, derived in odd_derivation.md.
    E_unit sqrt(nu_i nu_j) bounds each quadrature error; signs disappear
    only inside the absolute-value tail bounds, never in the head matrix.
    """
    from flint import arb
    from harden import dfact_log, digamma_rect_bound
    from assemble import to_arb
    env, N, q = cfg["env"], cfg["N"], cfg["q"]
    T, h = Fraction(cfg["T"]), Fraction(cfg["h"])
    ha = to_arb(h)
    npan = int(T / h)
    rho = 1 + arb(2).sqrt()
    b_e = ha / 2
    a_e = ha / arb(2).sqrt()
    comb_bound = sum((c * (b_e * ln).cosh() for _, c, ln in sym.pp), arb(0))
    H_bound, b_l1 = arb(0), arb(0)
    for lp, bs in sym.envs[env][1]:
        for kk, b in bs:
            H_bound += abs(b) * (b_e * kk * lp).cosh()
            b_l1 += abs(b)
    logpi = arb.pi().log()
    E_per_unit, shift_term = arb(0), arb(0)
    for k in range(npan):
        c0 = ha * k + ha / 2
        dg = digamma_rect_bound(c0 - a_e, c0 + a_e, b_e)
        sym_b = dg + logpi + comb_bound + H_bound + abs(beta)
        M = sym_b * 4 * La * (2 * La * b_e).exp()
        E_per_unit += ha / 2 * 64 * M / (15 * (rho ** 2 - 1) * rho ** (2 * q))
        shift_term += ha * M / arb("0.1") * shift
    E_unit = (E_per_unit + shift_term) / arb.pi()

    xT = Ta * La
    sup_dg = arb(0)
    for k in range(int(T) + 1):
        sup_dg = sup_dg.max(digamma_rect_bound(arb(k), arb(k + 1), arb(0)))
    Sup = sup_dg + logpi + sym.A_L + b_l1 + abs(beta)
    Kc = Ta / arb.pi() * Sup

    # Rodrigues: |j_n(x)| <= x^n/(2n+1)!!, Zhu (12), every integer n.
    # dfact_log(n) is log((2n+1)!!), not log(n!!). Odd n=2i+1 therefore
    # uses (4i+3)!!, and the first discarded denominator is (4N+3)!!.
    def a_n(n):
        return 2 * (La * (n + arb(1) / 2)).sqrt() * (n * xT.log() - dfact_log(n)).exp()

    # Rodrigues for the exp moment bounds i_n(a) by e^a a^n/(2n+1)!!.
    # This bounds the sinh moment at odd n; no even-order substitution.
    def pi_n(n):
        return 2 * (La * (n + arb(1) / 2)).sqrt() * (n * (La / 2).log() - dfact_log(n)).exp() * (La / 2).exp()

    # Retained orders 1,3,...,2N-1; first discarded odd order n0=2N+1.
    n0 = 2 * N + 1
    # a_(n+2)/a_n = x^2/((2n+3)(2n+5))*sqrt((n+5/2)/(n+1/2)).
    # Both factors decrease for n>=n0. The same formula with x=L/2
    # controls pi_n. Requiring both ratios <1 licenses geometric sums.
    r_a = xT ** 2 / ((2 * n0 + 3) * (2 * n0 + 5)) * ((n0 + arb(5) / 2) / (n0 + arb(1) / 2)).sqrt()
    r_p = (La / 2) ** 2 / ((2 * n0 + 3) * (2 * n0 + 5)) * ((n0 + arb(5) / 2) / (n0 + arb(1) / 2)).sqrt()
    assert bool(r_a < 1) and bool(r_p < 1), "tail ratio not < 1"
    alpha = a_n(n0) / (1 - r_a)
    pis = pi_n(n0) / (1 - r_p)
    # D=beta*I+C_tail-2*s_tail*s_tail^T. Absolute row sums bound the
    # deviation of D from beta*I, including the NEGATIVE pole diagonal.
    eps_D = Kc * a_n(n0) * alpha + 2 * pi_n(n0) * pis
    b_max = 2 * (La * nus[-1]).sqrt()
    b_sum = sum((2 * (La * nu).sqrt() for nu in nus), arb(0))
    p_max = arb(0)
    for p in pvec:
        p_max = p_max.max(abs(p))
    p_sum = sum((abs(p) for p in pvec), arb(0))
    # Absolute row/column sums of C_head,tail-2*s_head*s_tail^T;
    # Schur's test gives ||B|| <= sqrt(B1*Binf), Zhu (13).
    B1 = Kc * b_max * alpha + 2 * p_max * pis
    Binf = Kc * a_n(n0) * b_sum + 2 * pi_n(n0) * p_sum
    eps_B = (B1 * Binf).sqrt()
    return E_unit, eps_D, eps_B, Kc


def chol_mid(a, lam0):
    """Cholesky of the exact symmetric matrix a - lam0 I (a: rows of exact
    arbs), every computed entry snapped to its exact dyadic midpoint. The
    result Lt is just some exact lower-triangular matrix; correctness of the
    bound never depends on how accurate it is (the residual is enclosed).
    Returns (Lt, None) or (None, (j, pivot)) at the first nonpositive pivot."""
    from flint import arb
    n = len(a)
    Lt = [[] for _ in range(n)]
    for j in range(n):
        Lj = Lt[j]
        s = a[j][j] - lam0 - sum((x * x for x in Lj), arb(0))
        s = arb(s.mid())
        if not bool(s > 0):
            return None, (j, float(s.mid()))
        d = arb(s.sqrt().mid())
        inv = 1 / d
        for i in range(j + 1, n):
            Li = Lt[i]
            v = a[i][j] - sum((Li[k] * Lj[k] for k in range(j)), arb(0))
            Li.append(arb((v * inv).mid()))
        Lj.append(d)
    return Lt, None


def tri_solve(Lt, x):
    """Solve Lt Lt^T z = x on midpoints (measured use only)."""
    from flint import arb
    n = len(Lt)
    y = [arb(0)] * n
    for i in range(n):
        y[i] = arb(((x[i] - sum((Lt[i][k] * y[k] for k in range(i)), arb(0))) / Lt[i][i]).mid())
    z = [arb(0)] * n
    for i in reversed(range(n)):
        z[i] = arb(((y[i] - sum((Lt[k][i] * z[k] for k in range(i + 1, n)), arb(0))) / Lt[i][i]).mid())
    return z


def dyadic_str(x):
    m, e = x.man_exp()
    f = Fraction(int(m)) * Fraction(2) ** int(e)
    return f, f"{f.numerator}/{f.denominator}"


def round_down(f: Fraction, digits=12):
    if f <= 0:
        return "not positive"
    p = digits - 1 - math.floor(math.log10(float(f)))
    k = math.floor(f * Fraction(10) ** p)
    return f"{k}e{-p}"


def positivity(A, E_row, beta, eps_D, eps_B, iters=10, facs=("0.99", "0.95", "0.9", "0.5")):
    """RUNS.md stage B steps 2 to 7 on the Arb ball matrix A (arb_mat).
    E_row[i] = upper bound of sum_j eps_Q,ij (added to the radius row sums)."""
    from flint import arb, arb_mat
    n = A.nrows()
    t0 = time.time()
    mid = [[arb(A[i, j].mid()) for j in range(n)] for i in range(n)]
    out = {}
    # 5. e = max_i sum_j (rad A_ij + eps_Q,ij)
    e = arb(0)
    for i in range(n):
        s = sum((A[i, j].rad() for j in range(n)), arb(0)) + E_row[i]
        e = e.max(s)
    e = arb(e.upper())
    out["e"] = e.str(5, radius=False)
    # 2. measured lambda_min: inverse iteration with an unshifted mid Cholesky
    L0, fail = chol_mid(mid, arb(0))
    if L0 is None:
        out.update(ok=False, failed_at="unshifted midpoint Cholesky", pivot=fail)
        # A failed approximate pivot alone is not an enclosed negative sign.
        # Reconstruct its Schur witness and evaluate the full ball matrix.
        j = fail[0]
        head, bad = chol_mid([row[:j] for row in mid[:j]], arb(0))
        if bad is None:
            v = tri_solve(head, [-mid[i][j] for i in range(j)]) + [arb(1)] + [arb(0)] * (n-j-1)
            vv = arb_mat(n, 1, v)
            norm = (vv.transpose() * vv)[0, 0]
            rq = (vv.transpose() * A * vv)[0, 0] / norm
            # Ball A already carries rounding; E_row carries quadrature.
            eq = arb(0)
            for z in E_row:
                eq = eq.max(z)
            upper = (rq + eq).upper()
            out["negative_witness"] = {"rayleigh_upper": upper.str(15, radius=False),
                                       "negative_arb": bool(upper < 0)}
        return out
    x = [arb(1) / (1 + i) for i in range(n)]
    Mm = arb_mat(mid)
    for _ in range(iters):
        z = tri_solve(L0, x)
        nrm = arb(sum((v * v for v in z), arb(0)).sqrt().mid())
        x = [arb((v / nrm).mid()) for v in z]
    xv = arb_mat(n, 1, x)
    lam_meas = (xv.transpose() * Mm * xv)[0, 0] / (xv.transpose() * xv)[0, 0]
    out["lambda_meas"] = lam_meas.mid().str(12, radius=False)
    out["t_measure_s"] = time.time() - t0
    # 3. shifted Cholesky at lambda0 = fac * lambda_meas (exact dyadic)
    Lt, lam0, tried = None, None, []
    for fac in facs:
        lam0 = arb((arb(fac) * lam_meas).mid())
        Lt, fail = chol_mid(mid, lam0)
        tried.append({"fac": fac, "ok": Lt is not None, "fail": fail})
        if Lt is not None:
            break
    out["lambda0_tries"] = tried
    if Lt is None:
        out.update(ok=False, failed_at="shifted midpoint Cholesky at every lambda0")
        return out
    # 4. residual in arb_mat, all operands exact
    Lm = arb_mat(n, n)
    for i in range(n):
        for k, v in enumerate(Lt[i]):
            Lm[i, k] = v
    Rres = Mm - arb_mat(n, n, [lam0 if i == j else 0 for i in range(n) for j in range(n)]) - Lm * Lm.transpose()
    r = arb(0)
    for i in range(n):
        r = r.max(sum((abs(Rres[i, j]) for j in range(n)), arb(0)))
    r = arb(r.upper())
    lamA = lam0 - r - e
    bound = lamA.min(beta - eps_D) - eps_B
    lo, lo_s = dyadic_str(bound.lower())
    lamA_lo, _ = dyadic_str(lamA.lower())
    out.update(ok=lo > 0, lambda0_exact=dyadic_str(lam0)[1], lambda0=lam0.str(12, radius=False),
               r=r.str(5, radius=False), lambdaA_lower_rounded_down=round_down(lamA_lo),
               beta_minus_epsD=(beta - eps_D).str(15),
               lower_bound_exact=lo_s, lower_bound_rounded_down=round_down(lo),
               t_total_s=time.time() - t0)
    # lesion, measured: Cholesky must fail above lambda_min(mid A)
    over = arb((arb("1.01") * lam_meas).mid())
    Lx, fail = chol_mid(mid, over)
    out["lesion_overshoot_1.01"] = {"cholesky_ok": Lx is not None, "fail": fail}
    return out


def reduce_units(cfg, outdir):
    _setup()
    from flint import arb, arb_mat
    from assemble import decode_mats
    t_start = time.time()
    sym, S, beta, nus, pvec, La, Ta = common(cfg)
    N = cfg["N"]
    acc, secs, shift = None, [], arb(0)
    for k0, k1 in unit_ranges(cfg):
        p = Path(outdir) / f"{cfg['tag']}_{k0}_{k1}.json"
        d = json.loads(p.read_text())
        assert d["cfg"] == cfg and d["k0"] == k0 and d["k1"] == k1, p.name
        assert d["input_hashes"] == input_hashes(), "stale reducer input"
        mats = decode_mats(d["mats"])
        acc = mats if acc is None else {k: acc[k] + mats[k] for k in acc}
        secs.append(d["seconds"])
        m, e = d["shift_upper"]
        shift = shift.max(arb(int(m)) * arb(2) ** int(e))
    E_unit, eps_D, eps_B, Kc = error_terms(cfg, sym, beta, nus, pvec, La, Ta, shift)
    sq = [nu.sqrt() for nu in nus]
    sqsum = sum(sq, arb(0))
    E_row = [arb((E_unit * s * sqsum).upper()) for s in sq]
    # Zhu Lemma 6.1: the odd pole is -2*s*s^T, with s from sinh.
    P2 = arb_mat(N, N, [-2 * pvec[i] * pvec[j] for i in range(N) for j in range(N)])
    BI = arb_mat(N, N, [beta if i == j else 0 for i in range(N) for j in range(N)])
    C = acc["C"] if "C" in acc else acc["PsiB"] + acc["H"]
    out = {"cfg": cfg, "input_hashes": input_hashes(), "S": S.str(20), "beta": beta.str(20), "unit_seconds": secs,
           "unit_seconds_sum": sum(secs), "node_shift_upper": shift.str(5, radius=False),
           "eps_Q_max": (E_unit * nus[-1]).str(5, radius=False),
           "eps_D": eps_D.str(5), "eps_B": eps_B.str(5), "K": Kc.str(8),
           "lemma31": {"T_ge_15/4": True, "beta_positive_arb": bool(beta > 0),
                       "S_global_bound": "finite prime sum" if cfg["env"] == "none" else "envelope.json, P_L - H <= S on all of R"}}
    out["main"] = positivity(C + P2 + BI, E_row, beta, eps_D, eps_B)
    if cfg["split"]:
        # Deliberate wrong pole sign, +2*s*s^T instead of -2*s*s^T.
        # This adds 4*s*s^T >= 0, so the bottom eigenvalue cannot decrease.
        out["lesion_flip_pole"] = positivity(C - P2 + BI, E_row, beta, eps_D, eps_B)
        base = out["main"].get("lambda_meas")
        flipped = out["lesion_flip_pole"].get("lambda_meas")
        out["pole_control"] = {
            "expected": "wrong positive pole can only increase the matrix",
            "measured_increase": bool(base and flipped and Fraction(flipped) > Fraction(base)),
            "ratio": str(float(Fraction(flipped) / Fraction(base))) if base and flipped else None,
            "flip_refused": not out["lesion_flip_pole"]["ok"],
        }
        if cfg["env"] != "none":
            out["lesion_dropH"] = positivity(acc["PsiB"] + P2 + BI, E_row, beta, eps_D, eps_B)
            out["lesion_flipH"] = positivity(acc["PsiB"] - acc["H"] + P2 + BI, E_row, beta, eps_D, eps_B)
    if cfg["env"] == "none":
        measured = out["main"].get("lambda_meas")
        ratio = Fraction(measured) / Fraction("9.1183e-15") if measured else None
        out["validation_zhu62"] = {
            "source": "https://arxiv.org/html/2608.24827v2#S6.SS2",
            "reference_measured": "9.1183e-15", "reference_lower": "8.2065e-15",
            "ratio_measured": float(ratio) if ratio else None,
            "within_one_percent": bool(ratio and Fraction(99,100) < ratio < Fraction(101,100)),
            "lower_exceeds_published": (Fraction(out["main"].get("lower_bound_exact", "0"))
                                         > Fraction("8.2065e-15")),
        }
    if cfg["tag"] == "odd_val40_L08_v1":
        out["negative_control"] = {
            "endpoint_refused": not out["main"]["ok"],
            "negative_witness_enclosed": out["main"].get("negative_witness", {}).get("negative_arb", False),
        }
    out["reduce_seconds"] = time.time() - t_start
    Path(outdir, f"{cfg['tag']}_result.json").write_text(json.dumps(out, indent=1))
    return out


try:
    import modal

    app = modal.App("oob-envelope-odd-stage-b")
    image = (modal.Image.debian_slim(python_version="3.12")
             .pip_install("python-flint==0.9.0")
             .add_local_file(str(HERE / "stage_b_odd_modal.py"), "/root/odd_source.py")
             .add_local_file(str(HERE / "assemble.py"), "/root/assemble.py")
             .add_local_file(str(HERE / "harden.py"), "/root/harden.py")
             .add_local_file(str(HERE / "envelope.json"), "/root/envelope.json"))
    vol = modal.Volume.from_name("oob-envelope-stages", create_if_missing=True)

    @app.function(image=image, cpu=1.0, memory=2048, timeout=900, volumes={"/out": vol}, retries=0, max_containers=12)
    def unit(cfgname, k0, k1):
        res = run_unit(CFGS[cfgname], k0, k1, "/out")
        vol.commit()
        return res

    @app.function(image=image, cpu=1.0, memory=4096, timeout=1800, volumes={"/out": vol})
    def reduce(cfgname):
        vol.reload()
        out = reduce_units(CFGS[cfgname], "/out")
        vol.commit()
        return out

    @app.function(image=image, cpu=1.0, memory=256, timeout=30, volumes={"/out": vol})
    def check_zhu():
        vol.reload()
        d = json.loads(Path("/out", CFGS["zhu"]["tag"] + "_result.json").read_text())
        assert d["cfg"] == CFGS["zhu"]
        assert d["validation_zhu62"]["within_one_percent"], "stop: Zhu mismatch"
        assert d["main"]["ok"], "stop: Zhu lower bound failed"
        return True

    @app.local_entrypoint()
    def main(cfg: str = "zhu", only: int = -1, units_only: bool = False, reduce_only: bool = False):
        if cfg != "zhu":
            # All later configurations require the persisted Zhu gate.
            check_zhu.remote()
        c = CFGS[cfg]
        rng = unit_ranges(c)
        t_start = time.time()
        if not reduce_only:
            todo = [rng[only]] if only >= 0 else rng
            for res in unit.starmap([(cfg, a, b) for a, b in todo], order_outputs=False):
                print(json.dumps(res), flush=True)
            print(f"units wall {time.time() - t_start:.0f} s", flush=True)
        if only < 0 and not units_only:
            out = reduce.remote(cfg)
            print(json.dumps(out, indent=1), flush=True)
        print(f"total wall {time.time() - t_start:.0f} s", flush=True)
except ImportError:
    pass
