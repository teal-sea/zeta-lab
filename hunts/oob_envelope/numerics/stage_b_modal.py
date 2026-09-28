"""Stage B on Modal: enclosure-carrying lower bound for lambda_min(R_H(T#)).

Plan: RUNS.md, section "Stage B: hardened run". Two configurations:

  val : L = 4/5, T# = 100, sine:16, N = 96, GL-64, 256 bits. Validation of
        the whole pipeline against the reviewed harden.py result
        (lambda_min(R_H) >= 1.1579e-17). Units store C_Psi-beta and C_H
        separately so the drop-H lesion can be read from the same data.
  B   : L = 119/100, T# = 500, sine:16, N = 500, GL-96, 384 bits, 50 units.

One unit = a contiguous block of panels. It computes the Arb GL partial sum
    C_nm = (1/pi) sum_panels sum_nodes w (Psi_L + H - beta*) That_n That_m
(same arithmetic as harden.py step 1 and assemble.panel_sums), writes it to
the volume as soon as it finishes (exact dyadic midpoints plus radii), and
also records its largest node shift. A unit whose file exists is skipped.

The reducer (one container) sums the units in Arb and runs the positivity
step of RUNS.md:
 1. A~ = C + 2 p p^T + beta* I as Arb balls; eps_Q per entry (harden.py's
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
S a global bound for P_L - H from envelope.json) is asserted in code.

    modal run stage_b_modal.py --cfg val               # units + reducer
    modal run stage_b_modal.py --cfg B --only 49        # measure one unit
    modal run stage_b_modal.py --cfg B --units-only     # all units
    modal run stage_b_modal.py --cfg B --reduce-only    # positivity step
"""
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
CFGS = {
    "val": {"L": "4/5", "T": "100", "env": "sine:16", "N": 96, "q": 64, "prec": 256, "h": "1/2",
            "split": True, "units": 2, "tag": "stageBval2_L08"},
    # negative control: T# = 60, where R_H (sine:16, L = 0.8) was measured
    # indefinite (one negative eigenvalue, run_L08_N200.json); beta* > 0 there
    "val60": {"L": "4/5", "T": "60", "env": "sine:16", "N": 96, "q": 64, "prec": 256, "h": "1/2",
              "split": True, "units": 2, "tag": "stageBval60_L08"},
    "B": {"L": "119/100", "T": "500", "env": "sine:16", "N": 500, "q": 96, "prec": 384, "h": "1/2",
          "split": False, "units": 50, "tag": "stageB_L119"},
}


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
    """Symbol, S, beta*, p vector; Lemma 3.1 (modified) condition checked."""
    _setup()
    from flint import arb, ctx
    from assemble import Symbol, load_envelope, to_arb
    ctx.prec = cfg["prec"]
    L, T = Fraction(cfg["L"]), Fraction(cfg["T"])
    La, Ta = to_arb(L), to_arb(T)
    kind, D = cfg["env"].split(":")
    sym = Symbol(L, {cfg["env"]: load_envelope(L, kind, int(D))})
    S = sym.envs[cfg["env"]][0]
    beta = (Ta / (2 * arb.pi())).log() - 1 / Ta - S
    # modified Zhu Lemma 3.1: for t >= T# >= 15/4, Psi_L + H >= log(t/2pi) - 1/t - S
    # (P_L - H <= S for ALL real t, envelope.py), and the right side is
    # increasing in t, so Psi_L + H >= beta* on [T#, inf) once beta* > 0.
    assert T >= Fraction(15, 4)
    assert bool(beta > 0), f"beta* not positive: {beta}"
    N = cfg["N"]
    nus = [arb(2 * i) + arb(1) / 2 for i in range(N)]
    a = La / 2
    pvec = [2 * (La * nu).sqrt() * a.bessel_i(nu) * (arb.pi() / (2 * a)).sqrt() for nu in nus]
    return sym, S, beta, nus, pvec, La, Ta


def run_unit(cfg, k0, k1, outdir):
    _setup()
    from flint import arb, arb_mat
    from assemble import encode_mats, sph_j_all, to_arb
    path = Path(outdir) / f"{cfg['tag']}_{k0}_{k1}.json"
    if path.exists():
        return {"unit": [k0, k1], "skipped": True}
    start = time.time()
    sym, S, beta, nus, pvec, La, Ta = common(cfg)
    env, N, q = cfg["env"], cfg["N"], cfg["q"]
    ha = to_arb(Fraction(cfg["h"]))
    K = 2 * N - 1
    sc = [(-1) ** i * 2 * (La * nu).sqrt() for i, nu in enumerate(nus)]
    gl = [arb.legendre_p_root(q, k, weight=True) for k in range(q)]
    names = ["PsiB", "H", "G", "IB"] if cfg["split"] else ["C"]
    lam_in = 2 * La * arb("0.95")          # in-band frequency for the planted lesion
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
            cols.append([sc[i] * j[2 * i] for i in range(N)])
            ww = w * ha / 2 / arb.pi()
            sp, sh = sym.psi(t) - beta, sym.H(env, t)
            if cfg["split"]:
                wts["PsiB"].append(ww * sp)
                wts["H"].append(ww * sh)
                wts["G"].append(ww)
                wts["IB"].append(ww * (lam_in * t).cos())
            else:
                wts["C"].append(ww * (sp + sh))
        VT = arb_mat(q, N, [cols[c][r] for c in range(q) for r in range(N)])
        for nm in names:
            Vw = arb_mat(N, q, [cols[c][r] * wts[nm][c] for r in range(N) for c in range(q)])
            acc[nm] += Vw * VT
    secs = time.time() - start
    m, e = shift.upper().man_exp() if not shift.is_zero() else (0, 0)
    rec = {"cfg": cfg, "k0": k0, "k1": k1, "seconds": secs, "shift_upper": [str(m), int(e)],
           "mats": encode_mats(acc)}
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(rec))
    tmp.rename(path)
    return {"unit": [k0, k1], "seconds": secs}


# ------------------------------------------------------------------ reducer

def error_terms(cfg, sym, beta, nus, pvec, La, Ta, shift):
    """harden.py steps 2 and 3, verbatim arithmetic: E_unit (eps_Q,ij =
    E_unit sqrt(nu_i nu_j)), eps_D, eps_B, K."""
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

    def a_n(n):
        return 2 * (La * (n + arb(1) / 2)).sqrt() * (n * xT.log() - dfact_log(n)).exp()

    def pi_n(n):
        return 2 * (La * (n + arb(1) / 2)).sqrt() * (n * (La / 2).log() - dfact_log(n)).exp() * (La / 2).exp()

    n0 = 2 * N
    r_a = xT ** 2 / ((2 * n0 + 3) * (2 * n0 + 5)) * ((n0 + arb(5) / 2) / (n0 + arb(1) / 2)).sqrt()
    r_p = (La / 2) ** 2 / ((2 * n0 + 3) * (2 * n0 + 5)) * ((n0 + arb(5) / 2) / (n0 + arb(1) / 2)).sqrt()
    assert bool(r_a < 1) and bool(r_p < 1), "tail ratio not < 1"
    alpha = a_n(n0) / (1 - r_a)
    pis = pi_n(n0) / (1 - r_p)
    eps_D = Kc * a_n(n0) * alpha + 2 * pi_n(n0) * pis
    b_max = 2 * (La * nus[-1]).sqrt()
    b_sum = sum((2 * (La * nu).sqrt() for nu in nus), arb(0))
    p_max = max((abs(p) for p in pvec), key=lambda z: float(z.mid()))
    p_sum = sum((abs(p) for p in pvec), arb(0))
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
        mats = decode_mats(d["mats"])
        acc = mats if acc is None else {k: acc[k] + mats[k] for k in acc}
        secs.append(d["seconds"])
        m, e = d["shift_upper"]
        shift = shift.max(arb(int(m)) * arb(2) ** int(e))
    E_unit, eps_D, eps_B, Kc = error_terms(cfg, sym, beta, nus, pvec, La, Ta, shift)
    sq = [nu.sqrt() for nu in nus]
    sqsum = sum(sq, arb(0))
    E_row = [arb((E_unit * s * sqsum).upper()) for s in sq]
    P2 = arb_mat(N, N, [2 * pvec[i] * pvec[j] for i in range(N) for j in range(N)])
    BI = arb_mat(N, N, [beta if i == j else 0 for i in range(N) for j in range(N)])
    C = acc["C"] if "C" in acc else acc["PsiB"] + acc["H"]
    out = {"cfg": cfg, "S": S.str(20), "beta": beta.str(20), "unit_seconds": secs,
           "unit_seconds_sum": sum(secs), "node_shift_upper": shift.str(5, radius=False),
           "eps_Q_max": (E_unit * nus[-1]).str(5, radius=False),
           "eps_D": eps_D.str(5), "eps_B": eps_B.str(5), "K": Kc.str(8),
           "lemma31": {"T_ge_15/4": True, "beta_positive_arb": bool(beta > 0),
                       "S_global_bound": "envelope.json, P_L - H <= S on all of R"}}
    out["main"] = positivity(C + P2 + BI, E_row, beta, eps_D, eps_B)
    if cfg["split"]:
        # same data, lambda0 = 0.9999 lambda_meas: how close the method gets
        out["tight_0.9999"] = positivity(C + P2 + BI, E_row, beta, eps_D, eps_B, facs=("0.9999",))
        # lesion: drop the H term (Psi + H -> Psi) but keep beta* from S
        out["lesion_dropH"] = positivity(acc["PsiB"] + P2 + BI, E_row, beta, eps_D, eps_B)
        # lesion: flip the sign of H (Psi + H -> Psi - H), same beta*
        out["lesion_flipH"] = positivity(acc["PsiB"] - acc["H"] + P2 + BI, E_row, beta, eps_D, eps_B)
        # lesion: planted in-band terms (their full-line integral is not 0)
        A0 = C + P2 + BI
        out["lesion_inband_const_-2e-17"] = positivity(A0 - arb("2e-17") * acc["G"], E_row, beta, eps_D, eps_B)
        out["lesion_inband_cos_+1e-16"] = positivity(A0 + arb("1e-16") * acc["IB"], E_row, beta, eps_D, eps_B)
        out["lesion_inband_cos_-1e-16"] = positivity(A0 - arb("1e-16") * acc["IB"], E_row, beta, eps_D, eps_B)
        # harden.py route on the same data: Arb LDL of A~ + eps_Q - 1.158e-17 I
        from assemble import ldl_inertia
        A = C + P2 + BI
        E = E_unit
        rows = [[A[i, j] + arb(0, (E * sq[i] * sq[j]).upper()) - (arb("1.158e-17") if i == j else 0)
                 for j in range(N)] for i in range(N)]
        neg, pos, und, _ = ldl_inertia(rows)
        out["harden_route_ldl_1.158e-17"] = {"n_neg": neg, "undecided": und}
    if cfg["tag"] == "stageBval2_L08":
        lo = Fraction(out["main"]["lower_bound_exact"])
        ref = Fraction(1158, 10 ** 20) - Fraction(3031, 10 ** 47)
        out["validation"] = {"positive": lo > 0, "le_1.158e-17_minus_epsB": lo <= ref,
                             "ge_1.1579e-17": lo >= Fraction(11579, 10 ** 21),
                             "dropH_fails": not out["lesion_dropH"]["ok"],
                             "flipH_fails": not out["lesion_flipH"]["ok"],
                             "inband_const_fails": not out["lesion_inband_const_-2e-17"]["ok"],
                             "inband_cos_some_sign_fails": not (out["lesion_inband_cos_+1e-16"]["ok"]
                                                                and out["lesion_inband_cos_-1e-16"]["ok"])}
    if cfg["tag"] == "stageBval60_L08":
        out["negative_control"] = {"endpoint_not_positive": not out["main"]["ok"]}
    out["reduce_seconds"] = time.time() - t_start
    Path(outdir, f"{cfg['tag']}_result.json").write_text(json.dumps(out, indent=1))
    return out


try:
    import modal

    app = modal.App("oob-envelope-stage-b")
    image = (modal.Image.debian_slim(python_version="3.12")
             .pip_install("python-flint==0.9.0")
             .add_local_file(str(HERE / "assemble.py"), "/root/assemble.py")
             .add_local_file(str(HERE / "harden.py"), "/root/harden.py")
             .add_local_file(str(HERE / "envelope.json"), "/root/envelope.json"))
    vol = modal.Volume.from_name("oob-envelope-stages", create_if_missing=True)

    @app.function(image=image, cpu=1.0, memory=2048, timeout=900, volumes={"/out": vol}, retries=1)
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

    @app.local_entrypoint()
    def main(cfg: str = "val", only: int = -1, units_only: bool = False, reduce_only: bool = False):
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
