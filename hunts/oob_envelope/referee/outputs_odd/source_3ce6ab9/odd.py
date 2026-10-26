"""Independent odd CC/Arb route. Run numerical entrypoints on Modal only.

The mathematical contract and exact shifts are frozen in ODD_FORMULAS.md.
Only prior referee helpers are imported; no odd-worker code is used.
"""

import hashlib
import json
import time
from fractions import Fraction
from pathlib import Path

from flint import arb, acb, arb_mat, fmpq, ctx
from independent import cc_arb, error_ball, serialize_matrix, mp_matrix
from l119 import series, witness, envelope

CASES = {
    "zhu": {"L": "4/5", "T": 150, "N": 200, "bits": 768,
            "shift": "8e-15", "target": "7.99e-15", "upper": "1e-14"},
    "main": {"L": "119/100", "T": 500, "N": 500, "bits": 1280,
             "shift": "3e-44", "target": "2.99e-44", "upper": "4e-44"},
}
ORDER = 192


def rational(s):
    return arb(fmpq(str(Fraction(s))))


def odd_tail(L, T, size, bound):
    n = 2*size+1

    def squared_tail(x, multiplier):
        a = (2*L*(2*n+1)).sqrt()*multiplier
        for j in range(1, n+1):
            a *= x/(2*j+1)
        ratio = x*x/((2*n+3)*(2*n+5))*(arb(2*n+5)/(2*n+1)).sqrt()
        assert 0 <= ratio < 1
        return a*a/(1-ratio*ratio)

    U = squared_tail(L*T, arb(1))
    V = squared_tail(L/2, (L/2).exp())
    K = T*bound/arb.pi()
    eps_D = K*U+2*V
    eps_B = K*(2*L*U).sqrt()+2*((L.sinh()-L)*V).sqrt()
    return eps_D, eps_B, {"first_omitted_order": n, "U": str(U), "V": str(V),
                          "K": str(K), "odd_pole_norm_squared": str(L.sinh()-L)}


def setup(case):
    cfg = CASES[case]
    L, T, size = rational(cfg["L"]), arb(cfg["T"]), cfg["N"]
    assert ctx.prec == cfg["bits"]
    powers = [(2, 2), (3, 3), (4, 2)]
    if case == "main":
        powers += [(5, 5), (7, 7), (8, 2), (9, 3)]
        assert arb(10).log() < 2*L < arb(11).log()
        w = witness()
        env = envelope(w)
        S = rational(w["S"])
        terms = [(int(k)*arb(row["p"]).log(), rational(v))
                 for row in w["primes"] for k, v in row["b"].items()]
        assert all(freq >= 2*L for freq, _ in terms)
    else:
        assert arb(4).log() < 2*L < arb(5).log()
        terms, env = [], []
        S = sum((2*arb(p).log()/arb(n).sqrt() for n, p in powers), arb(0))
    comb = [(arb(n).log(), 2*arb(p).log()/arb(n).sqrt()) for n, p in powers]
    beta = (T/(2*arb.pi())).log()-1/T-S
    assert beta > 0
    rho, strip = 1+arb(2).sqrt(), arb(1)/4
    sym = arb(9)+2*(T+2)+arb.pi().log()+abs(beta)
    sym += sum((abs(c)*(lam*strip).cosh() for lam, c in comb+terms), arb(0))
    entry = 2*L*(4*size-1)*(2*L*strip).exp()*sym
    eps_Q = 4*T*entry/(arb.pi()*(rho-1)*rho**ORDER)
    az = (arb(1)/4).digamma()-arb.pi().log()
    at = acb(arb(1)/4, T/2).digamma().real-arb.pi().log()
    # Digamma's real part increases with t>=0, directly from its reciprocal series.
    bound = abs(az).max(abs(at))+abs(beta)+sum((abs(c) for _, c in comb+terms), arb(0))
    eps_D, eps_B, tails = odd_tail(L, T, size, bound)
    assert size*eps_Q < rational(cfg["shift"])/1000
    assert eps_B < rational(cfg["shift"])/1000
    budget = {**cfg, "case": case, "degree": ORDER, "panels": 2*cfg["T"],
              "S": str(S), "S_exact": w["S"] if case == "main" else None,
              "envelope": env, "beta": str(beta), "symbol_real_bound": str(bound),
              "M_entry": str(entry), "eps_Q_per_entry": str(eps_Q),
              "eps_D": str(eps_D), "eps_B": str(eps_B), "tails": tails}
    return L, T, beta, comb, terms, budget, eps_Q, eps_D, eps_B


def transforms(t, L, scales):
    x, size = L*t, len(scales)
    if x == 0:
        return [arb(0)]*size
    top = 2*size+64
    b = [arb(0)]*(top+2)
    b[top], b[top+1] = series(x, top), series(x, top+1)
    for n in range(top, 0, -1):
        b[n-1] = (2*n+1)*b[n]/x-b[n+1]
    assert b[0].overlaps(x.sinc()), "j0 normalization discrepancy"
    assert b[1].overlaps((x.sin()-x*x.cos())/(x*x)), "j1 normalization discrepancy"
    out = [scales[k]*b[2*k+1] for k in range(size)]
    assert max(v.rad() for v in out) < arb("1e-65"), "transform width gate"
    return out


def partial(case, start, stop, checkpoint):
    L, T, beta, comb, terms, budget, _, _, _ = setup(case)
    size = CASES[case]["N"]
    checkpoint(budget, "budget.json")
    nodes, weights = cc_arb(ORDER)
    scales = [(-1)**k*(2*L*(4*k+3)).sqrt() for k in range(size)]
    C = arb_mat(size, size)
    first = time.monotonic()
    for panel in range(start, stop):
        ts = [arb(panel)/2+(x+1)/4 for x in nodes]
        columns = [transforms(t, L, scales) for t in ts]
        multipliers = []
        for t, weight in zip(ts, weights):
            arch = acb(arb(1)/4, t/2).digamma().real-arb.pi().log()
            P = sum((c*(lam*t).cos() for lam, c in comb), arb(0))
            H = sum((c*(lam*t).cos() for lam, c in terms), arb(0))
            multipliers.append(weight*(arch-P+H-beta)/(4*arb.pi()))
        X = arb_mat([[v[i] for v in columns] for i in range(size)])
        Y = arb_mat([[v[i]*w for v, w in zip(columns, multipliers)] for i in range(size)])
        C += X*Y.transpose()
        checkpoint({"panels_done": panel-start+1, "panels_total": stop-start,
                    "assembly_elapsed_s": time.monotonic()-first})
    C = (C+C.transpose())/2
    checkpoint({"case": case, "start": start, "stop": stop, "N": size,
                "triangle": serialize_matrix(C)}, "matrix.json")
    radius = max(sum((C[i, j].rad() for j in range(size)), arb(0)) for i in range(size))
    assert radius < arb("1e-55"), "arithmetic width gate"
    return {"status": "completed", "case": case, "start": start, "stop": stop,
            "assembly_s": time.monotonic()-first, "arithmetic_row_radius": str(radius)}


def triangle(data):
    size = data["N"]
    A, k = arb_mat(size, size), 0
    for i in range(size):
        for j in range(i+1):
            mid, rad = data["triangle"][k]
            A[i, j] = A[j, i] = arb(tuple(mid), tuple(rad))
            k += 1
    assert k == len(data["triangle"])
    return A


def factor_bound(A, shift, checkpoint, prefix="", propose_vector=False):
    from mpmath import mp
    size = A.nrows()
    with mp.workdps(110):
        try:
            B = mp.cholesky(mp_matrix(A, mp)-mp.mpf(shift)*mp.eye(size))
        except ValueError as exc:
            return {"factor_exists": False, "reason": str(exc)}
        factor = arb_mat(size, size)
        for i in range(size):
            for j in range(i+1):
                sign, man, exp, _ = B[i, j]._mpf_
                factor[i, j] = arb(((-1 if sign else 1)*int(man), int(exp)))
                assert factor[i, j].rad() == 0
        exact_mid = arb_mat([[A[i, j].mid() for j in range(size)] for i in range(size)])
        res = exact_mid-factor*factor.transpose()
        for i in range(size):
            res[i, i] -= rational(shift)
        r = max(sum((abs(res[i, j]) for j in range(size)), arb(0)).abs_upper() for i in range(size))
        e = max(sum((A[i, j].rad() for j in range(size)), arb(0)).abs_upper() for i in range(size))
        checkpoint({"shift_exact": shift, "N": size, "triangle": serialize_matrix(factor)},
                   prefix+"factor.json")
        out = {"factor_exists": True, "residual_norm": str(r), "entry_error_norm": str(e),
               "shift_exact": shift, "head_lower": rational(shift)-r-e}
        if propose_vector:
            v = [mp.mpf(1)]+[mp.mpf(0)]*(size-1)
            for _ in range(8):
                y = []
                for i in range(size):
                    y.append((v[i]-mp.fsum(B[i,j]*y[j] for j in range(i)))/B[i,i])
                v = [mp.mpf(0)]*size
                for i in range(size-1,-1,-1):
                    v[i] = (y[i]-mp.fsum(B[j,i]*v[j] for j in range(i+1,size)))/B[i,i]
                norm = mp.sqrt(mp.fsum(x*x for x in v))
                v = [x/norm for x in v]
            dyadics = []
            for x in v:
                sign, man, exp, _ = x._mpf_
                dyadics.append([(-1 if sign else 1)*int(man), int(exp)])
            exact_v = arb_mat([[arb(tuple(x))] for x in dyadics])
            norm = (exact_v.transpose()*exact_v)[0,0]
            rayleigh = (exact_v.transpose()*A*exact_v)[0,0]/norm
            checkpoint({"vector_dyadic": dyadics, "norm_squared": str(norm),
                        "rayleigh_ball": str(rayleigh)}, prefix+"ritz.json")
            out.update(rayleigh=rayleigh, vector=exact_v)
        return out


def reduce(case, paths, checkpoint):
    cfg = CASES[case]
    L, T, beta, _, _, budget, eps_Q, eps_D, eps_B = setup(case)
    size = cfg["N"]
    checkpoint(budget, "budget.json")
    nodes, weights = cc_arb(ORDER)
    moments = {}
    for k in (0,1,2,3,4,16,64,128,192):
        defect = sum((w*x**k for x,w in zip(nodes,weights)),arb(0))-(arb(2)/(k+1) if k%2==0 else 0)
        assert defect.contains(0)
        moments[str(k)] = str(defect)
    checkpoint(moments, "quadrature_checks.json")
    A, coverage, manifests = arb_mat(size,size), [], []
    own_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    for path in paths:
        man = json.loads(path.with_name("manifest.json").read_text())
        assert man["status"] == "completed"
        assert man["input_sha256"]["odd.py"] == own_hash
        for name in ("independent.py", "l119.py", "frozen_envelope_L119.json"):
            assert man["input_sha256"][name] == hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        raw = path.read_bytes()
        assert hashlib.sha256(raw).hexdigest() == man["output_sha256"]["matrix.json"]
        data = json.loads(raw)
        assert data["case"] == case and data["N"] == size
        A += triangle(data)
        coverage += list(range(data["start"],data["stop"]))
        manifests.append(man)
    assert sorted(coverage) == list(range(2*cfg["T"])), "missing or duplicate panel"
    checkpoint({"units":manifests,"unit_count":len(manifests),"coverage":coverage,
                "hashes_verified":True}, "assembly_manifest.json")
    poles = [(2*L*(4*k+3)).sqrt()*series(L/2,2*k+1,True) for k in range(size)]
    # Direct elementary integral of normalized x*sinh(x/2), independent of series.
    first_pole = (arb(3)/(2*L)).sqrt()/L*(4*L*(L/2).cosh()-8*(L/2).sinh())
    assert poles[0].overlaps(first_pole) and poles[0] > 0
    assert sum((p*p for p in poles),arb(0)) <= L.sinh()-L or sum((p*p for p in poles),arb(0)).overlaps(L.sinh()-L)
    for i in range(size):
        for j in range(i+1):
            value = A[i,j]-2*poles[i]*poles[j]+error_ball(eps_Q)
            if i==j:
                value += beta
            A[i,j] = A[j,i] = value
    checkpoint({"N":size,"triangle":serialize_matrix(A)},"matrix.json")
    evidence = factor_bound(A,cfg["shift"],checkpoint,propose_vector=True)
    if not evidence["factor_exists"]:
        return {"status":"inconclusive","stage":"head_factor","evidence":evidence}
    head = evidence.pop("head_lower")
    rayleigh, vector = evidence.pop("rayleigh"), evidence.pop("vector")
    lower = head.min(beta-eps_D)-eps_B
    assert lower > rational(cfg["target"])
    assert rayleigh < rational(cfg["upper"])
    checkpoint({"head":evidence,"head_lower_ball":str(head),"lower_ball":str(lower),
                "lower_exact_dyadic":list(map(int,lower.lower().man_exp())),
                "safe_lower_decimal":cfg["target"],"R_rayleigh_ball":str(rayleigh)},
               "positivity.json")
    controls = {}
    if case=="main":
        # The actual assembled mutation differs by +4 pp^T. Use an exact
        # dyadic direction so its change in the result is itself enclosed.
        p = arb_mat([[v] for v in poles])
        wrong = A+4*p*p.transpose()
        v = arb_mat([[v.mid()] for v in poles])
        norm = (v.transpose()*v)[0,0]
        original_q = (v.transpose()*A*v)[0,0]/norm
        wrong_q = (v.transpose()*wrong*v)[0,0]/norm
        defect = wrong_q-original_q
        assert defect > 0
        assert not (2*poles[0]**2).overlaps(-2*first_pole**2)
        ground_delta = 4*(vector.transpose()*p)[0,0]**2/(vector.transpose()*vector)[0,0]
        assert ground_delta > 0
        controls["pole_sign"] = {"status":"pass","fault_rejected_by_pole_identity":True,
            "first_mode_correct_pole":str(-2*first_pole**2),
            "first_mode_wrong_pole":str(2*poles[0]**2),
            "original_rayleigh_on_pole_direction":str(original_q),
            "wrong_rayleigh_on_pole_direction":str(wrong_q),
            "enclosed_result_change":str(defect),"ground_witness_change":str(ground_delta),
            "direction_dyadic":[list(map(int,x.mid().man_exp())) for x in poles]}
        mutant = arb_mat(A)
        for i in range(size):
            mutant[i,i] -= rational("1e-42")
        negative_q = (vector.transpose()*mutant*vector)[0,0]/(vector.transpose()*vector)[0,0]
        assert negative_q < 0
        failed = factor_bound(mutant,"0",checkpoint,prefix="negative_")
        assert not failed["factor_exists"]
        controls["negative_operator"] = {"status":"pass","shift_exact":"-1e-42",
            "rayleigh_ball":str(negative_q),"no_positive_bound":True,"factor":failed}
        checkpoint(controls,"controls.json")
    return {"status":"completed","case":case,"scope":"full real odd form domain",
            "grade":"enclosure-carrying numerical step with ordinary analytic reduction",
            "budget":budget,"positivity":evidence,"safe_lower_decimal":cfg["target"],
            "lower_ball":str(lower),"lower_exact_dyadic":list(map(int,lower.lower().man_exp())),
            "R_rayleigh_ball":str(rayleigh),"controls":controls}
