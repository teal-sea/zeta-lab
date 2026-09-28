"""Independent L=119/100 enclosure. Numerical entrypoints run on Modal only.

The old referee CC rule, exact series seeds, and tail norm proof are reused.
No numerical-lane implementation is read or imported. See REVIEW.md.
"""

import json
import time
from fractions import Fraction
from pathlib import Path

from flint import arb, acb, arb_mat, fmpq, ctx
from independent import cc_arb, error_ball, tail_budget, serialize_matrix, mp_matrix

SIZE, ORDER, BITS = 500, 192, 1280


def witness():
    data = json.loads(Path(__file__).with_name("frozen_envelope_L119.json").read_text())
    return next(r for r in data["runs"]
                if r["L"] == "119/100" and r["kernel"] == "sine" and r["D"] == 16)


def envelope(w):
    """Positive atomic measures convolved with the nonnegative sine kernel.

    For three moments the measure has atoms at pi and +/-acos(c).
    Its masses and c follow from the symmetric 4 by 4 Toeplitz eigenvector.
    All low moments are enclosed, with their residuals charged to the slack.
    """
    a = [(arb.pi()*(j+1)/18).sin() for j in range(17)]
    norm = sum((v*v for v in a), arb(0))
    rho = [sum((a[j]*a[j+k] for j in range(17-k)), arb(0))/norm
           for k in range(17)]
    assert [(r["p"], r["m"]) for r in w["primes"]] == [(2, 3), (3, 2), (5, 1), (7, 1)]
    rows = []
    for row in w["primes"]:
        p, m = row["p"], row["m"]
        t = [arb(0)] + [arb(p).log()/arb(p**k).sqrt()/rho[k] for k in range(1, m+1)]
        if m == 1:
            M, pair, at_pi, c = t[1], arb(0), t[1], arb(0)
        elif m == 2:
            M = (t[2]+(t[2]**2+8*t[1]**2).sqrt())/2
            pair, at_pi, c = M, arb(0), -t[1]/M
        else:
            u, v, z = t[1:]
            M = (u+z+((z-u)**2+4*(u+v)**2).sqrt())/2
            c = (1-(M-z)/(u+v))/2
            pair = (M-u)/(1+c)
            at_pi = M-pair
        assert pair >= 0 and at_pi >= 0 and abs(c) < 1
        cosines = [arb(1), c]
        for k in range(2, 17):
            cosines.append(2*c*cosines[-1]-cosines[-2])
        ideal = [2*rho[k]*(pair*cosines[k]+at_pi*(-1)**k) for k in range(17)]
        low_loss = sum((abs(ideal[k]+2*arb(p).log()/arb(p**k).sqrt())
                        for k in range(1, m+1)), arb(0))
        assert set(map(int, row["b"])) == set(range(m+1, 17))
        high_loss = sum((abs(arb(fmpq(v))-ideal[int(k)]) for k, v in row["b"].items()), arb(0))
        slack = arb(fmpq(row["M_p"]))-M-low_loss-high_loss
        assert slack > 0, "atomic decomposition does not cover the frozen witness"
        assert (m+1)*arb(p).log() > arb(238)/100
        rows.append({"p": p, "M": str(M), "slack": str(slack),
                     "low_loss": str(low_loss), "high_loss": str(high_loss)})
    assert sum((Fraction(r["M_p"]) for r in w["primes"]), Fraction(0)) == Fraction(w["S"])
    return rows


def setup():
    ctx.prec = BITS
    L, T = arb(119)/100, arb(500)
    w = witness()
    env = envelope(w)
    beta = (T/(2*arb.pi())).log()-1/T-arb(fmpq(w["S"]))
    assert beta > 0 and arb(10).log() < 2*L < arb(11).log()
    powers = [(2, 2), (3, 3), (4, 2), (5, 5), (7, 7), (8, 2), (9, 3)]
    comb = [(arb(n).log(), 2*arb(p).log()/arb(n).sqrt()) for n, p in powers]
    terms = [(int(k)*arb(row["p"]).log(), arb(fmpq(v)))
             for row in w["primes"] for k, v in row["b"].items()]
    strip = arb(1)/4
    rho = 1+arb(2).sqrt()
    sym = arb(9)+2*(T+2)+arb.pi().log()+abs(beta)
    sym += sum((abs(c)*(lam*strip).cosh() for lam, c in comb+terms), arb(0))
    entry = 2*L*(4*SIZE-3)*(2*L*strip).exp()*sym
    # h=1/2, sum of 1000 panels: 4*T*M/(pi*(rho-1)*rho^q).
    eps_Q = 4*T*entry/(arb.pi()*(rho-1)*rho**ORDER)
    assert SIZE*eps_Q < arb("1e-55")
    az = (arb(1)/4).digamma()-arb.pi().log()
    at = acb(arb(1)/4, T/2).digamma().real-arb.pi().log()
    real_bound = abs(az).max(abs(at))+abs(beta)+sum((abs(c) for _, c in comb+terms), arb(0))
    eps_D, eps_B = tail_budget(L, T, SIZE, real_bound)
    return L, T, beta, comb, terms, {"N": SIZE, "L": "119/100", "T": "500",
        "CC_degree": ORDER, "bits": BITS, "S_exact": w["S"], "envelope": env,
        "beta": str(beta), "M_entry": str(entry), "symbol_real_bound": str(real_bound),
        "eps_Q_per_entry": str(eps_Q), "eps_D": str(eps_D), "eps_B": str(eps_B)}, eps_Q, eps_D, eps_B


def series(x, n, modified=False):
    prefactor = arb(1)
    for j in range(1, n+1):
        prefactor *= x/(2*j+1)
    term = total = arb(1)
    for k in range(2000):
        ratio = x*x/(2*(k+1)*(2*n+2*k+3))
        following = term*ratio*(1 if modified else -1)
        if ratio < arb(1)/2 and abs(following) < arb(2)**(-ctx.prec+64):
            return prefactor*(total+error_ball(2*abs(following)))
        total += following
        term = following
    raise ArithmeticError("series tail did not close")


def transforms(t, L, scales):
    x = L*t
    if x == 0:
        return [(2*L).sqrt()]+[arb(0)]*(SIZE-1)
    top = 2*SIZE+64
    b = [arb(0)]*(top+2)
    b[top], b[top+1] = series(x, top), series(x, top+1)
    for n in range(top, 0, -1):
        b[n-1] = (2*n+1)*b[n]/x-b[n+1]
    assert b[0].overlaps(x.sinc()), "j0 normalization discrepancy"
    out = [scales[k]*b[2*k] for k in range(SIZE)]
    width = max(v.rad() for v in out)
    assert width < arb("1e-65"), f"recurrence widths insufficient: {width}"
    return out


def partial(start, stop, checkpoint):
    L, T, beta, comb, terms, budget, eps_Q, eps_D, eps_B = setup()
    checkpoint(budget, "budget.json")
    nodes, weights = cc_arb(ORDER)
    scales = [(-1)**k*(2*L*(4*k+1)).sqrt() for k in range(SIZE)]
    C = arb_mat(SIZE, SIZE)
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
        X = arb_mat([[v[i] for v in columns] for i in range(SIZE)])
        Y = arb_mat([[v[i]*w for v, w in zip(columns, multipliers)] for i in range(SIZE)])
        C += X*Y.transpose()
        checkpoint({"panels_done": panel-start+1, "panels_total": stop-start,
                    "assembly_elapsed_s": time.monotonic()-first})
    # Both entries enclose the same integral. Averaging preserves containment
    # and makes the stored midpoint and radius matrices exactly symmetric.
    C = (C+C.transpose())/2
    checkpoint({"start": start, "stop": stop, "N": SIZE, "triangle": serialize_matrix(C)}, "matrix.json")
    radius = max(sum((C[i, j].rad() for j in range(SIZE)), arb(0)) for i in range(SIZE))
    assert radius < arb("1e-55"), "arithmetic entry error too wide"
    return {"start": start, "stop": stop, "assembly_s": time.monotonic()-first,
            "arithmetic_row_radius": str(radius), "status": "completed"}


def from_triangle(data):
    A = arb_mat(SIZE, SIZE)
    pos = 0
    for i in range(SIZE):
        for j in range(i+1):
            mid, rad = data["triangle"][pos]
            A[i, j] = A[j, i] = arb(tuple(mid), tuple(rad))
            pos += 1
    assert pos == len(data["triangle"])
    return A


def residual_bound(A, shift, checkpoint):
    """A rounded factor is only a witness. Arb checks its entire residual."""
    from mpmath import mp
    with mp.workdps(110):
        M = mp_matrix(A, mp)
        s = mp.mpf(shift)
        try:
            B = mp.cholesky(M-s*mp.eye(SIZE))
        except ValueError as exc:
            return {"factor_exists": False, "reason": str(exc)}
        factor = arb_mat(SIZE, SIZE)
        for i in range(SIZE):
            for j in range(i+1):
                sign, man, exp, _ = B[i, j]._mpf_
                factor[i, j] = arb(((-1 if sign else 1)*int(man), int(exp)))
        exact_mid = arb_mat([[A[i, j].mid() for j in range(SIZE)] for i in range(SIZE)])
        shift_ball = arb(fmpq(str(Fraction(shift))))
        res = exact_mid-factor*factor.transpose()
        for i in range(SIZE):
            res[i, i] -= shift_ball
        r = max(sum((abs(res[i, j]) for j in range(SIZE)), arb(0)).abs_upper() for i in range(SIZE))
        e = max(sum((A[i, j].rad() for j in range(SIZE)), arb(0)).abs_upper() for i in range(SIZE))
        checkpoint({"shift_exact": shift, "triangle": serialize_matrix(factor)}, "factor.json")
        return {"factor_exists": True, "r": str(r), "e": str(e),
                "leading_lower_ball": str(shift_ball-r-e), "lower": shift_ball-r-e}


def reduce(paths, checkpoint):
    L, T, beta, comb, terms, budget, eps_Q, eps_D, eps_B = setup()
    checkpoint(budget, "budget.json")
    A = arb_mat(SIZE, SIZE)
    coverage = []
    for path in paths:
        data = json.loads(Path(path).read_text())
        A += from_triangle(data)
        coverage += list(range(data["start"], data["stop"]))
    assert sorted(coverage) == list(range(1000)), "missing or repeated panel"
    poles = [(2*L*(4*k+1)).sqrt()*series(L/2, 2*k, True) for k in range(SIZE)]
    for i in range(SIZE):
        for j in range(i+1):
            v = A[i, j]+2*poles[i]*poles[j]+error_ball(eps_Q)
            if i == j:
                v += beta
            A[i, j] = A[j, i] = v
    checkpoint({"N": SIZE, "triangle": serialize_matrix(A)}, "matrix.json")
    evidence = residual_bound(A, "5.718e-48", checkpoint)
    if not evidence["factor_exists"]:
        return {"status": "inconclusive", "evidence": evidence}
    lower = evidence.pop("lower").min(beta-eps_D)-eps_B
    safe = "5.7179e-48"
    assert lower > arb(fmpq(str(Fraction(safe))))
    assert lower < arb("2.78e-38")
    # In-band constant mutation H -> H-C, beta -> beta-C gives exactly R-CI.
    # C=100 supplies a large negative constant-window Rayleigh quotient.
    # It deliberately violates the support identity; it is no new zeta claim.
    mutant = arb_mat(A)
    for i in range(SIZE):
        mutant[i, i] -= 100
    lesion_rayleigh = mutant[0, 0]
    assert lesion_rayleigh < 0
    # A negative first diagonal stops the same midpoint factor proposal.
    lesion = residual_bound(mutant, "0", checkpoint)
    assert not lesion["factor_exists"]
    return {"status": "completed", "scope": "full even sector", "budget": budget,
            "positivity": evidence, "safe_lower_decimal": safe,
            "lower_ball": str(lower), "lower_exact_dyadic": list(map(int, lower.lower().man_exp())),
            "passes_requested_5_7178e_48": bool(lower > arb("5.7178e-48")),
            "passes_author_5_71789230595e_48": bool(lower > arb("5.71789230595e-48")),
            "K1": bool(lower < arb("2.78e-38")),
            "lesion": {"constant": "-100", "beta_adjustment": "-100",
                       "constant_window_rayleigh": str(lesion_rayleigh), "factor_rejected": not lesion["factor_exists"]}}
