"""Independent referee computations. Unrun; execute only on approved Modal jobs.

No author implementation is imported. The frozen JSON supplies an exact witness,
not algorithms. The zeta path carries explicit quadrature and series remainders;
the DH control and the preliminary moment checks remain measured.
See REVIEW.md for the mathematical contract and unresolved obligations.
"""

import copy
import json
import math
import random
from fractions import Fraction
from pathlib import Path


def load_witness():
    data = json.loads(Path(__file__).with_name("frozen_envelope.json").read_text())
    return next(r for r in data["runs"]
                if r["L"] == "4/5" and r["kernel"] == "sine" and r["D"] == 16)


def sine_moments(mp, degree):
    a = [mp.sin(mp.pi * (j + 1) / (degree + 2)) for j in range(degree + 1)]
    norm = mp.fsum(x * x for x in a)
    return [mp.fsum(a[j] * a[j + k] for j in range(degree + 1 - k)) / norm
            for k in range(degree + 1)]


def separable(mp, degree=16):
    """Two-atom moment solutions, derived explicitly for p=2,3 at L=4/5."""
    rho = sine_moments(mp, degree)
    a = mp.log(2) / mp.sqrt(2) / rho[1]
    b = mp.log(2) / 2 / rho[2]
    M2 = (b + mp.sqrt(b * b + 8 * a * a)) / 2
    theta2 = mp.acos(-a / M2)
    M3 = mp.log(3) / mp.sqrt(3) / rho[1]
    return {
        2: (M2, {k: 2 * M2 * rho[k] * mp.cos(k * theta2)
                 for k in range(3, degree + 1)}),
        3: (M3, {k: 2 * M3 * rho[k] * (-1)**k
                 for k in range(2, degree + 1)}),
    }


def controls():
    """S, witness identity checks, K3, and explicit planted lesions."""
    from mpmath import mp
    with mp.workdps(90):
        witness = load_witness()
        construction = separable(mp)
        rho = sine_moments(mp, 16)
        records = []
        for row in witness["primes"]:
            p, m = row["p"], row["m"]
            M, ideal = construction[p]
            residual = mp.fsum(abs(mp.mpf(value) - ideal[int(k)])
                               for k, value in row["b"].items())
            slack = mp.mpf(row["M_p"]) - M - residual
            assert slack > 0, "frozen polynomial not covered by kernel decomposition"
            # Check the low moments of the two-atom construction independently.
            theta = mp.pi if p == 3 else mp.acos(-mp.log(2) / mp.sqrt(2) / rho[1] / M)
            moment_defect = max(abs(M * rho[k] * mp.cos(k * theta)
                                   + mp.log(p) / mp.power(p, mp.mpf(k) / 2))
                                for k in range(1, m + 1))
            assert moment_defect < mp.mpf("1e-80")
            records.append({"p": p, "M_ideal": mp.nstr(M, 85),
                            "coefficient_l1_error": mp.nstr(residual, 30),
                            "positive_slack_measured": mp.nstr(slack, 30)})
        ideal_sum = mp.fsum(x[0] for x in construction.values())
        frozen_sum = mp.fsum(mp.mpf(x["M_p"]) for x in witness["primes"])
        assert sum((Fraction(x["M_p"]) for x in witness["primes"]), Fraction(0)) == Fraction(witness["S"])
        assert abs(frozen_sum - ideal_sum - mp.mpf("2e-8")) < mp.mpf("1e-14")

        # Piecewise constant complex functions: integrate their overlap exactly
        # in the time variable. This is a finite identity test, not a truncated
        # frequency integral with an unaccounted tail.
        rng = random.Random(271828)
        L = mp.mpf(4) / 5
        edges = [-L + 2 * L * j / 16 for j in range(17)]
        vectors = [[mp.mpc(rng.randint(-9, 9), rng.randint(-9, 9))
                    for _ in range(16)] for _ in range(8)]
        vectors += [[mp.mpf(1)] * 16,
                    [mp.mpf(-1)] * 8 + [mp.mpf(1)] * 8]

        def corr(values, shift):
            return mp.fsum(values[i] * mp.conj(values[j]) * max(mp.mpf(0),
                min(edges[i + 1], edges[j + 1] + shift)
                - max(edges[i], edges[j] + shift))
                for i in range(16) for j in range(16))

        freqs = [mp.mpf(2) * L]
        freqs += [int(k) * mp.log(row["p"]) for row in witness["primes"]
                  for k in row["b"]]
        oob = max(abs(corr(v, f)) for v in vectors for f in freqs)
        assert oob < mp.mpf("1e-80")
        inband = 2 * L - mp.mpf(1) / 20
        defect = corr(vectors[-2], inband) / (2 * L)
        assert abs(defect - mp.mpf(1) / 32) < mp.mpf("1e-80")

        # Mutation is applied to the actual supplied polynomial. A torus
        # witness suffices to refute a per-prime envelope; no phase search
        # along a long t-interval is needed.
        flipped = copy.deepcopy(witness["primes"][0])
        flipped["b"] = {k: -mp.mpf(v) for k, v in flipped["b"].items()}
        worst = mp.inf
        for j in range(2049):
            theta = mp.pi * j / 2048
            phi = mp.fsum(2 * mp.log(2) / mp.power(2, mp.mpf(k) / 2)
                         * mp.cos(k * theta) for k in (1, 2))
            h = mp.fsum(v * mp.cos(int(k) * theta) for k, v in flipped["b"].items())
            worst = min(worst, mp.mpf(flipped["M_p"]) - phi + h)
        assert worst < -mp.mpf("1e-4"), "one-prime sign lesion escaped"

        # Independently enumerate the original comb. Dropping 4 makes a
        # different form even if its leading block happens to remain positive.
        actual = {n for n in range(2, 6) if mp.log(n) < 2 * L}
        assert actual == {2, 3, 4}
        damaged = actual - {4}
        # The same defining-coefficient gate is used by the matrix assembler.
        try:
            validate_zeta_support(damaged)
        except ValueError:
            dropped_caught = True
        else:
            dropped_caught = False
        assert dropped_caught, "dropped prime power escaped the assembly gate"
        dropped_shift_defect = mp.log(2) * (1 - mp.log(4) / (2 * L))
        assert dropped_shift_defect > 0
        frequency_checks = frequency_k3(witness)
        return {"grade": "measured", "S_ideal": mp.nstr(ideal_sum, 85),
                "S_frozen": witness["S"], "primes": records,
                "K3_time_domain_overlap_max": str(oob),
                "K3_seed": 271828, "K3_functions": len(vectors),
                "inband_normalized_defect": mp.nstr(defect, 40),
                "one_prime_sign_lesion_min": mp.nstr(worst, 40),
                "dropped_power_constant_test_defect": mp.nstr(dropped_shift_defect, 40),
                "lesions_detected": ["inband", "one_prime_sign", "dropped_power"],
                "frequency_K3": frequency_checks,
                "nonclaim": "No matrix positivity or integral enclosure follows."}


def frequency_k3(witness):
    """Measured frequency integrals, with an explicit analytic tail majorant.

    Polynomial window tests vanish with their first derivative at the edges.
    Integration by parts three times bounds their transforms by B/|t|^3.
    The majorant is evaluated in float64 here, not claimed as an enclosure.
    """
    import numpy as np
    from numpy.polynomial import polynomial as pol
    from numpy.polynomial.legendre import leggauss
    L = .8
    rng = random.Random(314159)
    taper = np.array([L**4, 0, -2*L*L, 0, 1])
    polys = [pol.polymul(taper, [complex(rng.randint(-2, 2), rng.randint(-2, 2))
                               for _ in range(4)]) for _ in range(4)]
    polys.append(pol.polymul(taper, [0, 1]))  # odd
    B = []
    for p in polys:
        second, third = pol.polyder(p, 2), pol.polyder(p, 3)
        B.append(abs(pol.polyval(L, second))+abs(pol.polyval(-L, second))
                 + 2*L*sum(abs(c)*L**k for k, c in enumerate(third)))
    terms = [(int(k)*math.log(row["p"]), float(Fraction(v)))
             for row in witness["primes"] for k, v in row["b"].items()]
    Hnorm = sum(abs(c) for _, c in terms)
    records = []
    for cutoff, q, xorder in [(128, 20, 256), (256, 24, 384)]:
        xs, xw = leggauss(xorder)
        xs, xw = L*xs, L*xw
        samples = np.array([pol.polyval(xs, p)*xw for p in polys]).T
        ts, tw = leggauss(q)
        sums = np.zeros((len(polys), 2))
        planted = 0.0
        for panel in range(cutoff):
            t = panel+(ts+1)/2
            weight = tw/2
            phase = np.exp(1j*np.outer(t, xs))
            Fpos, Fneg = phase @ samples, phase.conj() @ samples
            density = (abs(Fpos)**2+abs(Fneg)**2)/(2*math.pi)
            H = sum(c*np.cos(lam*t) for lam, c in terms)
            sums[:, 0] += (weight*H) @ density
            sums[:, 1] += (weight*np.cos(2*L*t)) @ density
            Fconstant = math.sqrt(2*L)*np.sinc(L*t/math.pi)
            planted += float(np.dot(weight, Fconstant**2*np.cos((2*L-.05)*t)/math.pi))
        tail = np.array(B)**2/(5*math.pi*cutoff**5)
        limits = tail[:, None]*np.array([Hnorm, 1.0])[None, :]
        assert np.all(abs(sums) <= limits+1e-10), "frequency K3 exceeds tail budget"
        constant_tail = 2/(math.pi*L*cutoff)
        assert abs(planted-1/32) < constant_tail+1e-10
        assert planted-constant_tail > 0, "frequency in-band lesion unresolved"
        records.append({"cutoff": cutoff, "t_order": q, "x_order": xorder,
                        "partial_integrals": sums.tolist(),
                        "analytic_tail_majorants_measured": limits.tolist(),
                        "inband_constant_partial": planted,
                        "inband_constant_tail_majorant": constant_tail,
                        "grade": "measured; floating quadrature errors not enclosed"})
    return records


def validate_zeta_support(candidate):
    """Exact integer prime-power enumeration for the frozen 4/5 window.

    The endpoint inequalities log(4)<8/5<log(5) are checked in Arb by the
    matrix caller. This gate validates every retained power, not just primes.
    """
    expected = set()
    for p in range(2, 5):
        if any(p % d == 0 for d in range(2, p)):
            continue
        power = p
        while power <= 4:
            expected.add(power)
            power *= p
    if set(candidate) != expected:
        raise ValueError("comb support differs from defining prime-power sum")


def cc_arb(order):
    """Clenshaw-Curtis nodes and weights, with both endpoints, on [-1,1]."""
    from flint import arb
    assert order > 0 and order % 2 == 0
    theta = [arb.pi() * j / order for j in range(order + 1)]
    nodes = [arb(1)] + [t.cos() for t in theta[1:-1]] + [arb(-1)]
    weights = [arb(1) / (order * order - 1)]
    for j in range(1, order):
        v = arb(1)
        for k in range(1, order // 2):
            v -= 2 * (2 * k * theta[j]).cos() / (4 * k * k - 1)
        v -= (order * theta[j]).cos() / (order * order - 1)
        weights.append(2 * v / order)
    weights.append(weights[0])
    assert abs(sum(weights, arb(0)) - 2) < arb("1e-70")
    assert abs(sum((w*x*x for w, x in zip(weights, nodes)), arb(0)) - arb(2)/3) < arb("1e-70")
    return nodes, weights


def envelope_arb(witness):
    """Enclose the two-atom proof for the exact rational frozen coefficients."""
    from flint import arb, fmpq
    a = [(arb.pi()*(j+1)/18).sin() for j in range(17)]
    norm = sum((x*x for x in a), arb(0))
    rho = [sum((a[j]*a[j+k] for j in range(17-k)), arb(0))/norm
           for k in range(17)]
    if sorted(row["p"] for row in witness["primes"]) != [2, 3]:
        raise ValueError("unexpected frozen prime inventory")
    total = Fraction(0)
    for row in witness["primes"]:
        p, m = row["p"], row["m"]
        if p == 2 and m == 2:
            u = arb(2).log()/arb(2).sqrt()/rho[1]
            v = arb(2).log()/2/rho[2]
            M = (v+(v*v+8*u*u).sqrt())/2
            theta = (-u/M).acos()
        elif p == 3 and m == 1:
            M = arb(3).log()/arb(3).sqrt()/rho[1]
            theta = arb.pi()
        else:
            raise ValueError("unexpected frozen prime set")
        if set(map(int, row["b"])) != set(range(m+1, 17)):
            raise ValueError("missing frozen out-of-band coefficient")
        loss = arb(0)
        for k, value in row["b"].items():
            k = int(k)
            if not k*arb(p).log() >= arb(8)/5:
                raise ValueError("in-band correction")
            loss += abs(arb(fmpq(value))-2*M*rho[k]*(k*theta).cos())
        constant = arb(fmpq(row["M_p"]))
        if not constant-M-loss > 0:
            raise ArithmeticError("envelope residual not dominated")
        total += Fraction(row["M_p"])
    if total != Fraction(witness["S"]):
        raise ValueError("inconsistent sum of constants")


def error_ball(radius):
    from flint import arb
    upper = tuple(int(x) for x in radius.abs_upper().man_exp())
    return arb(0, upper)


def spherical_series(x, n, modified=False):
    """Power series with a geometric bound on its uncomputed tail.

    This proposed enclosure routine has not been run or independently tested.
    Ratio magnitudes decrease with the summation index. See REVIEW.md.
    """
    from flint import arb
    prefactor = arb(1)
    for j in range(1, n + 1):
        prefactor *= x / (2*j + 1)
    term = total = arb(1)
    for k in range(1200):
        ratio = x*x / (2*(k+1)*(2*n+2*k+3))
        following = term * ratio * (1 if modified else -1)
        if ratio < arb(1)/2 and abs(following) < arb("1e-130"):
            return prefactor * (total + error_ball(2*abs(following)))
        total += following
        term = following
    raise ArithmeticError("series did not close its tail within 1200 terms")


def legendre_transform(t, L, size, extra):
    """Downward recurrence from two series enclosures, without normalization."""
    from flint import arb
    x = L * t
    if x == 0:
        return [(2 * L).sqrt()] + [arb(0)] * (size - 1)
    top = 2 * size + extra
    seq = [arb(0)] * (top + 2)
    seq[top] = spherical_series(x, top)
    seq[top+1] = spherical_series(x, top+1)
    for n in range(top, 0, -1):
        seq[n - 1] = (2 * n + 1) * seq[n] / x - seq[n + 1]
    if not seq[0].overlaps(x.sinc()):
        raise ArithmeticError("independent j0 normalization check failed")
    return [(-1)**k * (2 * L * (4 * k + 1)).sqrt() * seq[2*k]
            for k in range(size)]


def interval_ldl(matrix, shift):
    """Unpivoted Schur elimination; ambiguous pivots stop inconclusively."""
    from flint import arb
    n = matrix.nrows()
    a = [[matrix[i, j] - (shift if i == j else 0) for j in range(n)] for i in range(n)]
    for k in range(n):
        pivot = a[k][k]
        if pivot < 0:
            return {"status": "negative_pivot", "index": k, "pivot": str(pivot)}
        if not pivot > arb(0):
            return {"status": "undecided", "index": k, "pivot": str(pivot)}
        for i in range(k+1, n):
            for j in range(i, n):
                a[i][j] -= a[k][i]*a[k][j]/pivot
                a[j][i] = a[i][j]
    return {"status": "positive_definite"}


def tail_budget(L, T, size, symbol_bound):
    """L2 bounds on tail transforms and pole coefficients, derived afresh."""
    from flint import arb
    n = 2*size

    def tail_square(x, multiplier=arb(1)):
        first = (2*L*(2*n+1)).sqrt()*multiplier
        for k in range(1, n+1):
            first *= x/(2*k+1)
        ratio = x*x/((2*n+3)*(2*n+5))*(arb(2*n+5)/(2*n+1)).sqrt()
        if not ratio < 1:
            raise ArithmeticError("tail geometric majorant is not decreasing")
        return first*first/(1-ratio*ratio)

    fourier_tail = tail_square(L*T)
    pole_tail = tail_square(L/2, (L/2).exp())
    K = T*symbol_bound/arb.pi()
    eps_D = K*fourier_tail  # positive even pole term can be discarded here
    eps_B = K*(2*L*fourier_tail).sqrt() + 2*((L+L.sinh())*pole_tail).sqrt()
    return eps_D, eps_B


def serialize_matrix(matrix):
    """Exact dyadic midpoints and arithmetic radii, before any eigenanalysis."""
    return [[[int(x) for x in matrix[i, j].mid().man_exp()],
             [int(x) for x in matrix[i, j].rad().man_exp()]]
            for i in range(matrix.nrows()) for j in range(i + 1)]


def mp_matrix(matrix, mp):
    out = mp.matrix(matrix.nrows())
    for i in range(matrix.nrows()):
        for j in range(matrix.ncols()):
            m, e = matrix[i, j].mid().man_exp()
            out[i, j] = mp.mpf(int(m)) * mp.power(2, int(e))
    return out


def leading(order, bits, extra, checkpoint):
    """Same 96-dimensional space, different quadrature; no author code."""
    from flint import arb, acb, arb_mat, ctx, fmpq
    from mpmath import mp
    previous = ctx.prec
    ctx.prec = bits
    try:
        L, T, size = arb(4)/5, arb(100), 96
        witness = load_witness()
        envelope_arb(witness)
        S = arb(fmpq(witness["S"]))
        beta = (T / (2 * arb.pi())).log() - 1/T - S
        if not beta > 0:
            raise ArithmeticError("tail floor is not positive")
        terms = [(arb(int(k)) * arb(row["p"]).log(), arb(fmpq(v)))
                 for row in witness["primes"] for k, v in row["b"].items()]
        comb = [(arb(n).log(), 2 * arb(p).log() / arb(n).sqrt())
                for n, p in [(2, 2), (3, 3), (4, 2)]]
        if not arb(4).log() < 2*L < arb(5).log():
            raise ArithmeticError("prime-power endpoint comparison undecided")
        validate_zeta_support([2, 3, 4])
        nodes, weights = cc_arb(order)
        C = arb_mat(size, size)
        for panel in range(200):
            ts = [arb(panel)/2 + (x + 1)/4 for x in nodes]
            columns = [legendre_transform(t, L, size, extra) for t in ts]
            multipliers = []
            for t, w in zip(ts, weights):
                arch = acb(arb(1)/4, t/2).digamma().real - arb.pi().log()
                P = sum((c * (lam*t).cos() for lam, c in comb), arb(0))
                H = sum((c * (lam*t).cos() for lam, c in terms), arb(0))
                multipliers.append(w * (arch - P + H - beta) / (4 * arb.pi()))
            X = arb_mat([[v[i] for v in columns] for i in range(size)])
            Y = arb_mat([[v[i] * w for v, w in zip(columns, multipliers)]
                         for i in range(size)])
            C += X * Y.transpose()
            if panel % 20 == 19:
                checkpoint({"phase": "assembly", "panels_done": panel + 1,
                            "panels_total": 200})
        poles = [(2*L*(4*k+1)).sqrt()*spherical_series(L/2, 2*k, modified=True)
                 for k in range(size)]
        # Chebyshev interpolation remainder integrated over each panel.
        # The strip is |Im t| <= 1/4; Re(1/4 +/- it/2) >= 1/8.
        rho = 1 + arb(2).sqrt()
        strip = arb(1)/4
        M_symbol = arb(9)+2*(T+2)+arb.pi().log()+abs(beta)
        M_symbol += sum((abs(c)*(lam*strip).cosh() for lam, c in comb+terms), arb(0))
        M_entry = 2*L*(4*size-3)*(2*L*strip).exp()*M_symbol
        eps_Q = 200*2*M_entry/(arb.pi()*(rho-1)*rho**order)
        arch_zero = arb(arb(1)/4).digamma()-arb.pi().log()
        arch_T = acb(arb(1)/4, T/2).digamma().real-arb.pi().log()
        real_bound = abs(arch_zero).max(abs(arch_T))+abs(beta)
        real_bound += sum((abs(c) for _, c in comb+terms), arb(0))
        eps_D, eps_B = tail_budget(L, T, size, real_bound)
        A = arb_mat(size, size)
        for i in range(size):
            for j in range(size):
                A[i, j] = (C[i, j] + C[j, i])/2 + 2*poles[i]*poles[j]
                A[i, j] += error_ball(eps_Q)
            A[i, i] += beta
        raw = {"N": size, "quadrature_order": order, "bits": bits,
               "recurrence_extra": extra, "triangle": serialize_matrix(A),
               "phase": "matrix_before_eigenanalysis", "eps_Q_per_entry": str(eps_Q),
               "eps_D": str(eps_D), "eps_B": str(eps_B),
               "grade": "enclosure-carrying conditional on reviewed analytic budgets"}
        checkpoint(raw, artifact="matrix.json")
        ldl = {s: interval_ldl(A, arb(s)) for s in ["1.158e-17", "1.1585e-17"]}
        lower = arb("1.158e-17").min(beta-eps_D)-eps_B
        bound_ok = ldl["1.158e-17"]["status"] == "positive_definite"
        K1 = bool(lower < arb("2.27e-17")) if bound_ok else None
        checkpoint({"phase": "LDL", "tests": ldl, "lower": str(lower),
                    "K1": K1}, artifact="ldl.json")
        with mp.workdps(95):
            M = mp_matrix(A, mp)
            vals = mp.eigsy(M, eigvals_only=True)
            smallest = vals[0]
            # A finite Ritz value is NOT a lower bound on the whole window.
            # This comparison is only a benchmark consistency check.
            agrees = mp.mpf("1.158e-17") < smallest < mp.mpf("1.1585e-17")
            benchmark = smallest < mp.mpf("2.27e-17")
            return {"grade": "measured", "N": size, "T": "100", "L": "4/5",
                    "S": witness["S"], "quadrature_order": order, "bits": bits,
                    "recurrence_extra": extra,
                    "lambda_min": mp.nstr(smallest, 85),
                    "next_eigenvalue": mp.nstr(vals[1], 70),
                    "author_bracket_agreement": bool(agrees),
                    "K1_ritz_consistency_only": bool(benchmark),
                    "ldl": ldl, "eps_Q_per_entry": str(eps_Q),
                    "eps_D": str(eps_D), "eps_B": str(eps_B),
                    "full_space_lower_bound": str(lower) if bound_ok else None,
                    "full_space_evidence": ("enclosure-carrying conditional on analytic budgets"
                                            if bound_ok else "unresolved"),
                    "safe_endpoint_1_1579e_17": bool(bound_ok and lower > arb("1.1579e-17")),
                    "K1_full_bound": K1,
                    "nonclaim": "Composite depends on analytic budgets and envelope proof."}
    finally:
        ctx.prec = previous


def dh_control(order, checkpoint):
    """Independent DH time form and the same frequency-split reduction.

    A negative finite Rayleigh value can refute positivity; a positive Ritz
    value cannot establish it. Float64 suffices only for the large negative
    control, subject to quadrature convergence. Constants from SOURCE.md §4.
    """
    import numpy as np
    from scipy.special import digamma
    from scipy.integrate import quad
    from scipy.linalg import eigh

    width = math.log(47)
    L, size, T = width/2, 65, 100.0
    kappa = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5)-1)
    coeff = [0.0] * 47
    series = lambda n: [0.0, 1.0, kappa, -kappa, -1.0][n % 5]
    for n in range(2, 47):
        coeff[n] = series(n)*math.log(n) - sum(
            coeff[d]*series(n//d) for d in range(2, n) if n % d == 0)
    assert abs(coeff[6]-(1+kappa*kappa)*math.log(6)) < 1e-12
    S = sum(2*abs(coeff[n])/math.sqrt(n) for n in range(2, 47))
    beta = math.log(5*T/(2*math.pi))-1/T-S
    ids = np.arange(size)

    def qmat(y):
        s = np.sin(2*math.pi*ids*y/width)
        out = np.empty((size, size))
        out[0, 0] = 2*(1-y/width)
        for i in range(1, size):
            out[0, i] = out[i, 0] = -math.sqrt(2)*s[i]/(math.pi*i)
            for j in range(1, size):
                first = (2*(1-y/width)*math.cos(2*math.pi*i*y/width)
                         if i == j else (s[j]-s[i])/(math.pi*(i-j)))
                out[i, j] = first-(s[i]+s[j])/(math.pi*(i+j))
        return out

    # A Gauss rule here differs from the zeta reimplementation's CC rule.
    # Both are constructed afresh; no rival implementation is imported.
    from numpy.polynomial.legendre import leggauss
    nodes, weights = leggauss(order)
    unit = np.eye(size)
    Q = (math.log(5/math.pi)+float(digamma(1))
         - math.log1p(-math.exp(-2*width))) * unit
    for x, wt in zip((nodes+1)*width/2, weights*width/2):
        Q += wt*(2*math.exp(-2*x)*unit-math.exp(-1.5*x)*qmat(x))/(-math.expm1(-2*x))
    for n in range(2, 47):
        Q -= coeff[n]/math.sqrt(n)*qmat(math.log(n))
    vals, vectors = eigh(Q)
    vector = vectors[:, 0]
    checkpoint({"phase": "DH time form", "lambda_min": float(vals[0]),
                "vector": vector.tolist(), "q_order": order}, artifact="dh_witness.json")

    def transforms(t):
        ans = np.empty(size)
        ans[0] = math.sqrt(2*L)*np.sinc(t*L/math.pi)
        k = ids[1:]
        ans[1:] = (-1.0)**k * math.sqrt(L) * (
            np.sinc(t*L/math.pi+k)+np.sinc(t*L/math.pi-k))
        return ans

    R = beta*unit
    # 50 panels, q=32 or 48, chosen independently of the author's rule.
    small_nodes, small_weights = leggauss(order//16)
    for panel in range(50):
        ts = 2*panel+small_nodes+1
        X = np.array([transforms(t) for t in ts]).T
        symbol = digamma(.75+.5j*ts).real+math.log(5/math.pi)
        for n in range(2, 47):
            symbol -= 2*coeff[n]/math.sqrt(n)*np.cos(ts*math.log(n))
        R += (X*(small_weights*(symbol-beta)/math.pi)) @ X.T
    rayleigh_Q = float(vector @ Q @ vector)
    rayleigh_R = float(vector @ R @ vector)
    # Evaluate the same witness through separate adaptive scalar quadrature.
    def integrand(t):
        vF = float(vector @ transforms(t))
        P = sum(2*coeff[n]/math.sqrt(n)*math.cos(t*math.log(n)) for n in range(2, 47))
        return (float(digamma(.75+.5j*t).real)+math.log(5/math.pi)-P-beta)*vF*vF/math.pi
    adaptive, error = quad(integrand, 0, T, epsabs=1e-9, limit=1200,
                           points=list(range(1, 100)))
    adaptive += beta*float(vector @ vector)
    negative = rayleigh_Q < -.1 and rayleigh_R < 0
    return {"grade": "measured", "L": "log(47)/2", "N": size,
            "time_quadrature_order": order, "S_absolute_coefficients": S,
            "beta": beta, "Q_rayleigh": rayleigh_Q, "R_rayleigh": rayleigh_R,
            "R_scalar_adaptive": adaptive, "adaptive_reported_error": error,
            "R_matrix_scalar_agreement": abs(adaptive-rayleigh_R) < 1e-7,
            "K2_negative_witness": negative,
            "domination_on_witness_measured": rayleigh_R <= rayleigh_Q+1e-7,
            "positive_result": False,
            "rejection_observed": negative or beta <= 0,
            "nonpositive_essential_floor": beta <= 0,
            "nonclaim": "Quadrature and floating errors are not rigorous enclosures."}


def run(unit, checkpoint):
    if unit == "controls":
        return controls()
    if unit == "leading160":
        return leading(160, 512, 96, checkpoint)
    if unit == "leading192":
        return leading(192, 640, 160, checkpoint)
    if unit == "dh512":
        return dh_control(512, checkpoint)
    if unit == "dh768":
        return dh_control(768, checkpoint)
    raise ValueError("unknown unit")
