"""Check two exact square-construction candidates for the full theta kernel.

The score jets carry Arb enclosures including every omitted theta term.
Conditional-moment quadrature and eigenvalues are floating-point diagnostics.
No zero table or RH assumption enters either computation.
"""

from fractions import Fraction
import json
from pathlib import Path
from time import perf_counter

from flint import arb, ctx
from mpmath import mp

HERE = Path(__file__).resolve().parent
SEPARATIONS = ("0", "0.25", "0.5", "0.75", "1", "1.25", "1.5", "1.75",
               "2", "2.5", "3", "3.5")


def derivative_polynomial(order):
    """P_j for k_n^(j)(u)=exp(u/2) P_j(pi*n^2*exp(2u)) exp(-x)."""
    if not isinstance(order, int) or order < 0:
        raise ValueError("order must be a nonnegative integer")
    coefficients = [Fraction(0), Fraction(-6), Fraction(4)]
    for _ in range(order):
        new = [Fraction(0) for _ in range(len(coefficients)+1)]
        for j, coefficient in enumerate(coefficients):
            new[j] += (Fraction(1, 2)+2*j)*coefficient
            new[j+1] -= 2*coefficient
        coefficients = new
    return coefficients


def _arb_fraction(value):
    return arb(value.numerator)/value.denominator


def theta_jet_ball(u, order, terms=8):
    """Full-kernel derivative at real u>=0, including a geometric tail."""
    if terms < 1 or not u >= 0:
        raise ValueError("positive terms and nonnegative u are required")
    coefficients = derivative_polynomial(order)
    degree = len(coefficients)-1
    scale = arb.pi()*(2*u).exp()
    total = arb(0)
    for n in range(1, terms+1):
        x = scale*n*n
        value = arb(0)
        for coefficient in reversed(coefficients):
            value = value*x+_arb_fraction(coefficient)
        total += value*(-x).exp()
    x0 = scale*(terms+1)**2
    if not x0 >= 1:
        raise ArithmeticError("polynomial tail majorant does not apply")
    q = (arb(terms+2)/(terms+1))**(2*degree)*(-scale*(2*terms+3)).exp()
    if not 0 <= q < 1:
        raise ArithmeticError("geometric ratio not proved below one")
    mass = sum(abs(c) for c in coefficients)
    tail = (u/2).exp()*_arb_fraction(mass)*x0**degree*(-x0).exp()/(1-q)
    enclosed = (u/2).exp()*total+arb(0, tail)
    return enclosed, tail


def score_check(bits):
    with ctx.workprec(bits):
        u = arb(1)/10
        jets = [theta_jet_ball(u, j) for j in range(3)]
        k, dk, ddk = [v for v, _ in jets]
        if not k > 0:
            raise ArithmeticError("kernel denominator sign undecided")
        score = -dk/k
        slope = score*score-ddk/k
        if not score > 0 or not slope > 0:
            raise ArithmeticError("positive score and slope not established")
        diagonal = 4*u/score-2*u*u*slope/(score*score)
        off_diagonal = 2/slope
        eigenvalue = diagonal-off_diagonal
        square_identity = -2*(u*slope-score)**2/(score*score*slope)
        if not eigenvalue < 0 or not eigenvalue.overlaps(square_identity):
            raise ArithmeticError("local Gram obstruction not enclosed")
        central = [theta_jet_ball(arb(0), j)[0] for j in (0, 2, 4)]
        a = -central[1]/central[0]
        b = -central[2]/(6*central[0])+central[1]**2/(2*central[0]**2)
        if not a > 0 or not b > 0:
            raise ArithmeticError("central nonlinearity signs undecided")
        text = eigenvalue.str(45)
        if not arb(text) < 0:
            raise ArithmeticError("serialized negative enclosure lost its sign")
        return {"bits": bits, "u": "1/10", "theta_terms": 8,
                "jets": [v.str(45) for v, _ in jets],
                "tail_bounds": [v.str(20) for _, v in jets],
                "score": score.str(45), "slope": slope.str(45),
                "diagonal": diagonal.str(45), "off_diagonal": off_diagonal.str(45),
                "negative_eigenvalue": text, "identity_value": square_identity.str(45),
                "central_linear": a.str(45), "central_cubic": b.str(45)}


def theta_kernel(u, terms=8):
    """Float evaluation, using the exact evenness of the full kernel."""
    u = abs(u)
    scale = mp.pi*mp.exp(2*u)
    return mp.exp(u/2)*mp.fsum(
        (4*x*x-6*x)*mp.exp(-x) for x in (scale*n*n for n in range(1, terms+1))
    )


def conditional_ratios(separation, max_order=3, cutoff=4, terms=8):
    """K_n(x)/K_0(x), float quadrature on 0<=w<=cutoff.

    No interval bound on quadrature or the omitted w tail is asserted here.
    The exact full-kernel definition, not this discretization, is in SQUARES.md.
    """
    if max_order < 1 or cutoff < 2 or terms < 1:
        raise ValueError("positive order/terms and cutoff>=2 are required")
    x = mp.mpf(separation)
    base = theta_kernel(x/2, terms)**2
    cache = {}
    def density(w):
        if w not in cache:
            cache[w] = theta_kernel((x-w)/2, terms)*theta_kernel((x+w)/2, terms)/base
        return cache[w]
    breaks = [mp.mpf(0), mp.mpf(1)/4, mp.mpf(1)/2, mp.mpf(1), mp.mpf(2), mp.mpf(cutoff)]
    denominator = mp.quadgl(density, breaks)
    if not denominator > 0:
        raise ArithmeticError("conditional normalization is not positive")
    return [mp.quadgl(lambda w: w**(2*n)*density(w), breaks)
            / (mp.factorial(2*n)*denominator) for n in range(1, max_order+1)]


def run():
    started = perf_counter()
    result = {"rh_resolved": False, "score_grade": "Arb enclosures with theta tail bounds",
              "ratio_grade": "floating point only", "score_runs": [], "ratio_runs": []}
    for bits in (192, 256):
        result["score_runs"].append(score_check(bits))
        print(f"score: bits={bits}, negative two-point eigenvalue enclosed", flush=True)
    for dps in (35, 55):
        with mp.workdps(dps):
            values, rows = {}, []
            for i, x in enumerate(SEPARATIONS, 1):
                values[mp.mpf(x)] = conditional_ratios(x)
                rows.append({"x": x, "ratios": [mp.nstr(v, dps-6) for v in values[mp.mpf(x)]]})
                print(f"ratios: dps={dps}, separation {i}/{len(SEPARATIONS)}", flush=True)
            matrices = []
            for step in (mp.mpf(1)/4, mp.mpf(1)/2):
                for order in (1, 2, 3):
                    normalization = values[mp.mpf(0)][order-1]
                    matrix = mp.matrix([[values[abs(i-j)*step][order-1]/normalization
                                         for j in range(8)] for i in range(8)])
                    minimum = mp.eigsy(matrix, eigvals_only=True)[0]
                    matrices.append({"order": order, "step": str(step), "size": 8,
                                     "min_eigenvalue": mp.nstr(minimum, dps-6)})
            result["ratio_runs"].append({"dps": dps, "theta_terms": 8, "w_cutoff": 4,
                                        "rows": rows, "matrices": matrices})
    negatives = sum(mp.mpf(m["min_eigenvalue"]) < 0
                    for run in result["ratio_runs"] for m in run["matrices"])
    result["counts"] = {
        "score_enclosures": len(result["score_runs"]),
        "conditional_ratios": sum(len(row["ratios"]) for run in result["ratio_runs"] for row in run["rows"]),
        "gram_matrices": sum(len(run["matrices"]) for run in result["ratio_runs"]),
        "negative_ratio_gram_matrices": negatives,
    }
    result["elapsed_seconds"] = round(perf_counter()-started, 3)
    (HERE/"squares_results.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": "completed", **result["counts"],
                      "elapsed_seconds": result["elapsed_seconds"]}), flush=True)


if __name__ == "__main__":
    run()
