"""Enclose an integer-vector witness against K_1/K_0 positive definiteness.

Arb quadrature covers the finite integral. Explicit bounds cover both the
omitted theta terms and the infinite integration tail. See SQUARES.md.
"""

import json
from pathlib import Path
from time import perf_counter

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
WITNESS = (627, -2154, 1692, 1729, -1773, -2321, 1223, 3028, -52, -3258,
           -1433, 2691, 2691, -1433, -3258, -52, 3028, 1223, -2321,
           -1773, 1729, 1692, -2154, 627)
NORM2 = sum(v*v for v in WITNESS)


def x2_tail(terms):
    """Upper bound for sum_(n>terms) (pi*n^2)^2 exp(-pi*n^2)."""
    if terms < 1:
        raise ValueError("positive theta cutoff required")
    a0 = arb.pi()*(terms+1)**2
    q = (arb(terms+2)/(terms+1))**4*(-arb.pi()*(2*terms+3)).exp()
    if not 0 <= q < 1:
        raise ArithmeticError("tail ratio not below one")
    return a0*a0*(-a0).exp()/(1-q)


def kernel_finite(z, terms):
    """Analytic extension of the positive-half-line theta partial sum."""
    scale = arb.pi()*(2*z).exp()
    return (z/2).exp()*sum(
        (4*x*x-6*x)*(-x).exp() for x in (scale*n*n for n in range(1, terms+1))
    )


def global_bounds(terms, cutoff):
    upper_sum = sum((arb.pi()*n*n)**2*(-arb.pi()*n*n).exp()
                    for n in range(1, terms+1))+x2_tail(terms)
    if not 4*upper_sum < 2:
        raise ArithmeticError("global kernel upper bound k<2 not proved")
    epsilon = 4*x2_tail(terms)
    rate = arb.pi()*cutoff.exp()-arb(9)/4
    if not rate > 0:
        raise ArithmeticError("integration tail rate not positive")
    constant = 4*(arb.pi()+arb(9)*cutoff/4-arb.pi()*cutoff.exp()).exp()
    tail0 = constant/rate
    tail2 = constant*(cutoff**2/rate+2*cutoff/rate**2+2/rate**3)
    return epsilon, tail0, tail2


def ratio_ball(index, bits=128, terms=8, cutoff=4):
    """Full R_1(index/10), including all theta and integration tails."""
    with ctx.workprec(bits):
        x, end = arb(index)/10, arb(cutoff)
        if not 0 <= x <= end:
            raise ValueError("this tail bound requires 0<=x<=cutoff")
        epsilon, tail0, tail2 = global_bounds(terms, end)
        base = kernel_finite(acb(x/2), terms).real**2
        if not base > 0:
            raise ArithmeticError("positive rescaling not established")
        tolerance = arb(2)**(-(bits//2))
        def integrand(w, analytic, reflected):
            left = (w-x)/2 if reflected else (x-w)/2
            product = kernel_finite(left, terms)*kernel_finite((x+w)/2, terms)/base
            # Real and imaginary parts of the integral are respectively
            # the zeroth and second moments. No projection occurs in callback.
            return (1+acb(0, 1)*w*w)*product
        integral = acb(0)
        if index > 0:
            integral += acb.integral(lambda w, a: integrand(w, a, False), 0, x,
                                     rel_tol=tolerance, abs_tol=tolerance/100)
        if index < 10*cutoff:
            integral += acb.integral(lambda w, a: integrand(w, a, True), x, end,
                                     rel_tol=tolerance, abs_tol=tolerance/100)
        error0 = (4*epsilon*end+tail0)/base
        error2 = (4*epsilon*end**3/3+tail2)/base
        denominator = integral.real+arb(0, error0.upper())
        numerator = integral.imag+arb(0, error2.upper())
        if not denominator > 0:
            raise ArithmeticError(f"normalization not positive at x={index}/10")
        result = numerator/(2*denominator)
        if not result > 0:
            raise ArithmeticError(f"ratio sign undecided at x={index}/10")
        return result, {"theta_error0": (4*epsilon*end/base).str(20),
                        "theta_error2": (4*epsilon*end**3/(3*base)).str(20),
                        "integration_tail0": (tail0/base).str(20),
                        "integration_tail2": (tail2/base).str(20)}


def quadratic_form(ratios, vector=WITNESS):
    """Toeplitz quadratic form, normalized by ||v||^2 and R_1(0)."""
    norm = sum(v*v for v in vector)
    if not norm or len(ratios) < len(vector) or not ratios[0] > 0:
        raise ValueError("nonzero vector and enough positive-normalized ratios required")
    total = sum(vector[i]*vector[j]*ratios[abs(i-j)]
                for i in range(len(vector)) for j in range(len(vector)))
    return total/(norm*ratios[0])


def run():
    started = perf_counter()
    result = {"scope": "failure of ratio-factor square construction, not RH",
              "rh_resolved": False, "witness": list(WITNESS), "norm2": NORM2,
              "points": "j/10 for j=0,...,23", "runs": []}
    for bits in (128, 192):
        with ctx.workprec(bits):
            ratios, rows = [], []
            digits = bits//4
            for j in range(len(WITNESS)):
                value, errors = ratio_ball(j, bits)
                ratios.append(value)
                text = value.str(digits)
                if not arb(text).contains(value):
                    raise ArithmeticError("serialized ratio did not contain its enclosure")
                rows.append({"index": j, "ratio": text, "error_bounds": errors})
            value = quadratic_form(ratios)
            serialized = quadratic_form([arb(row["ratio"]) for row in rows])
            if not value < 0 or not serialized < 0:
                raise ArithmeticError("negative witness not established including tails")
            result["runs"].append({"bits": bits, "theta_terms": 8, "w_cutoff": 4,
                                   "rows": rows, "quadratic_form": value.str(digits),
                                   "serialized_quadratic_form": serialized.str(digits)})
            print(f"ratio witness: bits={bits}, 24/24 integrals enclosed, negative quadratic form", flush=True)
    result["counts"] = {
        "ratio_enclosures": sum(len(run["rows"]) for run in result["runs"]),
        "negative_witness_enclosures": len(result["runs"]),
        "failures": 0,
    }
    result["elapsed_seconds"] = round(perf_counter()-started, 3)
    (HERE/"ratio_witness_results.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": "completed", **result["counts"],
                      "elapsed_seconds": result["elapsed_seconds"]}), flush=True)


if __name__ == "__main__":
    run()
