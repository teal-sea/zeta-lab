"""Does the generating function reproduce Li's *definition* for this function?

The Cauchy route computes n [z^n] log F(1/(1-z)).  Li's definition is

    lambda_n = (1/(n-1)!) d^n/ds^n [ s^{n-1} log F(s) ] at s = 1,

and the substitution s = 1/(1-z) that connects them is a derivation, so it is a
place a mistake can hide: a neighbouring normalisation (a factor n, an index
shift, the wrong branch of the square root in the completion) would leave every
other check in this hunt green.  ``zeta.li.li_generating_function_defect`` runs
exactly this comparison for zeta; this file runs it for the Davenport-Heilbronn
function, where nothing has ever been compared before.

The literal path uses mpmath's Cauchy-integral differentiator on a disc of
radius 0.4 about s = 1.  That disc sits inside the rectangle ``radius_scan``
measured to be free of zeros of f, so log F has a branch on it and F is finite
there (the Gamma poles are at s = -1, -3, ...).  It loses digits fast with n,
which is why it is a small-n check and not a table.

The n = 1 row gets a third route, in closed form:

    lambda_1 = (log F)'(1) = -log(pi/5)/2 - euler/2 + f'(1)/f(1),

from log F(s) = -((s+1)/2) log(pi/5) + log Gamma((s+1)/2) + log f(s) and
psi(1) = -euler.  Unlike zeta's lambda_1 there is no closed form for f'(1)/f(1),
so this is a closed form for everything except one derivative, which is still
a different computation from either of the other two.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import json
import os
import sys
import time

from mpmath import mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from zeta.epstein import dh_f

from dhli import completed_dh_fast, li_coefficients_cauchy

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")


def literal_lambda(n: int, dps: int = 25, radius="0.4"):
    """lambda_n(DH) straight from the n-th derivative definition."""
    work = dps + 30
    with mp.workdps(work):
        f = lambda s: mp.power(s, n - 1) * mp.log(completed_dh_fast(s))
        v = mp.diff(f, mp.mpf(1), n, method="quad", radius=mp.mpf(radius))
        v = v / mp.factorial(n - 1)
        return mp.re(v), mp.im(v)


def closed_form_lambda1(dps: int = 30):
    work = dps + 20
    with mp.workdps(work):
        fp = mp.diff(lambda s: dh_f(s, mp.dps), mp.mpf(1), 1,
                     method="quad", radius=mp.mpf("0.4"))
        f1 = dh_f(1, work)
        return -mp.log(mp.pi / 5) / 2 - mp.euler / 2 + fp / f1


def main() -> None:
    t0 = time.time()
    dps = 25
    cauchy = li_coefficients_cauchy("dh", 4, dps=dps, radius="0.5", processes=1)
    rows = []
    for n in (1, 2, 3, 4):
        re, im = literal_lambda(n, dps=dps)
        with mp.workdps(dps + 30):
            d = abs(mp.mpf(cauchy[n - 1]) - re)
            rows.append(
                {
                    "n": n,
                    "cauchy": mp.nstr(mp.mpf(cauchy[n - 1]), 22),
                    "literal_definition": mp.nstr(re, 22),
                    "abs_defect": mp.nstr(d, 6),
                    "imag_residue_of_literal": mp.nstr(abs(im), 6),
                }
            )
        print(rows[-1], flush=True)
    cf = closed_form_lambda1(30)
    with mp.workdps(50):
        d1 = abs(mp.mpf(cauchy[0]) - cf)
    out = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "dps": dps,
        "rows": rows,
        "lambda_1_closed_form_route": mp.nstr(cf, 22),
        "lambda_1_closed_form_defect": mp.nstr(d1, 6),
        "seconds": round(time.time() - t0, 1),
    }
    os.makedirs(ART, exist_ok=True)
    p = os.path.join(ART, "definition_defect.json")
    with open(p, "w") as fh:
        json.dump(out, fh, indent=1)
    print("lambda_1 closed form", out["lambda_1_closed_form_route"],
          "defect", out["lambda_1_closed_form_defect"])
    print("wrote", p)


if __name__ == "__main__":
    main()
