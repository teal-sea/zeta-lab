"""Support run e6241336: one number, and three checks on it.

Question: what is ``abs(epstein_completed(0.8+85.7i, (2,1,3), dps=60))``, and
does it agree with 1.6e-58 to within an order of magnitude?

The evaluation is cancellation-heavy.  ``epstein_completed`` splits the Mellin
transform of the form's theta series at t = 1; the individual pieces at
s = 0.8 + 85.7i are of size 1e-3 and the answer is of size 1e-58, so roughly 55
digits cancel.  A ladder in ``dps`` is therefore the minimum honest reporting,
and three independent checks are added on top of it:

A. **normalisation.**  ``Lambda_Q(s) / ((sqrt(d)/pi)^s Gamma(s))`` must equal
   the convergent lattice sum ``sum_{(m,k) != (0,0)} Q(m,k)^{-s}`` at s = 4,
   where the Dirichlet series actually converges.
B. **the Dedekind identity, at the point in question.**  For discriminant -23
   the class number is 3, the reduced forms are (1,1,6), (2,1,3), (2,-1,3), and

       sum_Q Lambda_Q(s) = 2 (sqrt(23)/2pi)^s Gamma(s) zeta(s) L(s, chi_-23)

   with the factor 2 the number of units.  The right-hand side is built from
   mpmath's ``zeta`` and Hurwitz ``zeta``, so it reaches a quantity of size
   1e-58 with **no cancellation at all**.  That is the check that matters: it
   is a genuinely different route to the same number.
C. **the functional equation** across the inverse class,
   ``Lambda_(2,1,3)(s)`` against ``Lambda_(2,-1,3)(1-s)``.

Note the trap this script exists to avoid, which cost the first pass a run:
``s`` must be built **inside a high-precision block**.  ``mpc("0.8","85.7")``
evaluated at mpmath's default 15 digits rounds the argument to 53 bits, and
since ``d/ds log Lambda`` is about ``log|s|`` (roughly 4.5) there, a half-ulp
error in 85.7 moves the magnitude in its 15th digit.  ``epstein_completed``
cannot repair that: it calls ``mpmathify`` on whatever it is handed, and an
``mpf`` that arrives short of digits stays short.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath
from mpmath import mp

from zeta.epstein import epstein_completed

FORM = (2, 1, 3)
FORMS = {"(1,1,6)": (1, 1, 6), "(2,1,3)": (2, 1, 3), "(2,-1,3)": (2, -1, 3)}
D = 23
d = mpmath.mpf(D) / 4
CLAIMED = "1.6e-58"


def chi(n: int) -> int:
    """The Kronecker character of Q(sqrt(-23)), which is the Legendre symbol
    (n/23): 23 is 3 mod 4, so this character is odd, as an imaginary quadratic
    field requires.  Sanity: chi(2) = chi(3) = +1, and 2 and 3 are exactly the
    small numbers the form (2,1,3) represents."""
    n %= D
    return 0 if n == 0 else (1 if pow(n, (D - 1) // 2, D) == 1 else -1)


def L_chi(s):
    """L(s, chi_-23) through Hurwitz zeta, valid for every s."""
    return mpmath.mpf(D) ** (-s) * mpmath.fsum(
        chi(a) * mpmath.zeta(s, mpmath.mpf(a) / D) for a in range(1, D)
    )


def gamma_factor(s):
    """(sqrt(d)/pi)^s Gamma(s), with d = |D|/4, the completion Lambda carries."""
    return (mpmath.sqrt(d) / mpmath.pi) ** s * mpmath.gamma(s)


def main() -> dict:
    with mp.workdps(200):
        s = mpmath.mpc("0.8", "85.7")
        s_reflected = 1 - s
    with mp.workdps(15):
        s_short = mpmath.mpc("0.8", "85.7")

    out: dict = {
        "question": (
            "abs(epstein_completed(0.8+85.7i, (2,1,3), dps=60)) versus the "
            "claimed " + CLAIMED
        ),
        "s": "0.8+85.7i, built at 200 digits",
        "form": list(FORM),
    }

    values = {}
    ladder = []
    for dps in (40, 50, 60, 80, 120):
        value = epstein_completed(s, FORM, dps=dps)
        values[dps] = value
        with mp.workdps(dps + 20):
            ladder.append({"dps": dps, "magnitude": mpmath.nstr(abs(value), 25)})
    out["ladder"] = ladder

    with mp.workdps(140):
        reference = abs(values[120])
        at60 = abs(values[60])
        relative = abs(at60 - reference) / reference
        out["answer"] = {
            "dps60_magnitude": mpmath.nstr(at60, 25),
            "dps60_value_real": mpmath.nstr(values[60].real, 25),
            "dps60_value_imag": mpmath.nstr(values[60].imag, 25),
            "dps120_magnitude": mpmath.nstr(reference, 25),
            "dps60_relative_error": mpmath.nstr(relative, 4),
            "correct_digits_at_dps60": float(mpmath.nstr(-mpmath.log10(relative), 4)),
            "ratio_to_claimed": float(mpmath.nstr(at60 / mpmath.mpf(CLAIMED), 10)),
        }

    short = epstein_completed(s_short, FORM, dps=60)
    with mp.workdps(140):
        out["argument_precision_trap"] = {
            "note": "same call, s built at mpmath's default 15 digits",
            "magnitude": mpmath.nstr(abs(short), 25),
            "relative_error": mpmath.nstr(abs(abs(short) - reference) / reference, 4),
        }

    checks = []
    with mp.workdps(40):
        s4 = mpmath.mpf(4)
        for name, (a, b, c) in FORMS.items():
            direct = mpmath.fsum(
                mpmath.mpf(a * m * m + b * m * k + c * k * k) ** (-s4)
                for m in range(-400, 401)
                for k in range(-400, 401)
                if (m, k) != (0, 0)
            )
            implied = epstein_completed(s4, (a, b, c), dps=40) / gamma_factor(s4)
            checks.append({
                "check": "A normalisation at s=4",
                "form": name,
                "relative_difference": mpmath.nstr(abs(implied - direct) / abs(direct), 4),
            })

    for dps in (60, 120):
        lam = {name: epstein_completed(s, f, dps=dps) for name, f in FORMS.items()}
        with mp.workdps(dps + 20):
            lhs = lam["(1,1,6)"] + lam["(2,1,3)"] + lam["(2,-1,3)"]
            rhs = 2 * gamma_factor(s) * mpmath.zeta(s) * L_chi(s)
            checks.append({
                "check": "B Dedekind identity at s=0.8+85.7i",
                "dps": dps,
                "lhs": mpmath.nstr(lhs, 20),
                "rhs": mpmath.nstr(rhs, 20),
                "relative_difference": mpmath.nstr(abs(lhs - rhs) / abs(rhs), 4),
            })

    for dps in (60, 120):
        left = epstein_completed(s, (2, 1, 3), dps=dps)
        right = epstein_completed(s_reflected, (2, -1, 3), dps=dps)
        with mp.workdps(dps + 20):
            checks.append({
                "check": "C functional equation across the inverse class",
                "dps": dps,
                "relative_difference": mpmath.nstr(abs(left - right) / abs(left), 4),
            })

    out["checks"] = checks
    return out


if __name__ == "__main__":
    result = main()
    print(json.dumps(result, indent=2))
    target = Path(__file__).with_name("results.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
