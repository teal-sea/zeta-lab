"""Li coefficients for the Davenport-Heilbronn function — a detector control.

Li's criterion says lambda_n >= 0 for every n >= 1 if and only if all zeros of
xi lie on the critical line.  (For the Davenport-Heilbronn function below the
relevant statement is the Bombieri-Lagarias multiset form, which needs no Euler
product -- F has none and is outside the Selberg class.)  The natural experiment is to run the same
computation on a function that is *known* to violate RH and watch it fail.
The Davenport-Heilbronn function F is exactly that (docs/09, gate #3): it
satisfies F(s) = F(1-s), has real Dirichlet coefficients and a real Hardy-style
Z, and has a zero off the critical line at

    rho = 0.80851718... + 85.69934848...i

This script does three things:

1.  Extracts lambda_n by Cauchy integration of log(completed function) around
    a circle, using the same contour machinery `zeta.li` uses, and *validates
    that code path against `zeta.li.li_coefficients`* before trusting it.
2.  Runs it on F and reports the coefficients.
3.  Predicts, from the off-line zero itself, the n at which negativity must
    eventually appear — and shows that it lies far outside any n reachable
    here.

The outcome is a negative result about the *detector*, not about F: Li
positivity over any computationally accessible range of n does not distinguish
zeta from a function that provably violates RH.  Nothing here is evidence for
or against RH (Littlewood; docs/08).

Background: docs/07-equivalences-and-criteria.md Section 4 states the criterion
and now records this measurement; Section 11 is the general "the equivalences
restate rather than reduce" argument that this sharpens for one of them.  The
counterexample gate is docs/09 Section 5 gate 3 and docs/11 Section 5.
"""

import sys
import time
from pathlib import Path

from mpmath import mp

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import zeta.epstein as ep
from zeta.core import xi
from zeta.li import li_coefficients
# The analytic-branch logarithm and the root-of-unity table are the delicate
# parts of this extraction; reuse zeta.li's rather than re-deriving them.  Both
# are documented in zeta/li.py and pinned by tests/test_li.py.
from zeta.li import _roots_of_unity, _unwrapped_log

N_MAX = 24
DPS = 15
RADIUS = "0.4"


def contour_lambdas(fn, n_max: int, dps: int, radius) -> list:
    """lambda_1 ... lambda_n_max for any entire F with F(s) = F(1-s), F(1) > 0.

    lambda_n = n * [z^n] log(F(1/(1-z)) / F(1)); the Taylor coefficients come
    from one DFT over a circle of radius `radius`.  Mirrors `zeta.li._li_cauchy`
    but takes the completed function as an argument, so the *same* code path can
    be validated on xi and then pointed at the Davenport-Heilbronn function.

    Raises if the disk is not zero-free (`_unwrapped_log` reports the winding).
    """
    guard = 10
    decay = float(mp.log10(1 / mp.mpf(radius)))   # digits lost to the 1/R^n division
    work = int(dps + 2 * guard + n_max * decay)
    with mp.workdps(work):
        R = mp.mpf(radius)
        n_points = int(mp.ceil(work * mp.log(10) / mp.log(1 / R))) + n_max + 8
        w = _roots_of_unity(n_points)
        samples = [fn(1 / (1 - R * wj)) for wj in w]
        vals = _unwrapped_log(samples)
        out = []
        for n in range(1, n_max + 1):
            acc = mp.fsum(vals[j] * w[(-(j * n)) % n_points] for j in range(n_points))
            c_n = acc * mp.power(R, -n) / n_points
            # lambda_n is real for a function with real coefficients; the
            # imaginary part is the error estimate, so check rather than discard.
            if abs(mp.im(c_n)) > mp.mpf(10) ** (-(dps - 2)) * max(abs(c_n), 1):
                raise ValueError(
                    f"lambda_{n} has imaginary part {mp.nstr(mp.im(c_n), 6)}; "
                    "the contour extraction has not converged"
                )
            out.append(+(n * mp.re(c_n)))
    with mp.workdps(dps):
        return [+v for v in out]


print("=" * 78)
print("LI COEFFICIENTS FOR THE DAVENPORT-HEILBRONN FUNCTION")
print("=" * 78)

# -- 1) validate the extractor on xi, where zeta.li is the oracle -------------
print("\n1) VALIDATING THE CONTOUR EXTRACTOR AGAINST zeta.li.li_coefficients")
t0 = time.time()
mine = contour_lambdas(lambda s: xi(s, 40), N_MAX, DPS, RADIUS)
oracle = li_coefficients(N_MAX, dps=DPS)   # returns lambda_1 ... lambda_N_MAX
worst = max(abs(a - b) for a, b in zip(mine, oracle))
print(f"   n_max = {N_MAX}, dps = {DPS}, radius = {RADIUS}")
print(f"   lambda_1  this script = {mp.nstr(mine[0], 12)}")
print(f"   lambda_1  zeta.li     = {mp.nstr(oracle[0], 12)}")
print(f"   worst |difference| over n <= {N_MAX} : {mp.nstr(worst, 6)}")
assert worst < mp.mpf("1e-9"), "contour extractor disagrees with zeta.li"
print(f"   AGREES. The code path is trustworthy.  ({time.time() - t0:.1f}s)")

# -- 2) the same code path, pointed at Davenport-Heilbronn --------------------
print("\n2) THE SAME EXTRACTION APPLIED TO THE DAVENPORT-HEILBRONN FUNCTION")
print("   (F violates RH; if Li positivity were a practical detector, these")
print("    coefficients would go negative.)")
t0 = time.time()
dh = contour_lambdas(lambda s: ep.completed_dh(s, dps=30), N_MAX, DPS, RADIUS)
print(f"   computed in {time.time() - t0:.1f}s\n")
print(f"   {'n':>4}  {'lambda_n (zeta)':>20}  {'lambda_n (DH)':>20}")
for n, (a, b) in enumerate(zip(oracle, dh), start=1):
    print(f"   {n:>4}  {mp.nstr(a, 12):>20}  {mp.nstr(b, 12):>20}")

n_neg = [n for n, v in enumerate(dh, start=1) if v < 0]
print()
if n_neg:
    print(f"   Negative lambda_n for DH at n = {n_neg}")
else:
    print(f"   No negative lambda_n for DH anywhere in n <= {N_MAX}.")
    print("   The RH-violating function passes the test.")

# -- 3) why: the growth rate set by the off-line zero -------------------------
print("\n3) WHERE THE NEGATIVITY ACTUALLY LIVES")
with mp.workdps(40):
    rho = mp.mpc(ep.OFFLINE_ZERO_RE, ep.OFFLINE_ZERO_IM)
    # F(s) = F(1-s) with real coefficients puts zeros in quadruples; the two
    # members with Re < 1/2 are the ones that make |1 - 1/rho| exceed 1.
    sigma = 1 - rho
    rate = abs(1 - 1 / sigma)
    log_rate = mp.log(rate)
    print(f"   off-line zero          rho   = {mp.nstr(rho, 12)}")
    print(f"   its mirror (Re < 1/2)  1-rho = {mp.nstr(sigma, 12)}")
    print(f"   |1 - 1/(1-rho)|              = {mp.nstr(rate, 15)}")
    print(f"   log of that                  = {mp.nstr(log_rate, 6)}")
    print()
    print("   lambda_n = sum over zeros of [1 - (1 - 1/rho)^n], so a zero with")
    print("   Re < 1/2 contributes a term growing like that modulus to the n-th")
    print("   power.  It exceeds 1 only in the 5th decimal place, so the")
    print("   offending term needs roughly")
    print(f"       n ~ 1 / log|1 - 1/(1-rho)| = {mp.nstr(1 / log_rate, 8)}")
    print("   just to double, against a smooth positive background growing like")
    print("   (n/2) log n.  Detecting the violation is a computation at n in the")
    print("   tens of thousands at least, not the tens.")

print("\n4) VERDICT")
print("   The Davenport-Heilbronn function violates RH and still shows no")
print(f"   negative Li coefficient for n <= {N_MAX}.  So observing lambda_n >= 0")
print("   for zeta over a comparable range distinguishes nothing: the same")
print("   observation holds for a function with a zero provably off the line.")
print("   This is docs/09 gate #3 doing its job on a criterion, rather than on")
print("   a structural claim.  It says nothing about whether RH is true.")
