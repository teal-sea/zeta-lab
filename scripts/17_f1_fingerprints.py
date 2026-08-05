"""The q -> 1 limit: combinatorial shadows of geometry over a finite field.

Counts of points on the classical homogeneous spaces over F_q are polynomials
in q.  Setting q = 1 in those polynomials produces the corresponding *set*
counts: |P^{n-1}| -> n, the flag variety -> |S_n|, the Grassmannian -> a
binomial coefficient.  This is Tits' 1957 observation, and it is the entire
empirical basis for the phrase "the field with one element": the Weyl group
behaves like the q -> 1 degeneration of the group of Lie type.

Read docs/11-f1-and-the-missing-geometry.md first -- it covers the programs
(Soule, Connes-Consani, Borger's lambda-rings), Deninger's dynamical picture and
the four falsification gates.  This script is the computed version of its
Section 3 fingerprints plus one measurement docs/11 does not make.

Two things this script deliberately does *not* do.

It does not claim F_1 is a field.  No field has one element -- 0 != 1 is an
axiom.  "F_1" names a hoped-for object, and there are several inequivalent
proposals for it (Deitmar's monoid schemes, Connes-Consani, Toen-Vaquie,
Borger's Lambda-rings, Lorscheid's blueprints).  They agree on the shadows
computed below and none of them has yet produced the geometry over Spec Z that
the Riemann Hypothesis programme would need.

And it does not claim any of this bears on RH.  The section on Gamma factors
below states a claim that is often made loosely in this context and then
*measures* it, because the loose version is false as usually written.  See the
honest-scope rule in AGENTS.md, and docs/08 on why no computation here is
evidence for RH.
"""

import math

import sympy as sp
from mpmath import mp

from zeta.core import xi
import zeta.epstein as ep

q = sp.Symbol("q")


def q_integer(n):
    return (q**n - 1) / (q - 1)


def q_factorial(n):
    return sp.prod([q_integer(i) for i in range(1, n + 1)])


def q_binomial(n, k):
    return q_factorial(n) / (q_factorial(k) * q_factorial(n - k))


print("=" * 78)
print("q -> 1 FINGERPRINTS: counting geometry over a finite field")
print("=" * 78)

print("\n1) THE PROJECTIVE LINE")
print("   Over F_q, |P^1| = q + 1.")
print(f"   Limit as q -> 1: {sp.limit(q + 1, q, 1)} points.")

print("\n2) PROJECTIVE SPACE P^{n-1}")
for n in [3, 4, 5]:
    expr = sp.simplify(q_integer(n))
    limit_val = sp.limit(expr, q, 1)
    assert limit_val == n, f"|P^{n-1}| should degenerate to {n}"
    print(f"   |P^{n - 1}| over F_q = {expr}")
    print(f"   Limit as q -> 1: {limit_val} points  (= n)")

print("\n3) THE FLAG VARIETY GL_n / B")
print("   Over F_q this counts maximal flags of subspaces.")
for n in [3, 4, 5]:
    expr = sp.simplify(q_factorial(n))
    limit_val = sp.limit(expr, q, 1)
    assert limit_val == math.factorial(n), "flag count should degenerate to |S_n|"
    print(f"   n = {n}: {expr}")
    print(f"   Limit as q -> 1: {limit_val}  (= |S_{n}| = {math.factorial(n)})")

print("\n4) THE GRASSMANNIAN Gr(2, 4)")
expr = sp.simplify(q_binomial(4, 2))
limit_val = sp.limit(expr, q, 1)
assert limit_val == 6
print(f"   |Gr(2,4)| over F_q = {expr}")
print(f"   Limit as q -> 1: {limit_val}  (= C(4,2) = 6)")

print("\n" + "=" * 78)
print("THE ARCHIMEDEAN GAMMA FACTOR — A CLAIM, MEASURED")
print("=" * 78)
print("""
   The story usually continues: the Gamma factor Riemann attached to zeta(s)
   is the archimedean local factor of an F_1 zeta function, so those Gamma
   factors "are geometry".  The completed function is the object at stake,
   so the claim is testable: whichever archimedean factor is correct is the
   one that makes A(s) = A(1-s) hold.  A version of the formula that circulates
   informally is  s * (2*pi)^{-s/2} * Gamma(s/2), so measure both.
""")

with mp.workdps(25):
    s = mp.mpc("0.3", "7.1")

    def informal(z):
        return z * (2 * mp.pi) ** (-z / 2) * mp.gamma(z / 2) * mp.zeta(z)

    def riemann(z):
        return mp.pi ** (-z / 2) * mp.gamma(z / 2) * mp.zeta(z)

    d_informal = abs(informal(s) - informal(1 - s))
    d_riemann = abs(riemann(s) - riemann(1 - s))
    d_xi = abs(xi(s, 25) - xi(1 - s, 25))

    print(f"   test point s = {mp.nstr(s, 8)}, dps = 25\n")
    print(f"   s*(2pi)^(-s/2)*Gamma(s/2)*zeta(s)   |A(s) - A(1-s)| = {mp.nstr(d_informal, 8)}")
    print(f"   pi^(-s/2)*Gamma(s/2)*zeta(s)        |A(s) - A(1-s)| = {mp.nstr(d_riemann, 8)}")
    print(f"   zeta.core.xi                        |A(s) - A(1-s)| = {mp.nstr(d_xi, 8)}")

    assert d_informal > mp.mpf("1e-3"), "the informal factor was expected to fail"
    assert d_riemann < mp.mpf("1e-20"), "pi^(-s/2)Gamma(s/2) should symmetrise"
    print("""
   The informal factor has no functional equation at all: it conflates
   Gamma_R(s) = pi^{-s/2} Gamma(s/2) with Gamma_C(s) = 2 (2pi)^{-s} Gamma(s),
   and drops the s(s-1)/2 that makes xi entire.  Only pi^{-s/2} Gamma(s/2)
   symmetrises.  Quote the factor that passes this test, not the other one.
""")

print("=" * 78)
print("AND THE GATE THIS STORY HAS TO PASS")
print("=" * 78)
print("""
   Suppose a full F_1 geometry existed and explained why zeta's Gamma factors
   force its zeros onto the critical line.  The Davenport-Heilbronn function F
   also has a Gamma-factor functional equation F(s) = F(1-s), also has real
   coefficients and a real Hardy-style Z -- and has a zero OFF the line.  So an
   argument of the form "the Gamma factors are secretly geometry, therefore the
   zeros are on the line" applies verbatim to F, where the conclusion is false.
""")

with mp.workdps(30):
    rho = mp.mpc(ep.OFFLINE_ZERO_RE, ep.OFFLINE_ZERO_IM)
    residual = abs(ep.completed_dh(rho, dps=30))
    fe_defect = ep.dh_functional_equation_defect(mp.mpc("0.3", "7.1"), dps=30)
    print(f"   DH functional equation defect at 0.3+7.1i : {mp.nstr(fe_defect, 6)}")
    print(f"   DH off-line zero rho                      : {mp.nstr(rho, 14)}")
    print(f"   |completed_dh(rho)|                       : {mp.nstr(residual, 6)}")
    print(f"   Re(rho) - 1/2                             : {mp.nstr(mp.re(rho) - mp.mpf('0.5'), 6)}")

print("""
   Any structural story about zeta has to say what distinguishes it from F.
   The q -> 1 counts above are real mathematics.  They are not, on their own,
   a step towards RH -- what is missing over Spec Z is a Frobenius and a
   cohomology theory, and no amount of limit-taking in this script supplies it.
   See scripts/11_finite_field_rh.py for the case where that machinery does
   exist and RH is a theorem.
""")
