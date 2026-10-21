# OBSTRUCTION: what short windows and small-prime local factors cannot see

Hunt #149, step 5 of `MISSION.md`. **Disposition under `ALIGNMENT.md` section 5: restricted
class obstructed**, for the information class defined in section 1, at the conductors
q = 17 and q = 73. It refutes no named candidate, says nothing about other information
classes, and is not a verdict on any route to RH (section 5.1). The proof is an ordinary
argument written here and reviewed by nobody outside this hunt; its one numerical input,
a zero of F_chi off the critical line, is hardened (`ZEROS.md`). Every number below is
pinned by `test_rivals.py`.

## 1. The information class

Fix a prime q = 1 (mod 4), the order-4 character chi mod q, its root number e^{i theta},
and P = n(q) - 1 with n(q) the least quadratic non-residue mod q, so that every prime
p <= P is a square mod q. Let F = F_chi / (2 cos(theta/2)), normalised to a(1) = 1
(`MATCH.md` section 1; cos(theta/2) != 0 always). For an entire degree-1 function f with a
functional equation and a Dirichlet series with a(1) = 1, let I_P(f) be:

1. **archimedean data**: the conductor q and the Gamma factor Gamma_R(s + a) of its
   functional equation (the data the explicit formula's archimedean term reads);
2. **local data at the primes p <= P**: the restriction of the Dirichlet series to P-smooth
   integers, which contains every reading of "the local factor at p" for p <= P (the
   p-parts, any Euler factor that splits off, and the coefficients of -f'/f there);
3. **window data**: every band-N truncated Weil form Q_{c,N}(f) of
   `hunts/rogue_frontier/weil_trunc/galerkin.py` with 1 < c <= P + 1, for every N.

The class deliberately leaves out the root number and the dual. Those separate the pair at
once: L(s, chi) is not self-dual (its functional equation pairs it with L(s, chi-bar), and
eps^2 is not real), while F is self-dual with sign +1.

## 2. The statement

**Proposition (ordinary argument).** I_P(F) = I_P(L(s, chi)).

*Proof.* (1) By construction: the functional equation of F is derived from that of the
pair (L(s, chi), L(s, chi-bar)) in `MATCH.md` section 1 and carries the same Gamma factor
and conductor. (2) If chi(m) is real then b(mn) = chi(m) b(n) for all n, and chi(p) is real
at every residue prime, so on P-smooth integers b = chi exactly; this is checked in exact
arithmetic for n <= 10^4 (14 P-smooth integers for q = 17, 67 for q = 73, no failure).
(3) The archimedean block of Q_{c,N} is a function of the data in (1); the prime block is a
function of Lambda_f(n) for n < c, because the term at n = c carries weight
1 - log n / log c = 0 and sin(2 pi k log n / log c) = 0. For c <= P + 1 every such n is at
most P, hence P-smooth, and its divisors are P-smooth, so Lambda_f(n) is a function of (2):
Lambda_F(n) = Lambda(n) chi(n), real. A complex coefficient enters the form only through
its imaginary part, which vanishes here, so L's parity-coupling block is zero. Hence the
forms coincide. []

Measured confirmation (`MATCH.md` section 3): at N = 8 the full matrices agree to below
1e-40 at every c tried up to P + 1, and separate as soon as c passes n(q), by 1.9e-4 at
c = 3.001 for q = 17 and 5.7e-5 at c = 5.001 for q = 73.

**Corollary (the obstruction).** Let K be any criterion whose verdict on f is a function
of I_P(f). Then K(F) = K(L(s, chi)). F has zeros off the critical line: for q = 17 the
first lies in a decided Arb box of half-width 2^-30 around 0.66702533353 + 25.69077157780 i
(route B), is located to 1e-11 by the mpmath route, and PARI's own Newton iteration lands
inside that box to 40 digits; `ZEROS.md` has the census for both q to height 1000.
Therefore:

- no such K can be a sufficient condition for "every nontrivial zero lies on
  Re s = 1/2" on any class of functions that contains F, unless K fails at L(s, chi);
- so no such K can be the reason L(s, chi) has its zeros on the line;
- and if L(s, chi) satisfies GRH (it is expected to; this hunt does not test it), no such
  K is both necessary and sufficient for RH on a class containing both.

**A stronger form, from the same factorisation.** F_chi = L_QR(s, chi) times a combination
supported on the non-residue primes (`MATCH.md` section 2), so F and L(s, chi) also share
the exact Euler factor at **every** quadratic-residue prime, a set of primes of density
one half, and the coefficients of -F'/F agree with Lambda(n) chi(n) at every n with a
residue prime factor. Local data at any set of residue primes, however large, therefore
cannot separate them either. What separates them is the first non-residue prime: n(q) = 3
for q = 17, 5 for q = 73.

## 3. Scope

**What escapes the class.** Any criterion that reads a window with c > n(q); or the local
data at one non-residue prime p (F has no Euler factor there: Lambda_F(p) = +-k log p is
real where Lambda(p) chi(p) = +-i log p, and the power sums go non-unitary at p^2, e.g.
Lambda_F(9) = -(2 + k^2) log 3 for q = 17); or the root number and the dual. Weil
positivity of F's full form must fail somewhere, since F has zeros off the line, and by the
proposition the failure needs test functions with support longer than log n(q). Every
window form in `MATCH.md` section 3 is positive, for both functions.

**It does not transfer to zeta (Hamburger).** By Hamburger's theorem (1921; Titchmarsh,
*The Theory of the Riemann Zeta-Function*, section 2.13, cited, not re-derived), a
Dirichlet series that is meromorphic of finite order with finitely many poles and
satisfies zeta's functional equation, with conductor 1 and Gamma factor Gamma_R(s), is a
constant multiple of zeta. So zeta has no rival that shares its own conductor and Gamma
factor at all: the data in (1) already pin it, and there is nothing left for I_P to fail
to separate. The rivals live at conductors q > 1, as
Davenport-Heilbronn lives at 5. What the obstruction says about arguments aimed at zeta is
conditional on uniformity: a mechanism meant to work for every degree-1 L-function, with
the conductor as a parameter, must read something outside I_P at conductor 17 and 73.

**C4 at S = {inf, 2} cannot use these rivals yet.** The candidate C4 of
`hunts/weil_propagation/theory/RESULTS.md` section 7.2 asks for a set of places
S, containing infinity and every p <= c, on which the local data satisfy (U-S): atoms only at
prime powers and unitary local roots. On windows c in [2, 3), F_17 meets the finite-place
half of that at p = 2 exactly as L(s, chi mod 17) does (an atom at powers of 2 only, local
root chi(2) = -1). But C4's semilocal distribution and Sonin projection are built from the
local data of the places in S, and the conductor 17 enters F_17's and L's archimedean
constant log(17/pi) as the contribution of the ramified place 17, which is not in
S = {inf, 2}. `hunts/weil_propagation/c4_s2/` has built S = {inf, 2} only for zeta's
unramified data, and says so: its kernel leaves out "the conductor term of a ramified
character", and of Dedekind's log 23 it writes "It belongs to the ramified place 23, which
is not in S = {∞, 2}." (`c4_s2/kernel/RESULTS.md` section 4; also `kernel/INTERFACE.md`).
**Until ramified local Sonin data at q exist, C4 cannot be posed for
L(s, chi mod q) or for F_chi, and so cannot use these rivals.** Once they do, F_17 at
S = {inf, 2, 17} on c in [2, 3) would share every local datum with L(s, chi mod 17)
(both have a trivial factor at 17), so it could not refute C4 there, where both forms are
positive; it would show instead that any step propagating C4 past c = 3 has to use (U-S)
at the place 3, the first non-residue. That last sentence is an ordinary argument from
this hunt's proposition, not a computation in C4's framework.

**Which conductors.** The proof is uniform in q; the off-line zeros are checked here for
q = 17 and 73 only. P grows with the conductor: the least prime q = 1 (mod 4) whose least
non-residue is n is 5, 17, 73, 241, 1009, 2689, 8089, 33049, 53881 for n = 2, 3, 5, 7, 11,
13, 17, 19, 23 (exact search). By quadratic reciprocity and Dirichlet's theorem every P is
reached (q = 1 mod 8 and q = 1 mod p for each odd p <= P suffice), so every finite P has
such pairs, at conductors that grow with P.

## The doors

This hunt measures no ceiling, but the obstruction is an information-class statement, so
`CLAUDE.md`'s door analysis applies to it.

1. **Active constraints.** Three pieces of withheld information bind, and each alone
   separates the pair: (a) a window longer than log n(q), where the first non-residue
   prime enters with weight 1 - log n(q) / log c; (b) the local data at one non-residue
   prime; (c) the root number or the dual. Measured, (a) binds from zero: the largest
   entry difference is 1.9e-4 at c - n(q) = 0.001 for q = 17 and 2.4e-3 at 0.01.
2. **Frozen-constant inventory.** P = n(q) - 1 is fixed by q and is not a free choice
   (trade: a larger P costs a larger conductor, by the table above). The order of chi is 4
   here; a character of higher even order with real values at the small primes, or a
   combination of more than two L-functions with a common functional equation, would give
   other members of the family (not built; the trade is a larger linear solve). The
   normalisation a(1) = 1 needs cos(theta/2) != 0, which order 4 guarantees. The census
   height 1000 is a budget, not a property.
3. **Information class.** Door (a) stays inside the window-form family the class already
   reads, only with longer windows; where F's form first goes negative is an open
   measurement (for Davenport-Heilbronn it is (c, N) = (31, 60), `docs/37-methods.md`).
   Doors (b) and (c) read data outside the window family.
