# 45. RH to height 50, kernel-checked

> On 2026-10-22 this laboratory finished a Lean proof, about Mathlib's own
> `riemannZeta`, that every nontrivial zero up to height 50 lies on the critical
> line and is simple, and that there are exactly ten of them. It is a theorem, in
> the sense this repository reserves for the word: Lean's kernel accepts it with
> zero `sorry` and only the three standard axioms. This page leads with it and
> carries forward the results of [docs/39](39-built-on-the-quasi-riemann-theorem.md).

The theorem is finite. It says nothing above height 52 and nothing about the
Riemann hypothesis ([docs/08](08-why-it-is-hard.md)). Numerical verification of RH
reaches far higher, to 3 * 10^12; what is new here is that the statement is a
kernel-checked theorem rather than a computation, as far as a search of the formal
literature on 2026-10-22 reached. The rows carried from docs/39 keep their own
grades: they are conditional on OpenAI's theorem and unreviewed by any person.

## The results

| Result | Statement | Against | Grade | Where |
| --- | --- | --- | --- | --- |
| RH to height 50 | Every zero rho of Mathlib's riemannZeta with 0 < Re rho < 1 and 0 < Im rho <= 50 has Re rho = 1/2 and is simple, and there are exactly 10 of them; the same holds to height 52 | RH verified numerically to height 3 * 10^12 (Platt and Trudgian, 2021), a computation, not a formal proof. The formal results found locate no individual zero: anthropics/zeta-23-lean (a proportion theorem) and the 7/8 half-plane. A seven-search record found no earlier formal finite-height verification | kernel-checked: Lean 4 and Mathlib, zero sorry, only the three standard axioms, on Lean's kernel; a second kernel has not been run | [hunt #137](../hunts/rh_height_lean/RESULTS.md) |
| The input, replayed | Lean's kernel and the independent NanoDa kernel accept OpenAI's statements that zeta(s) and every Dirichlet L(s, chi) are nonzero for Re s > 7/8, and its Siegel-zero gap, with only the three standard axioms | OpenAI's own build; no outside replay was known | kernel-checked on two kernels, on this laboratory's compute; the argument is unreviewed by any person | [docs/38](38-the-quasi-riemann-claim.md), section 7 |
| Class numbers up to 1500 | h(D) >= sqrt(q) / (10 pi log log q) for every negative fundamental discriminant D, with q = -D; hence the complete list of imaginary quadratic fields of class number h, for every h <= 1500: 9,245,562 fields, the largest with q = 562,394,347 | Watkins (2004): h <= 100 unconditionally. [Cremona-Sutherland (2023), section 5](https://arxiv.org/html/2301.11169v4#S5): all h <= 1000, including even h, under GRH. OpenAI: the same shape of bound, constant not computed | proved, given the input; constants enclosure-carrying; lists by exact computation; unreviewed | [hunt #124](../hunts/qrh_class_number/RESULTS.md) |
| Primes between seventh powers | For every integer n >= 1 there is a prime p with n^7 < p < (n+1)^7, given also Kadiri, Lumley and Ng's explicit zero-density estimate; an eighth-power version on the same route is its audited predecessor | k = 9 from the input alone (hunt #126, next row); k = 86 for every n, unconditional (Lee, arXiv:2602.14340, 2026); already known for every n under full RH ([Chamberland-Straub](https://arxiv.org/abs/2602.22502)) | written conditional candidate, given the input and the density estimate; every numerical step enclosure-carrying; independent written audit by a separate agent context passed; reviewed by no person; not formalized | [October 8 extensions](../hunts/oct08_extensions/RESULTS.md) |
| Primes between ninth powers | For every integer n >= 1 there is a prime p with n^9 < p < (n+1)^9 | k = 86 for every n, unconditional (Lee, arXiv:2602.14340, 2026) | proved, given the input; every numerical step enclosure-carrying; unreviewed | [hunt #126](../hunts/qrh_prime_powers/RESULTS.md) |
| Small witnesses | For every nonprincipal Dirichlet character chi mod q >= 3, the least n with chi(n) not in {0, 1} is at most (log q)^8, so the least quadratic nonresidue mod p is at most (log p)^8; every odd composite n has a Miller-Rabin witness at most (0.7 log n)^8 | OpenAI: least quadratic nonresidue at most C (log p)^32, with C not stated | proved, given the input; enclosure-carrying; unreviewed | [hunt #125](../hunts/qrh_nonresidue/RESULTS.md) |
| Linnik's constant | The least prime congruent to a mod q, for (a, q) = 1, is at most C(eps) q^(7/3 + eps), with C(eps) effective | L = 5, unconditional (Xylouris 2011 and 2018) | proved, given the input and the Chen-Gupta-Li density estimate (arXiv:2507.08296, a preprint); 12/5 from refereed inputs alone; unreviewed | [hunt #123](../hunts/qrh_linnik/RESULTS.md) |

## RH to height 50

Riemann's hypothesis says every nontrivial zero of zeta has real part 1/2. Computers
have checked trillions of zeros, but a computation in floating-point or interval
arithmetic is not a proof a machine can check. Hunt #137 proves the first stretch in
Lean: up to height 50 there are exactly ten zeros, all on the line, all simple. The
route counts every zero in the strip with the argument principle, encloses the
Gamma-side term with a Stirling bound and the zeta side with interval boxes the kernel
decides, and matches the count against ten zeros already located on the line by sign
changes of Hardy's Z (hunts #132 and #133). Because the upper count is exact, no
zero off the line and no double zero can hide below height 50. Like every finite-height
verification it cannot distinguish zeta from the Davenport-Heilbronn function below
that function's first off-line zero, at height 85.699. The second target, height 100
with 29 zeros, has its numerical plan; nineteen more located zeros and new top-edge
enclosures are what it needs.

```bash
LAKE_DIR=$PWD/lean/.lake bash hunts/rh_height_lean/lean/build.sh --full <OUT>   # about 20 minutes, one core
.venv/bin/python lean/check_axioms.py <OUT>/<build log> --full                 # standard axioms only
```

## The earlier results

Carried from [docs/39](39-built-on-the-quasi-riemann-theorem.md), which has the full
account of each and the grades above. The openings below are quoted from it.

### The input

**OpenAI, "The Quasi-Riemann Hypothesis"**, OpenAI Math Release preprint dated
30 September 2026, Theorem 1.1: every finite-order Hecke L-function over
Q(sqrt(-3)), hence every Dirichlet L-function and zeta itself, has no zero in
Re s > 7/8. A companion dated 5 October 2026, written with human assistance,
proves the weaker half-plane Re s > 11/12 by part of the same method.

### Class numbers up to 1500

The class number h(D) of an imaginary quadratic field counts how far unique
factorisation fails in its ring of integers. Gauss asked which fields have class
number 1; the answer (nine fields) took until Heegner, Baker and Stark, and
Watkins completed every h <= 100 in 2004. The difficulty is always the same: a
lower bound h(D) >= f(D) that is explicit, so that only finitely many D can have
a given class number and one can search them all.

### A prime between consecutive ninth powers

Legendre's conjecture asks for a prime between consecutive squares, and it is
open. For a k-th power version valid for every n, the best unconditional k was
86 as of 2026. Given the 7/8 half-plane the explicit formula for primes has an
error of size x^(7/8) (log x)^2, which beats the gap (n+1)^k - n^k, about
k x^(1 - 1/k), exactly when k >= 9. The hunt closes k = 9 for every n: an exact
explicit formula for a smooth weight, sums over zeros bounded in closed form
from explicit zero counts, an Arb cover of 10 <= n <= e^100, an analytic tail,
and Pratt certificates for n <= 9. It closes even if no zero is assumed to lie on
the critical line; the published verification of RH up to height 3 * 10^12 only
widens the margins. OpenAI's weaker 11/12 half-plane alone gives k = 13. With the
same method and no further input k = 8 fails, so 9 is the floor of the
half-plane alone. The hunt's doors named the way below it: an explicit
zero-density estimate, which thins out the zeros near real part 7/8. The next
section takes that door.

### A prime between consecutive seventh powers

The October 8 extensions (`hunts/oct08_extensions/`, PR #282) keep hunt #126's
weight, explicit formula and tail routine and add one published input: Kadiri,
Lumley and Ng's explicit zero-density estimate (arXiv:2101.12263v1, Lemma 4.14
and Table 1), which bounds how many zeros have real part above sigma at five
values of sigma from 3/4 to 0.87. A single split at 0.85 already closes k = 8.
Splitting the zeros between 3/4 and 7/8 into all five strips, each counted with
a positive coefficient so that no two independently bounded counts are ever
subtracted, closes k = 7: for every integer n >= 1 there is a prime strictly
between n^7 and (n+1)^7, given the half-plane and that estimate. The finite
part is a cover of 2.25 <= log n <= 50 by 764 Arb cells, every margin above
0.13045, an analytic tail below 0.012961 beyond it, and trial-division
witnesses for n <= 9; the replay asserts each of those inequalities and
`tests/test_seventh_power_replay.py` runs it. The same bound fails at k = 6
near log n = 29: a failure of this bound, not a statement about primes.

### Small witnesses

If chi is a character mod q that is not identically 1 on the units, how far must
one search to find an n with chi(n) != 1? Under GRH the answer is about
(log q)^2 (Ankeny, Bach). With a zero-free half-plane Re s > theta the classical
exponent is 1/(1 - theta), which is 8 here. The hunt proves it with constant 1:
n <= (log q)^8 for every q >= 3, tight at q = 3, and (0.7 log q)^8 for q >= 5.
The sum over zeros is priced exactly by Hadamard's identity, with no zero
counting at all. Consequences: the least quadratic nonresidue mod p is at most
(log p)^8; every odd composite n has a Miller-Rabin witness at most
(0.7 log n)^8, so Miller's deterministic primality test runs with an explicit
witness range; and the units mod q are generated by the primes up to (log q)^8.
The exponent 8 is not new as a conditional statement (Rodosskii; Montgomery and
Vaughan, Theorem 13.12); the explicit constant and the all-moduli statement were
not found in the search. The least primitive root was also attempted: the bound
obtained is smaller than any power of p but not a power of log p.

### Linnik's constant

Linnik proved that every reduced class mod q contains a prime below q^L for some
fixed L; the best unconditional L is 5. Under GRH it is 2. With every zero at
real part at most 7/8, the Siegel zero, the Deuring-Heilbronn repulsion and the
log-free density estimates all drop out of the argument, and L is governed by
the zero-density exponent for the family of characters mod q on 1/2 <= sigma <=
7/8. With Chen, Gupta and Li's 2025 density estimate this gives L <= 7/3; with
refereed inputs alone, 12/5. Chen, Gupta and Li already state the conditional
implication without proof, so this is the unconditional instantiation and a
complete written proof rather than a new idea. Corollaries: the expected count of
primes in every class once x >= q^(7/3 + eps), and a prime in almost every class
below q^(7/6 + eps).

Related: [docs/39](39-built-on-the-quasi-riemann-theorem.md), [hunt #137](../hunts/rh_height_lean/RESULTS.md), [hunts/README.md](../hunts/README.md).
