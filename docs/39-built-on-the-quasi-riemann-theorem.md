# 39. Built on the quasi-Riemann theorem: what a zero-free half-plane at 7/8 buys

> On 2026-10-06 OpenAI released a proof that no Dirichlet L-function, zeta
> included, has a zero with real part above 7/8. On 2026-10-08 this laboratory
> rebuilt the Lean proof of that statement on its own compute, and two
> independent proof kernels accepted it. The same day, four theorems were proved
> here on top of it. This page states them, says what each one is measured
> against, and grades each one honestly.

Every result below except the first is **proved, given OpenAI's theorem**: the
argument is an ordinary written proof by this laboratory, read line by line by
the session that landed it, with every numerical step carried by Arb ball
arithmetic and every list produced by exact integer computation. **No outside
mathematician has reviewed any of them yet**, and OpenAI's own 195-page argument
has not been read in full by any person either. A composite claim takes the
grade of its weakest step (`AGENTS.md`), so that is the grade of everything
here: candidate, pending external review.

## The input

**OpenAI, "The Quasi-Riemann Hypothesis"**, OpenAI Math Release preprint dated
30 September 2026, Theorem 1.1: every finite-order Hecke L-function over
Q(sqrt(-3)), hence every Dirichlet L-function and zeta itself, has no zero in
Re s > 7/8. A companion dated 5 October 2026, written with human assistance,
proves the weaker half-plane Re s > 11/12 by part of the same method.

What this laboratory checked, recorded in [docs/38](38-the-quasi-riemann-claim.md):
the Lean statements match the paper and Mathlib's own `riemannZeta` and
`DirichletCharacter.LFunction` (section 3); the proof's import closure is free of
`sorry` at text level, once OpenAI's patch to one dependency is applied (section
4); the full build from the pinned public commit succeeds on this laboratory's
GitHub Actions runner in 2 h 15 min, `#print axioms` on the three statements
returns only `propext`, `Classical.choice` and `Quot.sound`, and Comparator with
the independent NanoDa kernel switched on accepts all three (section 7). What it
did not check: the mathematics of the 195 pages, the Hecke statement's module,
and anything about RH. 7/8 is not 1/2.

## The results

| Result | Statement | Against | Grade | Where |
| --- | --- | --- | --- | --- |
| The input, replayed | Lean's kernel and the independent NanoDa kernel accept OpenAI's statements that zeta(s) and every Dirichlet L(s, chi) are nonzero for Re s > 7/8, and its Siegel-zero gap, with only the three standard axioms | OpenAI's own build; no outside replay was known | kernel-checked on two kernels, on this laboratory's compute; the argument is unreviewed by any person | [docs/38](38-the-quasi-riemann-claim.md), section 7 |
| Class numbers up to 1500 | h(D) >= sqrt(q) / (10 pi log log q) for every negative fundamental discriminant D, with q = -D; hence the complete list of imaginary quadratic fields of class number h, for every h <= 1500: 9,245,562 fields, the largest with q = 562,394,347 | Watkins (2004): h <= 100 unconditionally. [Cremona-Sutherland (2023), section 5](https://arxiv.org/html/2301.11169v4#S5): all h <= 1000, including even h, under GRH. OpenAI: the same shape of bound, constant not computed | proved, given the input; constants enclosure-carrying; lists by exact computation; unreviewed | [hunt #124](../hunts/qrh_class_number/RESULTS.md) |
| Primes between ninth powers | For every integer n >= 1 there is a prime p with n^9 < p < (n+1)^9 | k = 86 for every n, unconditional (Lee, arXiv:2602.14340, 2026) | proved, given the input; every numerical step enclosure-carrying; unreviewed | [hunt #126](../hunts/qrh_prime_powers/RESULTS.md) |
| Small witnesses | For every nonprincipal Dirichlet character chi mod q >= 3, the least n with chi(n) not in {0, 1} is at most (log q)^8, so the least quadratic nonresidue mod p is at most (log p)^8; every odd composite n has a Miller-Rabin witness at most (0.7 log n)^8 | OpenAI: least quadratic nonresidue at most C (log p)^32, with C not stated | proved, given the input; enclosure-carrying; unreviewed | [hunt #125](../hunts/qrh_nonresidue/RESULTS.md) |
| Linnik's constant | The least prime congruent to a mod q, for (a, q) = 1, is at most C(eps) q^(7/3 + eps), with C(eps) effective | L = 5, unconditional (Xylouris 2011 and 2018) | proved, given the input and the Chen-Gupta-Li density estimate (arXiv:2507.08296, a preprint); 12/5 from refereed inputs alone; unreviewed | [hunt #123](../hunts/qrh_linnik/RESULTS.md) |

## Why a half-plane is worth so much

Almost every question about primes in arithmetic progressions, small
nonresidues or class numbers is decided by one thing: how close the zeros of
Dirichlet L-functions can come to the line Re s = 1. Classical zero-free regions
narrow as the modulus grows, and they leave room for one possible exceptional
real zero, the Landau-Siegel zero, which is why Siegel's theorem on class
numbers has a constant nobody can compute. A fixed half-plane removes all of that
at once: every zero sits at real part at most 7/8, for every modulus and at every
height. The arguments below are classical in shape. What is new is that the
hypothesis they need is now, given OpenAI's theorem, a fact, and that each one
is carried through with explicit constants until it says something concrete.

## Class numbers up to 1500

The class number h(D) of an imaginary quadratic field counts how far unique
factorisation fails in its ring of integers. Gauss asked which fields have class
number 1; the answer (nine fields) took until Heegner, Baker and Stark, and
Watkins completed every h <= 100 in 2004. The difficulty is always the same: a
lower bound h(D) >= f(D) that is explicit, so that only finitely many D can have
a given class number and one can search them all.

Given the 7/8 half-plane, Littlewood's short Euler product makes L(1, chi_D),
and with it h(D), explicitly large: h(D) >= sqrt(q) / (10 pi log log q) for
q = -D, with a sharper interval-by-interval table D(h) such that h(D) <= h
forces q <= D(h), for every h <= 2000 (for example D(100) = 48,611,613 and
D(1500) = 12,409,254,457). An exact reduced-form sieve, using no GRH, then
visited all 3.77 billion fundamental discriminants below D(1500) in 39
CPU-minutes. The result is the complete list for every h <= 1500. It reproduces
all 100 of Watkins' counts exactly, and its 750 odd class numbers agree exactly
with the GRH-conditional table of Holmin, Jones, Kurlberg, McLeman and
Petersen. [Cremona and Sutherland (2023), section 5](https://arxiv.org/html/2301.11169v4#S5)
already give a GRH-complete classification for every h <= 1000, including even
h: 4,115,897 fundamental discriminants (6,450,424 discriminants when
nonmaximal orders are included; their data are in
[EndECNF](https://github.com/AndrewVSutherland/EndECNF)). Thus the even lists
for 102 <= h <= 1000 are not first discoveries here. The distinction is the
weaker 7/8 zero-free hypothesis in place of GRH and the computed extension
from h <= 1000 to h <= 1500, with completeness conditional on that input and
the written analytic argument. Extending that cited table is not a claim of
global priority for the range above 1000.

The mechanism is Littlewood's and was run under a 3/4 hypothesis by Friedlander
and Iwaniec without constants; the explicit constant 1/(10 pi), cutoff table
and enumeration recorded here were computed by this laboratory. Proof: `RESULTS.md` sections 2 to 5 of the hunt.

## A prime between consecutive ninth powers

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
same method k = 8 fails, so 9 is the floor until a stronger input arrives.

## Small witnesses

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

## Linnik's constant

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

## What the half-plane does not buy

- **RH.** Nothing here says anything about real part 1/2.
- **Primes in short intervals.** The classical exponents for primes in short
  intervals are set by zero density near real part 3/4, which a half-plane at 7/8
  does not touch, so they do not improve. Hunt #121 (`hunts/qrh_conditional/`) prices every
  one of this laboratory's own walls under the 7/8 strip: one moves by a quarter
  power and stays three quarters short.
- **The k = 8 case, a polylogarithmic primitive root, and anything below the
  stated exponents.** Each hunt ends with a section "The doors" naming what would
  have to change.

## Check it yourself

```bash
# the complete class-number lists for h <= 100, given the theorem, in about 3 seconds
.venv/bin/python -m hunts.qrh_class_number.run_search 100 48611613 /tmp/cn100
# the same for h <= 1500 (about 39 CPU-minutes; resumable from chunk checkpoints)
.venv/bin/python -m hunts.qrh_class_number.run_search 1500 12409254457 /tmp/cn1500
# every hunt's own tests
.venv/bin/python -m pytest -q -n0 hunts/qrh_class_number hunts/qrh_prime_powers hunts/qrh_nonresidue hunts/qrh_linnik
```

The search driver rewrites the timing fields of the committed summary
`search_H<H>.json`; the counts and the sha256 of the list do not change. The
replay of the input runs on GitHub Actions: dispatch
`.github/workflows/replay-openai-003.yml` with mode `build`, then `comparator`.

A review of any of these is the most useful thing an outside reader could send.
Open an issue that names the hunt and the section.
