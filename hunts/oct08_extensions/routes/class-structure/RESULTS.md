# Genus-aware partial-form bounds

Checkpoint: class-structure-2026-10-08. Owner: delegated class_structure.
Read-only repository base `f4ef0715bbe2f4890b3dcea034757ef0c823053a`.
PR279 inputs pinned at `3f136908426167ff97888a6ae8b89087223509e6`.
Write scope: `task-3/routes/class-structure` only. No Git changes or external
compute. Applied mathbox research-program, proof-audit, literature-check and
computation-audit. Repository mission/results/runs and C/reference code read.

## Outcome

A useful candidate enhancement of the existing lower-bound sieve survives an
exact small-range test. It is an application of classical genus theory, **not
a novel theorem or a completed classification**. Whether the gain pays for
factoring and character evaluations at H=1500 is still unmeasured.

For all 4,055 odd negative fundamental discriminants with |D| <= 20,000,
counting only reduced forms with a <= 10, the genus bound improves even the
divisibility-rounded total-count bound in 1,918 cases. It rejects 330 extra
discriminants for H=20, one extra for H=50, and none extra for H=100.
These are threshold comparisons, not runtime improvements.

At D=-15015, fourteen such forms give a plain bound 14, or 16 after genus
divisibility rounding, while the genus bound gives 64. The full exact count
is 96. The factor-four improvement compares bounds, not speed.

## Exact target and argument

Let D=-n be odd, negative, fundamental, and n the product of t distinct odd
primes, with n=3 mod 4. Let S be any set of distinct canonical reduced
primitive positive-definite forms of discriminant D. For each prime p|n,
evaluate (m/p) at a represented integer m coprime to n. The vector of these
signs is the genus signature. Write N_s for the number of forms in S with
signature s, and g=2^(t-1).

Classical genus theory supplies a surjective homomorphism from the proper
class group to the sign vectors of product +1, with kernel the square
subgroup. Consequently each of its g fibers has exactly h(D)/g elements.
Distinct canonical forms represent distinct proper classes. Thus

    h(D) >= g max_s N_s >= g ceil(|S|/g) >= |S|.

The middle inequality is the pigeonhole principle. A correct rejection rule
for h(D)<=H is max_s N_s > floor(H/g). This conclusion is unconditional given
the classical genus-theory input; no zero-free hypothesis is used. The
finite implementation currently supports only odd fundamental D.

More generally, for any surjective homomorphism of finite groups G -> Q,
the same bound |G| >= |Q| max_q |S intersect fiber(q)| holds. The proof is
just equal coset cardinalities. This generality is classical and is not
claimed as research novelty.

The existing cn.c filter sums partial forms without this partition. The
proposed adaptation would retain a small counter per genus for survivors,
after cheap filters, and stop as soon as any counter crosses floor(H/g).
Doing this before streaming could lose the existing periodicity advantage.
No production implementation or speed claim has been made.

## Falsification and limits

Every discriminant in the stated finite domain passed full genus uniformity,
the product-sign convention, g distinct signatures, exact h comparison with
the pinned PR279 reference counter, and all three bound inequalities.
The two form counters share the mathematical reduced-form definition, but
use different boundary-loop conventions; this is not an independent PARI
implementation. All decisions use Python exact integers.

The tempting shortcut of multiplying the total count by g is false already
at D=-15: h=2, g=2, so that shortcut says 4<=2. The code checks this decoy.
Ramified leading coefficients cannot be fed into a character as though they
were coprime; the implementation finds a coprime represented value instead.
Its finite search for that value raises an error after 101 trials; it never
silently omits a form. The canonical reduced-form duplicate check is explicit.

**Genus checks cannot prove completeness of an enumerated list.** At D=-39
the four reduced forms are (1,1,10), (2,-1,5), (2,1,5), (3,3,4).
The first and last have signature (+,+), the middle two (-,-). Deleting one
form from each genus leaves a false count h=2 that passes divisibility,
the number of genera, and genus uniformity. Thus this invariant cannot fill
PR279's missing all-discriminant streamed-filter audit. This is an exact
counterexample to that proposed audit criterion, not to PR279's result.

## Sources and overlap

Cremona and Sutherland, *Computing the endomorphism ring of an elliptic curve
over a number field*, arXiv:2301.11169v4, section 5, checked 2026-10-08:
https://arxiv.org/html/2301.11169v4#S5
Their 4,115,897 fundamental discriminants with h<=1000 and the largest
|D|=227932027 match PR279's totals. Their all-orders list has 6,450,424
discriminants and assumes GRH for completeness. Accordingly PR279 is not
the first even-class-number classification above 100.

Genus theory is a classical external input. Primary-source retrieval for its
exact formulation was unsuccessful in this session (the attempted Conrad
PDF was inaccessible, and searches returned mostly irrelevant results).
The universal genus-to-filter implication is therefore marked **conditional
on that named external theorem pending exact-source verification** in this
audit, despite the 4,055 finite checks. No novelty claim is supported by this
bounded search. A source-checking reviewer should use the principal genus
theorem for imaginary quadratic fields and the odd fundamental discriminant
genus-character formula; verify surjectivity, not only the character map.

## Reproduction and independent audit

From zeta-research:

    .venv/bin/python ../routes/class-structure/probe.py

Python 3.13.14, one process, hard CPU cap 20 seconds, measured about 2 seconds.
No numerical libraries or network required. Output in probe.json. The exact
row hash is 52cc9a4beb6fff3a7a6d7a1838216c007c1c17035abbc1bf13a86df849d9071f.
reference_pinned.py is the unmodified classno.py from the pinned PR279 SHA.

Independent audit path: derive the equal-coset bound from the stated class
group map; check signatures using a second coprime represented integer;
recompute full h using PARI qfbclassno or another reduced-form enumerator;
verify the D=-39 deletion decoy; then benchmark the survivor-stage filter
against cn.c on disjoint windows without changing the recorded master data.
Do not interpret a matched hash as proof of a universal statement.

Status: promising implementation experiment; universal application awaits
exact-source review, H=1500 relevance and net speed remain open. No new
classification or genuinely new mathematical discovery has been established.
