# OEIS-CORRECTION.md: draft texts for OEIS (WP7)

**DRAFT. Nothing in this file has been posted. Posting to OEIS is an
operator action, explicitly outside this hunt's permissions (MISSION.md,
agents_may_not).** The mathematical claims below rest on `THEOREM.md`
(proofs) and `decided.json` / `theorem_inputs.json` (enclosures, both
backends); they carry the composite grade recorded in `RESULTS.md`
section 7 and are pending external review, which the operator should
weigh before posting. Names, dates and A-numbers for the new sequence are
placeholders for the operator to fill.

---

## 1. Draft comment for A107311

To follow (or replace, at the editors' discretion) the Dec 21 2024
conjecture block; written to OEIS comment style, ASCII math, sentences
signed by the poster.

> The two conjectures in the Dec 21 2024 comment are false. The supremum
> of the real parts of the zeros of the prime zeta function
> P(s) = Sum_{p prime} p^(-s) is not this constant but the root
> sigma_c = 1.7795446535469941... of P(x) = 2^(1-x) (the balance of the
> p = 2 term against the sum over odd primes), which exceeds this
> constant by more than 1/20. For Re(s) >= sigma_c, |P(s)| > 0 by the
> triangle inequality together with the linear independence of the
> log p over the rationals; for every sigma < sigma_c the strip
> sigma < Re(s) < sigma_c contains infinitely many zeros of P, by a
> Bohr-Kronecker-Rouche argument. All these zeros lie in the half-plane
> of absolute convergence Re(s) > 1. Conjecture 2 fails for every
> possible bound, not only this constant: the subseries over
> {p prime >= 3} has zeros with real parts arbitrarily close to its own
> threshold 1.8252259560738457..., and the subseries over
> {p prime >= prime(k)} has threshold at least
> log_2(3*prime(k)/(5*log(prime(k)))), which is unbounded in k (via the
> Rosser-Schoenfeld inequality pi(2x) - pi(x) > 3x/(5*log(x))). This
> constant keeps its established role for the partial sums of zeta
> (Borwein et al., 2007, Theorem 3.1): it is the limit of the
> triangle-inequality bounds beta_X of Gonek and Ledoan, and by
> Montgomery's theorem the real parts of actual zeros of the partial
> sums tend to 1, so this constant is not approached by zeros in that
> family either. - [OPERATOR NAME], [DATE]

Optional link entry to accompany the comment:

> [OPERATOR NAME], <a href="[REPOSITORY URL]/hunts/prime_zeta_rightmost">
> The rightmost zeros of the prime zeta function</a>, zeta-lab
> repository, 2026. [Proofs, interval enclosures on two backends, and
> the computation record for the constants above.]

References the comment leans on (already in or adjacent to the entry):

- P. Borwein, G. Fee, R. Ferguson, A. van der Waall, Zeros of Partial
  Sums of the Riemann Zeta Function, Experiment. Math. 16 (2007), no. 1,
  pp. 21-40. (Already linked in A107311.)
- S. M. Gonek and A. H. Ledoan, Zeros of partial sums of the Riemann
  zeta-function, Int. Math. Res. Not. IMRN 2010, no. 10, pp. 1775-1791.
- J. B. Rosser and L. Schoenfeld, Approximate formulas for some
  functions of prime numbers, Illinois J. Math. 6 (1962), pp. 64-94.

---

## 2. Draft new-sequence submission: decimal expansion of sigma_c

All digits below are exactly the digits on which both endpoints of the
decided flint enclosure agree (python-flint (arb), 350 bits, width
7.889e-32, `decided.json`; mpmath.iv at dps 40 confirms to its own
width). 31 digits are decided; a deeper bisection with the same
instrument yields more.

**%N (Name):**

> Decimal expansion of the real root of 2^(-x) = Sum_{p prime >= 3}
> p^(-x).

**%D (Data, offset 1,2):**

> 1, 7, 7, 9, 5, 4, 4, 6, 5, 3, 5, 4, 6, 9, 9, 4, 1, 1, 6, 4, 4, 5, 8,
> 9, 8, 7, 8, 6, 9, 6, 5

**%C (Comments):**

> Equivalently, the root of P(x) = 2^(1-x), where P is the prime zeta
> function P(s) = Sum_{p prime} p^(-s): the point where the leading term
> 2^(-x) exactly balances the tail over the odd primes.
>
> This is the supremum of the real parts of the zeros of the prime zeta
> function: P(s) has no zeros with Re(s) >= this constant, and every
> strip sigma < Re(s) < (this constant) with sigma > 1 contains
> infinitely many zeros of P. The supremum is approached but not
> attained. All such zeros lie in Re(s) > 1.
>
> Larger than A107311 (= 1.7286..., the root of zeta(x) = 2, the
> corresponding threshold for the partial sums of zeta) by more than
> 1/20. The Dec 21 2024 conjectures in A107311, which proposed that
> constant as the bound for zeros of the prime zeta function and its
> subset series, are false; this constant is the correct threshold for
> the full series. Subset series have their own thresholds: 1.8252259...
> for {p prime >= 3}, and unbounded thresholds for the tails
> {p prime >= prime(k)}.

**%F (Formula):**

> Unique real solution x > 1 of Sum_{p prime} p^(-x) = 2^(1-x).

**%e (Example):**

> 1.779544653546994116445898786965...

**%t (Mathematica):**

> x /. FindRoot[PrimeZetaP[x] == 2^(1 - x), {x, 9/5},
>   WorkingPrecision -> 40]

**%o (Program, PARI):**

> (PARI) solve(x=1.7, 1.9, suminf(k=1, moebius(k)/k*log(zeta(k*x))) - 2^(1-x))

**%Y (Cross-references):**

> Cf. A107311.

**%K (Keywords):** nonn,cons

**%O (Offset):** 1,2

**%H (Link):**

> [OPERATOR NAME], <a href="[REPOSITORY URL]/hunts/prime_zeta_rightmost">
> The rightmost zeros of the prime zeta function</a>, zeta-lab
> repository, 2026.

Operator notes, not for submission: the digit list stops where the two
enclosure endpoints stop agreeing (31 digits); OEIS convention prefers
about 20 terms minimum for cons sequences, which this meets. If the
editors want the customary ~100 digits, re-run `decide.py` with a deeper
target width first and extend the data line only from digits on which
both endpoints of the new enclosure agree. A companion submission for
the {p >= 3} threshold 1.8252259560738457623878727108... (the 29 digits
on which both endpoints of the decided flint enclosure in `decided.json`
agree) is possible on the same pattern but is left to the operator's
judgment.
