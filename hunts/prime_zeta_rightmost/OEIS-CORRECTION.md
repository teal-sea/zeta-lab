# OEIS-CORRECTION.md: draft texts for OEIS (WP7)

**DRAFT. Nothing in this file has been posted. Posting to OEIS is an
operator action, explicitly outside this hunt's permissions (MISSION.md,
agents_may_not).**

**Rewritten 2026-08-16, after MISSION.md kill condition 2 fired.** That
condition says: *a literature source is found proving the sigma_c threshold
for P, in which case the finding is reclassified as a rediscovery and the
OEIS correction cites that source instead of this work.* Two such sources
exist (SOURCE.md sections 4.1 and 4.2), so the drafts below cite them for
the threshold, and attribute to this work only what remains its own:

- the refutation *connection*, that is, pointing the published mathematics
  at A107311's two conjectures, which no source in the literature engages;
- the unboundedness of the tail-subset thresholds (Theorem C2, Corollary
  C3), for which no prior art was located by four independent searches;
- the constant sigma_3 for {p prime >= 3}, a new instance of the published
  theory.

Everything else in the drafts belongs to Belovas, Cepaityte and
Sabaliauskas (2025) or to Sepulcre and Vidal (2022). The mathematical
claims rest on those papers plus `THEOREM.md` (this hunt's own proofs,
correct but second) and `decided.json` / `theorem_inputs.json` (enclosures,
both backends); they carry the composite grade recorded in `RESULTS.md`
section 7 and are pending external verification, which the operator should
weigh before posting. Names, dates and A-numbers for the new sequence are
placeholders for the operator to fill.

The two sources, in full, since both drafts cite them:

- **[B]** I. Belovas, R. Cepaityte and M. Sabaliauskas, *On the zero-free
  region and the distribution of zeros of the prime zeta function*, An. St.
  Univ. Ovidius Constanta Ser. Mat. **33**(2) (2025), 27-44, DOI
  `10.2478/auom-2025-0017`. Open access. Their Theorem 1: the prime zeta
  function has no zeros in the half-plane sigma > sigma_0, where
  sigma_0 = 1.77954465354699... is the zero of
  U(sigma) = 2^(1-sigma) - zeta_P(sigma).
- **[SV]** J. M. Sepulcre and T. Vidal, *On the real projections of zeros
  of analytic almost periodic functions*, Carpathian J. Math. **38** (2022),
  no. 2, 489-501 (preprint arXiv:1805.02041, 2018, where the same statement
  is Theorem 6). Their Theorem 4.3 characterizes the closure of the real
  projections of the zeros of an almost periodic Dirichlet series with
  Q-linearly independent frequencies; specialized to the prime zeta
  function it gives both halves, that the half-plane above sigma_0 is
  zero-free and that sigma_0 is approached.

---

## 1. Draft comment for A107311

To follow (or replace, at the editors' discretion) the Dec 21 2024
conjecture block; written to OEIS comment style, ASCII math, sentences
signed by the poster. The threshold and its proof are cited, not claimed.

> The two conjectures in the Dec 21 2024 comment are false. The supremum of
> the real parts of the zeros of the prime zeta function
> P(s) = Sum_{p prime} p^(-s) is not this constant but
> sigma_c = 1.7795446535469941..., the root of P(x) = 2^(1-x), that is the
> balance of the p = 2 term against the sum over the odd primes. Belovas,
> Cepaityte and Sabaliauskas (2025), Theorem 1, prove that P has no zeros
> with Re(s) > sigma_c; the same statement follows from Theorem 4.3 of
> Sepulcre and Vidal (2022), which also gives the other half, that every
> strip sigma < Re(s) < sigma_c with sigma > 1 contains zeros of P, so that
> sigma_c is the supremum and is not attained. Since sigma_c exceeds this
> constant by more than 1/20, Conjecture 1 fails. All the zeros concerned
> lie in the half-plane of absolute convergence Re(s) > 1.
>
> Conjecture 2 fails for every possible bound, not only for this constant.
> The subseries over {p prime >= 3} has its own threshold
> 1.8252259560738457..., already larger than sigma_c, and the subseries
> over {p prime >= prime(k)} has threshold at least
> log_2(3*prime(k)/(5*log(prime(k)))), which is unbounded in k (via the
> Rosser-Schoenfeld inequality pi(2x) - pi(x) > 3x/(5*log(x))). So no
> constant bounds the real parts of the zeros across all subsets of the
> primes.
>
> This constant keeps its established role for the partial sums of zeta
> (Borwein et al., 2007, Theorem 3.1): it is the limit of the
> triangle-inequality bounds beta_X of Gonek and Ledoan, and by
> Montgomery's theorem the real parts of the actual zeros of the partial
> sums tend to 1, so this constant is not approached by zeros in that
> family either. - [OPERATOR NAME], [DATE]

Attribution inside that comment, so the operator can check it before
posting: sigma_c and its zero-free half-plane are Belovas et al.'s; the
sharpness and the general mechanism are Sepulcre and Vidal's; what is being
contributed here is that these results refute the entry's conjectures,
together with the {p >= 3} threshold and the tail-subset unboundedness.

Link entries to accompany the comment (the first two are the sources the
comment leans on and should be posted with it):

> Igoris Belovas, Rugile Cepaityte, and Martynas Sabaliauskas, <a
> href="https://www.anstuocmath.ro/mathematics/anale2025v2/2_Igoris_Belovas_et_al.pdf">
> On the zero-free region and the distribution of zeros of the prime zeta
> function</a>, An. St. Univ. Ovidius Constanta Ser. Mat. 33(2) (2025),
> 27-44.

> J. M. Sepulcre and T. Vidal, <a href="https://arxiv.org/abs/1805.02041">
> On the real projections of zeros of almost periodic functions</a>,
> arXiv:1805.02041 [math.CV], 2018; published as "On the real projections
> of zeros of analytic almost periodic functions", Carpathian J. Math. 38
> (2022), no. 2, 489-501.

> [OPERATOR NAME], <a href="[REPOSITORY URL]/hunts/prime_zeta_rightmost">
> The rightmost zeros of the prime zeta function</a>, zeta-lab
> repository, 2026. [The refutation of the conjectures above, the
> {p prime >= 3} threshold, the tail-subset bound, and interval enclosures
> of the constants on two independent backends.]

Further references the comment leans on (already in or adjacent to the
entry):

- P. Borwein, G. Fee, R. Ferguson, A. van der Waall, Zeros of Partial
  Sums of the Riemann Zeta Function, Experiment. Math. 16 (2007), no. 1,
  pp. 21-40. (Already linked in A107311.)
- S. M. Gonek and A. H. Ledoan, Zeros of partial sums of the Riemann
  zeta-function, Int. Math. Res. Not. IMRN 2010, no. 10, pp. 1775-1791.
- J. B. Rosser and L. Schoenfeld, Approximate formulas for some
  functions of prime numbers, Illinois J. Math. 6 (1962), pp. 64-94.
- C. J. Moreno, The zeros of exponential polynomials (I), Compositio Math.
  26 (1973), no. 1, pp. 69-78. (The Geometric Principle both [B] and [SV]
  rest on; optional for an OEIS comment.)

---

## 2. Draft new-sequence submission: decimal expansion of sigma_c

**The constant is Belovas et al.'s sigma_0**, published in 2025 to 15
printed digits with the remark that it can be computed to any necessary
precision. This submission contributes the expansion, not the constant, and
the comment field says so. All digits below are exactly the digits on which
both endpoints of the decided flint enclosure agree (python-flint (arb),
350 bits, width 7.889e-32, `decided.json`; mpmath.iv at dps 40 confirms to
its own width). 31 digits are decided; a deeper bisection with the same
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
> This constant is the sigma_0 of Theorem 1 of Belovas, Cepaityte and
> Sabaliauskas (2025), who prove that the prime zeta function has no zeros
> in the half-plane Re(s) > sigma_0 and give its value as
> 1.77954465354699... .
>
> It is the supremum of the real parts of the zeros of the prime zeta
> function, approached but not attained: this is Theorem 4.3 of Sepulcre
> and Vidal (2022) applied to P(s), whose frequencies log(p) are linearly
> independent over the rationals. Every strip sigma < Re(s) < this constant
> with sigma > 1 contains zeros of P, and all such zeros lie in Re(s) > 1.
>
> Larger than A107311 (= 1.7286..., the root of zeta(x) = 2, the
> corresponding threshold for the partial sums of zeta) by more than
> 1/20. The Dec 21 2024 conjectures in A107311, which proposed that
> constant as the bound for the zeros of the prime zeta function and of its
> subset series, are therefore false; this constant is the correct
> threshold for the full series. Subset series have their own thresholds:
> 1.8252259... for {p prime >= 3}, which is larger still, and unbounded
> thresholds for the tails {p prime >= prime(k)}.

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

**%H (Links):**

> Igoris Belovas, Rugile Cepaityte, and Martynas Sabaliauskas, <a
> href="https://www.anstuocmath.ro/mathematics/anale2025v2/2_Igoris_Belovas_et_al.pdf">
> On the zero-free region and the distribution of zeros of the prime zeta
> function</a>, An. St. Univ. Ovidius Constanta Ser. Mat. 33(2) (2025),
> 27-44. [Theorem 1: this constant is the boundary of the zero-free
> half-plane.]

> J. M. Sepulcre and T. Vidal, <a href="https://arxiv.org/abs/1805.02041">
> On the real projections of zeros of almost periodic functions</a>,
> arXiv:1805.02041 [math.CV], 2018. [Theorem 6, published as Theorem 4.3:
> the characterization that makes this constant the supremum.]

> [OPERATOR NAME], <a href="[REPOSITORY URL]/hunts/prime_zeta_rightmost">
> The rightmost zeros of the prime zeta function</a>, zeta-lab
> repository, 2026. [Interval enclosures of this constant on two
> independent backends.]

Operator notes, not for submission: the digit list stops where the two
enclosure endpoints stop agreeing (31 digits); OEIS convention prefers
about 20 terms minimum for cons sequences, which this meets. If the
editors want the customary ~100 digits, re-run `decide.py` with a deeper
target width first and extend the data line only from digits on which
both endpoints of the new enclosure agree. Check first whether Belovas et
al. or anyone else has already submitted this constant, since it has been
in print since June 2025; the searches this hunt ran are not a reliable
guide, for the reasons in SOURCE.md section 4.6.

A companion submission for the {p >= 3} threshold
1.8252259560738457623878727108... (the digits on which both endpoints of
the decided flint enclosure in `decided.json` agree) is possible on the
same pattern and is left to the operator's judgment. That constant, unlike
sigma_c, was not found in any source: it is a new instance of the published
theory rather than a published value, and its comment field may say that
the {p prime >= 3} subseries out-walls the full series by more than 0.045.

---

## 3. The bridge observation, which does not belong on OEIS

Recorded here because the operator will ask where it goes, and the answer
is: not into either draft above, except as the single sentence already
present in section 2's comment field.

Belovas et al. state their sharpness claim as **Conjecture 1** and leave it
open: with sigma_T = max{sigma : P(sigma + it) = 0, |t| < T}, they conjecture
that sigma_T tends to sigma_0 as T grows, their own numerics reaching only
1.682628788045196... at |t| < 200000. That conjecture is a corollary of
Sepulcre and Vidal Theorem 4.3, whose "if" direction places sigma_0 in the
closure of the real projections of the zeros; and the "only if" direction of
the same theorem already contains their Theorem 1. Their theorem and their
open conjecture are the two directions of one published characterization
that predates both, and neither paper cites the other: one is filed under
number theory, the other under almost periodic functions (MSC 30B50,
30D20).

Grade, stated exactly: the specialization and the derivation are proved in
`PRIOR-ART.md` sections 6 and 7 against both sources read verbatim, with no
gap found; not refereed, not kernel-checked, pending external verification.
It is an observation about the literature, not a new theorem, and this hunt
neither proved Theorem 4.3 nor proved Conjecture 1.

The right destination is a note to the authors of [B] and, if it holds up
under their reading, a citation in whatever venue carries the correction to
A107311. An OEIS comment is the wrong place for it: OEIS comments are about
the sequence, and this is about two papers. Section 2's comment field says
only that Theorem 4.3 makes the constant the supremum, which is the part
that concerns the sequence. Deciding whether to write that note is an
operator action, like posting anything else in this file.
