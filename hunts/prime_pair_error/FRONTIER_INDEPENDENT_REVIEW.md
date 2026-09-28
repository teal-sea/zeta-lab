# Independent review of the Farey repair and signed-mean divisor draft

Date: 2026-09-12. Source base: `zeta-lab` commit
`3b0fc2e3c97b46cc1fde6af0ff3dd856898d95fb`.

**Primary verdict: conditional on the named inherited inputs.** The mathematical
derivations reviewed below survive under those inputs. I found no fatal defect
in the Farey baseline or signed-mean sections 1–9. The unproved prime-counting
estimate remains unproved. This is an independent handwritten audit, not
external peer review, a formal proof, or evidence about RH.

The exact reviewed draft hashes, before integration, are:

| Artifact | SHA-256 |
|---|---|
| `farey-repair-draft.md` | `cd19db4516f8978aa4466a019b74c05425b2a41a6fa4578b0a59125b870ab8fc` |
| `signed-mean-draft.md` | `1af64620833ef469f0f941e8bd4acf4816883170a3e47d700b7ea8323be3f723` |

I read the raw drafts end to end, re-derived the critical implications, read
the applicable root instructions and the original correction definition, and
used fresh finite checks that import neither the authors' code nor repository
mathematical implementations. Settled Theorem B and the old full upper bound
were not re-audited. No repository or remote files were changed by this review.

## 1. Exact surviving claims

The Farey claim is the following upper bound. For integer `N >= 16`, real
`1 <= Q <= N^(2/5)`, reduced numerators, all prime powers in `Lambda`, and
`Q <= q < 2Q` with `q <= sqrt(N)`, the block residual has integrated second
moment `O(N log N)` and integrated fourth moment
`O(N^3 (log N)^9 / Q)`. The constants are absolute, apart from inherited
absolute constants. There is no matching lower bound or optimality claim.

The signed-mean claim is an equivalence for the scalar quantity
`M_N = 2 |sum_h(r_N(h)-C_N(h))|^2 / N`, with the sharp endpoints,
infinite singular series, and exact correction at `Z = exp(sqrt(log N))`:
RH is equivalent to `M_N = O_epsilon(N^(2+epsilon))` for every positive
epsilon. Exceptional data can change with every integer `N`. This is not
an equivalence for the full corrected energy.

The divisor claims are exact identities and their uniform estimates. In the
notation of the draft,

\[
 L_KR(N)=G(N)+(1+\gamma)N-Q_{N,K},\qquad
 |Q_{N,K}|\ll N/K,
\]

for every integer `1 <= K <= N`. Hence `L_K R(N) = O(N/K + log N)`.
This does not bound `R(N)` by itself. The power-mode multiplier is
`zeta(rho)`, with error `O_rho((N/K)^Re(rho))`. Conditional on a zero
`rho` in `0 < Re(rho) < 1`, the constructed model preserves positivity,
monotonicity, the exact integral normalization, the inherited PNT envelope,
and all these scale bounds. It does not preserve the exact arithmetic
forcing or prime-power support. At any zero of multiplicity `m`, exact
forcing inversion leaves residue `-m/rho` in the transform of `R`.

## 2. Dependencies and obligation matrix

The Farey main route is:

`separation + circle Parseval + Chebyshev` -> second moment for `F`;
`dyadic reciprocal-totient bound + Parseval` -> second moment for the model;
these two estimates -> residual second moment;
`Vaughan + Q <= N^(2/5)` -> residual supremum;
`supremum times second moment` -> the fourth moment.

The optional route is:

`clipped Gallagher` -> short interval sums;
`reduced Gauss diagonalization + inducing Gauss factor` -> primitive weights;
`primitive interval large sieve + integrated coefficient count` -> second
moment, with centered principal and omitted-prime-power terms bounded
separately.

The signed route is:

`uniform signed correction + CHHL first moment + diagonal bound + exact pairs`
-> exact `B_N` identity with `A_N = O(N log^2 N)`;
`von Koch` -> forward implication;
`psi >= 0 + integer-to-real extension + Mellin holomorphy + functional equation`
-> converse.

The renewal route is:

`sum_{d|m} Lambda(d)=log m` -> exact divisor identity;
`unconditional PNT + Laurent constant` -> integral `-1-gamma`;
`bounded variation quadrature` -> exact scale identity and bound;
`Euler summation` -> transfer multiplier;
`compact integral correction + derivative bound` -> monotone model;
`Mellin convolution + local zero factorization` -> residue computation.

| Obligation | Result | Detail |
|---|---|---|
| Farey overlap and circle endpoints | Passed | Radius is at most `1/4` at the stated minimum; multiplicity is at most an absolute constant. |
| Residual second moment | Passed | The two terms separately cost `O(N log N)` and `O(N)`. |
| Fourth-moment range and logarithm | Passed | The `N^(4/5)` term imposes the stated range; squaring `L^4` and using `NL` gives `L^9`. |
| Exact character identities | Passed | The centered principal term and the nonreduced extension are retained correctly. |
| Imprimitive Gauss weights | Passed | Nonzero only for squarefree `q/d` coprime to `d`; weight is `d/phi(d)`, after summing the multiplier. |
| Gallagher support and prime powers | Passed | Support is clipped and has length `N+h`; the model subtracts the integer count. |
| New `Z` substitution | Passed | Uniformity uses only `q < Z`, `beta >= 3/4`, and the Mertens product bound. |
| Mean criterion epsilon quantifiers | Passed | Use `epsilon=2 theta`; real endpoints differ by less than one. |
| Integral constant and quadrature signs | Passed | The constant is `-1-gamma`; both endpoints `K=1,N` are included. |
| All-`K` mode estimate | Passed | The remainder constant may depend on the fixed exponent, not on `K,N`. |
| Model admissibility | Passed in its stated domain | Nonnegative monotone functions with the listed retained properties, not prime-power summatory functions. |
| Multiple-zero cancellation claim | Passed | Numerator has order `m-1`, so division leaves a simple pole. |
| Fixed power saving or RH input bound | Not addressed | Neither draft proves one. |
| Global impossibility or unconditional off-critical counterexample | Not established | The model statement is conditional on the specified zero. |
| Inherited classical estimates | Conditional source leaves | Accepted in their recorded form; no fresh global source review. |

The inherited leaves are the Vaughan estimate, primitive interval large
sieve, Gallagher lemma, Chebyshev bounds, Mertens product bound, CHHL
singular-series first moment, unconditional PNT error, classical RH
prime-counting consequence, Euler product and functional equation.
Their local locators are those named in the drafts. The correction's signed
argument in `CORRECTED_RH_BRIDGE.md`, sections 2–3, was read directly and its
parameter substitution re-derived. No transfer of an old full-energy bound
to the new `Z` is needed or justified by this review.

## 3. Decisive mathematical checks

For the Farey proof, let `m(alpha)` count block arcs covering a point. Reduced
centers have separation at least `1/(4Q^2)` and all relevant centers lie in
an interval of length at most `2/(Q sqrt N)`. Thus `m <= 9` with harmless
endpoint conventions, and the sum of local `|F|^2` integrals is bounded by
`9 sum_{n<=N} Lambda(n)^2`. The model has total cost at most
`N sum_{Q<=q<2Q} mu(q)^2/phi(q) = O(N)`. This independently establishes the
entire main second-moment step without any AP variance assertion.

I also reconstructed the inducing Gauss formula. Insert inclusion-exclusion
only for primes of `q` absent from the conductor `d`. For each resulting
divisor `e`, the sum has modulus `q/e`, a multiple of `d`. Summing over
primitive periods leaves zero unless `q/e=d`. The surviving term is exactly
`mu(q/d) chi*(q/d) tau_d(chi*)`. If `q/d` is not squarefree or is not
coprime to `d`, it vanishes. Thus the proposed conductor factor is correct
even for nonsquarefree `q`, and no universal imprimitive `1/Q` discount
is available for the different AP-variance weights.

For the signed correction, every prime divisor of `q` lies below the new
`Z`, giving `sigma_1(q)/q <= q/phi(q) <= b_Z`. The recorded quantitative
signed estimate is consequently at most `(14/3) N b_Z^4`. Since
`log(2Z) = O(sqrt(log N))`, it is `O(N log^2 N)`. Its proof sums in `h`
for fixed `N`, so changing exceptional data between cutoffs causes no loss
of uniformity. The parameter `beta >= 3/4` holds eventually from the
exceptionality definition; the criterion concerns sufficiently large `N`.

The mean converse uses the exact inequality

\[
 |R(N)|\le \frac{2|B_N|+|A_N|}{N}
 =\sqrt{2M_N/N}+O(\log^2N).
\]

There is no approximate denominator or omitted `R(N)^2` term. This is why
the reduction does not require an unproved smallness assumption on `R`.

For renewal, a direct change of variables gives
`integral_K^N R(N/t) dt = N integral_1^(N/K) R(u) u^(-2) du`.
The right-endpoint sum is over `k=K+1,...,N`; changing it to `k=K,...,N`
would be wrong. Total variation bounds the error with these exact endpoints,
including jumps. Also
`-zeta'(s)/(s zeta(s))-1/(s-1)` tends to `-1-gamma`, not `-gamma`.
Substitution gives precisely the sign of `Q` in (15).

The multiplier can be checked with an explicit remainder. Taking `a=1`
and the source's integer index `K-1` in the
[NIST DLMF Euler summation formula 25.11.5](https://dlmf.nist.gov/25.11.E5)
gives, for `beta=Re(rho)>0`,

\[
 \sum_{k=1}^K k^{-\rho}-\frac{K^{1-\rho}}{1-\rho}
 -\zeta(\rho)
 =\rho\int_{K-1}^{\infty}\frac{\{x\}}{(x+1)^{\rho+1}}dx,
\]

whose modulus is at most `|rho| K^(-beta)/beta`. This proves uniformity
down to `K=1`. The exact source formula and its hypotheses were checked on
2026-09-12. No height-uniform assertion is being made.

The model passes its stated admissibility checks. Its perturbation vanishes
on `[1,2]`, while `1 < exp(gamma) < 2`; above `2` the baseline derivative
is one and the perturbation derivative has modulus at most `1/2`.
Consequently there is no hidden negative segment near the left boundary.
The compact correction has zero weighted integral, and bounded variation
makes its divisor transform equal its linear integral term plus `O(1)`.
The retained `zeta(rho) N^rho` term is essential. At a zero it disappears;
for a generic complex exponent it does not. The resulting all-scale model
therefore gives the stated conditional compatibility result only.

Finally, write `zeta(s)=(s-rho)^m g(s)` with `g(rho) != 0`. Then
`zeta'/zeta = m/(s-rho)+g'/g`, so
`-zeta'/(s zeta)-1/(s-1)` has residue `-m/rho`. Forcing cancellation is
not restored by multiplicity. This is a transform calculation, not a new
zero-location bound.

## 4. Defects, severity, and requested revisions

**Fatal defects in the audited deductions: none found.**

Two ordinary changes should be made before integration:

1. Narrow signed-mean section 11's phrase “Refuted as an inference.” The
   demonstrated conclusion is that the proposed absolute-value induction is
   not justified because its coefficient grows with `K`. The conditional
   off-critical model cannot supply an unconditional counterexample to an
   implication equivalent to RH. Suggested sentence: “The proposed
   absolute-value induction is not justified; its coefficient grows as (19).”
2. Section 10's present-tense statement that the environment lacks `mpmath`
   is stale. Say the original diagnostic used only the standard library.
   That preserves what the computation actually did without making a claim
   about later environment state.

The Farey small-`N` concern is already fixed: the reviewed draft says
`N >= 16`. At `N=3,q=1`, the parameter interval could exceed one period,
so the literal “bounded by one full-circle integral” line would need an
extra multiplicity constant. This does not affect the present statement.

Appendix B correctly identifies that the displayed residue coefficient has
size `1/|Im rho|`, not `1/|Im rho|^2`. It safely withdraws the proposed
absolute-convergence argument without re-opening the separately settled
Mellin-pole theorem. No broader conclusion about possible truncated explicit
formulas follows from this correction.

## 5. Fresh bounded checks

Command:

```text
.venv/bin/python hunts/prime_pair_error/frontier_review_checks.py
```

Raw result: `frontier_review_checks.json`.
Source: `frontier_review_checks.py`.
The run took under one second. Character values came from python-flint and
were deliberately converted to floating point; other calculations used
45-digit mpmath arithmetic. These are non-enclosing diagnostics.

| Fresh check | Coverage | Maximum observed defect or ratio |
|---|---|---:|
| Inducing Gauss identity | All 180 characters for `1 <= q <= 24`, including 8 noncoprime inducing repetitions | `1.78e-15` |
| Reduced-numerator diagonalization | Arbitrary complex coefficients, `1 <= q <= 24` | `2.28e-12` |
| Gauss square-mass identity | `1 <= q <= 24` | `5.69e-14` |
| Divisor identity | `N=2,...,20,63,64,65` | `2.25e-44` |
| Exact renewal | All 401 pairs `1 <= K <= N` at those cutoffs | `5.05e-44` |
| Quadrature magnitude / displayed variation bound | Same 401 pairs | `0.263` |
| Exact mode algebra | `rho=0.75+2i`, every `K`, `N=16,17,64,65` | `3.34e-44` |
| Smooth model integral normalization | Same fixed exponent | `4.38e-47` |

Two deliberate faults discriminated the conventions: replacing `-1-gamma`
by `-gamma` gave exactly `N` error; changing `[1,2)` to `[1,2]` gave a
nonzero error of about `0.9923` at even cutoffs. The fixed exponent has
`|zeta(rho)|` about `0.6181`, so it checks retention of the nonzero leading
multiplier. No zero was searched, constructed, or numerically assumed.
These checks do not prove any asymptotic estimate, zero claim, or RH.

## 6. Exact remaining gap and cheapest useful next step

With `K=floor(sqrt N)`, the proven identity is
`R(N)=D_N+O(sqrt N)`. Thus the missing RH-scale statement is exactly
`|D_N|=O_epsilon(N^(1/2+epsilon))` for every positive epsilon. The integral
in `D_N` reaches beyond `N`, and the absolute-value coefficient grows.
Neither a smaller quadrature constant nor a different fixed split supplies
that missing estimate.

The cheapest next action is to integrate the surviving statements with the
two scope edits above and retain this specific unresolved inequality. A
further numerical sweep is not needed to validate the written algebra and
would not address the gap. Any future claimed inverse estimate must add
arithmetic information strong enough to handle the `zeta` multiplier or
prove why a particular use of exact forcing has that strength.

## 7. Separately requested narrow parameter check

After completing the main audit, the parent requested a logical check of
proposed repairs to `MAJOR_ARC_EXPLICIT.md`, section 5. This note checks only
the following window and Page-matching implications. It is not a re-audit
or acceptance of that document's old full upper bound, conditional lower
bound, phase estimates, source explicit formula, or parity extension.

The proposed extra guards

\[
 0<\varepsilon<\kappa,\qquad \kappa+\varepsilon<1/4,
\]

together with the existing strict conditions

\[
 c_0<\kappa,\quad
 \kappa+3\varepsilon<\min(\sqrt c,\sqrt b),\quad
 \kappa+3\varepsilon<1/3,
\]

are sufficient for the particular error comparisons identified by the
parent. The original `kappa+3 epsilon < 1/3` alone does not imply
`2 kappa+2 epsilon < 1/2`: for example, `kappa=.27, epsilon=.01`
satisfy the former and violate the latter.

For the quadratic remainder, the displayed principal amplitudes give

\[
 \frac{|W|^2}{|H W|}\asymp \frac{|W|}{|H|}
 \ll \sqrt{\widetilde q}\,e^{-\kappa\sqrt\ell}
 \le e^{(\varepsilon/2-\kappa)\sqrt\ell}=o(1).
\]

Thus `epsilon < kappa` is more than sufficient. For the integrated model
subtraction, the required comparison is
`kappa+epsilon < c_m`; the inherited `c_m=1/4-o(1)` makes the new strict
guard `kappa+epsilon < 1/4` sufficient eventually. Strictness matters.

Let `A=kappa+3 epsilon`. The existing condition `A<min(sqrt(c),sqrt(b))`
implies `c/A>A>kappa+epsilon` and `b/A>A>kappa+epsilon`.
Consequently adding the separately Page-limited real-zero error parallel
to the `c`-controlled error preserves negligibility. Page uniqueness does
not imply that every other zero satisfies the individual zero-free-region
bound: a possible real zero can fail the latter while lying outside the
Page region. It must be bounded by Page separately.

The TT-exceptional coexistence argument can be replaced by exclusion.
If `q_e` divides `qtilde`, both primitive conductors are at most `qtilde`.
The proposed zero `betatilde` lies inside the Page region with
`Q=qtilde` and the chosen `T`. Since `beta_e > 1-c_0/sqrt(ell) > betatilde`,
the TT zero lies inside it too and is distinct. This contradicts the
stated Page uniqueness. Thus the offending TT term is absent in this
case; its unsupported relative `o(1)` estimate is unnecessary.

One further ordinary notation repair is needed when these estimates are
written. With `T=qtilde^2 exp(kappa sqrt(ell)) ell^4`, one has
`log(3 qtilde T) <= A sqrt(ell)+4 log(ell)+O(1)`. Therefore the asserted
decay coefficient `c/A` is only `c/A+o(1)` at the displayed level; the same
holds for `b/A`. Use an explicit `1+o(1)` in the exponent or choose a fixed
slightly smaller coefficient. A fixed `ell^2` prefactor need not absorb the
entire denominator correction. The strict margins above make this repair
harmless for the comparisons under review.

The repaired guards leave a nonempty window with `kappa` just above `c_0`
and sufficiently small positive `epsilon` under the parent's stated
`c_0 <= 1/12` and the existing bounds `c_0 <= sqrt(c)/2,sqrt(b)/2`.

## Integration note from the coordinator

The two requested wording edits were applied. The Farey proof is integrated
as `FAREY_BASELINE_REPAIR.md`; the signed proof as `SIGNED_MEAN_RENEWAL.md`.
Inline mathematics was formatted, source attribution clarified, and the
author's finite diagnostic table replaced by a pointer to this independent
check. No mathematical claim in sections 1–9 was strengthened. The script's
source paths now use those two canonical filenames; rerunning it records
the integrated source hashes in `frontier_review_checks.json`.

The narrow section-5 guards, Page exclusion and exponential slack described
in section 7 were applied to `MAJOR_ARC_EXPLICIT.md`. Its corollary first
weakens any larger asserted exponent to one sufficiently close to the
threshold, so the chosen midpoint satisfies the new guards. The parity
extension retains its existing unreviewed status.
