# Independent referee report on Part 3

*Editorial note, 2026-09-06: the absolute path of the reviewer's worktree was replaced
with "an isolated local worktree" to satisfy `tests/test_repo_hygiene.py`, which bars
machine-local paths from tracked files. Nothing else in this report was altered; no
finding, verdict or quoted text is affected.*

Reviewed on 2026-09-06 against author commit
`37c2a53a` in an isolated local worktree, including the complete
Sections 14 to 19 of `RESULTS.md`, all of `wronskian.py`,
`results_wronskian.json`, and `tests/test_prime_pair_residue.py`. PR #186 is
merge `561446e0`; Part 3 was a subsequent local commit, later pushed as PR #188.
The audit was performed with main through `de1ea66` incorporated in an isolated
worktree. Earlier numerical records are preserved.
The conclusions below are judgments of written proofs, not formal verification
or evidence inferred from finite numerical agreement.

## Verdicts

| Claim | Verdict | Required qualification or repair |
|---|---|---|
| A: `W(N) << N^(Theta + Theta_chi) log^4 N` | **Proof valid after specified repair.** | State the endpoint convention and local logarithmic-derivative lemma correctly; expand the uniform Perron remainder as below. The exponent and four logarithms survive. |
| A's consequence under the two RH assumptions | **Proof verified**, using repaired A. | RH is required for both zeta and the primitive character modulo 3. No converse for `(T)` is proved. |
| B: `E(N) = Omega(N^(1 + 2 Theta_chi - epsilon))` | **Proof verified.** | The actual committed proof already has the necessary case split. Its sequence and supremum arguments are made explicit below. |
| `H_chi(N) = c_H N + O(N^(3/4))` and auxiliary `= -c_H N + o(N)` | **Proof valid after specified repair.** | Include the growth of the second L-factor in the contour estimate, distinguish the two signs, and label finite products as approximations. |
| `(T)` is as hard as the two RH statements | **Proof has a specific unresolved gap.** | The first unsupported implication is `(T) =>` the two RH statements. No cited sum-side converse supplies it. Delete the equivalence claim. |
| `O(N)` is best possible for `T-I` | **Proof has a specific unresolved gap.** | The first unsupported step rules out cancellation of the linear auxiliary term by `W`. No result here does so. Delete the optimality claim. |

No mathematical refutation of A or B was found. There is no outstanding
double-zero summation lemma needed for their stated bounds after the details
below are supplied. Simplicity, distinct ordinates, zero spacing, an attained
supremum, and a global zero-free strip are not assumptions of these proofs.

## 1. The exact reduction and endpoints

Use the notation of Part 3, with right-continuous `psi` and `P`, and integer
`N >= 2`. The four reduced residue cases give (E0). Expanding the two class
prefix sums and using the finite summation-by-parts identity gives (E1),
including `(N-1)/2`. Separating pairs incident to a power of 3 gives (E2).
Subtracting the singular-series sum gives (E3). Applying the discrete product
rule to `R(n)P(n)` gives (E4), including its displayed `Q`.

In particular,

```
W = RP/2 - J + Q,             Q = O(N log N),
T - I = RP/2 - J + O(N log N).
```

These are finite identities plus an elementary bound. There is no
interchange of infinite sums in the reduction. For example the exact
left-endpoint symmetric identity is

```
sum [P(n-1) dR(n) + R(n-1) dP(n)]
    = R(N)P(N) - sum Lambda(n)^2 chi(n) + P(N).
```

The explanatory symmetric identity in the submitted Section 16 omitted
the last `P(N)`. Its omission does not affect the correctly implemented (E4).

Write `ell = log(2N)`. Montgomery and Vaughan's **Theorem 12.5**, including
its proof on pp. 400 to 401, gives the truncated formula for the midpoint
function `psi_mid`, with remainder

```
O(log x min(1, x/(U <x>)) + (x/U) log^2(xU)),
```

where `<x>` is the distance to the nearest *other* prime power. At an integer
`m`, `psi(m) = psi_mid(m) + Lambda(m)/2`. Consequently, with the first height
`U=N`, uniformly for `2 <= m <= N`,

```
R(m) = -sum_{|gamma|<=N} m^rho/rho
       + O((m/N) ell^2 + log(2m)).                         (R1)
```

The constant and trivial-zero terms in that theorem are bounded for `m>=2`.
It applies to arbitrary heights: its proof chooses a nearby good height and
then removes the additional zeros, at cost `O(m log U/U)`. Thus a zero with
ordinate exactly `N` is not an unaddressed contour pole. The endpoint half
jump is explicitly included above.

Multiplying (R1) by `Lambda(m)chi(m)` and summing gives

```
J(N) = -sum_{|gamma|<=N} A_rho(N)/rho + O(N ell^2),
A_rho(N) = sum_{m<=N} Lambda(m)chi(m)m^rho.                 (R2)
```

Indeed, `sum m Lambda(m) <= N psi(N) << N^2` and
`sum Lambda(m)log(2m) << N ell`. This checks all prime-power endpoints,
including `m=N`. All sums exchanged here are finite.

The same book's **Theorem 12.10**, for the fixed primitive odd character,
gives `P(N) << N^Theta_chi ell^2`; (R1) gives
`R(N) << N^Theta ell^2`. Thus `RP << N^(Theta+Theta_chi) ell^4`.
[Source: explicit-formula chapter, theorems and proofs.](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/16.0_pp_397_418_Explicit_formulae.pdf)

## 2. Perron with the moving weight

Fix a zeta zero `rho=beta+i gamma`, `|gamma|<=N`, and set
`c=1+beta+1/log N`. The absolutely convergent Dirichlet series on this line is
`-L'/L(w-rho,chi)`. Choose `V_rho` in `[2N,2N+1]` such that each of
`V_rho-gamma` and `-V_rho-gamma` is at distance at least `a/ell` from every
L-zero ordinate, with a fixed sufficiently small `a>0`. Only `O(ell)` zeros
can exclude portions of this unit interval; their excluded lengths total
less than one. Both shifted heights have absolute value at least `N`.

The bound in **Corollary 5.3** must be applied to all coefficients, including
those with `m>N`. On `N/2<m<2N`, `|a_m| <= (2N)^beta log(2N)`; hence its
near-endpoint sum, with `m=N` excluded, is at most

```
C N^beta ell sum_{1<=h<=N} min(1, N/(V_rho h))
    << N^beta ell^2.
```

Its remaining term is at most

```
C (1+N^c)/V_rho sum_{m>=1} Lambda(m)m^(beta-c)
    << N^beta ell,
```

since `beta-c=-1-1/log N`. Perron returns the half-weighted endpoint;
restoring the full `m=N` term costs `O(N^beta ell)`. These estimates are
uniform in `beta` and `gamma`; taking absolute values of `m^(i gamma)`
costs nothing. This supplies the calculation compressed in submitted Step 2.
Partial summation against a pointwise error for `P` would introduce a factor
`|rho|` and would not justify the claimed uniform remainder.
[Source: Corollary 5.3 and its preceding endpoint convention.](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/09.0_pp_137_167_Dirichlet_series_II.pdf)

Shift this finite contour to `Re w=-delta`, where `delta` is either `1/8`
or `3/16`, chosen with `|beta+delta-1|>=1/40`. The two forbidden intervals
are disjoint. The crossed poles and their contributions are exactly

```
w=rho+rho':   -N^(rho+rho')/(rho+rho'), |gamma+gamma'|<V_rho;
w=0:         -L'/L(-rho,chi);
w=rho-1:     -N^(rho-1)/(rho-1), if beta>1-delta.
```

Multiplicity is included. There is no principal-character pole. No pole
coalesces with `w=0`, since the nontrivial-zero real parts are positive and
zeta has no real zero in `(0,1)`.

The submitted (F3) needs a qualification: a local expansion using only
nontrivial zeros is not uniformly bounded near a trivial zero. For example
`L'/L(s,chi_3)` has a pole at `s=-1`. Use that expansion at large `|Im s|`,
and keep the trivial poles explicitly or stay a fixed distance from them at
bounded height. The finite contour just chosen does stay that distance away.
The book's printed Lemma 12.6 also needs this bounded-height qualification
if its summation is understood to include only nontrivial zeros.

On the horizontal sides the local expansion gives `O(ell^2)`, because
there are `O(ell)` nearby zeros and each denominator is at least `a/ell`.
The functional equation gives the same or better bound further left. Their
combined integral is

```
O(ell^2/V_rho integral_{-delta}^c N^sigma d sigma)
    = O(N^beta ell).
```

On the vertical side the real-part separation from all nontrivial zeros is
at least `delta`; the chosen separation from the trivial zero deals with
bounded heights. Thus the logarithmic derivative is `O(ell)` and this side
contributes `O(N^(-delta) ell^2)`. The classical zeta zero-free region and
reflection give `beta >> 1/ell`. Applying the local expansion at `-rho`
therefore bounds its residue by `O(ell^2)`. The possible trivial residue is
`O(N^(beta-1)/|gamma|)`; the finitely many low zeta zeros cause no problem.
We obtain, uniformly,

```
A_rho(N) = -sum_{rho' in D_rho} N^(rho+rho')/(rho+rho')
            + O(N^beta ell^2),
D_rho = {rho': |gamma+gamma'|<V_rho}.                      (R3)
```

The local counts, good-height argument and left-half-plane estimates are
the elementary contour tools in Montgomery and Vaughan, Lemmas 12.6 to
12.9, with the qualification just stated. No Goldbach theorem supplies (R3).

## 3. The double-zero kernel, including opposite ordinates

Here is the actual kernel for the quantity requested in the review, rather
than just for `J`. For each fixed `rho`, apply Perron to `-L'/L(z,chi)` with
the asymmetric heights `-V_rho-gamma` and `V_rho-gamma`. They have size
between `N` and `3N+1` and the same good-height separation. The same endpoint
estimate gives

```
P(N) = -sum_{rho' in D_rho} N^rho'/rho' + O(ell^2).        (R4)
```

For completeness, the asymmetric Perron tails for `m!=N` are bounded by
the sum of the two endpoint estimates `C(N/m)^c/(N|log(N/m)|)`.
At `m=N` the integral need not give exactly one half: the unequal heights
can also give a bounded imaginary part. Its entire discrepancy from the
full endpoint is `O(Lambda(N))`, included in `O(ell^2)`. The contour can
be shifted to `Re z=-1/4`; its sole extra residue is the fixed value
`-L'/L(0,chi)`, and its vertical integral is `O(N^(-1/4)ell^2)`.

Using the same `D_rho` in (R3) and (R4), and (R1) at `N`, gives

```
J - RP/2 = sum_{|gamma|<=N} sum_{rho' in D_rho}
             N^(rho+rho') K(rho,rho')
           + O(N ell^2 + N^Theta ell^4 + N^Theta_chi ell^4),

K(rho,rho') = 1/[rho(rho+rho')] - 1/(2rho rho')
            = (rho'-rho)/[2rho rho'(rho+rho')].             (R5)
```

The three errors come respectively from insertion in `J`, the weighted
Perron remainders and (R4), and multiplication of the remainder in (R1)
by `P(N)`. In particular no rectangular cutoff or independent infinite
limit was silently substituted for the slanted sets `D_rho`.

For fixed `rho`, every `rho'` in `D_rho` has `|gamma'|<=3N+1`. Divide them
into the two unit intervals with `j<=|gamma+gamma'|<j+1`. Each bin contains
`O(ell)` zeros, with multiplicity. For `j>=1` its contribution to
`sum 1/|rho+rho'|` is `O(ell/j)`. For `j=0`, even when the ordinates are
exact opposites,

```
|rho+rho'| >= beta+beta' >= beta >> 1/ell.
```

Thus the central bin is `O(ell^2)` and all other bins total
`O(ell sum_{j<=2N+1} 1/j)=O(ell^2)`. Separately, unit-interval counting gives
`sum_{|gamma|<=N} 1/|rho| << ell^2` and
`sum_{|gamma'|<=3N+1} 1/|rho'| << ell^2`.
Possible low zeros of either fixed function contribute constants.
Consequently

```
sum_{|gamma|<=N} sum_{rho' in D_rho} |K(rho,rho')|
 <= sum 1/(|rho| |rho+rho'|) + (1/2) sum 1/(|rho| |rho'|)
 << ell^4.                                               (R6)
```

Since `beta<=Theta`, `beta'<=Theta_chi`, every numerator has modulus at
most `N^(Theta+Theta_chi)`. The errors in (R5) are absorbed because
`Theta,Theta_chi>=1/2`. Equations (R5), (R6), (E3) and (E4) prove A with
its stated exponent and logarithmic power. There is **no epsilon loss**.
An unattained supremum is still an upper bound on each real part.

This is a finite, growing-height estimate. It neither asserts absolute
convergence of an infinite double sum nor uses an exchange of its limits.
Under the two RH assumptions `beta+beta'=1`; the central bin is then even
easier. Excluding common or opposite ordinates is unnecessary. The submitted
sentence asserting that the double sum has no nonoscillating term must be
qualified: absence of opposite ordinates is not established here.

## 4. The unconditional transfer in B

The original committed Section 18 already separates `Theta_chi<=Theta`
from `Theta<Theta_chi`. It does **not** assume `Theta<1` in the first case.

In the first case use CHHL Theorem 2 directly, with the requested epsilon.
Its exponent is at least the desired one, even if `Theta=1`. In its proof,
the unweighted sum is `R(N)(2N+R(N))+O(N log N)`, and PNT gives
`R(N)/N -> 0`; no uniform zero-free strip is needed.
[CHHL, Theorem 2 and Section 3.](https://arxiv.org/pdf/2308.14888)

In the second case put `B=Theta_chi`; now `Theta<B<=1` really implies
`Theta<1`. For real `x>=1`, finite summation gives

```
I(x) = sum_{m<=x} Lambda(m)chi(m)(x/2-m).
```

For `Re s>1`, absolute convergence permits termwise integration:
the sum of the absolute integrals is bounded by a constant depending on
`Re s` times `sum Lambda(m)m^(-Re s)`. Direct integration yields

```
integral_1^infinity I(x)x^(-s-2) dx
   = -(L'/L)(s,chi) (1-s)/(2s(s+1)).                     (R7)
```

At a zero `rho'` of multiplicity `h`, this meromorphic function has residue
`h(rho'-1)/(2rho'(rho'+1))`, which is nonzero: `0<Re rho'<1`.
There are no coefficients from another L-function to cancel that pole.

Fix `epsilon>0` and choose

```
eta = min(epsilon, 1-Theta)/2 > 0,
alpha = 1+B-eta > 1,
d = alpha-(Theta+B) = 1-Theta-eta >= (1-Theta)/2 > 0.
```

By the definition of supremum there is a zero with `Re rho'>B-eta`,
regardless of whether a rightmost zero exists. If `I(x)=O(x^alpha)`,
the left side of (R7) is holomorphic throughout `Re s>B-eta`, contradicting
this nonzero pole by analytic continuation from `Re s>1`.
Thus `I` is not `O(x^alpha)`. This argument only proves an absolute-value
oscillation, and does not assert `Omega_+` or `Omega_-` separately.

For `N<=x<N+1` the exact identity is
`I(x)-I(N)=(x-N)P(N)/2=O(N)`, by Chebyshev. Since `alpha>1`,
an `O(N^alpha)` bound on integers would imply the contradicted real bound.
Therefore the ratio `|I(N)|/N^alpha` is unbounded on the integers. In
particular there is an unbounded sequence with `|I(N)|>=N^alpha`.

On that sequence A gives
`|T-I|/N^alpha << N^(-d)ell^4 -> 0`. For all sufficiently large members,
`|T(N)| >= N^alpha/2`. Finally

```
T(N)^2 <= (sum_{k<=N} chi(k)^2) E(N)/2 <= N E(N)/2,
E(N) >= N^(2alpha-1)/2 >= N^(1+2B-epsilon)/2.
```

This is an **Omega bound along an unbounded sequence**, not an eventual
lower bound for every integer. The sequence and thresholds may depend on
epsilon. This also completes the transfer when `B=1` but `Theta<1`.

## 5. The auxiliary constant

The divisor expansion must include `1[2|k]`:
`S(k)=2C2 1[2|k] sum_{d|k, d odd squarefree} g(d)`.
Finite interchange with the triangular weight gives the submitted formula
for `H`. Its Dirichlet series, initially absolutely convergent for `Re s>1`, is

```
D(s) = -2^(1-s) C2 L(s,chi)L(1+s,chi)K(s),
K(s) = (1+2^(-1-s))
       product_{p>3} (1+chi(p)/((p-2)p^s))(1-chi(p)/p^(1+s)).
```

The local errors from 1 are `O(p^(-2-Re s)+p^(-2-2Re s))`, so the product
converges absolutely and locally uniformly for `Re s>-1/2`.
The Riesz integral `D(s)N^(s+1)/(s(s+1))` therefore shifts to `Re s=-1/4`,
crossing only the pole of its kernel at zero. The submitted proof bounded
only the first L-factor. The missing bound is

```
L(-1/4+it,chi) << (1+|t|)^(3/4),
L(3/4+it,chi) <<_nu (1+|t|)^(1/8+nu),   0<nu<1/8.
```

The functional equation and convexity give these estimates. Hence the
integrand on the new vertical line is
`O_nu(N^(3/4)(1+|t|)^(-9/8+nu))`, which is integrable. The horizontal
integrals vanish as their height grows, for each fixed `N`, by the same
bounds uniformly across the strip. This proves the claimed
`H=c_H N+O(N^(3/4))`. The extra `nu` concerns height growth only and does
not become an epsilon loss in the power of `N`.

Using `L(0,chi)=1/3` gives

```
c_H = -(2C2/3) product_{p>3}(1+chi(p)/(p-2)) < 0.
```

The prime-ordered product converges by PNT in the two classes, or by
factoring out `L(1,chi)`. The fixed-character PNT also gives, for some `c>0`,

```
P(N)/2 + X_chi(N) = O(N log N exp(-c sqrt(log N))) = o(N).
```

To bound the exceptional sum uniformly, split its arguments below `sqrt N`
and above it; apply Chebyshev to the former and PNT to the latter, reducing
`c` if needed. The individual bracket in (E2) is bounded by *three*, not
two, times `max_{x<=N}|P(x)|`. Thus the auxiliary coefficient is **`-c_H>0`**.

The independent recomputation at the existing cutoff `N=200000` used a
separate integer factor sieve, enumeration of prime powers, and mpmath at
40 decimal digits, without importing `probe`, `residue`, or `wronskian`:

| Quantity divided by N | Independent value |
|---|---:|
| `H_chi` | `-0.3131254443203751984` |
| `P/2` | `+0.0011345887547197570` |
| `X_chi` | `+0.0289017020741249601` |
| `P/2 + X_chi - H_chi` | `+0.3431617351492199154` |

The last three entries explain the spot-check discrepancy exactly. They
agree with the existing JSON at its floating precision. In that JSON,
`G_infinity` and `c_H` were evaluated with primes only through 2000000:
the independently reproduced latter value is `-0.3130624168166045`.
Neither field is an exact limit or comes with a tail estimate.

There is also an absolutely convergent way to check the limiting constant.
Since `L(1,chi)=pi/(3 sqrt(3))`, multiplying the Euler factors gives

```
c_H = -pi/(4 sqrt(3)) product_{p>3, p=2 mod 3}(1-4/(p-1)^2).                (R8)
```

For primes `p=1 mod 3` the factors cancel exactly. At the *same* existing
prime cutoff 2000000, (R8) gives `-0.3130478575251646`. If `c_cut` denotes
this truncated value, positivity of all factors and the elementary bound
`1-product(1-a_p) <= sum a_p` give

```
c_cut <= c_H <= c_cut + |c_cut| 4/(2000000-1).
```

The mathematical tail allowance is less than `0.000000626097`; a conservative
numerical interval is `-0.313047858 < c_H < -0.313047231`.
The displayed decimals are high-precision numerical evaluations, not
outward-rounded machine enclosures. This places the magnitude near `0.31305`;
the original `0.3131` was a coarse approximation. No historical JSON value
is overwritten. The asymptotic is established by the contour argument,
not by agreement at these cutoffs.

Neither that asymptotic nor the five values of `W/N` excludes
`W=c_H N+o(N)`. Therefore the asserted optimality of `O(N)` for `T-I`
does not follow and is withdrawn.

## 6. Literature, originality, and relevance

The sources actually needed for A are the classical explicit formulas,
Perron with remainder, local zero counting, the functional equation and
the classical zero-free region. Those have been checked in Montgomery and
Vaughan's author-hosted chapters, not inferred from citations to a Goldbach
paper. B additionally uses CHHL's Theorem 2; its full proof in Section 3
was checked. CHHL appeared online in 2025; the journal citation is
*Journal of Number Theory* **278 (2026), 422 to 450**.
[Publisher record.](https://www.sciencedirect.com/science/article/pii/S0022314X25001453)

BHMS Theorem 1(1) concerns a sum-side counting function with error
`x^(1+B_q)` after subtracting only its smooth leading term. Its Theorem 2
subtracts the single-zero terms too and has error `x^(2B_q^*)log^5(qx)`.
The second is the closer structural comparison to A, which has already
removed `I`. Neither theorem proves this difference-side kernel estimate.
Their Theorem 1(2) uses DZC and nonvanishing character coefficients and
retains a `B_q=1` alternative unless `a=b`. Their Theorem 3(2) instead
requires an **attained** rightmost zero belonging to a unique character,
with squarefree conductor coprime to the target residue. These hypotheses
cannot be compressed to just DZC or transferred to `(T)`.
[BHMS, precise theorem statements and preliminary lemmas.](https://arxiv.org/pdf/1704.06103)

Languasco and Zaccagnini's 2012 Theorems 1 and 2 and their proofs concern
sum-side averages and exponential weighting. Their `N log^3 N` estimate
is on RH and is not an estimate for `J`.
[Theorems, lemmas, and proof.](https://arxiv.org/pdf/1011.3198)
Goldston and Yang's Theorems 1 and 2 concern the same sum-side average and
its order-one Cesaro version. Their proof uses averaged mean-square bounds
for the prime-counting remainder. The arithmetic constraint and the
Gamma-factor double-zero kernels in these papers differ from (R5).
[Goldston and Yang, including Section 7.](https://arxiv.org/pdf/1601.06902)

There is a further concrete citation correction: Languasco and Zaccagnini's
2015 Theorem 1 proves the Cesaro formula for `k>1`. The threshold `k>1/2`
is only for absolute convergence of its double series. The authors explicitly
distinguish these in the paragraph following the theorem; the submitted
Section 19 conflated them. Goldston and Yang's displayed (2.1) also omits the
factor 2 on its single-zero term; their (1.4), Lemma 2 and proof retain it,
as does Languasco and Zaccagnini's 2012 Theorem 1. Neither display is used
to import an unproved identity into this review.
[Cesaro theorem and its stated limitation.](https://arxiv.org/pdf/1206.0251)

The historical survey is useful context, not additional proof of A or a
converse. A conditional implication cannot establish an equivalence. This
review makes no novelty claim: the named papers and targeted searches for
the character-weighted prime-difference statistic did not identify a prior
statement of A or B, but that search is not exhaustive. The derivation's
provenance in this hunt and priority in the literature are separate matters.

The relevance is a lower-bound obstruction for `E`, not a new upper bound
on `E` and not evidence for RH. These distinctions do not diminish the
valid finite identities, numerical record, or the repaired analytic bounds.

## 7. Strongest surviving statement and disposition

For the primitive real nonprincipal character modulo 3, with `Theta` and
`Theta_chi` the zero-real-part suprema and `N` tending through the positive
integers, the repaired proof gives unconditionally

```
W(N), T(N)-I(N) = O(N^(Theta+Theta_chi) log^4 N),
E(N) = Omega(N^(1+2 max(Theta,Theta_chi)-epsilon)) for every epsilon>0.
```

Here the first line bounds each quantity separately; the second is along
an unbounded sequence. Under RH for **both** functions the first line
specializes to `T(N)=I(N)+O(N log^4 N)`. CHHL's unconditional
`Omega(N^2 (log log log N)^2)` remains an additional surviving bound.

Recommendation: retain A and B with the repairs and qualifications above;
retain the numerical results unchanged; remove the unproved equivalence,
optimality, and noncoincidence assertions. This is a completed independent
written-proof audit, not an external mathematical endorsement or a
kernel-checked result. No new experiment or modulus expansion is proposed.

## Validation record

The 27 tests in `tests/test_prime_pair_residue.py` pass, including the four
new assertions against independently recomputed values at the existing cutoff.
Fourteen document-numbering, door and static hunt-discipline checks also pass.
`scripts/make_context.py --check` reports the generated index current;
`git diff --check` passes. `results.json`, `results_residue.json` and
`results_wronskian.json` are byte-for-byte unchanged from the author's commit.
The arithmetic backend check reports `python-flint` with both backends available.

The broader fast baseline run terminated with SIGTERM (exit 143) before
completion. Its partial progress included a failure marker but no completed
failure report. A separate broader hunt check was also terminated. This is
not a green whole-repository baseline; no unrelated repair was attempted.
The numerical checks establish the reported finite evaluations and identities,
not the zero-sum estimates or the asymptotic assertions.
