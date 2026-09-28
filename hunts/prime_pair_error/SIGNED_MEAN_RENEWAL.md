# Signed mean and the divisor renewal

Base: `zeta-lab` commit `3b0fc2e3c97b46cc1fde6af0ff3dd856898d95fb`.
Date: 2026-09-12. Handwritten derivations for independent review; no novelty
claim. Review status is recorded in `FRONTIER_INDEPENDENT_REVIEW.md`.

The objects below retain the original sharp endpoints, all prime powers, the
infinite singular series, and the exact exceptional correction. This argument
does not estimate the full corrected energy by a new method.

## 1. Inputs and the scalar target

For integers \(N\ge2\), write
\[
 \psi_2(N,h)=\sum_{n=1}^{N-h}\Lambda(n)\Lambda(n+h),\qquad
 r_N(h)=\psi_2(N,h)-(N-h)\mathfrak S(h),
\]
where \(1\le h\le N\), and put
\[
 B_N=\sum_{h=1}^N(r_N(h)-C_N(h)),\qquad
 M_N=\frac{2|B_N|^2}{N},\qquad R(x)=\psi(x)-x\quad(x\ge1).
\]

Use \(Z=\exp(\sqrt{\log N})\) here. The exact correction \(C_N\) is
the one in `CORRECTED_RH_BRIDGE.md`, equation (5), with this \(Z\).
Its exceptional conductor, character, zero, and presence may change at every
integer \(N\). If there are no applicable exceptional data, \(C_N=0\).
The signed bound in that document is uniform in those data and is proved
before specializing \(Z\):
\[
 \left|\sum_{h\le N}C_N(h)\right|
 \ll N(\log(2Z))^4\ll N(\log N)^2.                 \tag{1}
\]
Indeed its displayed quantitative bound uses only \(\beta\ge3/4\),

\[
 (q/\phi(q))^2b_Z
 \left[\tfrac83 1_{q\text{ odd}}N^\beta
             +2\frac{\sigma_1(q)}q N^{2\beta-1}\right],
\]

and \(\sigma_1(q)/q\le q/\phi(q)\le b_Z\ll\log(2Z)\).
The odd, 4-part, and 8-part cases were all included in that proof. Source
exceptionality gives \(\beta\ge3/4\) for all sufficiently large \(N\).
Nothing here assumes the correction is the same at two different cutoffs.

The inherited first-moment inputs are
\[
 d_N:=\sum_{n\le N}\Lambda(n)^2=O(N\log N),\qquad
 S_N:=2\sum_{h\le N}(N-h)\mathfrak S(h)=N^2+O(N\log N). \tag{2}
\]
The singular-series mean is the CHHL input already used in
`CORRECTED_RH_BRIDGE.md`; the diagonal bound also follows from Chebyshev
and \(\Lambda(n)\le\log N\).
The exact pair identity is
\[
 \psi(N)^2=d_N+2\sum_{h\le N}\psi_2(N,h).             \tag{3}
\]
It follows by partitioning ordered pairs of integers at most \(N\) into
equal pairs and the two orientations of each distinct pair. Thus it retains
every proper prime power and the diagonal.

Define the explicit remainder
\[
 A_N=d_N+S_N-N^2+2\sum_{h\le N}C_N(h).
\]
Then, exactly,
\[
 2B_N=\psi(N)^2-N^2-A_N,
 \qquad
 B_N=NR(N)+\tfrac12R(N)^2-\tfrac12A_N,               \tag{4}
\]
and (1)-(2) imply \(A_N=O(N\log^2N)\), uniformly in the changing
exceptional data.

## 2. Two-way mean criterion

The exact equivalence is
\[
 \boxed{\quad
 \mathrm{RH}\quad\Longleftrightarrow\quad
 (\forall\epsilon>0)\ M_N\ll_\epsilon N^{2+\epsilon}
 \text{ for all sufficiently large integers }N.
 \quad}                                                        \tag{5}
\]

For the forward direction use the classical RH consequence

\[
 R(x)=O(x^{1/2}\log^2x).
\]

This is the standard von Koch prime-counting formulation already recorded
in `docs/00-orientation.md`; it is an external classical input, not proved
by the renewal argument below. Equation (4) gives

\[
 B_N=O(N^{3/2}\log^2N),\qquad M_N=O(N^2\log^4N),     \tag{6}
\]

which implies the right side of (5).

Conversely \(\psi(N)\ge0\), so \(\psi(N)+N\ge N\). From (4),

\[
 |R(N)|\le\frac{2|B_N|+|A_N|}{N}
       \le\sqrt{\frac{2M_N}{N}}+O(\log^2N).          \tag{7}
\]

For any \(\theta>0\), apply the hypothesis with \(\epsilon=2\theta\)
to obtain \(R(N)=O_\theta(N^{1/2+\theta})\). For real \(x\ge2\), take
\(N=\lfloor x\rfloor\); then \(\psi(x)=\psi(N)\) and \(x-N<1\).
Thus \(R(x)=O_\theta(x^{1/2+\theta})\) for every \(\theta>0\).

For completeness, on \(\Re s>1\) the Euler product and partial summation
give
\[
 -\frac{\zeta'(s)}{\zeta(s)}-
rac{s}{s-1}
       =s\int_1^\infty R(x)x^{-s-1}\,dx.             \tag{8}
\]
For each \(\theta>0\) the right side is holomorphic on
\(\Re s>1/2+\theta\), by locally uniform absolute convergence.
Consequently the left side has no pole in \(\Re s>1/2\); a zero of
\(\zeta\) there would produce one. The functional equation reflects
nontrivial zeros across \(\Re s=1/2\), proving RH.

This scalar equivalence is a reduction, not progress toward proving its
input. Unlike the full-energy criterion, it is two-way. It does not say
that RH implies a near-quadratic bound for the full corrected energy.

## 3. The exact arithmetic recurrence and its linear forcing

For each positive integer \(m\), unique factorization gives
\[
 \sum_{d\mid m}\Lambda(d)=\log m.
\]
For \(m=\prod_p p^{a_p}\), the left side is
\(\sum_p\sum_{j=1}^{a_p}\log p=\log m\). Summing over \(m\le N\),
and reversing the finite sums, gives the exact sharp-cutoff identities
\[
 \sum_{d\le N}\Lambda(d)\lfloor N/d\rfloor
  =\log(N!)
  =\sum_{k=1}^N\psi(N/k).                            \tag{9}
\]
Subtract \(N H_N\), where \(H_N=\sum_{k\le N}1/k\). Then
\[
 \sum_{k=1}^N R(N/k)=G(N),\qquad
 G(N)=\log(N!)-NH_N.                                 \tag{10}
\]
Stirling's formula and the harmonic-number expansion give
\[
 G(N)=-(1+\gamma)N+\tfrac12\log N
             +\tfrac12\log(2\pi)-\tfrac12+O(N^{-1}). \tag{11}
\]
The error can be sharpened, but that has no bearing on the argument.

The direct recurrence \(R(N)=G(N)-\sum_{k=2}^N R(N/k)\) therefore has
an order-\(N\) forcing term. Merely treating it as \(O(N)\) cannot
yield a fixed power saving. The following step removes that linear term
before testing whether a genuine contraction remains.

## 4. Cancelling the linear term and deriving a scale relation

Use only the inherited unconditional prime-counting estimate

\[
 R(x)\ll x\exp(-c\sqrt{\log x})
\]

for sufficiently large \(x\); the stronger inherited rate is unnecessary.
It guarantees absolute convergence of

\[
 I:=\int_1^\infty\frac{R(u)}{u^2}\,du.
\]

The value is

\[
 I=-(1+\gamma).                                      \tag{12}
\]

Proof: divide (8) by \(s\) and let real \(s\downarrow1\). Dominated
convergence applies to the integral, because \(R(u)/u^2\) is absolutely
integrable. The Laurent expansion
\(\zeta(s)=(s-1)^{-1}+\gamma+O(s-1)\) yields

\[
 -\frac{\zeta'(s)}{s\zeta(s)}-\frac1{s-1}
       =-(1+\gamma)+O(s-1).
\]

Fix integers \(1\le K\le N\), and set \(y=N/K\). Define the *exact*
quadrature error
\[
 Q_{N,K}=\sum_{k=K+1}^N R(N/k)
                -N\int_1^{N/K}\frac{R(u)}{u^2}\,du. \tag{13}
\]
For \(f(t)=R(N/t)\) on ([K,N]), comparison of each right endpoint
with the integral over ([k-1,k]) gives
\[
 |Q_{N,K}|\le\operatorname{Var}_{[K,N]} f
          =\operatorname{Var}_{[1,y]}R
          \le\psi(y)+y\ll N/K.                      \tag{14}
\]
For the equality of variations, composition with the decreasing continuous
bijection \(t\mapsto N/t\) reverses partitions without changing their
variation sums. For the last inequality use \(R=\psi-\mathrm{id}\),
monotonicity of \(\psi\), and the inherited Chebyshev bound
\(\psi(y)\ll y\). Endpoint jumps cause no problem: their contributions
are included in total variation. If \(K=N\), both sides of (13) are zero.

Combining (10), (12), and (13) gives the exact relation
\[
 \boxed{
 \sum_{k=1}^K R(N/k)
      -N\int_{N/K}^\infty\frac{R(u)}{u^2}\,du
   =G(N)+(1+\gamma)N-Q_{N,K}.}                       \tag{15}
\]
Consequently, uniformly for every integer \(1\le K\le N\),
\[
 \boxed{
 \sum_{k=1}^K R(N/k)
      -N\int_{N/K}^\infty\frac{R(u)}{u^2}\,du
       =O(N/K+\log N).}                             \tag{16}
\]

This is an actual scale estimate derived from the arithmetic identity.
At \(K=\lfloor\sqrt N\rfloor\), its forcing is \(O(\sqrt N)\).
It is an estimate for a combination containing (R\(N\)); it is not yet
an estimate for (R\(N\)) itself. Its integral includes \(u>N\), so it
is not a recurrence solely in previously controlled smaller arguments.

## 5. The attempted contraction and its exact missing estimate

Set \(K=\lfloor\sqrt N\rfloor\), and write
\[
 D_N:=N\int_{N/K}^\infty\frac{R(u)}{u^2}\,du
                     -\sum_{k=2}^K R(N/k).
\]
Then (15) proves

\[
 R(N)=D_N+O(\sqrt N).                                \tag{17}
\]

For the RH target the missing arithmetic inequality is exactly

\[
 \boxed{\quad |D_N|\ll_\epsilon N^{1/2+\epsilon}
                      \quad\text{for every }\epsilon>0.\quad}  \tag{18}
\]

A fixed saving \(D_N\ll N^{1-\delta}\), \(0<\delta\le1/2\), would
already yield \(R(N)\ll N^{1-\delta}\),
\(B_N\ll N^{2-\delta}\), and \(M_N\ll N^{3-2\delta}\), by (4).
Neither such a saving nor (18) has been established here.

Taking absolute values does not contract even a *putative* envelope
\(|R(u)|\le A u^\theta\), \(0<\theta<1\). It only gives

\[
 |D_N|\le A N^\theta
  \left(\frac{K^{1-\theta}}{1-\theta}
                     +\sum_{k=2}^K k^{-\theta}\right).         \tag{19}
\]

The coefficient grows as \(2K^{1-\theta}/(1-\theta)\), rather than
being less than one. This is a precise failure of the proposed absolute
value induction, not a theorem that every conceivable signed argument
must fail. The signed test below explains the relevant unresolved modes.

## 6. The transfer multiplier, including all scales

For fixed \(\rho\ne1\) with \(0<\beta:=\Re\rho<1\), define
\(f_\rho(u)=u^\rho\), using the real logarithm for \(u>0\).
Let

\[
 (L_K f)(N):=\sum_{k=1}^K f(N/k)
                   -N\int_{N/K}^\infty f(u)\frac{du}{u^2}.
\]

The integral converges absolutely for \(f=f_\rho\), and direct evaluation
gives the exact formula

\[
 (L_K f_\rho)(N)
       =N^\rho\left(\sum_{k=1}^K k^{-\rho}
                          -\frac{K^{1-\rho}}{1-\rho}\right).  \tag{20}
\]

Euler summation gives, for fixed \(\rho\) in this strip,

\[
 \sum_{k=1}^K k^{-\rho}
       -\frac{K^{1-\rho}}{1-\rho}
       =\zeta(\rho)+O_\rho(K^{-\beta}).              \tag{21}
\]

One proof is to compare \(k^{-\rho}\) on each unit interval with its
integral. The discrepancy series converges absolutely at its derivative
scale, since

\[
 \sum_{k>K}\sup_{t\in[k,k+1]}|\rho t^{-\rho-1}|
                         \ll_\rho K^{-\beta}.
\]

Its limiting function agrees with \(\zeta(s)\) on \(\Re s>1\) after
including the integral term, and therefore gives its analytic continuation
to \(\Re s>0\), \(s\ne1\). This is also the specialization of the
[NIST Euler-Maclaurin representation](https://dlmf.nist.gov/25.11.E5),
with Hurwitz parameter 1 and truncation index \(K-1\). This precise
source formula and its \(\Re s>0\) domain were checked on 2026-09-12.
Thus

\[
 \boxed{\quad
 (L_K f_\rho)(N)=\zeta(\rho)N^\rho
                         +O_\rho((N/K)^\beta).\quad}           \tag{22}
\]

If \(\zeta(\rho)=0\), then for **every** \(1\le K\le N\),

\[
 |(L_K f_\rho)(N)|\ll_\rho (N/K)^\beta\le C_\rho N/K.          \tag{23}
\]

This includes \(K=\sqrt N\) and \(K=N\). Consequently the displayed
error allowance in (16) is compatible with a mode of size \(N^\beta\)
whenever that mode is attached to a zeta zero. A hypothetical
\(\beta>1/2\) is not excluded by making \(N/K\) as small as possible.
For a nonzero value \(\zeta(\rho)\), the leading term in (22) is retained;
an arbitrary off-critical power is **not** claimed to pass all scales.
No off-critical zero is asserted to exist.

## 7. An explicit boundary correction: bounded divisor forcing

The pure mode has the wrong integral in (12). That objection can be
removed explicitly. Define

\[
 F_\rho(u)=u^\rho-\frac{2}{1-\rho}1_{[1,2)}(u)
                  \quad (u\ge1).
\]

Then

\[
 \int_1^\infty F_\rho(u)\frac{du}{u^2}=0,            \tag{24}
\]

because the two terms contribute \(1/(1-\rho)\) and
\(2(1-1/2)/(1-\rho)\). Let \(Tf(x)=\sum_{k\le x}f(x/k)\).
For integer \(N\ge2\), exactly,

\[
 (TF_\rho)(N)=N^\rho\sum_{k=1}^N k^{-\rho}
       -\frac{2}{1-\rho}(N-\lfloor N/2\rfloor).
\]

Equation (21) with \(K=N\) now gives

\[
 (TF_\rho)(N)=\zeta(\rho)N^\rho+O_\rho(1).          \tag{25}
\]

Thus at a zeta zero an unbounded \(N^\beta\) function has bounded
divisor forcing, even with the correct zero integral for a perturbation.
It is an approximate null mode with explicitly identified bounded forcing,
not a nonzero exact solution of \(TF=0\). The latter would be impossible
under a fixed zero boundary convention, by triangular inversion.

## 8. Positivity and monotonicity do not remove the hypothetical mode

The jump in the preceding convenient cutoff is unnecessary. Here is a
model that is nonnegative and nondecreasing, including its small-argument
boundary, and meets the same normalization and every scale bound whenever
\(\zeta(\rho)=0\).

Put \(a=e^\gamma>1\) and define

\[
 \Psi_0(u)=(u-a)_+,\qquad R_0(u)=\Psi_0(u)-u=-\min(u,a).
\]

Then \(\Psi_0(1)=0\), \(\Psi_0\ge0\), \(\Psi_0\) is nondecreasing,
and direct integration gives

\[
 \int_1^\infty R_0(u)\frac{du}{u^2}=-\log a-1=-(1+\gamma).      \tag{26}
\]

Choose the explicit \(C^1\) cutoff

\[
 h(u)=\begin{cases}
 0,&u\le2,\\
 3(u-2)^2-2(u-2)^3,&2<u<3,\\
 1,&u\ge3,
 \end{cases}
\]

and \(b(u)=(u-3)^2(4-u)^2\) for \(3\le u\le4\), zero elsewhere.
Let

\[
 J_\rho=\int_1^\infty h(u)u^{\rho-2}\,du,\qquad
 J_b=\int_3^4b(u)u^{-2}\,du>0,
\]

and define

\[
 \widetilde F_\rho(u)=h(u)u^\rho-(J_\rho/J_b)b(u).
\]

This function is \(C^1\), vanishes for \(u\le2\), equals \(u^\rho\)
for \(u\ge4\), and has integral zero against \(u^{-2}du\). Its
derivative has finite supremum: it is bounded on the compact transition
region and has magnitude \(|\rho|u^{\beta-1}\) afterwards. Define

\[
 D_\rho=\max(1,\sup_{u\ge1}|\widetilde F_\rho'(u)|),\qquad
 0<|\eta|\le(2D_\rho)^{-1},
\]

with \(\eta\) real, and put

\[
 \Psi_\eta(u)=\Psi_0(u)+\eta\Re\widetilde F_\rho(u),\qquad
 R_\eta(u)=\Psi_\eta(u)-u.
\]

On \(u\le2\) this equals the nonnegative increasing baseline. On
\(u>2>a\) its derivative is at least \(1-|\eta|D_\rho\ge1/2\).
Hence \(\Psi_\eta(1)=0\), \(\Psi_\eta\ge0\), and \(\Psi_\eta\) is
nondecreasing on its whole domain. Also

\[
 \int_1^\infty R_\eta(u)\frac{du}{u^2}=-(1+\gamma),\qquad
 R_\eta(u)=-a+\eta\Re u^\rho\quad(u\ge4).            \tag{27}
\]

The error is \(O_\rho(u^\beta)\). Since \(\beta<1\), this satisfies
the inherited \(u\exp(-c\sqrt{\log u})\) envelope for every fixed
\(c>0\), after increasing the starting point and constant. It also has
the same (O\(y\)) variation bound used in (14).

To check the scale relation, write

\[
 H_\rho(u)=\widetilde F_\rho(u)-u^\rho.
\]

It is supported on ([1,4]), has bounded variation, and its integral
against \(u^{-2}du\) is \(-1/(1-\rho)\). For integer \(N\ge4\),
right-endpoint quadrature for \(H_\rho(N/t)\), whose variation is bounded
independently of \(N\), proves

\[
 (TH_\rho)(N)=N\int_1^4 H_\rho(u)\frac{du}{u^2}+O_\rho(1).
\]

For precision, comparing the sum over \(k=1,\dots,N\) with the integral
over ([1,N]) costs at most its variation plus its first endpoint;
both are bounded here. Combining with (21) gives

\[
 (T\widetilde F_\rho)(N)=\zeta(\rho)N^\rho+O_\rho(1).          \tag{28}
\]

The same quadrature for the bounded monotone function \(R_0(N/t)\)
gives

\[
 (TR_0)(N)=-(1+\gamma)N+O(1),
\]

using (26) and \(R_0(u)=-a\) beyond (a). Therefore

\[
 (TR_\eta)(N)=-(1+\gamma)N
              +\eta\Re(\zeta(\rho)N^\rho)+O_{\rho,\eta}(1).   \tag{29}
\]

Apply the same tail quadrature proof (13)-(15) to \(R_\eta\), whose
normalization is exactly (27). Equations (27)-(29) imply

\[
 (L_KR_\eta)(N)=\eta\Re(\zeta(\rho)N^\rho)
                   +O_{\rho,\eta}(N/K+1)
\]

uniformly for every \(1\le K\le N\). If \(\zeta(\rho)=0\), the
model satisfies the full bound (16), with room to spare, while
\(R_\eta(u)=-a+\eta\Re u^\rho\) has oscillations of order \(u^\beta\).
For nonreal \(\rho\), take \(u\) along exponential sequences at the
extrema of the cosine; rounding those sequences to integers preserves
their order because consecutive logarithmic increments tend to zero.

**Scope.** This model is not the von Mangoldt summatory function. It
does not have prime-power support, and it does not satisfy the exact
prescribed identity \(TR=G\). Its forcing differs from that exact forcing
by \(O(\log N)\) when \(\zeta(\rho)=0\). That is precisely the amount
already allowed after passing to (16). It proves compatibility of the
retained positivity, monotonicity, normalization, PNT envelope, and
all-\(K\) scale estimates with a hypothetical off-critical zero mode.
It neither constructs an off-critical zero nor refutes RH or the exact
arithmetic identity. An argument using more of that exact identity is not
ruled out by this model.

## 9. What retaining the exact forcing entails

The exact divisor identity can be kept instead of weakened to (16).
For real \(x\ge1\), define

\[
 G(x)=\log(\lfloor x\rfloor!)-xH_{\lfloor x\rfloor}.
\]

Then \(TR(x)=G(x)\) exactly, since
\(\sum_{k\le x}\psi(x/k)=\log(\lfloor x\rfloor!)\).
On \(\Re s>1\), absolute convergence permits the Mellin calculation

\[
 \widehat G(s):=\int_1^\infty G(x)x^{-s-1}\,dx
       =\zeta(s)\widehat R(s)
       =-\frac{\zeta'(s)}s-\frac{\zeta(s)}{s-1}.      \tag{30}
\]

The first equality follows by setting \(x=ku\) in each term of (TR);
the last follows from (8). Thus inversion is division by \(\zeta(s)\),
not an automatically stable averaging operation.

If \(\rho\ne0,1\) is a zero of multiplicity \(m\), write
\(\zeta(s)=(s-\rho)^m g(s)\), \(g(\rho)\ne0\). The continued quotient
in (30) is

\[
 \frac{\widehat G(s)}{\zeta(s)}
       =-\frac1s\frac{\zeta'(s)}{\zeta(s)}-\frac1{s-1}
       =-\frac{m}{\rho(s-\rho)}+O(1).               \tag{31}
\]

In particular the exact forcing does not cancel such a zero upon
inversion. For a simple zero its numerator is nonzero; for a multiple
zero its numerator has order (m-1), leaving the same simple pole
after division. This calculation is conditional only in referring to
the location of a particular possible zero, and it includes multiplicity.
It is an exact diagnosis of this divisor route's spectral obstruction,
not a new zero-free theorem.

## 10. Bounded arithmetic diagnostics

The independent reviewer wrote `frontier_review_checks.py` from the
identities rather than importing a campaign implementation. Its recorded
output is `frontier_review_checks.json`; coverage, arithmetic precision,
endpoint checks and deliberate fault controls are stated in
`FRONTIER_INDEPENDENT_REVIEW.md`. These finite diagnostics test the
identities and conventions. They do not establish an asymptotic estimate,
an off-critical zero, or RH.

## 11. Status and the remaining door

Handwritten deductions examined in `FRONTIER_INDEPENDENT_REVIEW.md`:

- The mean criterion (5), uniformly with \(Z=\exp(\sqrt{\log N})\).
- The exact recurrence (15), the uniform bound (16), and its concrete
  \(O(\sqrt N)\) forcing at the square-root split.
- The multiplier formula (22), the normalized bounded-forcing construction
  (25), and the positivity-preserving model (26)-(29).
- The exact-forcing inversion and multiplicity calculation (30)-(31).

Not established: any new unconditional fixed power saving for \(R\),
\(B_N\), \(M_N\), or the full corrected energy; inequality (18); any
exclusion of a zero with real part greater than (1/2).

Refuted as an inference: an \(O(\sqrt N)\) forcing bound at a square-root
divisor split by itself is an \(O(\sqrt N)\) bound for (R\(N\)).
The attempted absolute-value induction has the growing coefficient (19).
The stronger statement that the retained envelopes and positivity rule
out an off-critical mode has not been proved; (26)-(29) show exactly why
a hypothetical zero would survive those inputs. This is not an
unconditional counterexample to a theorem equivalent to RH.

The remaining door in this bounded route is additional arithmetic control
of the signed quantity \(D_N\) in (18), or another use of the exact
prime-power identity that supplies a justified inverse estimate past its
zeta multiplier. Refining the (O\(N/K\)) quadrature constant, freezing a
different \(K\), or using monotonicity already consumed in (14) does not
supply that missing estimate.
