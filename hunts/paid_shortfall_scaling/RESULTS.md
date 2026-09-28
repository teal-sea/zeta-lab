# Scaling the paid bound: what changes the leading cost

Mathematical base: `4efa72ad70a1e535709c33d0eded886d29c19274`.
This continues [paid_shortfall](../paid_shortfall/RESULTS.md). Its definitions
of `W_c`, `B_N`, `psi(N)`, `w_q`, and `C_N^U` are unchanged.

## Outcome and status

This pass supplies three elementary constructions/identities and a scoped
limitation. The perfect-power cap's total saving can be evaluated with a short
signed sum of logarithmic factorials. Its saving for the old fixed-seed,
square-root-support lifts is only `O(N^(1/4) log N)`. A new explicit balanced
Mobius-prefix family permits paid deficits and has coefficient mass at most
twice its support. Uniformly averaging its cutoffs is not consistently better;
choosing the least complete cost in a bounded cutoff interval cannot worsen it.
Holding those coefficients fixed, a small-prime composite-exclusion cap lowers
the full excess at `N=36864` from `877.252193` to `220.982190`.

The target `C_N^U <= N+O(sqrt(N) log(N)^2)` remains **unproved**. There is no
new prime-counting bound or claimed growth exponent. The all-N statements
below are elementary written derivations, not Lean results or externally
reviewed proofs. Numerical checks, source hashes, and finite ranges are in
`RUNS.md`. Novelty has not been assessed.

## 1. Exactly how much the perfect-power cap can change

For integer `d>=2`, let `r(d)` be its largest integer power exponent, and put

\[
 h(d)=\log d\left(1-\frac1{r(d)}\right),\quad
 T(X)=\sum_{2\le d\le X}h(d),\quad L(X)=\log(\lfloor X\rfloor!).
\]

For any finitely supported real coefficient vector, let
`delta_q=(1-W_c(q))_+` and `D_N=max_{q in Q_N}delta_q`. Its saving is exactly

\[
 S_N=C_N^w(c)-C_N^U(c)=\sum_{d=2}^N h(d)\delta_{\lfloor N/d\rfloor},
 \qquad 0\le S_N\le D_NT(N).                         \tag{1}
\]

For every integer `N>=2`, square extraction gives

\[
 0\le S_N-\sum_{2\le b\le\sqrt N}\log b\,
                 \delta_{\lfloor N/b^2\rfloor}
 \le D_N\sum_{k=3}^{\lfloor\log_2N\rfloor}(k-1)L(N^{1/k})
 \le8D_NN^{1/3}\log N.                              \tag{2}
\]

To prove the first inequality, write `d=a^r` with maximal exponent `r`.
A square contributes the baseline `log(d)/2`; its remaining contribution
is nonnegative. Every nonzero remainder has `r>=3` and is bounded by its
own `(k,b)=(r,a)` term in the positive sum in (2). Overcounting other power
representations only increases this majorant.

For the last inequality, `L(v)<=v log v` for `v>=1`. With
`K=floor(log_2 N)`, the sum without `D_N` is at most

\[
 \log N\left(\frac23 N^{1/3}+(K-3)_+N^{1/4}\right).
\]

The elementary maximum `max_{x>=1}(log x)x^(-1/12)=12/e` shows that the
coefficient of `N^(1/3) log N` is at most `2/3+12/(e log2)<8`.
Thus

\[
 L(\sqrt N)\le T(N)\le L(\sqrt N)+8N^{1/3}\log N,
 \quad T(N)=\tfrac12\sqrt N\log N-\sqrt N
                   +O(N^{1/3}\log N).                \tag{3}
\]

The leading coefficient one-half is sharp for the universal comparison:
`c=0` has `delta=1` and `S_N=T(N)`. If
`D_N=o(sqrt(N)/log N)`, (1) is `o(N)`, so this cap replacement cannot change
a leading term `C N+o(N)` in the raw cost. The same bound holds for the
difference of the two infima over any common, nonempty coefficient class
with uniform deficit bound `D_N`; it does not require attained optima.

This is not an unrestricted no-go. For `c_1=-t`, `t>=0`, the integer `d=4`
alone gives `S_N>=log2(1+t floor(N/4))` for `N>=4`, unbounded as `t` grows.

### The old early-truncated lift pays even less

Its deficit satisfies `delta_q<=H sum_{ell>=0}1_{q>=R M^ell}`. Therefore

\[
 S_N\le H\sum_{\ell\ge0}T(N/(RM^\ell)).              \tag{4}
\]

Writing `x=N/R`, (3) and geometric summation bound this by

\[
 H\log^+x\left[
 \frac{\sqrt x}{2(1-M^{-1/2})}
 +\frac{8x^{1/3}}{1-M^{-1/3}}\right].                \tag{5}
\]

The same formula is a harmless upper bound when `x<2`, when the exact sum
vanishes. At square-root support, fixed seed parameters give `x<J sqrt N`,
hence `S_N=O_{a,M}(N^(1/4) log N)`. For the base-6 digit construction,
`delta_q=1_{R|q}` gives the sharper finite bound `S_N<=T(N/R)` directly.

## 2. A short exact formula for the entire cap saving

For `k>=2`, define `b_k=-prod_{p|k}(1-p)`, the product over distinct primes.
For `X>=4`, let `K=floor(log_2 X)` and use exact integer roots. Then

\[
 \boxed{T(X)=\sum_{k=2}^{K}b_k L(X^{1/k}).}           \tag{6}
\]

For `0<=X<4`, both sides are zero with an empty sum. The first coefficients,
from `k=2` through `12`, are `1,2,1,4,-2,6,1,2,-4,10,-2`. Negative signs
must be retained; this is an identity, not a positive-term bound.

Proof: temporarily set `b_1=-1`. Multiplicativity and a finite geometric sum
give

\[
 \sum_{k\mid r}\frac{-b_k}{k}
 =\prod_{p^a\parallel r}\left(1+(1-p)\sum_{i=1}^a p^{-i}\right)
 =\frac1r.
\]

Thus `sum_{k|r,k>=2}b_k/k=1-1/r`. If `d=a^r` has primitive base `a`, the
factorial expansion counts `d` exactly at exponents `k|r`, with contribution
`log(d) sum b_k/k=h(d)`. Summing proves (6). The implementation first takes
`n=floor X` and uses integer comparisons to ensure `root^k<=n<(root+1)^k`.
No floating-point root is rounded to decide a perfect power.

## 3. Explicit scale-dependent coefficients

For integer `y>=2`, write `S(m)=sum_{j<=m}mu(j)/j` and take

\[
 c_j^{(y)}=\mu(j)\ (j<y),\qquad c_y^{(y)}=-yS(y-1).
                                                               \tag{7}
\]

These rational coefficients require arithmetic only through `y`. They obey

\[
 \sum_j c_j^{(y)}/j=0,\qquad W_y(q)=1\ (1\le q<y),\qquad
 A_y=\sum_j|c_j^{(y)}|\le2y-1.                       \tag{8}
\]

Balance is immediate. Coverage is the finite divisor identity
`sum_{j<=q}mu(j)floor(q/j)=1`, with no `j=y` contribution before `q=y`.
For the mass bound, put `m=y-1`. That same identity yields
`m S(m)=1+sum_{j<=m}mu(j){m/j}`. The `j=1` fractional part vanishes,
so `|S(m)|<=1`, proving (8). Balance also gives `|W_y(q)|<=A_y` and
`D_N<=1+A_y<=2y` without any positivity assumption.

Define the exact logarithmic main coefficient

\[
 \kappa_y=\sum_{j<y}\frac{\mu(j)}j\log(y/j).
\]

The elementary factorial remainder proves, for every integer `N>=2`,

\[
 |B_N(c^{(y)})-\kappa_yN|\le A_y(1+\log N).          \tag{9}
\]

Deficits occur only for `d<=N/y`. Thus the complete bound retains a
well-defined repair bill `P_N^U`, with

\[
 \psi(N)\le C_N^U(c^{(y)})=B_N(c^{(y)})+P_N^U,
 \quad 0\le P_N^U\le D_N L(N/y),\quad
 0\le C_N^w-C_N^U\le D_NT(N/y).                     \tag{10}
\]

At `y=floor(sqrt N)`, the factorial error in (9) already has square-root
scale, but the available crude bound on `P_N^U` does not. The missing bound
is on the **combined** quantity `(kappa_y-1)N+P_N^U`, allowing its actual
signs, not merely on `kappa_y` approaching one. In particular (8) and (10)
bound the cap saving by `O(N^(3/4) log N)` for this specific family. This is
a bound on the saving, not on its full excess or a demonstrated exponent.

### Averaging and selecting cutoffs are different operations

Let `a=max(2,ceil(y/2))` and average (7) over `a<=h<=y`. The resulting coefficients
have support at most `y`, zero harmonic drift, coverage one for `q<a`, and
mass at most `a+y-1`. No new positivity assumption is made.

For any finite convex average `bar c=sum alpha_h c_h` and **common caps**,
define `A_q=sum alpha_h(1-W_h(q))_+` and
`P_q=sum alpha_h(W_h(q)-1)_+`. Directly from the positive-part identity,

\[
 C_N^U(\bar c)=\sum_h\alpha_h C_N^U(c_h)
                  -\sum_q U_q\min(A_q,P_q).          \tag{11}
\]

This improves the average cost when members straddle coverage one in a cell
of positive capacity. It does not promise an improvement over the best member.

There is also an explicit cost-adaptive choice: select the smallest index
`h` minimizing `C_N^U(c^(h))` over `a<=h<=y`. The comparison does not require
knowing `psi(N)`. Indeed each candidate's exact excess is

\[
 C_N^U(c^{(h)})-\psi(N)=\sum_{2\le d\le N/h}
 \left[\Lambda(d)(W_h(\lfloor N/d\rfloor)-1)_+
 +(u(d)-\Lambda(d))(1-W_h(\lfloor N/d\rfloor))_+\right]. \tag{12}
\]

Only integers through `N/a` enter any comparison. The common unknown
`psi(N)` cancels. Since `h=y` remains eligible, selection never worsens that
endpoint's complete cost. This is a finite rule at every N, not a proof of
an asymptotic rate. Coefficient construction also needs Mobius values through
`y`, so the total arithmetic cutoff is `max(y,floor(N/a))`. In the intended
regime `N>=4`, `y=floor(sqrt N)`, this is just `floor(N/a)`.

## 4. Finite discriminator, not an exponent fit

The following are rounded **complete costs minus N**, using perfect-power
caps. All displayed values are backed by separately serialized rational
enclosures from two interval implementations. No optimizer over free
coefficients was used.

| N | support limit y | endpoint h=y | uniform average | selected cutoff h | selected cost minus N |
|---:|---:|---:|---:|---:|---:|
|144|12|2.075449|4.149979|12|2.075449|
|576|24|22.601527|21.416228|18|19.629813|
|2304|48|61.443499|84.068618|48|61.443499|
|9216|96|250.804520|300.370636|95|249.098861|
|36864|192|877.252193|1038.000679|192|877.252193|

Uniform averaging improved one of five endpoints. Cutoff selection improved
two and tied three. At the largest cutoff the raw endpoint cost was
`N+904.873880`, so perfect-power information saved `27.621687`, not the
whole excess. The base-6 control at the same support ceiling cost
`N+6895.149543`; it is a transparent control, not the repository's best
coefficient construction or a modern prime-counting benchmark.

## 5. Ordinary-composite exclusion changes the repair bill

For a finite set of primes `S`, define `v_S(d)=0` if some `p in S` divides
`d` and removing all its powers leaves an integer greater than one. Otherwise
put `v_S(d)=u(d)`. The zero case has at least two distinct prime factors, so
its Mangoldt weight is zero. A prime power is never removed. Consequently
`Lambda(d)<=v_S(d)<=u(d)` for every positive integer, and enlarging `S`
can only lower the cap. Summing over cells gives another valid paid bound,
with exactly the same coefficients and full-cost identity.

This is elementary divisibility information, not an assumption about primes.
It does not eliminate every ordinary composite: `143=11*13` survives when
`S={2,3,5,7}`. The code rejects composite exclusion divisors, since using 4
in place of a prime could incorrectly eliminate the prime power 16.

Keeping the endpoint coefficients `h=y` fixed isolates the effect of this
arithmetic information. The entries below are rounded complete costs minus N,
not just penalty savings. Exact coefficients and two-backend rational enclosures
at both requested precisions are in `computations/check-003/results.json`.
The code reconstructs the exact prime-log vectors before enclosure evaluation.

| N | perfect powers only | exclude via 2 | exclude via 2,3,5,7 |
|---:|---:|---:|---:|
|144|2.075449|2.075449|2.075449|
|576|22.601527|8.030006|2.432134|
|2304|61.443499|33.148332|18.526281|
|9216|250.804520|118.905287|45.747925|
|36864|877.252193|428.106422|220.982190|

At the largest cutoff, the factorial part is `N+9.667993`. The repair bill
falls from `867.584200` to `211.314197`. This explains the finite gain without
crediting coefficient cancellation that did not change. It supplies no
uniform rate, and is not compared here to optimized or modern prime bounds.

## 6. Disposition and next mathematical obligation

The cap-scaling question has an explicit answer with deficit dependence,
including a sharper bound for the old lifts and a fast exact mass identity.
The constructive pass has an explicit varying family, a full finite-cost
identity, a bounded coefficient budget, and a computable choice rule. Its
uniform RH-scale rate remains unresolved.

There is no basis here to launch a larger version of the same grid or fit an
exponent to five points. A next constructive improvement must control the
combined main-term discrepancy and localized paid penalty. Small-prime
exclusion now provides a concrete arithmetic ingredient; what remains is to
control the weighted deficits on surviving rough composites, together with
the prime-power surplus, uniformly in N. Its finite gain is not that control. A
failure of uniform averaging on this finite set does not close weighted
mixtures, other coefficient families, or the broader factorial route.

The prior finite Möbius-prefix and harmonic-drift identities are recorded in
[the earlier barrier study](../prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/BARRIER.md).
This study does not endorse every historical asymptotic assertion in that
document. Its new calculations use the finite identities explicitly proved
above, with paid deficits and a named information boundary.
