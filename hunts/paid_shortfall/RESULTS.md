# Paying for an early-truncated factorial lift

## What this attempt establishes

The paid-shortfall construction has an explicit, fully charged family:
truncate a finite balanced seed lift at square-root support. Its repair
bill is at most order `sqrt(N) log N`, with constants stated below. The
factorial remainder is at most order `log(N)^2` for a fixed seed.

This does **not** make the whole prime-counting error square-root sized.
The leading term of the old seed survives. For the two seeds checked here
it is `C N` with `C > 1`, so the excess over `N` is still linear.

A separate exact example at `N=14`, using the same paid-bound definition,
shows why adding arithmetic information is actionable: a perfect-power
cap removes an artificial-mass obstruction that the raw logarithmic cap
cannot remove, even after optimizing all coefficients with support at most
three. This is a finite example, not a uniform estimate.

Status: explicit mathematical derivations, independently checked algebra,
and small deterministic checks recorded in `RUNS.md`. No Lean proof or
external review has been completed. Novelty has not been assessed.

## 1. Definitions and the complete paid cost

Let `N >= 2` be an integer. Put

\[
 Q_N=\{\lfloor N/d\rfloor:2\le d\le N\},\qquad
 W_c(q)=\sum_j c_j\lfloor q/j\rfloor,
 \qquad B_N(c)=\sum_j c_j\log(\lfloor N/j\rfloor!).
\]

Here the coefficients have finite support on positive integer indices.
Let `Lambda` be the von Mangoldt function and define the true and raw
available masses of a quotient cell by

\[
 m_q=\sum_{\lfloor N/d\rfloor=q}\Lambda(d),\qquad
 w_q=\sum_{\lfloor N/d\rfloor=q}\log d.
\]

For any cap `U_q >= m_q`, the paid cost is

\[
 C_N^U(c)=B_N(c)+\sum_{q\in Q_N}U_q(1-W_c(q))_+.
\]

The divisor identity `log n = sum_{d|n} Lambda(d)` gives
`B_N(c)=sum_q m_q W_c(q)`. Consequently the **exact** excess is

\[
 C_N^U(c)-\psi(N)=
 \sum_q m_q(W_c(q)-1)_+
 +\sum_q(U_q-m_q)(1-W_c(q))_+\ \ge 0.                 \tag{1}
\]

The first term charges surplus coverage. The second charges slack in the
available information precisely where coverage is missing. Neither is
dropped in this study. Write `C_N=C_N^w` for the raw cap.

## 2. Early-truncation lemma

Fix an integer `M >= 2` and finitely supported real coefficients `a_j`,
with support in `1 <= j <= J`, satisfying

\[
 \sum_j\frac{a_j}{j}=0,\qquad
 g(t)=\sum_j a_j\lfloor t/j\rfloor,\qquad
 W_\infty(t)=\sum_{k\ge0}g(t/M^k)\ge1\quad(t\ge1).
\]

Assume also `g(t) <= H` for `t >= 0`, with `H >= 0`. The lift is finite
at every fixed `t`, since `g(t)=0` for `0 <= t < 1`. Define

\[
 A=\sum_j|a_j|,\quad
 \kappa=-\sum_j\frac{a_j\log j}{j},\quad
 C=\frac{\kappa}{1-1/M},\quad L(x)=\log(\lfloor x\rfloor!).
\]

Take any integer `K >= 0`, set `R=M^(K+1)`, and use the explicit coefficients

\[
 c_n=\sum_{\substack{jM^k=n\\0\le k\le K}}a_j,
 \qquad W_K(t)=\sum_{k=0}^K g(t/M^k).
\]

Their support is at most `J M^K`. With

\[
 E_N=A\sum_{k=0}^K\bigl(1+\log^+(N/M^k)\bigr),
\]

the full bound is

\[
 \psi(N)\le C_N(c)
 \le C(1-1/R)N+E_N+
 H\sum_{\ell\ge0}L\!\left(\frac{N}{RM^\ell}\right). \tag{2}
\]

Moreover,

\[
 |B_N(c)-C(1-1/R)N|\le E_N,                          \tag{3}
\]

and, writing `x=N/R`, the repair term is at most

\[
 \frac{H}{1-1/M}\,x\log^+x.                          \tag{4}
\]

These statements also cover `N < R`, when the repair bill is zero.

### Proof, including the bill

First, the omitted lift controls the deficit:

\[
 (1-W_K(q))_+
 \le\left(\sum_{k>K}g(q/M^k)\right)_+
 \le H\sum_{\ell\ge0}{\bf1}_{q\ge RM^\ell}.
\]

No assumption that `g` is nonnegative is needed for this step. Since
`R M^ell` is an integer, `floor(N/d) >= R M^ell` if and only if
`d <= floor(N/(R M^ell))`. Thus

\[
 \sum_q w_q(1-W_K(q))_+
 \le H\sum_{\ell\ge0}\sum_{2\le d\le N/(RM^\ell)}\log d
 =H\sum_{\ell\ge0}L(N/(RM^\ell)).                  \tag{5}
\]

All sums are finite. The elementary estimate
`L(v) <= v log^+ v` bounds the last sum by the geometric series in (4).

For completeness, integral comparison for the increasing function `log t`
gives, for every real `v>0`,

\[
 |L(v)-(v\log v-v)|\le1+\log^+v.
\]

One way to see the bound is to put `n=floor v`: the error at `n` lies
between `1` and `1+log n`; extending `n log n-n` from `n` to `v<n+1`
subtracts a number in `[0,log v]`. The case `0<v<1` follows directly.
Apply this estimate to `v=N/(jM^k)` and use `j>=1`. Balance cancels both
the `N log N` and the `N` terms inside each scale, leaving
`kappa N/M^k`. Summing the scales proves (3). Adding (5) and using (1)
proves (2).

### Square-root support, and the surviving obstruction

For `N >= J^2`, take the largest `K >= 0` with `J M^K <= sqrt N`.
Then `R > sqrt N/J`, while

\[
 E_N=A\left((K+1)(1+\log N)
       -\frac{K(K+1)}2\log M\right).
\]

The repair bill is at most

\[
 \frac{HJ}{1-1/M}\sqrt N\log(J\sqrt N).              \tag{6}
\]

For a fixed seed, (3), nonnegativity of the repair bill, and (6) give

\[
 C_N(c)-N=(C-1)N+O_{a,M}(\sqrt N\log N).             \tag{7}
\]

This controls truncation, not the leading excess. Changing the seed with
`N` requires controlling `A`, `H`, `J`, `M`, and `C` together. The fixed-seed
big-O must not be reused with growing seed complexity hidden in its constant.

## 3. An explicit base-6 construction

Use

\[
 g(t)=\lfloor t\rfloor-\lfloor t/2\rfloor
                 -\lfloor t/3\rfloor-\lfloor t/6\rfloor.
\]

It is balanced and periodic of period six. Its values on integer residues
`0,1,2,3,4,5` are respectively `0,1,1,1,1,2`. Therefore it is nonnegative,
bounded by two, and at least one on `1 <= t < 6`. Dividing any `t>=1` by
the appropriate power of six proves full-lift coverage.

For `r=K+1` and `R=6^r`, the truncated lift telescopes to coefficients

\[
 c_1=1,\quad c_R=-1,\quad
 c_{2\cdot6^k}=c_{3\cdot6^k}=-1\quad(0\le k<r).
\]

At an integer `q`, each summand reads one base-6 digit. All weights are
nonnegative and every nonzero digit has weight at least one. Hence

\[
 (1-W_K(q))_+={\bf1}_{R\mid q}.                      \tag{8}
\]

The exact repair bill is `sum_{q in Q_N, R|q} w_q`, bounded by `L(N/R)`.
The combined coefficient mass is `2r+2`, giving the sharper explicit bounds

\[
 C_6(1-1/R)N-(2r+2)(1+\log N)
 \le C_N(c)
 \le C_6(1-1/R)N+(2r+2)(1+\log N)+L(N/R),
\]

where

\[
 C_6=(4\log2+3\log3)/5>1.
\]

This is an especially transparent example, not a leading-constant record.
The existing pilot's seed
`a={1:1,2:-1,3:-1,5:-1,30:1}`, with `M=6`, has `A=5`, `J=30`,
`H=1`, and the smaller constant

\[
 C_{30}=(14\log2+9\log3+5\log5)/25>1.
\]

The generic early-truncation lemma applies to it too. It does not apply
unchanged to an infinite nested adaptive lift masquerading as a finite seed.

## 4. A finite obstruction removed by arithmetic capacity

For `d>=2`, let `r(d)` be the largest integer `r>=1` for which `d=b^r`
with integer `b>=2`, and put

\[
 u(d)=\log d/r(d),\qquad
 U_q=\sum_{\lfloor N/d\rfloor=q}u(d).
\]

If `d=p^k` is a prime power, `r(d)=k`, so `u(d)=Lambda(d)`. Otherwise
`Lambda(d)=0 <= u(d) <= log d`. Thus `m_q <= U_q <= w_q`. Computing
`r(d)` requires only exact integer-power tests, not a primality oracle.

At `N=14`, restrict coefficient support to `j<=3`. The quotient cells in
ascending order are `(1,2,3,4,7)`. Choose

\[
 (c_1,c_2,c_3)=(1,-1,-3/2),\qquad
 (W_c(q))_q=(1,1,1/2,1/2,1).
\]

Only the cells containing `d=4` and `d=3` need repair. Direct substitution
in (1) gives

\[
 C_{14}^{w}(c)=\psi(14)+\tfrac12\log2,
 \qquad C_{14}^{U}(c)=\psi(14).                       \tag{9}
\]

The raw-cap excess is unavoidable for **every** choice of coefficients
with this support, not just this candidate. To prove it, set

\[
 \epsilon=\tfrac12\log2,\quad
 v=(-1,1,2,0,-1),\quad x=m+\epsilon v.
\]

The three moments `sum_q v_q floor(q/j)` are zero for `j=1,2,3`, and
`sum_q v_q=1`. The vector `x` is feasible for the raw caps: withdrawals in
cells one and seven are smaller than the actual masses; cell two has slack
`log6 > epsilon`; cell three uses its entire slack `log2`; cell four is
unchanged. In particular `0<=x_q<=w_q`.

For any real `W` and `0<=x<=w`,
`x(W-1)+w(1-W)_+ >= 0`. Summing and using the zero moments proves

\[
 C_{14}^{w}(c')\ge\sum_qx_q=\psi(14)+\tfrac12\log2
 \quad\text{for every }c'\text{ supported on }j\le3.
\]

Together with (9), this proves both finite optima exactly. No assertion
is made about the raw optimum with unrestricted support.

More generally, replacing the raw cap by the perfect-power cap saves exactly

\[
 C_N^w(c)-C_N^U(c)=\sum_{d=2}^N
 \log d\left(1-\frac1{r(d)}\right)
 (1-W_c(\lfloor N/d\rfloor))_+.
\]

This information excludes some artificial mass. It does not eliminate the
slack from ordinary composite numbers, and no growth estimate follows
from this example.

## 5. Provenance, checks, and the doors

The paid functional and capped dual were preserved from the September 7
research conversation. The balanced-seed factorial main term and remainder
are inherited from the [existing pilot](../prime_pair_error/frontier/2026-09-06/factorial_certificate_pilot/PILOT.md).
The delta here is the explicitly charged early truncation, its support-cost
bound, and the exact raw-cap versus perfect-power-cap comparison. This
study claims neither first discovery nor a new best prime-counting bound.

`construction.py` and `tests/test_paid_shortfall.py` check rational floor
identities, exact prime-log coefficient identities, small cap inequalities,
both seed families, and interval/logarithm refinements. The run manifest
records the finite domain, output hashes, software, and non-claims. Finite
checks can falsify an implementation or formula here; the all-`N` assertion
rests on the displayed derivation, not on the size of that finite domain.

The result closes one practical gap: truncating a finite lift need not
leave an unpriced deficit. The mathematical door still open is a uniform
construction whose **entire** paid cost is `N+O(sqrt(N) log(N)^2)`, including
the leading term and any growing family constants. Improving a cap can help
only where the candidate has a deficit, as (1) makes explicit. Improving
coverage alone while retaining a fixed leading excess cannot deliver that
target. Neither this upper-bound construction nor the finite example claims
to establish RH, a two-sided error estimate, or a new exponent.
