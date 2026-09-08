# The low-cost class misses the height kernel at N=10000

Continuation of PR #207 from `3099c7a`. The consumed input from Fable's
[PR #208](https://github.com/teal-sea/zeta-lab/pull/208) is pinned at
`600ff8044ed9f5e30b9dd9ddc5f488faf1af329a`. Both PRs remain open.

**Tested statement.** Set N=10000, y=100 and retain the exact Q_N and prime
weights m_q of [FINITE_TRANSFER.md](FINITE_TRANSFER.md). The class

\[
 \mathcal C=\{c\in\mathbb R^{100}: W_c(q)\ge1\ (q\in Q_N),\quad B_c(N)\le20000\}
\]

has empty intersection with

\[
 \mathcal K_W=\{c: W_c\text{ is constant on }P\},\qquad
 P=\{q\in Q_N:m_q>0\}.
\]

In fact the same exclusion holds without the cost cap. It follows from an
explicit integer relation on 21 positive-mass cells, not a rank calculation.
A quantitative consequence for every c in C is

\[
 \operatorname{Var}_p(W_c)\ge
 0.000047479444811021465439658291,\qquad p_q=m_q/\psi(N).
\]

The bound is positive but quantitatively weak: paying the smallest-atom
loss converts it to an excess bound of only 0.574078509186..., whereas the
checked exact optimizer already has excess 226.832689612321.... This does
not identify the minimum variance over C or establish a useful asymptotic
transfer. No other N was investigated in this continuation.

Evidence: exact integer/rational identities, fresh interval enclosures for
all logarithmic quantities, and an independent factorization/factorial
evaluation. No optimization was run. The algebra has an independent agent
review; it has not been formalized or externally reviewed.

## 1. Exactly which ingredients of #208 were consumed

The source is
`certificate_lp_frontier/results/dual_witness_N10000_y100.json` inside
`hunts/prime_pair_error/frontier/2026-09-06/`, at the pinned commit above.
The minimal extract [height_kernel_input.json](height_kernel_input.json)
contains its basis S, sparse primal c*, reported gain interval and dual
minimum, with the original artifact's SHA-256 and full source path. We did
not rerun its simplex calculation or audit its other experiments.

The independent reconstruction in [height_kernel.py](height_kernel.py)
checks these consumed ingredients:

- S has 100 distinct attainable cells; A_S=(floor(s/j)) is invertible with
  determinant -1328. Both products with its rational inverse equal I.
- A_S c*=1 exactly, and W_{c*}>=1 on all 198 attainable cells.
- **The archived rational N=10000 vector in #203 equals c* entry for entry.**
  This is an exact comparison of all 100 fractions, not agreement of costs.
- With the 1229 primes p<=N, reconstruct the integer coefficient matrix
  \[
  E_{jp}=\sum_{k\ge1}\left\lfloor\frac{\lfloor N/j\rfloor}{p^k}\right\rfloor,
  \quad L_j=\sum_p E_{jp}\log p,
  \quad V=(A_S^T)^{-1}E.
  \]
  All 122900 entries of A_S^T V=E agree exactly. Thus
  nu_s=sum_p V_{sp} log p satisfies A_S^T nu=L with no rationalization of
  the logarithms.
- Fresh 80-digit interval evaluation proves every one of the 100 nu_s
  strictly positive. Their minimum is enclosed by
  \[
  [0.000612063301151538696782037139,
   0.000612063301151538696782037140].
  \]

These checks establish the tight primal/positive dual identity, optimality
and uniqueness required here. They do not extend #208's results to another
size or consume its separate witness constructions.

For every feasible c, exact dual moments give

\[
 B_c-T^*=\sum_{s\in S}\nu_s(W_c(s)-1),\qquad
 T^*=B_{c^*}=\sum_s\nu_s.
\]

If B_c=T*, every summand is nonnegative and every nu_s is positive, so
A_S c=1 and c=c*. In particular **all nonzero cost-preserving feasible
displacements from the archived c*** are excluded. The two-cell obstruction
previously recorded in #207 was only one instance of this stronger fact.
This does not prohibit cost-preserving directions through higher-cost points.

## 2. Keep the full slack parameterization and budget

Every feasible vector is represented uniquely by

\[
 c=c^*+A_S^{-1}z,\quad z\ge0,\quad \nu^Tz\le\Delta,\qquad
 \Delta=20000-T^*,
\]

**together with** all remaining inequalities

\[
 F_q A_S^{-1}z\ge 1-W_{c^*}(q),\qquad q\in Q_N\setminus S.
\]

Here F_q=(floor(q/j))_{j<=100}. The identities are exact and retain the
symbolic Delta; the broad budget is enclosed by

\[
 T^*\in[10240.229382875436286119982112072461,
          10240.229382875436286119982112072462],
\]
\[
 \Delta\in[9759.770617124563713880017887927538,
             9759.770617124563713880017887927539].
\]

There is no restriction to a small neighborhood of c*. Dropping the
remaining coverage inequalities would change this class. An exact control
is z=e_1 in basis order, where the first basis cell is s=1: its basis
slacks are (1,0,...,0), and its cost is below 20000 by enclosure, but
W_{c*+A_S^{-1}e_1}(20)=-13/83. Cell 20 is outside S. This shows that the
remaining coverage inequalities cannot simply be dropped; it does not
assert that each of those 98 rows is individually indispensable.

Strict positivity of nu also gives 0<=z_s<=Delta/nu_s for every basis
coordinate. With the remaining closed inequalities retained, this is a
compact nonempty class, containing c*. Therefore its minimum variance
exists; the quantitative result below bounds its value away from zero.

## 3. Explicit exclusion of the height kernel

The following integers, zero at every unlisted cell, form the witness:

| q | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| w_q | 1 | -1 | 2 | -2 | 2 | -1 | -1 | 2 | -1 | -1 | 1 |

| q | 14 | 17 | 20 | 24 | 34 | 41 | 51 | 61 | 103 | 123 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| w_q | 1 | -2 | 2 | -1 | 1 | -1 | 1 | -1 | -1 | 1 |

Every listed q has positive m_q. Direct integer evaluation gives

\[
 \sum_q w_q=1,\qquad
 \sum_q w_q\lfloor q/j\rfloor=0\quad(1\le j\le100). \tag{1}
\]

Consequently sum_q w_q W_c(q)=0 for every real coefficient vector c. If
W_c is constant k on P, (1) gives 0=k sum_q w_q=k. Coverage at the positive
cell q=1 requires k>=1, a contradiction. This proves the claimed empty
intersection, even for the larger class with no cost restriction.

This is the **height** kernel, not the sawtooth kernel. By identity (R) in
the preceding note, the variance tested here is exactly the sum of the
finite residual variance and the squared drift mismatch. No balance
condition is imposed, and neither of those two terms is dropped.

## 4. Quantitative finite separation

Write Psi=psi(N), M=E_p W_c=B_c/Psi, and v=Var_p(W_c). Define

\[
 H=\sum_{q\in P}\frac{w_q^2}{m_q},\qquad D=\Psi H-1.
\]

Set u_q=w_q/p_q-1. Its weighted mean is zero. By (1),

\[
 \mathbb E_p[u(W_c-M)]=-M,\qquad \mathbb E_p u^2=D.
\]

Weighted Cauchy-Schwarz therefore proves, for every real c,

\[
 \boxed{v\ge\frac{M^2}{D}
       =\frac{B_c^2}{\Psi^2D}.} \tag{2}
\]

Every feasible c has B_c>=T*, so the full slack class obeys

\[
 v\ge\frac{(T^*+\nu^Tz)^2}{\Psi^2D}
   \ge\frac{(T^*)^2}{\Psi^2D}. \tag{3}
\]

This proof is valid on the entire broad class, including its boundary. The
upper cost cap is unnecessary for exclusion or for (2). No eigenvalue
plot, numerical rank tolerance or unproved estimate for m_q is involved.

Fresh interval arithmetic yields the following quantities, with full
outward decimal endpoints in
[height_kernel_results.json](height_kernel_results.json):

| Quantity | Value shown for readability |
|---|---:|
| Psi | 10013.39669326311478372032459447 |
| H | 2.19983034934611529112273266409 |
| D | 22026.77394588223345511471273674 |
| 1/D, using only M>=1 | 0.00004539929462466489317955 |
| (T*/Psi)^2/D, using optimality | 0.00004747944481102146543966 |
| Var_p(W_{c*}), for comparison | 0.04415622794410292829369053 |

The displayed decimals in the table are approximations; the stated lower
bound at the top of this note uses the lower enclosure endpoint. The
optimizer's variance is not asserted to minimize variance over C. Inequality
(3) is a lower bound on that minimum, not its computed value.

## 5. Paying the smallest-atom loss

Let X=W_c-1>=0, mu=E_p X, and E=B_c-Psi=Psi mu. At this cutoff the smallest
positive mass is exactly log2: every positive mass is at least log2, and
the cell q=5000 contains only d=2. Thus alpha=min p_q=log2/Psi. The finite
inequality already proved in #207 is

\[
 v\le\mu^2(1/\alpha-1),\qquad
 E\ge\Psi\sqrt{\frac{\log2}{\Psi-\log2}\,v}.
\]

Combining it with (3) gives

\[
 E\ge T^*\sqrt{\frac{\log2}{(\Psi-\log2)D}}
   \ge 0.574078509186175103450365662447. \tag{4}
\]

Without the consumed optimality lower bound, the direct combination with
1/D gives 0.561362019406..., and retaining M=1+mu and solving for mu gives
the slightly stronger valid bound

\[
 E\ge\frac{\Psi}{\sqrt{D(\Psi/\log2-1)}-1}
   \ge0.561393491742547236853468688646.
\]

The denominator is positive by enclosure. These are finite, unconditional
consequences of coverage and the row relation. They are **not useful
improvements to the known objective bound**:

\[
 T^*-\Psi\in[226.832689612321502399657517602273,
                226.832689612321502399657517602274].
\]

In particular, positive variance has not been mistaken for a sufficiently
large linear excess. Obtaining a useful excess bound through this route
still requires a substantially stronger variance estimate or a proved
shape/range estimate that improves the atom conversion, potentially both.
No such extra estimate is assumed here. Uniqueness of c* alone does not
supply one for the rest of the broad class.

## 6. Reproduction and evidence boundary

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
.venv/bin/python hunts/quotient_certificate/height_kernel.py --output /tmp/height-kernel.json
.venv/bin/python -m pytest -q -n 0 -m "not slow" tests/test_quotient_height_kernel.py
```

The script uses FLINT rational matrices for exact identities and a fresh
mpmath interval context for logarithms. Each exported decimal interval is
rounded outward from its exact binary endpoints. The replay checks the
same constants at 70 interval digits, then independently factors integers
through N=10000 and evaluates factorials at 110 digits. A planted wrong
primal and a duplicated basis cell must fail. An exact control verifies
the retained non-basis inequality in Section 2.

The saved final reconstruction and enclosure run took 0.31 seconds. The
focused and governance selection passed 36 tests with four slow tests
deselected in 8.60 seconds. Numerical libraries and FLINT used one thread.
The prior #207 input commit had green numerical and governance CI. No
optimization, larger-N computation or manually dispatched CI experiment
was used for this continuation, and no local process remains running.

Prime data are consumed to evaluate the finite measure and to check that
the relation lies on its positive support. This is a finite statement with
explicit prime information, not a prime-blind construction or a uniform
analytic estimate. The source artifacts and Fable's files remain unchanged.

## 7. The doors

- **Active constraints:** all 198 attainable rows, including zero-mass rows;
  B_c<=20000; no balance condition. All 98 non-basis rows remain in the
  slack description, with q=20 providing an explicit omission control.
- **Frozen choices:** N=10000, y=100, the existing dictionary and actual
  prime-weighted height variance. This result tests the combined residual
  and drift in (R), not just the sawtooth covariance.
- **Information class:** exact finite rows, an attributed saved primal/dual
  basis and prime-log enclosures. No simplex run, larger-N experiment or
  new dictionary is used.
- **First remaining gap:** the kernel intersection is settled, but a useful
  quantitative variance-to-excess transfer on the broad class is not.
  Bound (3) is far below the optimizer's observed variance, and (4) is far
  below the known excess. The value of the minimum variance over the full
  class has not been computed. Sharper variance separation and additional
  valid shape/range control remain unestablished. No follow-on computation
  is queued.
