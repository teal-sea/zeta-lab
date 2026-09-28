# Prefix transport needs lower-prefix refills, even at N=10000

Continuation of PR #207 from `45b3d9b`. The construction consumed here is
Fable's [PR #208, Section 6](https://github.com/teal-sea/zeta-lab/blob/3d8aa03034d5207cdab3129eb78534c0f77d2384/hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/DUAL_WITNESS.md#6-a-tractable-non-basic-construction-exchanges-through-the-prefix),
pinned at `3d8aa03034d5207cdab3129eb78534c0f77d2384`.

**Result.** At N=10000, y=100, the profitable exchange 103 to 101 passes
the source-capacity condition and every top-half prefix condition, but has
exactly zero capacity starting from the real prime measure. It withdraws
from cell 33, whose real mass is zero. Thus even an arbitrarily small
positive fraction of source mass need not work below the top half. The
exact repair for this exchange is an accumulated refill at cell 33, along
with five other explicitly identified capacities. This refutes a proposed
simplification of the capacity conditions, not Fable's complete conditions
or the saved feasible sequence.

The evidence is hardened: integer moment identities and product comparisons,
an independent triangular solve and prime factorization, and interval
enclosures for the decimal consequences. No optimization or search is used.
The result is not formalized or externally reviewed. The completed height
kernel investigation is not reopened, and PR #207 remains open for review.

## 1. The two coordinator deductions

Retain Q_N={floor(N/d): 2<=d<=N}, A_{qj}=floor(q/j), and

\[
 m_q=\sum_{N/(q+1)<d\le N/q}\Lambda(d),\qquad
 \Psi=\psi(N)=\sum_qm_q,\qquad L=A^Tm.
\]

For every feasible c, W_c=Ac>=1 on **all** Q_N, and
B_c=L^Tc. Write E_c=B_c-\Psi. If a real signed measure w on Q_N satisfies
A^Tw=0 and sum w=1, it has a negative entry: the j=1 column is strictly
positive. If none of its negative entries lies on a zero-mass cell, put

\[
 t=\min_{w_q<0}\frac{m_q}{-w_q}>0.
\]

Then m+tw>=0 and A^T(m+tw)=L, so

\[
 B_c=(m+tw)^TW_c\ge\sum_q(m_q+tw_q)=\Psi+t,
 \qquad E_c\ge t.                                      \tag{1}
\]

This is ordinary finite duality. It does not require the cost budget or a
variance estimate. For the saved 21-cell relation in
[HEIGHT_KERNEL.md](HEIGHT_KERNEL.md), **t=log(97)**. To check every capacity
without rounding logarithms, let M_q be the product of the prime base p
once for each prime power p^k in the cell, so m_q=log M_q. All 11 negative
coordinates satisfy M_q>=97^{-w_q}, with equality only at q=103. The exact
products are in [transport_capacity_results.json](transport_capacity_results.json).

An even smaller control is

\[
 \delta=\log(97)(e_1+e_{102}-e_{103}).
\]

All three cells are attainable. For j=1 the floor difference between 103
and 102 is one. For 2<=j<=100 it is zero, since the prime 103 has no such
divisor. These are exactly the entries of row 1. Also m_{103}=log97 and
m_{102}=0. Hence m+delta is feasible and (1) gives

\[
 E_c\ge\log97\in
 [4.574710978503382822116721621703,
  4.574710978503382822116721621704].
\]

The zero-real-mass destination 102 is essential to this control's support;
we have not restricted the dual class to positive-real-mass cells.

For deduction B, take the full class W_c>=1 on Q_N, B_c<=20000. The saved
optimizer c* belongs to this class and has

\[
 v_*:=\operatorname{Var}_{m/\Psi}(W_{c^*})\in
 [0.044156227944102928293690533273,
  0.044156227944102928293690533274].
\]

Any uniform nonnegative constant lower bound v_c>=v_0 on this class must
have v_0<=v_*. The smallest positive atom is alpha=log2/\Psi. Feeding only
v_0 into the established conversion

\[
 E_c\ge\Psi\sqrt{\frac{\alpha v_0}{1-\alpha}}
\]

can therefore never return more than

\[
 \Psi\sqrt{\frac{\log2\,v_*}{\Psi-\log2}}
 \in[17.507109839685324966496006467143,
      17.507109839685324966496006467342].                 \tag{2}
\]

This limits that particular constant-variance/smallest-atom procedure.
It does not upper-bound E_c or other variance-based arguments. The already
checked optimal excess is 226.832689612321..., much larger than (1) or (2).

## 2. True integer rates and an exact suffix identity

Assume {1,...,y} is contained in Q_N, as at the fixed case here. For q>y
define, with R_q(y+1)=0,

\[
 R_q(s)=\sum_{k\le y/s}\mu(k)\left\lfloor\frac q{sk}\right\rfloor,
 \quad r_s(q)=R_q(s)-R_q(s+1),\quad
 z_q=e_q-\sum_{s\le y}r_s(q)e_s.
\]

These are signed integer rates, not probabilities. Summation by parts and
the divisor identity sum_{k|n}mu(k)=1_{n=1} give

\[
 \sum_{s=1}^yr_s(q)\lfloor s/j\rfloor
 =\sum_{\ell\le y/j}R_q(\ell j)
 =\sum_{n\le y/j}\lfloor q/(jn)\rfloor\sum_{k\mid n}\mu(k)
 =\lfloor q/j\rfloor.
\]

Thus A^Tz_q=0 and sum z_q=1-W_mu(q), where
W_mu(q)=sum_{j<=y}mu(j)floor(q/j). These are the identities used from #208.

**Endpoint correction to the source prose.** For y/2<s<y,
r_s(q)=floor(q/s)-floor(q/(s+1)) is nonnegative but need not be at most
one. At s=y, the correct rate is r_y(q)=floor(q/y). At q=5000,y=100,
r_{51}=2 and r_{100}=50. The pinned source's implementation uses the
correct endpoint; its Section 6 description as 0-or-1 steps cannot be
used as a bound. We also use R_q only as its signed Mobius sum, not as an
unproved nonnegative counting interpretation. Fable's files are untouched.

There is, however, an exact useful aggregate identity. For every integer
y/2<u<=y,

\[
 \sum_{s=u}^y r_s(q)=R_q(u)=\lfloor q/u\rfloor.          \tag{3}
\]

Consequently any finite above-prefix coefficients eta_q have net prefix
drains C_s=sum_q eta_q r_s(q) satisfying

\[
 \sum_{s=u}^y C_s=\sum_{q>y}\eta_q\lfloor q/u\rfloor,
 \qquad
 \sum_{s=u}^y m_s=
 \psi(\lfloor N/u\rfloor)-\psi(\lfloor N/(y+1)\rfloor). \tag{4}
\]

The second equality follows by joining the disjoint integer cells. Thus
C_s<=m_s for all prefix cells implies each corresponding suffix inequality
in (4). No prime-distribution estimate is involved. Aggregate necessary
conditions do not assert feasibility at individual cells or below u.

## 3. A precise capacity shortcut and its exact counterexample

**Proposed statement P, tested here.** At N=10000,y=100 there exists a
kappa in (0,1] such that every pair of distinct attainable a,b>100 with
m_a>0 and W_mu(a)>W_mu(b), satisfying

\[
 m_s+m_a\bigl(r_s(a)-r_s(b)\bigr)\ge0
 \quad(51\le s\le100),                                \tag{5}
\]

has a feasible exchange m+theta(z_b-z_a)>=0 at theta=kappa m_a.
Destinations with m_b=0 are allowed. This is the proposed shortcut of
replacing the remaining lower-prefix tests by a positive fraction of donor
capacity. It is not an assertion that #208's full criterion omitted them.

**P is false, even for one pair.** Set a=103 and b=101. The source cell
contains only d=97, so m_a=log97. The destination contains only d=99,
so m_b=0. The exact values W_mu(103)=4 and W_mu(101)=2 make the gain 2theta.
The nonzero prefix changes are:

| s | 1 | 3 | 5 | 6 | 16 | 17 | 33 | 34 | 50 | 51 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| r_s(103)-r_s(101) | 3 | -1 | -1 | 1 | 1 | -1 | -1 | 1 | -1 | 1 |

Above the prefix, add +1 at 101 and -1 at 103. These 12 integers annihilate
all 100 floor columns and sum to 2. Every change at s>50 is nonnegative,
so (5) holds for any theta>=0. Nevertheless, cell 33 consists of

\[
 \{295,\ldots,303\}=
 \{5\cdot59,\ 2^3\cdot37,\ 3^3\cdot11,\ 2\cdot149,
 13\cdot23,\ 2^2\cdot3\cdot5^2,\ 7\cdot43,
 2\cdot151,\ 3\cdot101\}.
\]

None is a prime power: m_{33}=0. Its change is -theta, so **every positive
theta fails**. Exact product comparisons show that at theta=log97 all
other touched cells are nonnegative. This isolates the first obstruction
to P in a single lower-prefix coordinate.

The normalized signed measure w=(z_{101}-z_{103})/2 has A^Tw=0 and sum w=1,
but w_{33}=-1/2 on a zero-mass cell. Thus it fails the normalized target's
zero-mass sign condition, independently of C. It is a counterexample to P,
not a counterexample to the existence of a different successful family.

**Exact repair.** For any current nonnegative measure nu on Q_N, the
largest feasible amount for this direction is

\[
 \theta_{\max}=
 \min\{\nu_3,\nu_5,\nu_{17},\nu_{33},\nu_{50},\nu_{103}\}. \tag{6}
\]

These are exactly the six negative coordinates, each with coefficient -1;
all other coordinates stay fixed or increase. If nu already has the
required moments, every step up to (6) preserves them and gives added gain
2theta. Starting from m, (6) is zero. Earlier refills can change this.
For a sequence, all intermediate measures need these capacity checks;
for a final dual witness only its final nonnegativity is required.

## 4. The quantitative accumulated estimate still needed

Here is the precise analytic obligation, rather than a claim of a family
satisfying it. For a finite collection of prefix exchanges with amounts
u_l>=0 withdrawn at a_l>y and v_l>=0 added at b_l>y, put

\[
 \eta_q=\sum_{l:b_l=q}v_l-\sum_{l:a_l=q}u_l,\qquad
 \delta=\sum_{q>y}\eta_qz_q,
 \quad G=\sum_q\eta_q(1-W_mu(q)).
\]

Only attainable a_l,b_l are permitted. Individual destinations need not
carry real mass. The exact accumulated prefix withdrawal and refill are

\[
 D_s=\sum_l\{v_l(r_s(b_l))_++u_l(-r_s(a_l))_+\},\qquad
 F_s=\sum_l\{u_l(r_s(a_l))_++v_l(-r_s(b_l))_+\},
 \quad C_s=D_s-F_s.
\]

The final coordinates are m_q+eta_q above y and m_s-C_s in the prefix.
This accounts for negative rates and overlapping sources, destinations
and refills. In particular, a bound for gross withdrawals that discards
available refills can be much stronger than is necessary.

For a proposed family, sufficient quantitative estimates are, for a
constant K>=1,

\[
 (-\eta_q)_+\le K m_q\quad(q>y),\qquad
 (D_s-F_s)_+\le K m_s\quad(s\le y).                     \tag{7}
\]

Then m+delta/K is a nonnegative dual measure and gives **E_c>=G/K** when
G>0. To imply the requested rate one must additionally prove, with g_0>0,

\[
 G\ge g_0 N/\sqrt y.                                   \tag{8}
\]

If K and g_0 are uniform for an actual family, w=delta/G meets the
normalized capacity target with C=K/g_0, and E_c>=N/(C sqrt y). This is
standard capacity bookkeeping, not the research result of this note.
For nonuniform K(N) and a proved gain G(N), the resulting lower bound is
G(N)/K(N). No such uniform or growing family is established here.

One can state the unsolved local estimate directly in arithmetic terms:

\[
 T_s=\sum_{k\le y/s}\mu(k)\sum_{q>y}\eta_q
                  \left\lfloor\frac q{sk}\right\rfloor,
 \quad T_{y+1}=0,
 \qquad T_s-T_{s+1}=C_s\le K m_s.                       \tag{9}
\]

At a zero-mass cell (9) requires T_s<=T_{s+1} exactly. At positive-mass
cells it requires a comparison with the actual sum of log p over prime
powers in (floor(N/(s+1)),floor(N/s)]. Equations (3)-(4) control upper
suffix sums but do not prove (9); P already fails at s=33. The first
unproved estimate for a construction is this **local net-drain bound
including zero-mass cells**, jointly with sufficient profitable supply
(8). Source mass alone does not imply it.

No individual bound m_s asymptotic to N/s^2 is assumed. A positive lower
bound of that form for every lower-prefix cell would already be false at
s=33, where the integer interval has nine elements and zero mass. Any
analytic construction using prime-mass lower bounds must specify the cells
or aggregates on which those bounds hold, prove their errors, and still
resolve zero-mass drains. The finite checks here evaluate exact prime
data; they do not produce a prime-blind family.

## 5. Checks, resources and scope

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
.venv/bin/python hunts/quotient_certificate/transport_capacity.py --output /tmp/transport-capacity.json
.venv/bin/python -m pytest -q -n 0 -m "not slow" tests/test_quotient_transport_capacity.py
```

The fixed script took 0.017 seconds and reports 1/1 completed controls.
The six focused tests and governance selection passed 35 tests, four slow
tests deselected, in 4.63 seconds, using one numerical thread. The checks
independently solve the triangular rate identities, factor the relevant
integers, test (3)-(4) and the signed accumulation identities, exercise
(6) before and after a refill, and recompute (2) from the archived rational
primal at 110 digits. Decimal endpoints come from fresh interval arithmetic.
No search, optimizer, larger-N computation or queued follow-on run is used.

**Doors.** The dictionary and full attainable support remain fixed; all
zero-real-mass destinations and constraints are retained. The low-cost
class B_c<=20000 is used in (2); the direct dual bounds apply to every
feasible c without that cap. The new output is the exact obstruction to
P and its refill condition (6), with the true-rate identities needed to
state (7)-(9). The first remaining gap is a constructed family for which
those local capacities and adequate gain can both be proved. This result
neither refutes such a family nor supplies a scaling rate.
