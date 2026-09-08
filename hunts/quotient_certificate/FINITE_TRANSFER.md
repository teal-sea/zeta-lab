# Finite prime-weighted transfer: an exact sampling obstruction

Input: `880ec07ae605d93f4c49e4464d8b4526457cfb65`. This is a continuation
after #203, #205 and #206, preserving their artifacts and corrections.

Continuation: [HEIGHT_KERNEL.md](HEIGHT_KERNEL.md) checks #208's exact
optimizer, extends the archived-vector uniqueness conclusion to every
cost-preserving feasible displacement from it, and excludes the height
kernel at N=10000. The earlier investigation below is retained as recorded.

**Result.** At N=10000, y=100, an explicit rational vector has c_1=1,
sum_{j>=2}|c_j|=1, and W_c(q)>=1 for every positive integer q. Its sawtooth
sum is identically zero on the 99 positive-mass attainable cells, although
its common-period variance is strictly positive. Thus the candidate finite
comparison in Section 3 fails inside the feasible class. The witness is
saved in [finite_transfer_counterexample.json](finite_transfer_counterexample.json).

**Boundary.** Its objective is B_c=log(N!), so this does not refute a transfer
restricted to low-cost or optimal certificates. There is a concrete reason
to retain that restriction: at the saved N=10000 certificate, the two
zero-mass constraints q=60 and q=333 block every nonzero displacement along
this particular null direction. Both facts are exact, not fitted behavior.

The witness has independent integer/rational checks. The general statements
below have algebraic proofs and finite checks; they have not been formalized
or externally reviewed. No novelty or asymptotic barrier is claimed.

## 1. Exact finite measure, including the discarded cells

For integers N>=2 and y>=1, retain

\[
 Q_N=\{\lfloor N/d\rfloor:2\le d\le N\},\quad
 m_q=\sum_{\lfloor N/(q+1)\rfloor<d\le\lfloor N/q\rfloor}\Lambda(d),
 \quad \Psi=\psi(N)=\sum_{q\in Q_N}m_q.
\]

Let P={q in Q_N:m_q>0}, s=|P|, and p_q=m_q/Psi on P. The LP still requires
coverage on **all Q_N**, including its zero-mass cells. Only the quadratic
form discards those cells. The measure is exact; no N/q^2 approximation is
used. Here and below Var means variance under p unless explicitly labeled
as a common-period variance.

Set f_j(q)={q/j}-(j-1)/(2j), F_{qj}=floor(q/j), U_{qj}=f_j(q), a_j=1/j,
b_j=(j-1)/(2j), and let t be the column with entries q. Then

\[
 F=t a^T-U-\mathbf1 b^T,\qquad
 W_c(q)=q A_c-S_c(q)-b^Tc,\quad A_c=a^Tc,\quad S_c=Uc.
\]

Equivalently W_c(q)=q A_c-sum_j c_j {q/j}. No balance condition is imposed.
Write C=diag(p)-pp^T, bar q=p^T t, bar f=U^Tp, and

\[
 C_f=U^TCU,\quad h=U^TCt,\quad V_q=t^TCt,\quad
 G=F^TCF=C_f-ah^T-ha^T+V_q aa^T.
\]

These are finite weighted forms, not the periodic gcd matrix. All centering
and drift terms are necessary:

\[
 \bar W=c^TF^Tp=A_c\bar q-c^T(\bar f+b),\qquad
 v=\operatorname{Var}(W_c)=c^TGc
   =c^TC_fc-2A_c c^Th+A_c^2V_q.
\]

For X_q=W_c(q)-1>=0, put mu=E_p X and E=B_c(N)-psi(N). The factorial
convolution from #203 gives, exactly,

\[
 E=\sum_qm_qX_q=\Psi\mu,\qquad
 \mu=c^TF^Tp-1,\qquad
 \mathbb E_pX^2=c^TF^T\operatorname{diag}(p)Fc-2c^TF^Tp+1=v+\mu^2.
\]

The full-period means of f_j are zero; their finite means bar f_j generally
are not. Dropping bar f or the linear term changes this problem.

## 2. Null directions and rank

Strict positivity of p on P gives exact, weight-independent kernel tests:

\[
 \mathcal K_S=\ker C_f=\{c:Uc\text{ is constant on }P\},\qquad
 \mathcal K_W=\ker G=\{c:Fc\text{ is constant on }P\}.
\]

In particular e_1 lies in K_S because f_1=0, whereas F e_1=t is not
constant when s>=2. The rank bounds are

\[
 \operatorname{rank}C_f\le\min(y-1,s-1),\qquad
 \operatorname{rank}G\le\min(y,s-1).
\]

For an anchor q_0 in P, the rows F_q-F_{q_0} form an integer matrix D_W
with kernel K_W and the same rank as G. For the sawtooths, use the integer
matrix R with columns j=2,...,y and rows

\[
 R_{qj}=(q\bmod j)-(q_0\bmod j),\quad q\in P\setminus\{q_0\}.
\]

Then R(c_j/j)_{j>=2}=0 exactly characterizes K_S modulo e_1. By contrast,
the full-period matrix has kernel exactly span(e_1): its Jordan divisor
factorization is triangular with positive diagonal for j>=2.

## 3. One candidate comparison, and its feasible counterexample

The candidate is deliberately quantified before testing:

> There exists kappa>0 such that for every integer N>=4, every integer
> 2<=y<=floor(sqrt(N)), and every real c in R^y satisfying W_c(q)>=1 for
> every q in Q_N,
> \[
> \operatorname{Var}_p(S_c)\ge\kappa\,
> \operatorname{Var}_{\rm period}(S_c). \tag{T}
> \]

The period is lcm(1,...,y), sampled at integer arguments. Issue
[#204](https://github.com/teal-sea/zeta-lab/issues/204) supplies

\[
 K^{\rm per}_{ij}=\frac{\gcd(i,j)^2-1}{12ij},\qquad
 \operatorname{Var}_{\rm period}(S_c)
 \ge\frac{\|c-A_ce_1\|_2^2}{24H_y^2}.
\]

(T) is the missing sampling comparison, not a consequence of that identity.
It is false, even if kappa is allowed to depend positively on the single
pair (N,y)=(10000,100).

Here is a general construction explaining the failure. Whenever rank(R)<y-1,
choose a nonzero rational vector z in ker R. Clear denominators in
v_j=j z_j for j>=2 and put v_1=0. Let D=sum_{j>=2}|v_j| and set

\[
 c=e_1+v/D.
\]

Then S_c is constant on P, giving finite variance zero. If k is the largest
nonzero index of v, the d=k term of the Jordan factorization contributes
J_2(k)c_k^2/(12k^2)>0, giving positive full-period variance. And, for **every
integer q>=1**, not just the positive-mass cells,

\[
 W_c(q)\ge q-\sum_{j>=2}|c_j|\lfloor q/j\rfloor
          \ge q-\lfloor q/2\rfloor\ge1.
\]

This proves feasibility without repairing or inflating c_1. It also proves
sum|c_j|=2, so an upper coefficient-norm bound of 2 does not fix (T).

At N=10000, y=100, the exact counts are |Q_N|=198 and |P|=99. The saved
98-by-99 residue matrix has rank 95. The explicit witness has 42 nonzero
tail coefficients, rational denominator D recorded in the JSON, and

\[
 A_c=1,\quad S_c(q)=0\ (q\in P),\quad W_c(q)=q\ (q\in P),\quad
 \operatorname{Var}_{\rm period}(S_c)>0.
\]

Its period variance is approximately 0.00317744210; positivity is checked
as an exact rational inequality, not from this decimal. The exact integer
numerators, full rational variance, positive-mass cells and construction
are saved together. Tests independently factor every d<=10000, check all
198 attainable constraints, and evaluate every sawtooth at every positive
cell. This is a witness, not just a dimension count or an eigenvalue plot.

Prime support was used to find the vector. That is legitimate for refuting
a statement about **every feasible c**. It supplies no prime-blind
construction algorithm. The vector is unbalanced and expensive:
W_c(q)=q on P implies B_c=log(N!) by the factorial convolution. No claim
is made about a balanced subclass, optimal coefficients, a sufficiently
large N threshold, or the asymptotic optimum.

### What the same direction does to the saved low-excess certificate

Let c* be #203's saved rational N=10000,y=100 vector, and let v=c-e_1 be
the normalized tail above. On P, W_v=0, so B_{c*+tv}=B_{c*} for every real t.
However its exact allowable interval under **all Q_N constraints** is

\[
 \{t:c^*+tv\text{ is feasible}\}=[0,0].
\]

Both q=60 and q=333 have mass zero and W_{c*}=1. At q=60, W_v<0 forces
t<=0; at q=333, W_v>0 forces t>=0. The two exact rational slopes are in
the JSON. Thus this null direction cannot be used to assert failure at the
saved low-excess vector. We have tested this one direction, not the entire
four-dimensional residue nullspace or the feasible cone.

## 4. Drift is a separate obstruction, with an exact repair

For s>=2 define beta=Cov(q,S_c)/V_q=c^Th/V_q. Orthogonality to q gives

\[
 \boxed{\operatorname{Var}(W_c)
 =\operatorname{Var}(S_c-\beta q)+(A_c-\beta)^2V_q.} \tag{R}
\]

Consequently, with R_f=C_f-hh^T/V_q,

\[
 \operatorname{Var}(W_c)\ge c^TR_fc,\qquad
 \ker R_f=\{c:Uc\in\operatorname{span}(\mathbf1,t)\},\qquad
 \operatorname{rank}R_f\le\min(y-1,s-2).
\]

This is a valid finite weighted repair with constant 1 and no error term.
It removes exactly the affine part of the sampled fluctuation; its own
positive lower bound still has to be proved on the intended coefficient
class. When s=1 all variances vanish and beta is unnecessary.

An exact drift control is N=9,y=3,c=(1,-1,-1). Here
Q_N=P={1,2,3,4}, the masses are (log210,log2,log3,log2), and Psi=log2520.
Direct integer evaluation gives W_c=1 on all four cells and

\[
 A_c=1/6,\quad b^Tc=-7/12,\quad S_c(q)=q/6-5/12,\quad
 \operatorname{Var}_{\rm period}(S_c)=59/432.
\]

The period-six samples of 12 S_c are (-3,-1,1,3,-7,7). Thus the full-period
variance is positive and the **finite** sawtooth variance V_q/36 is also
positive, while the finite height variance and linear excess are both zero.
In (R), beta=A_c, and both nonnegative terms vanish. This control shows why
even a valid sampling comparison for a restricted class would still need
the drift step. The factorial check is 9!/(4!3!)=2520.

## 5. Second moments to nonnegative linear excess

For any finite positive probability measure with s>=2, let
alpha=min_q p_q, mu=E_p X and v=Var_p X, where X>=0. Since each
p_q X_q<=mu, max X<=mu/alpha. Therefore

\[
 \mathbb E X^2\le\mu\max X\le\mu^2/\alpha,\quad
 \boxed{E=\Psi\mu\ge\Psi\sqrt{\frac{\alpha}{1-\alpha}v}.} \tag{M}
\]

This provides a valid finite bridge, with the smallest-atom loss visible.
It makes no unproved shape assumption. For N>=4, every positive mass is at
least log2, and the cell q=floor(N/2) contains only d=2, with mass log2.
Thus alpha=log2/Psi exactly, and alpha/(1-alpha)=log2/(Psi-log2). For mu
versus sqrt(v), this factor shrinks as Psi grows; it is not a
scale-independent conversion of variance to mean. Without an atom or shape
bound such a conversion is false: a spike
on an atom of probability epsilon has mu/sqrt(v)=sqrt(epsilon/(1-epsilon)).

(M) is sharp within the stated feasible class already at N=4,y=2. For any
real t>=0, c=(1,t-1) has slack (0,t) on Q_4={1,2}, whose masses are
(log6,log2). Thus alpha=log2/log12,
mu=alpha t and v=alpha(1-alpha)t^2, with equality in (M).

An alternative **requires an extra hypothesis**: if 0<=X<=M with M>0,
then E X^2<=M mu and

\[
 E\ge\Psi(v+\mu^2)/M\ge\Psi v/M.
\]

Using the observed max X verifies this finite inequality but supplies no
independent analytic bound on M. A scale-independent root-variance bound
instead follows from an explicitly assumed shape estimate E X^2<=K mu^2
with K>1: E>=Psi sqrt(v/(K-1)). Such a K is not proved here.

### A finite bound after quotienting out the actual height kernel

There is also a fully explicit, though weak, coefficient estimate. For N>=4,
y>=1, choose q_0 in P, let D_W be as in Section 2, r=rank D_W>=1, and
L=||D_W||_F^2>=1. The pairwise variance identity gives

\[
 v=\tfrac12\sum_{q,r}p_qp_r(W(q)-W(r))^2
 \ge p_{q_0}\alpha\|D_Wc\|_2^2
 \ge\frac{p_{q_0}\alpha}{L^{r-1}}
       \operatorname{dist}(c,\mathcal K_W)^2. \tag{F}
\]

For the last inequality, the product of the r positive eigenvalues of
D_W^T D_W is the sum of squares of its r-by-r integer minors, hence at
least 1. Each eigenvalue is at most L, so the least positive one is at
least L^{-(r-1)}. This is an algebraic estimate, not a spectral plot.
Combining (F) with (M) gives

\[
 E\ge\Psi\alpha\sqrt{\frac{p_{q_0}}{(1-\alpha)L^{r-1}}}
       \operatorname{dist}(c,\mathcal K_W).
\]

This is a valid finite inequality for every feasible c. Its constant can
be extremely small, and feasible vectors can lie in K_W, as at N=9.
It supplies neither a useful asymptotic rate nor a positive optimum floor.
Using zero-mass rows in D_W would invalidate the proof.

## 6. Replay of existing coefficients, no new optimization

The nine 50/80-digit controls in
[finite_transfer_results.json](finite_transfer_results.json) include the
N=9 drift control, e_1, four members of the sharp N=4 family, and #203's
three unchanged rational feasible vectors. Both components of (R) and all
three centered terms of Var(W) are evaluated separately. Feasibility and
drift use exact rational arithmetic; logarithmic moments are measured.

| N | y | positive / all cells | Var(W) | residual variance in (R) | E | bound (M) |
|---:|---:|---:|---:|---:|---:|---:|
| 1000 | 31 | 40 / 61 | 0.0354190 | 0.0315120 | 41.2822 | 4.94834 |
| 10000 | 100 | 99 / 198 | 0.0441562 | 0.0357344 | 226.833 | 17.5071 |
| 100000 | 316 | 275 / 630 | 0.0311386 | 0.0287579 | 1035.23 | 46.4704 |

These values test the forms on the saved feasible coefficients. They are
not estimates of an optimum over coefficient classes, eigenvalue evidence,
or an asymptotic fit. The source archive's SHA-256 is saved with the replay.
The comparison data agree with certificate_lp_frontier/RESULTS.md Section
4.6 to its printed precision; this continuation does not audit its batch
or its interpretation of an exponent.

Reproduce from the repo root, with one thread per numerical library:

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
.venv/bin/python hunts/quotient_certificate/finite_transfer_exact.py --output /tmp/finite-transfer-exact.json
.venv/bin/python hunts/quotient_certificate/finite_transfer.py --output /tmp/finite-transfer-moments.json
.venv/bin/python -m pytest -q -n 0 -m "not slow" tests/test_quotient_finite_transfer.py
```

The construction is one fixed small exact linear-algebra calculation. It
does not solve an LP, load new numerical batches, or change old archives.
The saved final runs took 0.40 seconds for the exact construction and 6.83
seconds for nine moment checks at both precisions. The focused and governance
selection passed 40 tests with four slow tests deselected in 13.63 seconds.
The full fast suite was already green on the exact input commit in GitHub
run 34152586099; this continuation relies on that baseline plus its focused
checks, rather than rerunning the full suite locally.

Two preliminary validation attempts were stopped: an accidentally included
slow governance check after about one minute, and generic SymPy rank
simplification after 96.70 seconds. Only this session's processes were
stopped. The final rank check uses exact rational row reduction and the
final pytest command explicitly deselects slow tests. No LP or additional
CI experiment was launched, and no follow-on process is queued.

## 7. The doors

- **Active constraints:** positivity remains imposed on all Q_N. The cells
  with m_q=0 disappear from the covariance but still restrict admissible
  coefficient directions. The saved q=60,333 obstruction makes that
  distinction concrete.
- **Frozen choices:** one cutoff N, support j<=y, the existing floor
  dictionary, and the actual prime-weighted measure. No balance condition,
  alternate dual assignment, or change of norm is smuggled in.
- **Information class:** the counterexample is constructed with prime
  support; its coverage proof is arithmetic and holds on every integer.
  Prime data evaluate all finite moments. No prime-blind analytic sampling
  estimate or near-optimal coefficient construction is supplied.
- **First remaining transfer gap:** control the finite residual in (R)
  together with its drift mismatch on a precisely specified low-cost
  feasible class, retaining the zero-mass inequalities. A possible class
  for cross-review is N>=10000, y=floor(sqrt(N)), coverage on Q_N and
  B_c<=2N. No positive comparison is asserted for that class here. The
  explicit sampling-null witness lies outside it, and its direction is
  blocked at the saved low-excess vector. The full feasible cone and a
  quantitative bound on this class remain unresolved. Any subsequent
  second-moment estimate must also pay (M)'s atom loss or prove a stronger
  shape/range bound.
