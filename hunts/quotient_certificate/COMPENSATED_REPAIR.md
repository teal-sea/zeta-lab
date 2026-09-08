# A quantitative repair lemma and the fixed compensated-fold bundle

Continuation of PR #207 from `02e6780`. The consumed definition is Fable's
[PR #208, Section 8](https://github.com/teal-sea/zeta-lab/blob/f4ae24f027f07916037ca8fe6c56c95a29cbf4d7/hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/DUAL_WITNESS.md#8-one-prescribed-family-halving-folds-and-exactly-where-it-fails)
and `fold_family.py` at `f4ae24f027f07916037ca8fe6c56c95a29cbf4d7`.
This reads the new fold construction, beyond the prefix exchanges consumed
in [TRANSPORT_CAPACITY.md](TRANSPORT_CAPACITY.md).

**Result.** A prescribed collection of repairs with contractive secondary
empty-cell deficits has an explicit finite total repair budget. This
budget controls both the capacity spent at positive-mass cells and any
gain sacrificed by repairs. The proof below gives the coefficients; it
does not assume that the completed bundle is feasible.

The coordinator's fixed bundle is the one-block case with no secondary
deficits or gain loss. At N=1000,y=31 it gives the exact bound

\[
 E_c=B_c-\psi(N)\ge\frac{10}{3}\log7
 \in[6.486367163517711017017842478143,
      6.486367163517711017017842478144]                 \tag{1}
\]

for every feasible certificate. This is a finite example, not a new best
bound or a scaling result. The three source labels are supplied data, not
a rule for other N. Both PRs stay open, and earlier results are preserved.

Evidence: exact integer identities and product comparisons, independent
triangular reconstruction and factorization, interval enclosures and an
independent mathematical review. This is hardened evidence, not a
formalized proof or external verification. No novelty claim is made.

## 1. Fixed definitions and the independently checked bundle

Retain every attainable cell Q_N={floor(N/d):2<=d<=N}, including empty
cells. Put A_{qj}=floor(q/j), m_q=sum Lambda(d) over its exact integer
cell, Z={q:m_q=0}, and P=Q_N minus Z. For any supported zero-moment
perturbation H with m+H>=0, finite duality gives

\[
 E_c\ge\sum_qH_q\qquad\text{whenever }W_c=Ac\ge1.
                                                               \tag{2}
\]

No cost cap or balance condition is used here.

Assume the prefix {1,...,y} is attainable. Fable's fold at an attainable
a>y is

\[
 F_a=-e_a+2e_{\lfloor a/2\rfloor}
          +\sum_{i=1}^y\kappa_i(a)e_i,\quad
 \kappa_i=T_i-T_{i+1},\quad T_{y+1}=0,
\]
\[
 T_i=\sum_{k\le y/i}\mu(k)(\lfloor a/(ik)\rfloor\bmod2).
                                                               \tag{3}
\]

The halved cell is attainable since floor(floor(N/d)/2)=floor(N/(2d)).
If that destination is inside the prefix, its +2 is added to the prefix
coefficient. At the endpoint, kappa_y=(floor(a/y) mod 2); there is no
subtraction of a fictitious T_{y+1} value from an untruncated sum.

The moment defect of the first two terms is the negative of the parity
vector (floor(a/j) mod 2). Mobius inversion in the unitriangular prefix
basis gives (3), hence

\[
 A^TF_a=0,\qquad g(a):=\sum_q(F_a)_q
 =1+\sum_{j\le y}\mu(j)(\lfloor a/j\rfloor\bmod2).
\]

Our check independently solves that triangular system by back substitution
and verifies all 31 moments of each consumed fold. Only these exact fold
identities are consumed, not an assumed square-root size for g(a).

At N=1000,y=31, set

\[
 U=F_{76}+2F_{200},\quad R=F_{333},\quad D=U+R.
\]

The gains are g(76)=2, g(200)=4, g(333)=0, so sum U=sum D=10. The crucial
entries, retaining every multiplicity, are:

| Cell | Real mass | F_76 | F_200 | F_333 | D |
|---|---|---:|---:|---:|---:|
| 19 | 0 | -1 | 0 | 1 | 0 |
| 25 | 0 | 1 | -1 | 1 | 0 |
| 20 | log7 | 0 | -1 | -1 | -3 |

There are 61 attainable cells, of which 21 have zero mass. The only
negative entries of U on Z are U_{19}=U_{25}=-1. R is nonnegative on
**all** Z and equals one on both deficit cells. In particular, its empty
destination 166 receives two; it is not removed from the dual support.

For M_q equal to the product of prime bases over the prime powers in
cell q, m_q=log M_q. Every negative coordinate of D satisfies

\[
 M_q^3\ge7^{-D_q},                                    \tag{4}
\]

with equality only at q=20. Its cell consists of d=48,49,50 and only
49=7^2 contributes. Thus m+(log7/3)D>=0 on all Q_N, and its scale
log7/3 is maximal for this fixed direction: any larger scale makes cell
20 negative. Equations (2) and sum D=10 give (1).

Fold(333) was excluded by the earlier source filter g(a)>0. Its zero gain
is compatible with a useful repair here. This does not establish that
zero-gain moves are necessary for successful constructions in general.

## 2. Conditional lemma: repair budgets from a contraction

The lemma applies to any fixed finite N,y and its actual measure m. It
can be used with prescribed finite bundles of (3). Let U,R_1,...,R_r be
supported on Q_N and have zero moments. They are the seed and prescribed
repair components, whose gains may have either sign. Choose disjoint
nonempty blocks Z_1,...,Z_r of empty cells. Every empty cell outside these
blocks must have U_q>=0 and (R_i)_q>=0 for every i.

The following are **hypotheses on individual components and their
interaction**, not on the feasibility of the completed bundle.

1. Repair R_i supplies at least one unit at every cell in its own block.
   On another block Z_k it supplies at least -C_{ki}, where C>=0 and
   C_{ii}=0. Define d_k=max_{q in Z_k}(-U_q)_+.
2. There are prices p_i>0 and 0<=rho<1 such that
   \[
   \sum_k p_k C_{ki}\le\rho p_i\quad\text{for every }i. \tag{5}
   \]
   Thus a repair's priced secondary deficits cost at most rho times its
   own price. This permits cycles, provided they contract in this norm.
3. On every positive-mass cell q, including sources, there are
   nonnegative envelopes b_0(q),b(q) such that
   \[
   (-U_q)_+\le b_0(q),\qquad (-(R_i)_q)_+\le p_i b(q).
                                                               \tag{6}
   \]
4. The seed gain is at least G_0, and each repair's gain is at least
   -ell p_i for some ell>=0. Positive repair gains can be retained for a
   sharper calculation, but are not needed for this lower bound.

Put

\[
 S=\frac{\sum_i p_i d_i}{1-\rho},\qquad
 t=(I-C)^{-1}d,\qquad D=U+\sum_i t_iR_i.                \tag{7}
\]

Then t exists, is nonnegative, and p^Tt<=S. The vector D has no negative
entry on any empty cell. If K>0 satisfies

\[
 b_0(q)+Sb(q)\le K m_q\quad(q\in P),                  \tag{8}
\]

then m+D/K is a nonnegative measure with the required moments, and

\[
 \boxed{E_c\ge\frac{G_0-\ell S}{K}.}                  \tag{9}
\]

For a positive bound require G_0>ell S. Neither a zero nor a negative
repair gain is silently discarded from this requirement.

**Proof.** From (5), p^TC^nd<=rho^n p^Td. Thus the nonnegative series
t=sum_{n>=0}C^nd converges with p^Tt<=S and satisfies t=d+Ct. It also
proves invertibility, since C is a contraction in the weighted l1 norm.
For q in Z_k, the component bounds give

\[
 D_q\ge-d_k+t_k-\sum_i C_{ki}t_i=0.
\]

The remaining empty cells are nonnegative by hypothesis. On P, (6) gives

\[
 (-D_q)_+\le(-U_q)_++\sum_i t_i(-(R_i)_q)_+
           \le b_0(q)+b(q)p^Tt\le b_0(q)+Sb(q)\le Km_q.
\]

Hence m+D/K>=0. Zero moments are preserved, and
sum D>=G_0-ell p^Tt>=G_0-ell S, proving (9) by (2).

This is an explicit sufficient repair rule with a proved bound on its
total amount and loss. It replaces an unbounded cascade of newly created
deficits by (7); it does not optimize over final feasible measures. The
series is a mathematical proof, not a queued iterative computation.
Conditions (5) and (8) are sufficient, not necessary for a successful
bundle. Grouping cells lets one repair fill several deficits at once.

## 3. The lemma attains the fixed bundle's full capacity

For the supplied U and R use the single block Z_1={19,25}. Then
d=p=t=1, C=0, rho=0, S=1, G_0=10, ell=0. All other empty cells meet the
nonnegativity requirement. In particular, no secondary deficit is hidden
outside the block.

On P take the gross envelopes

\[
 b_0(q)=(-U_q)_+,\qquad b(q)=(-R_q)_+.
\]

These deliberately discard positive-cell refills when bounding the
withdrawal. There are 18 positive-mass cells where b_0+b is nonzero. At
each one the stronger integer comparison

\[
 M_q^3\ge7^{b_0(q)+b(q)}                              \tag{10}
\]

holds, again with equality only at q=20. Taking logarithms proves (8)
with K=3/log7. Thus the conditional lemma itself gives (1), with no loss
relative to the exact final capacity (4). This is more than checking the
final net vector: even the sufficient component envelope in the proof
passes. Equation (10) is a finite arithmetic check, not a bound on prime
mass assumed from interval length.

The adjacent test also exercises nonzero secondary deficits and strictly
negative repair gains in an abstract four-row, one-moment example. Its
matrix has C_{12}=1/4, C_{21}=1/2, p=(1,1), rho=1/2, d=(1,1),
t=(10/7,12/7), S=4. The repair gains are -1/2 and -7/4. It verifies the
loss term in (9) rather than testing only the zero-loss special case. It
is a rational algebra control, not another prime-mass experiment.

## 4. What would turn this into a quantitative family

The proved statement is the implication (5)-(8) to (9). Selecting the
repairs remains Fable's construction task. For a prescribed family at
y=floor(sqrt N), a sufficient set of uniform estimates would be

\[
 G_0\ge g_0 N/\sqrt y,\qquad
 \ell\frac{p^Td}{1-\rho}\le(1-\eta)G_0,\qquad
 b_0(q)+\frac{p^Td}{1-\rho}b(q)\le K_0m_q,            \tag{11}
\]

where g_0,K_0>0 and 0<eta<=1 are constants and (5) holds with rho<1.
They would give E_c>=eta g_0 N/(K_0 sqrt y). Nonuniform estimates give
exactly the lower bound in (9), using their actual parameters. No estimate
in (11) is inferred from the one bundle or from fitted parity fluctuations.

**First unproved arithmetic step:** produce a prescribed repair selection
and block structure whose empty-cell interaction satisfies a quantitative
contraction (5) with controlled total budget S. The labels 76,200,333 do
not supply that selection for other N. Even after that step, retaining
enough gain and proving (8) against actual prime masses are separate
obligations. A contraction alone could require expensive repairs or lose
all the original gain.

All prime information needed is explicit: the exact zero set for the
block conditions and the positive masses for (8). No replacement
m_q approximately N/q^2, lower bound from cell length, or assumed
short-interval prime density enters the proof. For a prime-blind analytic
construction, these component and mass estimates would themselves need
arithmetic proofs with stated errors. The finite product checks at N=1000
are not those proofs.

## 5. Reproduction and boundaries

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
.venv/bin/python hunts/quotient_certificate/compensated_repair.py --output /tmp/compensated-repair.json
.venv/bin/python -m pytest -q -n 0 -m "not slow" tests/test_quotient_compensated_repair.py
```

[compensated_repair_results.json](compensated_repair_results.json) saves
all three folds, all empty-cell profiles, the final bundle, both sets of
integer product checks and outward-rounded interval endpoints. The script
checks one prescribed bundle and reports every completed or failed run.
It took 0.006 seconds with one numerical thread. The six focused tests
and governance selection passed 35 tests, four slow tests deselected, in
20.17 seconds. Independent tests use integer factorization, triangular
inversion and a 110-digit value of (1).

**Doors.** All 61 attainable cells and accumulated changes are retained;
sources and empty destinations share the same measure. The only numerical
prime instance is N=1000,y=31. There is no search for bundles, optimizer,
larger-N batch, background job or queued follow-on run. The full exact
capacity and a conditional repair-budget argument are delivered; a
uniform prescribed arithmetic family remains unproved. Prior archives
and Fable's files are untouched.
