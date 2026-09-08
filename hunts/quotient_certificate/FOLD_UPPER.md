# A finite upper certificate for nonnegative halving-fold gains

Continuation of PR #207 from `cce45bd`. The rational upper certificate is
supplied by the coordinator and recorded in
[fold_upper_input.json](fold_upper_input.json). The comparison witness is
the previously verified prefix-exchange gain at Fable's PR #208,
`a343fed9b396bfa32b7f415576842e8c051458b5`. This continuation neither
rechecks the 615-unit bundle nor converts the prefix-exchange witness.

Before delivery, Fable advanced to `37be52efef9520009807143c049a5fa7b1191119`.
The new [Section 11](https://github.com/teal-sea/zeta-lab/blob/37be52efef9520009807143c049a5fa7b1191119/hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/DUAL_WITNESS.md#11-the-132729535-witness-in-the-signed-fold-basis-the-excluded-move-is-the-un-fold)
was read for comparison. The upper-bound interpretation and the scope
correction in Section 3 below remain part of this lane's handoff.

**Verified statement.** Set N=10000,y=100. Include **every** attainable
source a>100, whether its initial mass is positive or zero and whether
its fold gain is positive, zero or negative. Let F have these Fold(a)
columns and let g_a=sum_q F_{qa}. Then

\[
 \boxed{\quad x\in\mathbb R_{\ge0}^{98},\quad m+Fx\ge0
 \quad\Longrightarrow\quad g^Tx\le\beta^Tm<66.339.\quad} \tag{1}
\]

The exact cost beta^Tm is enclosed by

\[
 [66.338408961958118926068407103496232250236945532,
  66.338408961958118926068407103496232250236945533].       \tag{2}
\]

Thus the entire enlarged nonnegative halving-fold family cannot attain
the saved prefix-exchange gain 26545907/200000=132.729535. The bound is
on the gains produced by this restricted family, not an upper bound on
certificate excess B_c-psi(N) or on T*-psi(N). There is no matching
lower certificate or exact restricted optimum claim, and no growth
statement in N.

The companion recurrence is complete when coefficients may be signed.
That is standard triangular algebra, proved in Section 4. It does not
extend (1) to signed coefficients or supply a rule that chooses feasible
signed exchanges.

Evidence: exact integer column inequalities and moments, fresh interval
arithmetic, independently reconstructed columns and prime products, and
independent algebra review. The finite assertion is hardened, not
formalized or externally reviewed. No novelty claim is made.

## 1. The exact domain and the fold convention

Write

\[
 Q_N=\{\lfloor N/d\rfloor:2\le d\le N\},\quad
 A_{qj}=\lfloor q/j\rfloor,\quad
 m_q=\sum_{\lfloor N/(q+1)\rfloor<d\le\lfloor N/q\rfloor}\Lambda(d).
\]

There are 198 attainable rows. The prefix {1,...,100} is contained in
Q_N. The 98 columns are indexed by H=Q_N minus that prefix: 35 have
positive initial mass and 63 have zero initial mass. None is dropped.
Nonnegativity of m+Fx is imposed on all 198 rows, including empty rows
above and inside the prefix.

For an attainable a>y the column is

\[
 F_a=-e_a+2e_{\lfloor a/2\rfloor}
       +\sum_{i\le y}(T_i(a)-T_{i+1}(a))e_i,
 \qquad T_{y+1}(a)=0,
\]
\[
 T_i(a)=\sum_{k\le y/i}\mu(k)
                  (\lfloor a/(ik)\rfloor\bmod2).       \tag{3}
\]

The destination is added to the prefix term when it is a prefix cell.
In particular, the endpoint correction is T_y(a), not a difference
with an untruncated value at y+1. Halving preserves attainability:
if a=floor(N/d)>=2, then floor(a/2)=floor(N/(2d))>=1 and 2d<=N.

The parity identity

\[
 \lfloor a/j\rfloor-2\lfloor\lfloor a/2\rfloor/j\rfloor
       =\lfloor a/j\rfloor\bmod2
\]

and prefix Mobius inversion give A^TF_a=0. All 100 moments of all 98
columns are checked as integer identities, including the empty-source
columns. Thus g^Tx=sum_q(Fx)_q is exactly the additional mass of the
perturbation. For any feasible floor certificate c, the dual measure
m+Fx gives the lower bound B_c-psi(N)>=g^Tx. Statement (1) caps the lower
bound obtainable from this cone of perturbations.

## 2. The rational certificate and the inequality signs

Let B be the 52-entry nonnegative integer vector in
[fold_upper_input.json](fold_upper_input.json), extended by zero on the
other attainable rows, and put beta=B/1387. The independent check verifies

\[
 B_q\ge0\quad(q\in Q_N),\qquad
 s_a=-1387g_a-\sum_qB_qF_{qa}\ge0\quad(a\in H).        \tag{4}
\]

There are 52 tight and 46 strict column inequalities. The largest integer
slack is 13269, at a=5000. The full 98-row check table, including each
source's initial-mass status, is saved in
[fold_upper_results.json](fold_upper_results.json).

For x>=0 with m+Fx>=0, the complete upper-bound proof is

\[
 0\le\beta^T(m+Fx),\qquad
 x^TF^T\beta\le-g^Tx,
\]
\[
 \boxed{\beta^Tm\ \ge\ -\beta^TFx\ \ge\ g^Tx.}       \tag{5}
\]

The first inequality uses row nonnegativity and beta>=0. The second
uses (4) **and x>=0**. Multiplication by arbitrary signed coordinates
does not preserve that second inequality. The strict slacks also show
that this is not a certificate satisfying F^T beta=-g for free signed
variables.

Only eight supported entries of B have positive initial mass:

| q | B_q | Exact cell product M_q |
|---|---:|---:|
| 34 | 1248 | 17*293 |
| 43 | 754 | 229 |
| 50 | 1673 | 197*199 |
| 52 | 2635 | 191 |
| 169 | 1101 | 59 |
| 204 | 3052 | 7 |
| 434 | 7629 | 23 |
| 1250 | 16456 | 2 |

Here M_q is the product of each prime base once for every prime power
in its integer cell, so m_q=log M_q. The other 44 supported entries of
B are on empty rows; they still contribute to the constraints (4).
Consequently the cost in (2) is exactly

\[
 \frac1{1387}\bigl(
 16456\log2+3052\log7+1248\log17+7629\log23+1101\log59
 +2635\log191+1673\log197+1673\log199+754\log229
 +1248\log293\bigr).                                 \tag{6}
\]

The main check groups coefficients of log p and evaluates (6) in a fresh
90-digit interval context. A separate route factors the cell integers,
forms M_q, and sums B_q log M_q/1387 in a fresh 105-digit interval
context. Both give the outward-rounded 45-decimal enclosure (2).
No approximation to m_q by interval length or N/q^2 is used.

## 3. Precisely what is excluded

The excluded family consists of **all nonnegative real combinations**
of the 98 halving folds whose final measure m+Fx is nonnegative. It
includes integer bundles with arbitrary common scale, arbitrary real
weights, negative-gain folds with nonnegative coefficients, and folds
at initially empty sources. It is larger than the earlier family that
allowed only real-mass sources.

Since the rational saved gain 26545907/200000 exceeds 66.339, no member
of this family recovers that gain. The saved gain and its prior
verification are consumed from
[the pinned prefix-exchange archive](https://github.com/teal-sea/zeta-lab/blob/a343fed9b396bfa32b7f415576842e8c051458b5/hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/results/fake_mass_N10000_y100.json).
Its coordinates and feasibility are not audited again here.

This result does not exclude arbitrary signed folds, general prefix
exchanges, other dictionaries or the full T* problem. A fold with
negative unit gain and a fold with a negative coefficient are different
notions: (1) allows the former and restricts the latter. Nothing has been
established about a rate as N varies or about equality in (1).

**Correction to the other lane's Section 11 wording.** Nonnegative folds
can deposit above the prefix through their halved destinations: F_434
contributes +2 at cell 217>100. More generally the high-row identity (7)
does not force (Fx)_q<=0 when x>=0. Thus the restriction is nonnegativity
of the fold coordinates, not an absence of all above-prefix deposits.
The value in (2) is an upper bound, not an established optimum from which
an exact gain deficit can be calculated.

## 4. Signed recurrence, including prefix reconstruction

The following argument is valid for any integer N>=2 and y>=1 for which
{1,...,y} is contained in Q_N. Let H=Q_N minus the prefix, and use **all**
folds with sources in H. Extend x by zero at indices outside H.

At a row q>y, prefix correction terms vanish, leaving only the source
and the two possible parents whose halved destination is q:

\[
 (Fx)_q=-x_q+2x_{2q}+2x_{2q+1}.                       \tag{7}
\]

Thus a prescribed supported vector delta must have

\[
 \boxed{x_q=2x_{2q}+2x_{2q+1}-\delta_q\quad(q\in H)}. \tag{8}
\]

Evaluate in descending q. Parents are strictly larger than q, and
missing indices have coefficient zero, so this defines a unique finite
solution on the high rows. With rows and columns in decreasing order,
the high-row submatrix of F is lower triangular with diagonal -1.

Suppose now that A^T delta=0. Equation (8) makes
h=delta-Fx supported entirely on the prefix. Since A^TF=0, it also has
zero moments. The prefix matrix

\[
 A_0=(\lfloor i/j\rfloor)_{1\le i,j\le y}
\]

is unit lower triangular. Hence A_0^T h=0 forces h=0. This proves full
reconstruction, including the prefix, rather than merely agreement on
the rows above y.

The folds therefore form a basis of ker(A^T) over the reals or rationals.
Their high-row matrix is unimodular, so they also form an integer basis
of ker(A^T) intersected with the integer lattice. Integer delta gives
integer x directly in (8). If H is empty, the prefix matrix makes the
kernel zero and the empty basis statement remains valid.

The checker rejects vectors with nonzero moments; adding a prefix error
does not become a valid reconstruction simply because the high rows
are unchanged. Independent tests also reconstruct all 98 alternative
zero-moment vectors e_a minus the prefix expansion of the full row a,
and one exact rational signed combination. These are algebra controls,
not new feasible witnesses or a conversion of Fable's saved witness.

**Scope consequence.** Every supported perturbation with zero moments
has signed fold coordinates. Therefore the previously verified
132.729535 perturbation must have at least one negative fold coefficient:
if all were nonnegative, it would contradict (1). This determines no
individual coefficient and supplies no capacity bound for chosen signed
coefficients. The final requirement m+Fx>=0 remains indispensable.

This is standard triangular algebra. It supplies a complete coordinate
system, not the missing arithmetic estimate or a selection rule for
useful signed exchanges.

## 5. Checks, manifest and remaining scope

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
.venv/bin/python hunts/quotient_certificate/fold_upper.py \
  --output /tmp/fold-upper.json --manifest /tmp/fold-upper-manifest.json
.venv/bin/python -m pytest -q -n 0 -m "not slow" tests/test_quotient_fold_upper.py
```

The saved checker run took 0.073 seconds with one numerical thread. Its
[computation manifest](fold_upper_manifest.json) records the exact input
and source checksums, software versions, command, commit and dirty state,
arithmetic conventions, output checksum and limits. The manifest passed
the mathbox computation-audit schema check. Negative B and a zero-vector
false certificate are rejection controls; nonzero prefix residuals and
missing prefix or halved cells must also be rejected.
The seven focused tests passed in 1.94 seconds after the final manifest
update. The governance selection passed 29 tests in 4.99 seconds, with
four slow tests deselected. Independent algebra review passed.

**Doors.** The finite upper certificate is complete for the nonnegative
fold family at N=10000,y=100. The signed completeness statement is proved
under the explicit attainable-prefix assumption. No matching optimum,
signed capacity construction, witness-coordinate identification or
asymptotic estimate is supplied. Those are not hidden inside a change of
coordinates. The remaining research step is an arithmetic choice of
signed exchanges with a proved final capacity bound, owned by the other
lane. No optimizer, larger-N batch, background research job, old bundle
recheck or queued follow-on run is used. Prior archives and Fable's files
remain untouched; both PRs remain open.
