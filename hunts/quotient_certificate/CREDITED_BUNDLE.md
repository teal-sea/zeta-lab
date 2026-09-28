# The supplied N10000 bundle fits the repair lemma after regrouping

Continuation of PR #207 from `d79fe15`. The other lane's current input is
[PR #208, Section 9](https://github.com/teal-sea/zeta-lab/blob/0eb39186334612b3e55db315758c49ab87a29763/hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/DUAL_WITNESS.md#9-compensated-folds-the-coordinators-bundle-the-band-lemma-and-a-prescribed-repair-rule)
at `0eb39186334612b3e55db315758c49ab87a29763`, including Rule C and its
reported failure at cell 33. The supplied weighted bundle below repairs
that seed at this finite input. No Rule C run or original LP is repeated.

Before delivery, the other lane advanced to `a343fed9b396bfa32b7f415576842e8c051458b5`.
Its new [Section 10](https://github.com/teal-sea/zeta-lab/blob/a343fed9b396bfa32b7f415576842e8c051458b5/hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/DUAL_WITNESS.md#10-the-compensated-bundle-at-104-100-why-rule-c-misses-it-and-the-credit-identity)
was read for comparison: its credit identity and finite capacity agree
with the independent checks below. The original fold/Rule C input remains
pinned at `0eb3918`.

**Completed argument.** At N=10000,y=100 the fixed bundle has zero moments,
no empty-cell withdrawal and exact maximal scale log(229)/146. Moreover,
the existing [repair lemma](COMPENSATED_REPAIR.md#2-conditional-lemma-repair-budgets-from-a-contraction)
applies with seed V=Fold(103) and one grouped repair R=D-V. Its parameters
are explicit, and its component capacity envelope retains the full scale.
Keeping the known positive gain of R gives

\[
 E_c\ge\frac{615}{146}\log229
 \in[22.888623508122310847886026687798,
      22.888623508122310847886026687799].                \tag{1}
\]

This holds for every c with W_c(q)>=1 on all 198 attainable cells. A cost
cap and balance condition are unnecessary. It is a finite bound, not a
new best bound or a parameterized construction. The coordinator supplied
the coefficients from a small feasibility LP; this continuation verifies
them by integer arithmetic and applies the existing lemma. It does not
derive the coefficients by an arithmetic selection rule.

Evidence: exact moments, integer product comparisons, independent
triangular reconstruction and factorization, interval enclosures and an
independent mathematical review. The evidence is hardened; the result has
not been formalized or externally reviewed. Both PRs remain open.

## 1. Precisely which vector is checked

Use the exact Q_N, prime masses m_q and floor matrix A_{qj}=floor(q/j).
Write Z={q:m_q=0}. Every cell, including zero-mass destinations, remains
in the measure. Fold(a)=F_a uses (3) of
[COMPENSATED_REPAIR.md](COMPENSATED_REPAIR.md), including T_{y+1}=0 and
the added destination coefficient when floor(a/2) lies in the prefix.

Among the 35 attainable real-mass cells a>100, the prescribed filter
g(a)=sum F_a>0 selects exactly these 28 sources:

```
103, 112, 120, 123, 126, 136, 140, 149, 156, 163, 169, 188,
204, 270, 312, 322, 344, 370, 434, 526, 625, 769, 909, 1111,
1428, 2000, 3333, 5000
```

Let U be one copy of each selected fold. Then sum U=91. Define the
additional repair H and the full bundle by

\[
 H=57F_{163}+7F_{232}+5F_{270}+74F_{434}
       +40F_{625}+22F_{1250}+12F_{2500}+4F_{5000},
 \qquad D=2U+H.                                      \tag{2}
\]

Sources appearing in both U and H have their multiplicities added.
There are 31 distinct folds in D. Every source has positive real mass,
every fold is supported on Q_N, and all 100 moments of each fold vanish
exactly. Thus A^TD=0 independently of capacity or gain calculations.

The signed gain account is:

| Additional source a | Multiplicity | g(a) | Contribution |
|---|---:|---:|---:|
| 163 | 57 | 1 | 57 |
| 232 | 7 | -5 | -35 |
| 270 | 5 | 1 | 5 |
| 434 | 74 | 5 | 370 |
| 625 | 40 | 1 | 40 |
| 1250 | 22 | 0 | 0 |
| 2500 | 12 | -1 | -12 |
| 5000 | 4 | 2 | 8 |

The additional positive gain is 480, its loss is 47, and sum H=433.
Consequently sum D=182+433=615. The negative and zero gain components
have not been excluded from the capacity calculation.

## 2. The credits and the exact direct capacity

There are 99 initially empty cells. The exact empty-cell profiles are
saved in [credited_bundle_results.json](credited_bundle_results.json).
In particular:

| Empty cell | 2U | H | D | V=F_103 | R=D-V |
|---|---:|---:|---:|---:|---:|
| 33 | -22 | 22 | 0 | -1 | 1 |
| 54 | 2 | -2 | 0 | 0 | 0 |
| 62 | 4 | -4 | 0 | 0 | 0 |
| 100 | 42 | 69 | 111 | 1 | 110 |

All other empty cells also have D_q>=0. Cells 54 and 62 are the only
empty cells where H is negative: their original seed credits are spent
exactly. Discarding those credits would falsely reject (2).

Let M_q be the product of the prime base p once for each prime power
p^k in cell q. Then m_q=log M_q exactly. For all 51 negative coordinates
of D, the independent checks give

\[
 M_q^{146}\ge229^{-D_q},                              \tag{3}
\]

with equality only at q=43. Its integer cell is {228,...,232}; only the
prime 229 contributes, so m_{43}=log229 and D_{43}=-146. Therefore

\[
 m+\lambda D\ge0\quad\text{at}\quad
 \lambda=\frac{\log229}{146}
 \in[0.037217273996946846907131750711,
      0.037217273996946846907131750712].
\]

Any larger scale makes cell 43 negative. For a feasible certificate,
A^T(m+lambda D)=A^Tm gives B_c>=(sum m)+lambda sum D. This proves (1)
directly, using the actual measure rather than an interval-length proxy.

## 3. Why retaining 2U as the lemma's seed fails

This is a limitation of that sufficient decomposition, not a rejection
of the bundle. In the existing lemma let J=sum_i t_i R_i be the total
added repair, where t=d+Ct and d>=0. On a protected empty block Z_k,
its hypotheses imply

\[
 J_q\ge t_k-\sum_i C_{ki}t_i=d_k\ge0.
\]

Outside the protected blocks, each repair is required to be nonnegative.
Thus every output of that lemma has J_q>=0 on **every** empty cell. With
a fixed seed 2U, its output must satisfy D_q>=2U_q on Z.

The specified D violates that necessary property at 54 and 62, where
H is respectively -2 and -4. No grouping of H alone, no choice of prices
and no contractive matrix satisfying the existing hypotheses can produce
this D while retaining all of 2U as the seed. In a one-component attempt,
H already violates nonnegativity outside deficit blocks at those cells;
placing them inside a block does not evade the displayed consequence.

This identifies exactly which hypothesis is too restrictive: the lemma
forces the aggregate repair to be nonnegative on empty cells and cannot
spend positive credits left in its seed. Its hypotheses are sufficient,
not necessary. The direct net-capacity argument in Section 2 retains the
credits and passes.

## 4. An explicit decomposition that does satisfy the existing lemma

Take the first profitable fold in the supplied seed list as V=F_103 and
group every remaining supplied term into

\[
 R=D-F_{103}=(2U-F_{103})+H.                           \tag{4}
\]

This removes one of the two supplied copies of F_103 from the group; all
remaining fold multiplicities stay nonnegative. No coefficient of D is
changed, and no new bundle is selected.

The only nonzero empty-cell entries of V are V_{33}=-1 and V_{100}=1.
The table above gives R_{33}=1 and R_{100}=110; on every other empty cell
R equals the already checked D and is nonnegative. In particular, both
the positive credits and their matching withdrawals at 54 and 62 are
inside the same zero-moment component R, yielding R_{54}=R_{62}=0.

The existing lemma's complete block and price data are

\[
 Z_1=\{33\},\quad p_1=1,\quad C=[0],\quad\rho=0,
 \quad d_1=1,\quad t_1=(I-C)^{-1}d_1=1,\quad S=1.      \tag{5}
\]

V is nonnegative on every other empty cell, and R is nonnegative on all
of them. Its own block receives one unit, as required. Thus all the
empty-cell repair hypotheses hold, without dropping the seed credits.

For every positive-mass cell use the component envelopes

\[
 b_0(q)=(-V_q)_+,\qquad b(q)=(-R_q)_+.
\]

There are 52 cells with b_0+b>0. Exact integer comparison proves

\[
 M_q^{146}\ge229^{b_0(q)+b(q)}
 \quad\Longrightarrow\quad
 b_0(q)+Sb(q)\le\frac{146}{\log229}m_q.               \tag{6}
\]

Equality occurs only at cell 43, where V_{43}=0 and R_{43}=-146.
Hence K=146/log229 in the lemma, and even its conservative component
envelope retains the exact full scale from Section 2.

**Gain must be retained explicitly.** The regrouped seed has gain 3 and
the repair has gain 612=179+480-47. Thus G_0=3 and ell=0 satisfy the
lemma's gain hypotheses. The boxed bound (G_0-ell S)/K alone would give
only 3/K: it deliberately discards positive repair gain. Keeping the
known term t_1 sum R=612 in the same proof gives

\[
 E_c\ge\frac{\sum V+t_1\sum R}{K}
       =\frac{3+612}{146/\log229},
\]

which is (1). The seed gain has not been silently relabeled as 615.

This is a verification decomposition of the supplied bundle. Since R
uses its full known combination, (4) is not an arithmetic rule that
constructs repairs for new inputs. No new abstract repair lemma is needed.

## 5. Proved scope and the first remaining gap

The finite input is settled: the full prescribed seed has a weighted
repair, including its lower-half deficit at 33. The direct measure and
the regrouped application of the existing lemma both give (1), with the
exact maximal scale for this direction. Rule C's reported stopping
condition does not imply absence of weighted repairs at this input.

The first remaining gap is an arithmetic derivation of a prescribed
weighted combination or equivalent grouping, with controlled capacities
and retained gain on a stated parameter domain. The known bundle and its
regrouping prove none of those uniform estimates. A lower-half supply
question can remain open without being called insufficient here for
every possible bundle. Selecting or simplifying the family remains the
other lane's task.

The only prime assumptions in this argument are evaluated finite facts:
the exact zero set, positive source masses and products M_q. No estimate
of m_q by N/q^2 or unproved short-interval prime hypothesis is used.

## 6. Reproduction and boundaries

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
.venv/bin/python hunts/quotient_certificate/credited_bundle.py --output /tmp/credited-bundle.json
.venv/bin/python -m pytest -q -n 0 -m "not slow" tests/test_quotient_credited_bundle.py
```

The saved fixed run took 0.142 seconds with one numerical thread. It
reports one requested and completed bundle, all 198 cells, the 99 empty
profiles, both sets of integer product comparisons, all signed gains and
the lemma parameters. Tests independently factor integers through 10000,
solve each used parity vector by triangular back substitution, check the
old decomposition's credit obstruction and the new decomposition's full
hypotheses, and compare interval values with 110-digit evaluations.
The six focused tests passed in 6.20 seconds; 29 governance tests passed
in 11.50 seconds, with four slow tests deselected. Independent review of
the proof and its finite-scope boundary passed.

**Doors.** All attainable cells, original seed credits, prefix endpoint
and accumulated changes remain in the calculation. This is one supplied
N=10000,y=100 bundle. There is no duplicate bundle search, LP, larger-N
batch, background research job or new lane. Prior results and Fable's
files remain untouched. Both PRs stay open; no merge or follow-on run is
queued.
