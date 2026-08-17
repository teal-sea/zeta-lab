# Reimplementation and audit of Bian's F_kappa(alpha,T) coefficient computation

**Status: exploratory hunt record. Nothing here is a theorem about zeta
zeros; every claim below is a statement about finite combinatorial
quantities, checked exactly in rational arithmetic, or about asymptotics of
explicit prime sums under the standard prime number theorem. Everything
sits under RH and under the hypotheses of Bian's Theorem 1 (in particular
his truncation structure with the parameter B); see "Scope and
inheritance" at the end.**

Date: 2026-08-17. Source: Ji Bian, *The Pair Correlation of Zeros of
xi^(kappa)(s)*, PhD thesis, University of Rochester, 2008 (advisor
S. Gonek). All page references are to the printed pagination.

## What this directory contains

| file | content |
|---|---|
| `bian_mathematica.txt` | faithful transcription of the complete Mathematica source, Appendix A (pp. 99-153) |
| `bian_engine.py` | exact Python reimplementation (Fraction arithmetic): a literal port used as oracle, plus a fast signature-based engine; three evaluation modes (`skip`, `zero`, `corrected`); two assemblies (`coefficient` = eq (10.1), `coefficient_figure` = the thesis code's `cinfiopkapa`) |
| `validate_pairs.py` | independent symbolic recomputation of the constants C(v,w) from the defining recursion (3.6) plus the thesis's own Lemma 8; battery of 20 pairs |
| `validate_numeric.py` | sieve-based numerical check of S(v,w;x) against candidate leading constants |
| `analyze.py` | structure analysis of the extended tables (growth, recurrences, factorizations, OEIS queries) |
| `closed_form.py` | closed generating identity for the corrected C(v,w), machine-checked against the symbolic route |
| `coefficients.json` | checkpointed extended tables, per evaluation mode |

## 1. What was reimplemented

Bian computes, under RH, the pair correlation form factor of the zeros of
the kappa-th derivative of xi,

    F_kappa(alpha,T) = (1+o(1)) T^{-2|alpha|} log T
                     + sum_{i=1}^{2 kappa B + 1} C_{kappa,i} |alpha|^i
                     + o_{kappa,B}(1),      |alpha| < 1,

with (his eq (10.1), for i >= 3)

    C_{kappa,i} = 2^{i-1} sum_{l,k >= 1} (-1)^{l+k}
                  sum_{|v_l|+|w_k| = i-1} theta(v_l,w_k) C(v_l,w_k),

where v_l, w_k run over integral vectors with components in {1..kappa},
theta(v,w) = [max(l,k) <= min(|v|,|w|)], and C(v,w) is the 14-fold
combinatorial sum of his eq (7.8), built on the inner constant
C(alpha,beta,alpha',beta') of eq (6.23). C_{kappa,1} = 1 and
C_{kappa,2} = -4 are universal (his Lemma 12); they come from analytic
main terms outside this machinery and are carried as constants here, as
Bian carried them.

The reimplementation has two independent layers that are cross-checked
against each other (literal port vs fast engine: exact agreement on every
tested case, see `--selftest`), and four exact algorithmic reorganisations
in the fast layer (permanent collapse of the double permutation sum,
multinomial aggregation of the E-matrix sums, kappa-independence of
C(v,w), and signature caching). The fast engine reaches Bian's 2008
endpoint (the full Figure 10.1 grid, i <= 11, kappa <= 9) in about 0.2
seconds, and i = 20 in under an hour on one core.

## 2. Validation: the published table is reproduced exactly

The OCR-recovered Figure 10.1 grid (99 cells, kappa = 1..9, i = 1..11) is
reproduced **cell for cell, exactly, in rational arithmetic**, by:

    mode "skip"  +  assembly `coefficient_figure` (= the code's cinfiopkapa)

together with three side checks:

* the kappa = 1 row equals the Farmer-Gonek closed form
  |a| - 4a^2 + sum_k ((k-1)!/(2k)!)(2|a|)^{2k+1} exactly (this row is the
  only externally validated one; Farmer-Gonek, arXiv:0803.0425, treats
  xi');
* Lemma 12 stabilisation (C_{kappa,i} = C_{i-2,i} for kappa >= i-2) holds
  exactly, with the observed onsets matching the grid;
* the literal Mathematica port and the fast engine agree.

So the transcription and the reimplementation are faithful: whatever the
thesis code computed, this code computes.

## 3. The audit: what the thesis code computes is not eq (10.1), and eq (6.18) itself overcounts

**The suspected (6.23) discrepancy dissolves.** The starting question was
whether the printed binomial symbols (beta_i over c_i) in (6.23) (which
would suggest a division by (beta_i - c_i)!) disagree with the code's
`prodfacvec[beta1]/prodfacvec[c]`. They do not: (6.14) constrains c_i to
E_{alpha_i}(beta_i), i.e. |c_i| = beta_i, so the symbol is the
multinomial beta_i!/(c_{i,1}! ... c_{i,alpha_i}!), which is exactly the
code's ratio. There is no numerical difference on that point. The real
divergences are elsewhere.

The reproduction exposed three separate defects. Each is pinned by a
finite, exactly checkable witness; none of them touches the kappa = 1 row,
which is exactly the row with an independent check in the literature.

### Defect A (assembly): `coffdiagkapa` truncates the (10.1) sum

`ctablefull` computes C_{kappa,i} as `cdiagkapa + coffdiagkapa`, which was
clearly intended to equal the full double sum of (10.1) via the l,k
symmetry. But the off-diagonal loop runs j from i+1 to floor((n-i)/2)
(printed p. 151) where matching (10.1) requires j up to floor((n-1)/2).
First dropped pair: (l,k) = (2,3) at i = 7, and

    consikapa(6,2,3,kappa=2) = C((1,2),(1,1,1)) + C((2,1),(1,1,1)) = 1/30  (nonzero).

Hence `finalconsikapa` (his own direct implementation of (10.1), which
appears in the same appendix) and `cinfiopkapa` (which generated Figure
10.1) disagree from i = 7 on. In the skip mode of this engine:

    C_{2,7}: figure 544/45, eq (10.1) 352/45  (delta -64/15)

and analogous kappa-stable deltas at i = 9, 10, 11 (delta = 0 at i = 8;
at kappa = 1 all off-diagonal terms vanish by theta, so that row is
immune). The published Figure 10.1 columns i in {7, 9, 10, 11} for
kappa >= 2 are therefore not the coefficients of his own expansion
(10.1) even granting his other conventions.

### Defect B (phantom slots): the code evaluates terms that are exactly zero as nonzero

In (7.8) the extra unit vector f (which distributes the final log n of
the last convolution link) ranges over all V_l = ceil(v_l/2) positions of
the last block, including positions beyond the support of the chosen
composition. Such a "phantom" position s has alpha_s = 0: its convolution
slot is forced to d_s = 1, and the term carries log^{1}(d_s) = log(1) = 0.
The literal printed (6.23) agrees: c_s ranges over E_0(1) = empty set, so
the term vanishes. Bian's `fulllist`/`fulllistkapa` instead **skip** the
alpha_s = 0 block (`If[alfa[[i]] == 0, Continue[]]`), which evaluates the
term as a nonzero quantity.

Finite witness: for every j, b_j(p) = (-1)^j log^j p on primes and
B((1),n) = -Lambda(n) log n is supported on prime powers, so

    S((j),(1);x) = (-1)^{j+1} sum_{p<=x} log^{j+3} p + O(sqrt(x) log^{j+3} x),

i.e. |C((j),(1))| = 1 exactly. The skip convention gives 6/5 (j=3),
7/6 (j=4), 9/7 (j=5). The zero reading gives 1 for all j. First effect on
the table: i = 5, kappa = 3 (published 332/5; zero reading gives 60,
before the further correction below).

### Defect C (normalization): eq (6.18) overcounts each side by prod_i alpha_i!

(6.18) expands Lambda_alpha log^beta(n) over all sigma in S_m (m = |alpha|)
while also carrying the factors alpha_i! from (6.13). The sigma-sum
already enumerates every assignment of the primes to the blocks
prod_i alpha_i! times (the within-block order is immaterial because the
inner c-sum is symmetric), so each side is overcounted by
prod_i alpha_i!. Finite witness at n = 6, alpha = (2), beta = (1):

    Lambda_2(6) log 6 = 2 log2 log3 log6,   printed (6.18) RHS = 4 log2 log3 log6.

The overcount factor prod_i alpha_i! prod_i alpha'_i! propagates verbatim
into (6.23) and into `cons4vec` (the factor `prodfacvec[alfa1]
prodfacvec[alfa2]` in `cons2`). It equals 1 exactly when every flat
alpha-entry is <= 1, which covers the whole kappa = 1 row: the one
externally checkable row cannot see it. First effect on the table: i = 5,
kappa = 2 (via C((2),(2))).

### The corrected constants, validated two independent ways

Mode `corrected` = zero reading + removal of the alpha-factorial
overcount (in `cons4_sig`, F0 uses prod b! instead of prod a! b!).

Validation 1 (symbolic, independent of all of ch. 6-7): on the squarefree
slice n = p_1...p_m, B(v,n) is computed directly from the defining
recursion (3.6) by set-partition convolution (sympy, exact); B(v,.)B(w,.)
is homogeneous of degree |v|+|w|+2 in the log p_i; the standard
multi-prime asymptotic (= the thesis's own Lemma 8, whose 1/m! is
correct) then gives the true C(v,w) as a finite rational sum over
monomials. On a battery of 20 pairs (components up to 5, dimensions up to
3), `corrected` agrees with this route **on every pair**; `skip` and
`zero` disagree on every pair containing a component >= 2 (overcount)
resp. >= 3 (phantom). See `validate_pairs.py` output.

Validation 2 (numerical): sieve computation of S(v,w;x) to x = 10^7 from
the b_j recursion, sliced by omega(n) on squarefree n, against exact
smoothed prime integrals (sympy-exact polynomial integration). Slice
ratios: omega = 1: 0.9995; omega = 2: 0.915; omega = 3: 0.747, each
consistent with the corrected constants once the O(1/log x) corner
deficits of the prime density approximation are allowed for, and
inconsistent by factors 4 to 6 with the published constants
(`validate_numeric.py`, and the slice test in the session log).

### A closed generating identity for the corrected C(v,w)

The corrected constants turn out to be far more tractable than the
published machinery suggests. Combining the exponential generating
function sum_j b_j(n) y^j/j! = prod_{p|n} (e^{-y log p} - 1) (from
zeta(s+y)/zeta(s)) with Lemma 8 in integral form and a Frullani integral
gives, for v of dimension l and w of dimension k (derivation in the
docstring of `closed_form.py`):

    Phi = prod_{j<=l} prod_{j'<=k}
          (y_j + c_{jj'})(z_{j'} + c_{jj'}) / ( c_{jj'} (y_j + z_{j'} + c_{jj'}) ),
    c_{jj'} = t - lambda [j=l] - mu [j'=k],

    C(v,w) = (prod v_j!)(prod w_j!)/(|v|+|w|+1)!
             * [y^v z^w lambda mu] Phi at t = 1.

Machine-checked (exact rational arithmetic) against the independent
symbolic route on all single-component pairs a,b <= 5 and on twelve
multi-component pairs including ((3,2),(2,2,1)) and ((1,1,1,1),(2,2));
it also
returns exact 0 on theta(v,w) = 0 pairs, so the theta bookkeeping is
subsumed. For single components the coefficient extraction gives the
closed form

    C((a),(b)) = (-1)^{a+b} * ab / (a+b-1)

(also confirmed by hand for a,b <= 7 against the symbolic route). No
comparably simple structure is visible in the published (skip) values.
Grade: the identity is a derived statement whose instances are verified
exactly on the battery above; a written general proof would be routine
but has not been written out, so call it hardened at the instances and
derived in general. It suggests the entire corrected C_{kappa,i} table
is coefficient extraction from a rational generating object, which is
the natural follow-up.

### What survives, what changes

* The kappa = 1 row (= Farmer-Gonek) survives all three defects
  untouched, in every mode and both assemblies.
* C_{kappa,1} = 1, C_{kappa,2} = -4, C_{kappa,3} = 4, C_{kappa,4} = -16
  (kappa >= 2) survive.
* Lemma 12 (stabilisation at kappa = i-2) survives: its proof only uses
  the height bound, which is orthogonal to all three defects.
* The qualitative conclusion of ch. 10 (coefficients become stationary
  under repeated differentiation, consistent with Farmer-Rhoades) is
  unaffected in kind, but every published numerical value with
  kappa >= 2 and i >= 5 changes. The corrected table begins to differ at
  C_{2,5}: published 28, corrected 52/3.

## 4. Extended tables (i up to 20; Bian's 2008 computation stopped at i = 11)

Full data in `coefficients.json` (all values exact rationals): per mode
(`skip`, `corrected`), rows kappa = 1..6 for i = 1..20 in both assemblies,
and both diagonals. Reproduce with `bian_engine.py --extend 20
[--reading corrected]`. Highlights:

**Published stable diagonal continued in Bian's own convention** (figure
assembly, skip mode), i = 12..20, continuing his printed
1, -4, 4, -16, 332/5, -224, 241424/315, -729784/315, 2912944/405,
-42709312/2025, 657260864/10395:

    i=12  -363490912/2025
    i=13   32318975168/61425
    i=14  -998386095104/675675
    i=15   102594101460736/23648625
    i=16  -52520705353984/4343625
    i=17   8661323223160544/241215975
    i=18  -3292629906658587904/32564156625
    i=19   193039973155501766144/618718975875
    i=20  -20386492282427984896/22915517625

(The same JSON also carries the eq-(10.1)-assembly skip diagonal, which
fixes Defect A alone.)

**Corrected stable diagonal** (eq (10.1) assembly, corrected mode),
i = 1..20:

    1, -4, 4, -16, 148/3, -416/3, 3344/9, -14464/15, 769144/315,
    -5726144/945, 69843904/4725, -1598848/45, 4381591232/51975,
    -30833961472/155925, 2171755595008/4729725,
    -224873947749376/212837625, 171076574719936/70945875,
    -5033594097664/921375, 133459120184121344/10854718875,
    -298546329313613824/10854718875

**Cost scaling** (seconds per level on one core, computing both
assemblies and six kappa rows exactly; the engine reaches Bian's whole
2008 endpoint, i <= 11, in ~0.1 s):

    i:          12    13    14    15    16    17    18    19     20
    skip:      0.3   0.9   2.0   6.4  15.4  36.9   131   346   1532
    corrected: 0.5   1.5   4.2   4.2  10.2  33.0   118   324    760

Growth is roughly 2.5-3.5x per level (the signature-pair double sums
dominate; both modes cost about the same). Extrapolating, i = 24 or so is
reachable in a day on one core; the 2008 hardware limit at i = 11 is now
a sub-second computation.

## 5. Structure of the sequences (task 4 analysis)

(a) **kappa = 1 row**: equals the Farmer-Gonek closed form exactly for
every computed i up to 20, in both assemblies and all three modes:
C_{1,2k+1} = ((k-1)!/(2k)!) 2^{2k+1} and C_{1,i} = 0 for even i >= 4.
This is simultaneously the strongest validation of the engine and the
reason none of the three defects was ever visible from the literature
side.

(b) **Stable diagonals**:

* No linear recurrence with constant coefficients (searched exactly to
  order ~N/2) and no P-recursive recurrence (order <= 3, polynomial
  degree <= 3, exact nullspace search) fits either diagonal, raw or under
  the factorial normalizations tried (`analyze.py`).
* OEIS: no hits for the numerator or denominator sequences of either
  diagonal or of the kappa = 2 rows (queried 2026-08-17).
* Denominators are 3-smooth-times-primorial-like (e.g. published i = 19:
  3^7 5^3 7^2 11 13 17 19); numerators carry large sporadic prime
  factors (e.g. 400758208831 at i = 15), which argues against a simple
  hypergeometric closed form for the diagonal as a sequence in i.
* Growth, published diagonal: |C_i|^{1/i} climbs through 2.80 at i = 19
  with an even/odd ratio oscillation (~2.8 vs ~3.0); no clean one-term
  asymptotic emerges from 20 terms.
* Growth, corrected diagonal: strikingly regular compared to the
  published one. The ratios r_i = C_{i+1}/C_i are monotone in absolute
  value and decrease steadily toward -2 (exact values in
  `render_tables.py` output):

      i:    5      8      11     14     17     19
      r_i:  -2.811 -2.532 -2.404 -2.322 -2.266 -2.237

  The subexponential factor is less settled: a_i = (i+1/2)(|r_i|/2 - 1),
  which would converge to the exponent a if |C_i| ~ K 2^i i^a, rises to
  ~2.335 near i = 14 and then drifts down (2.311 at i = 19), so the data
  is consistent with an exponent in the vicinity of 7/3 but does not pin
  it; no identification is claimed. Chasing the singularity structure of
  the generating identity above at alpha = -1/2 is the principled way to
  settle it.
* Coherence check on the corrected diagonal: its ratios converge to -2,
  i.e. radius of convergence exactly 1/2 in |alpha|. Bian's own picket
  fence model (his Lemma 13, the kappa -> infinity heuristic limit) has
  its phase transition exactly at |alpha| = 1/2. The published diagonal's
  ratios drift toward ~2.8-3.0 (radius ~0.35) and admit no such
  interpretation. This is observed structure, not a proof, but it is the
  kind of internal consistency the corrected table has and the published
  one lacks.

(c) **kappa = 2 rows** (both modes): irregular sign patterns (complex
singularity structure) with |C_{2,i}|^{1/i} still drifting downward at
i = 20 (~0.64 in the corrected row), so the radius of convergence exceeds
1 and is not pinned by 20 terms; qualitatively unlike both the kappa = 1
row (entire, FG closed form) and the stable diagonal (radius 1/2). No
recurrence found; no OEIS hits.

## Scope and inheritance

* Everything here concerns the coefficients of Bian's Theorem 1 expansion
  and their combinatorial definition. Theorem 1 itself is conditional on
  RH; its proof also carries the B-truncation structure: the expansion
  holds for each fixed B with error o_{kappa,B}(1), and the tail-bound
  question (letting B grow with T, or bounding the tail of the i-sum
  uniformly) is the open analytic gap this table work feeds. Nothing here
  addresses that gap.
* The identification of the three defects is a claim about finite
  algebra and about asymptotics of explicit prime sums (Mertens/PNT
  level); the witnesses are checkable by a stranger with the files in
  this directory.
* "Original vs novel": the audit findings are original to this session in
  the provenance sense. No literature search for later corrections of
  Bian's thesis has been run beyond Farmer-Gonek; if a published erratum
  or a later paper recomputes these tables, the novelty claim would need
  that search before being made. The lab's knownness default applies: the
  literature was not consulted beyond the sources named here.
