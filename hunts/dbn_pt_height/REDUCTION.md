# REDUCTION: what the 0.1875 package reduces Lambda <= 3/16 to, and what the 0.16 and 0.1595 rows add

Chain lane of hunt #147, 2026-10-21, repaired the same day after an adversarial
review. Reading only; every citation `[Q:ID]` is re-read from its hashed source
by `test_chain.py` (see CHAIN.md, "How to read this file"). Bundle members are
cited by basename, line and SHA-256 (all in `chain.json`); their directory
names are not written here because they carry the stem this tree reserves for
`zeta/rigor.py`.

## 0. Which reduction is which

The four pieces named in the task (collision exclusion on [t, 3/16], an
interior x <= 6.0e12 using Platt-Trudgian at X/2, an exterior to about
6.65e13, a tail module) are the modules of the **0.16 package** (PR 208,
fork commit `6baae4c`) [Q:C6] [Q:F12]. That package takes Lambda <= 3/16 as an
*anchor* from the **0.1875 package** (Zenodo 21175533) [Q:C3] [Q:C5] [Q:F5].
The 0.1875 package's own reduction is different: it instantiates Polymath 15's
criterion at the site X' = 6000000185827 [Q:Z1] [Q:Z2]. Both are listed below:
part A is the 0.1875 reduction, part B the collision-exclusion reduction that
the 0.16 and 0.1595 rows build on top of it. All rows below 0.2 are
self-archived and unrefereed; the catalogue's own note says so: "The last
refereed bound is $0.2$" [Q:C2]. The paper deposited in the 0.1875 record is,
by the bundle's own description, the 0.1965 paper [Q:Z31]; the 0.1875 claim
itself is read here from the bundle's assembly writeup.

## A. The 0.1875 package: Lambda <= 1680/10^4 + (39/1000)/2 = 3/16

| # | lemma | source | hypotheses | gaps |
|---|---|---|---|---|
| A0 | Polymath criterion: (i) RH to X/2, (ii) asymptotic region, (iii) barrier give Lambda <= t0 + y0^2/2 [Q:P1] [Q:P2] [Q:P3] [Q:P4] [Q:P5] | Polymath 15 Theorem 1.2 (refereed; proof via its Section 3 and de Bruijn's Theorem 13); restated in the bundle's criterion file [Q:Z14] | t0, X > 0, 0 < y0 <= 1; the slab form also needs y0^2 + 2 t0 <= 1 | the bundle's instantiation at the 0.2 row swaps the labels and credits row 2's right region to a sweep the Polymath record lacks [Q:Z11] [Q:Z12] (CHAIN.md, sections 2 and 3) |
| A1 | effective approximation H_t/B_t = f_t + O(e_A + e_B + e_C0) | Polymath 15 Theorem 1.3 (refereed); the bundle's error-terms audit, e.g. about 1.03e-7 at the row-2 barrier corner [Q:Z19] | the region of Theorem 1.3 | the project's PARI code uses a sub-term smaller than the published one [Q:Z20]; the audit calls it harmless (not rerun here) |
| A2 | hypothesis (i): RH to X'/2 = 3000000092913.5, margin 350479773/2 [Q:Z3] | Platt-Trudgian Theorem 1 [Q:PT1] (refereed) | none beyond the published theorem | none. **Zeta-specific input 1** |
| A3 | hypothesis (iii): boundary winding 0 on [X', X'+1] x [33/200, 1] for all t in [0, 1809/10^4] [Q:Z4], with N = 690988 constant on the slab | the bundle's barrier-slab leg: output of the Polymath C barrier code at the 6e12 site (the same site as the 2020 run [Q:R6]), a corner-audit second line, a site-glue leg | the Polymath barrier method's mesh and derivative bounds; (33/200)^2 <= 39/1000 so the slab covers the triangle | a barrier computation in no refereed record [Q:Z4] [Q:C2]; issue 151 reports a typo in the paper's printed barrier condition and says the production code does not consume it [Q:I9] |
| A4 | hypothesis (ii), finite windows N in [690988, 2745000], all y in [sqrt(39/1000), sqrt(1 - 2t)], t in [1680, 1685]/10^4 [Q:Z5] | the bundle's `lwin2_compose` leg, composing a banked lower bound of at least 19/200 for an Euler-3 L-type functional with mollifier {1,2,3,6} [Q:Z21] [Q:Z9], banked on eleven t-tiles [Q:Z28] | the banked fact as cited; the y-transfer A6; the error budget A1 | **the banked lower bound over about two million windows is cited and not reproduced** [Q:Z8] [Q:Z10]. A producer that could regenerate it ships: the parametric sweep program of the 0.1965 chain takes the t-tile, y^2 and the mollifier type as arguments [Q:Z24], its type 3 is the divisor set {1,2,3,6} [Q:Z25], and it evaluates the repository's L-type functional [Q:Z26]. Its invocation for the lwin2 tiles and its output are absent: the only run script calls it at t in [0.1770, 0.1775] with type 2 [Q:Z27] [Q:Z22], and every compressed log in the bundle belongs to a run at t = 0.1770, 0.1775 or the box between them [Q:Z29] [Q:Z30] (the test re-lists the members naming `lwin2` or the cap 2745000, none of them C or GP source: writeups, maps, manifests, verifiers and their logs; and it classifies every log). The README states that every claim can be re-verified from the bundle alone [Q:Z17]; for this leg that would mean running the shipped producer at the lwin2 tiles. **Zeta-specific input 2** |
| A5 | hypothesis (ii), tail N >= 2745000 on the band [1680, 1696]/10^4, full y-range [Q:Z6] | recomputed live in the assembly script | the package's tail device and its monotonicity constants | own device, unrefereed [Q:Z6] [Q:C2]. **Zeta-specific input 2** |
| A6 | y-transfer: a sweep at y = y0 covers [y0, y_max] [Q:Z15] | the bundle's `y_reduction` Theorem 1 | the bound must have the form the writeup calls a standard window majorant [Q:Z34] | own lemma, unrefereed [Q:Z15] [Q:C2]; the Polymath project found its earlier y-monotonicity assumption false [Q:I5] |
| A7 | composition: Lambda <= 3/16 at X', sole RH input Platt-Trudgian [Q:Z1] [Q:Z7] | the bundle's `assembly_1875` leg | A0 to A6 | self-archived, unrefereed [Q:C2] |

The arithmetic of A2 and A3 (3/16, X'/2, the margin, the slab floor, N
constant on the slab) is re-derived by `test_chain.py`.

## B. Collision exclusion anchored at 3/16: the 0.16 and 0.1595 rows

Both packages state (they are unrefereed, and the 0.1595 claim was refused on
the evidence by an outside reader, below) that H_t has no multiple real zero
for every t in a closed band [a, 3/16] and every real x, and conclude
Lambda < a: a = 4/25 for the 0.16 row [Q:F1] [Q:F2], a = 319/2000 for the
0.1595 row [Q:G2]. The sole RH input is Platt-Trudgian at X'/2 [Q:F2].

| # | rows | lemma | source | hypotheses | gaps |
|---|---|---|---|---|---|
| B0 | both | anchor Lambda <= b = 3/16 | bank line V1-H-213, which is the `assembly_1875` package of part A [Q:F5] [Q:F17] [Q:G7] | all of part A | cited, not re-verified [Q:F15]. The frozen copy in the 0.16 bundle differs from the Zenodo writeup in one word at line 74, a substitution: "campaign-targeted" in the Zenodo writeup [Q:Z23], "operator-targeted" in the copy [Q:F18]; no mathematical content differs (the test diffs the two files) |
| B1 | both | collision principle: if a <= Lambda <= b with a > 0, then H_Lambda has a multiple real zero, using a uniform remote tail (zeros with \|Re z\| >= 4 pi exp(128/r) + 1 real and simple for t in [r, 1/2]) [Q:F4] | bank lines 590 and 588; proof shipped as frozen text | the tail theorem with its explicit constant | own theorem, unrefereed [Q:F4] [Q:C2]; Polymath's Theorem 1.5 (distribution of zeroes) has only unspecified absolute constants [Q:P19] |
| B2 | both | **interior** x in [0, X']: Platt-Trudgian at X'/2 makes every zero of H_0 with \|Re z\| <= X' real [Q:F6]; a compact separator and Hermite propagation keep them real on [0, b], simple on (0, b] | bank lines 590, 617, 599 | the separator B3 | own lemmas, unrefereed [Q:F6] [Q:C2]. **Zeta-specific input 1** |
| B3 | both | separator: H_t(+-X' + iy) != 0 for t in [0, b], \|y\| <= 1, normalized modulus above 7/800 [Q:F7] | bank lines 596 and 616, a frozen numerical summary | de Bruijn's strip for the padding | the numerical production is not rerun by the bundle [Q:F13] |
| B4 | 0.16 | **exterior** [X', W], W = 66476100549959: a weighted Gram inequality on the four-prime torus 2, 3, 5, 7 at (4/25, X', 690988) [Q:F9], carried to every index in [690988, 2299999] [Q:F8] and lifted to H_t | bank lines 767, 774, 720, 733, 744, 754, 738, 710, 725 | the wall identities, re-derived by the test: s_C(4/25) < X' < s_{C+1}(3/16) and s_H(4/25) < W < s_J(3/16) < W + 1, C = 690988, H = 2299999, J = 2300000 | source productions not rerun [Q:F13]; bank authentication left to an external verifier [Q:F14]; external audits open and release held at the snapshot [Q:F3]. **Zeta-specific input 2** |
| B5 | 0.16 | **tail** [W, infinity), every N >= 2299999, no terminal cutoff [Q:F10], with an Euler13 witness [Q:F11] | bank lines 729 and 772 | as B4 | frozen output, not rerun [Q:F13]. **Zeta-specific input 2** |
| B6 | 0.1595 | one **exterior** x >= X' for every N >= 690988, no terminal cutoff [Q:C7] [Q:G6], from bank line 782 [Q:G3] on the banked 767 source [Q:G4]; no 729/772 tail [Q:G5] | bank lines 782, 767, 774, 744, 754, 771, 779, 710, 725 | as B4 | hash commitments "are not proofs of bank acceptance or numerical inequalities" [Q:G8]; reviews open [Q:G1]; release held [Q:G9]. **Zeta-specific input 2** |
| B7 | both | coverage: the boxes union to the closed band times [0, infinity), negative x by evenness [Q:F12] [Q:G6] | the bundles' coverage checks | B2 to B6 | none found |

An outside reader who went through the 0.1595 package file by file (PR 210,
2026-10-15) found that "no function in the five scripts evaluates ζ, H_t or
the 690,988-term Dirichlet polynomial" [Q:C9], that the anchor "is your own
July row" [Q:C10], and recorded the claim as refused on the evidence. The
package's own PR text says a passing run "is a mechanical check, not a
referee's verdict" [Q:C11].

## C. Which rows depend on which

| row | anchor | uses the 0.1875 reduction | inherits the row-2 gap of CHAIN.md |
|---|---|---|---|
| 0.2 | Polymath Table 1 row 2 with Platt-Trudgian [Q:PT3] [Q:C1] | no | yes |
| 0.1875 | its own site X' [Q:Z2] | it is the reduction | no |
| **0.16** | Lambda <= 3/16 [Q:C3] [Q:C5] [Q:F5] | **yes** | no |
| **0.1595** | Lambda <= 3/16 [Q:C4] [Q:C8] [Q:G7] | **yes** | no |
| 0.172422 | version 1 states the published Lambda <= 0.2 [Q:K1] [Q:K2]; version 1.1, which the catalogue cites [Q:C12], derives its own Lambda <= 0.2 (its own unrefereed claim) [Q:K4] [Q:K5] [Q:K6] | no | no, as cited (version 1 as stated did) |

So **both the 0.16 and the 0.1595 rows depend on the 0.1875 reduction**, through
the anchor b = 3/16, and on everything in part A, including the banked A4
bound whose run the 0.1875 bundle does not hold. The 0.172422 row depends on
neither the 0.1875 reduction nor row 2 in the version the catalogue cites. Its
first record, created on 5 September 2026, combined its collision exclusion
"with the published bound" 0.2 [Q:K1], as did its announcement on the blog that
day [Q:K2]. Its version 1.1 (the catalogue's "v2" [Q:C12]), whose record was
created on 8 September 2026, recalls that Platt and Trudgian "recorded the
resulting bound" 0.2 [Q:K7] but derives its own
anchor from its separator, its tail theorem and Platt and Trudgian's height
[Q:K4], so that the final argument "does not depend logically on an external
assertion" [Q:K5]; it keeps the endpoint 0.172422 [Q:K3]. That anchor rests on
the package's own unrefereed theorems, which this lane did not examine. The
catalogue's note "The three $0.16$-range packages all descend from the
$0.1875$ row" [Q:C2] holds for the 0.16 and 0.1595 rows; if the third package
it means is the 0.172422 row (the only other row below 0.1875; the note names
none), it does not hold for that one in either version.

## D. The two zeta-specific inputs, and Davenport-Heilbronn

**Input 1, the verification height.** RH verified to height X/2 by Platt and
Trudgian, T = 3000175332800 [Q:PT1]. It enters as hypothesis (i) of the
criterion [Q:P2] (row 2; A2 [Q:Z3]) and as the initial reality of the interior
module (B2 [Q:F6]).

**Input 2, the Euler-mollified lower bound.** A lower bound on the
Riemann-Siegel-type approximation f_t of Polymath's Theorem 1.3 to the right
of the barrier, obtained after an Euler-product mollifier: Euler-2 (`trib2`)
at N0 for row 2 [Q:P11]; an Euler-3 L-type functional in A4 [Q:Z21]; the
four-prime torus Gram inequality and an Euler13 witness in B4 and B5 [Q:F9]
[Q:F11]; the same banked source in B6. The mollifier is motivated by zeta's
Euler product, the heuristic f_t proportional to a product over p <= P
[Q:P18] [Q:P20].

**Davenport-Heilbronn.** The laboratory's pinned off-line zero of the
Davenport-Heilbronn function is rho = 0.80851718245663738555... +
85.699348485377592171929...i [Q:L1] [Q:L2] (`zeta/epstein.py`, which records
Spira 1994 as agreeing; pinned by `tests/test_epstein.py`). The test
re-evaluates |F_DH(rho)| < 1e-20 at dps 40. In Polymath's frame
s = 1/2 + iz/2 it is z = 2 Im rho - i (2 Re rho - 1), about 171.4 - 0.617i.

- **Input 1 fails for DH.** The criterion's hypothesis (i) excludes zeros with
  (1 + y0)/2 <= sigma <= 1 and 0 <= T <= X/2. With y0 = 0.16733 (row 2) or
  y0 = sqrt(39/1000) (the 0.1875 site), (1 + y0)/2 < Re rho = 0.8085... <= 1,
  and Im rho = 85.699... is far below X/2 at either site. The interior module
  fails the same way: H_0 for DH has the nonreal zero z with |Re z| = 171.4,
  far inside |Re z| <= X'. Both checks are re-derived by the test.
- **Input 2 is not tested for DH in this lane.** Testing it needs the DH
  analogue of f_t with its error terms; that is where the evaluator lane's
  refusal gate sits.

**The structural DH gate passes:** the reduction names its two zeta-specific
inputs, and DH fails the first, at the zero 0.8085 + 85.699i. The other
lemmas are of two kinds. Some are statements about the heat flow with no
arithmetic in them (the criterion, de Bruijn's theorem, the collision principle
given its tail, Hermite propagation, coverage). The rest are numerical facts
about zeta's own H_t (the effective approximation A1, the barrier A3, the
separator B3, the explicit remote tail B1), which a rival would have to redo
for itself but which do not test where its zeros are; the two inputs above are
where zeta's zeros and its Euler product enter.

Grades: the DH zero is *measured* in the laboratory (mpmath, |F| small,
winding number 1) and matches a published independent value, so the failure of
input 1 for DH is as firm as that zero. The lemma inventory above is a reading
of the sources, graded as what each source shows.

## E. Open issues

- Input 2 was not tested for Davenport-Heilbronn; that needs a DH analogue of
  f_t with error terms (the evaluator lane's refusal gate).
- The 0.172422 package's own anchor theorems (its separator and its tail
  theorem) were not examined; part C records only what each version states it
  depends on.
- The paper PDF of the 0.1875 record was hashed, not read; the 0.1875 claim
  was read in the bundle's writeups.
- Whether the shipped producer, run at the lwin2 tiles, would reproduce the
  banked bound was not tested: this lane does not compile or run downloaded
  code.

## F. Context recorded on 2026-10-26

This hunt audits the refereed 0.2 chain. It is not a race to a lower bound,
and nothing here ranks the rows below 0.2. When the lanes were resumed, the
catalogue's self-archived rows reached 0.1595: PR 210, which carries that row
together with the 0.16 row of PR 208, was merged on 2026-10-18 (UTC). Parts B
and C read both rows in the versions the catalogue cites. Separately, the
abstract of an arXiv preprint, 2610.32694 by Michel Planat, states that its
argument "bounds the de Bruijn--Newman constant by $\Lambda\le433/2500=0.1732$
without a QRH assumption." [Q:AX1]. That claim is unrefereed, and only the
abstract was read. Whether it inherits the row-2 gap of CHAIN.md, or anchors
at 3/16, was not examined.
