# Review request: the imaginary quadratic fields of class number h <= 5000

Prepared 2026-11-21 for one outside reader who knows analytic number theory
and has not seen this repository. Nothing here has been sent. Every number
is copied from `RESULTS.md` or a committed JSON file of this directory, and a
test (`test_every_large_number_in_the_review_packet_is_on_record` in
`test_grh_class_number.py`) checks that every number
with five or more digits in this page occurs there. Paths are relative to
the repository root.

## 1. The statement

Let D < 0 run over fundamental discriminants and let chi_D be the Kronecker
symbol, a real primitive odd character of conductor |D|. **Assume that
L(s, chi_D) has no zero with Re s > 1/2 for every such D with
|D| > 16 396 235 837** (hypothesis H(1/2) for those chi_D only, nothing
about zeta or any other L-function). Then the imaginary quadratic fields of
class number h, for every h <= 5000, are exactly the 102 746 940 fields
found by an exact search of all fundamental |D| <= 16 396 235 837, the
largest being D = -6 912 348 787 (h = 4967); below that bound the search
reads no hypothesis.

The analytic input is an explicit GRH form of Littlewood's lower bound for
L(1, chi_D) (Theorem B of `RESULTS.md` section 1), evaluated in Arb ball
arithmetic on a gap-free cover, which shows h(D) > 5000 for every
|D| > 16 396 235 837 under H(1/2).

**Status in this laboratory's record (updated 2026-11-21): proved, given the
Alpoge theorem below; candidate, pending external review.** A composite
claim takes the grade of its weakest step. With the hypothesis supplied from
outside, the weakest step is this laboratory's written proof of Theorem B
and of the tail argument, which no person has reviewed. That is what this
request is for.

**What verification of the hypothesis exists, and where.** On 2026-11-20
Levent Alpoge posted a Lean 4 archive (announced at alpo.ge/remark.pdf). Two
pages, both read on 2026-11-21 by the session that prepared this packet:

- *Lean verification of the Riemann Hypothesis*, a joint statement of the
  Lean and Mathlib communities, endorsed by the Lean FRO and the Mathlib
  Initiative, dated 2026-11-21
  (leanprover-community.github.io/blog/posts/riemann-hypothesis/). It states
  that both the statement and the proof of Mathlib's `RiemannHypothesis` are
  correct: the library compiles, the proved theorem was matched against a
  statement file importing only Mathlib by two independent tools, and the
  exported proof was accepted by Lean's kernel and by several independently
  written checkers.
- A. Sutherland's verification page (math.mit.edu/~drew/grh/, last updated
  2026-11-21 12:55 UTC). It reports that every module compiles, that the
  five theorems of the archive's `Main.lean` rest on `propext`,
  `Classical.choice` and `Quot.sound` only, that every module was replayed
  through the Lean kernel, that two independently written kernels accept the
  full export, and that all five statements were matched against a challenge
  file importing only Mathlib. Its third statement,
  `LFunction_ne_zero_of_half_lt_re`, says: for every N >= 1, every Dirichlet
  character chi mod N and every s with Re s > 1/2, L(chi, s) != 0 unless chi
  is trivial and s = 1. Its scope note: Dirichlet L-functions, not Dedekind
  zeta functions or Hecke L-functions. At its update time some runs were
  still in progress (the Lean default and paranoid kernels on the export, and
  one end-to-end comparator run).

That third statement contains H(1/2) for every chi_D. **This laboratory has
not replayed or checked the archive**: its own replay had not produced a
verdict when this packet was written. The bridge from that Lean statement to
the classical L(s, chi_D) (chi_D is a Dirichlet character mod |D| whose
Mathlib L-function is the classical one) is routine and is not written
anywhere in this work.

## 2. What is new against the literature, and what is not

The published frontier found is Garcia, Grenie, Lee and Molteni,
arXiv:2610.14257v1 (9 October 2026; text re-read for this packet). They
assume GRH for the Dedekind zeta function of the imaginary quadratic field K,
prove the cutoff 8 213 527 466 for h <= 2000, and give the complete list of
imaginary quadratic fields with class number up to 2000, with a per-field
data file on G. Molteni's web page.

- **Not new: everything with h <= 2000.** The list here has 16 453 493 fields
  with h <= 2000, the largest D = -1 062 350 083, the same count and largest
  discriminant in each of the 20 rows of their Table 1, and the same set of
  discriminants for every h <= 2000 as Molteni's per-field file
  (`controls_molteni.json`; the file itself, 165 MB, is not committed, its
  sha256 is). Our cutoff there is smaller (2 576 135 045 against their
  8 213 527 466), which changes no field.
- **New: the range 2000 < h <= 5000**, 86 293 447 fields. In the search
  recorded in `RESULTS.md` section 7 (one extended web search; zbMATH and
  OEIS were not searched) no complete list over all h above 2000 was found
  under any hypothesis. That is a statement about the search, not a claim of
  novelty.
- **Partial outside checks above 2000.** For every odd h < 5000 the counts
  equal the GRH-conditional counts of Holmin, Jones, Kurlberg, McLeman and
  Petersen (arXiv:1510.04387; 2500 values of h, 9 681 947 fields). For even
  h in (2000, 5000], 78 323 558 fields, there is no outside table (section
  4, item 3).
- **Unresolved: whether the published list rests on a further GRH through
  PARI.** Their paper says the computations were performed with PARI/GP and
  names no routine. If their class numbers came from a GRH-conditional
  class-group routine, their list below their cutoff carries a hypothesis
  that the exact counting here does not. This laboratory has not resolved
  it; it changes nothing above 2000.
- Also reproduced: Watkins' unconditional lists for h <= 100 (as cited by
  Garcia et al.; 42 272 fields), and Cremona and Sutherland
  (arXiv:2301.11169v4, as transcribed in this laboratory's literature
  notes), 4 115 897 fields with h <= 1000, the largest 227 932 027.

The explicit bound itself is larger than the closed form of Lamzouri, Li and
Soundararajan, Theorem 1.5 (Math. Comp. 84 (2015)), as extended to every
q >= 3 by Languasco and Trudgian (arXiv:2011.08348), on every cell tested
from 10^2 to 10^50 (`RESULTS.md` section 6(b)). A reviewer measured that
their route, evaluated numerically rather than in closed form, is stronger
again, by 7 to 16% in L (float grade, not adopted; `RESULTS.md`, the doors).
So the bound is not claimed as the best available, only as sufficient.

## 3. The proof, in the order a referee should read it

The proof is written in two files: the sibling hunt
`hunts/qrh_class_number/RESULTS.md`, which proves Theorem B for a general
abscissa sigma0 (it was built for the half-plane Re s > 7/8), and
`hunts/grh_class_number/RESULTS.md`, which restates every step at
sigma0 = 1/2 and rederives the two that change. Read them side by side.

1. **Setting and hypothesis.** `grh_class_number/RESULTS.md` section 0:
   notation, Dirichlet's formula h(D) = sqrt(q) L(1, chi_D) / pi for D < -4,
   H(1/2), and the range of D for which each result uses it.
2. **Statement of Theorem B.** Same file, section 1: the inequality
   log L(1, chi) >= M(a, b) - (R(x, delta_x) + R(y, delta_y) + T(x) + T(y)) / (b - a),
   with M, R, G and T defined there.
3. **(2.1) Explicit formula** with kernel t^w / w^2. Sibling section 2 (2.1)
   for the statement; `grh_class_number/RESULTS.md` section 2 (2.1) for the
   residues and the contour shift, written out. No hypothesis on the zeros.
4. **(2.2) Two cutoffs.** Subtract the identity at y from the identity at x
   and integrate over sigma in [1, inf). Sibling (2.2), including the bound
   T(t) for the trivial zeros; restated at 1/2 in the same section here.
5. **(2.3) Positivity.** Hadamard's product for xi(s, chi) gives
   sum_rho (sigma - beta) / |sigma - rho|^2 <= G(sigma) for real sigma > 1,
   by the worst character chi(p) = -1 prime by prime. Sibling (2.3).
6. **(2.4) The zero sum, the only place H(1/2) enters.** Two ranges,
   sigma >= 1 + delta and 1 <= sigma <= 1 + delta, each a monotonicity
   statement in beta (and in gamma^2 for the second). Sibling (2.4), and
   `grh_class_number/RESULTS.md` (2.4), which checks that both statements
   hold for every beta < sigma, so the step is uniform in sigma0 < 1.
7. **(2.5) The prime sum** bounded below by M(a, b). Sibling (2.5).
8. **(2.6) Evaluation in Arb.** Sibling (2.6) (prime sums exact below 10^7,
   Rosser and Schoenfeld above, upper Riemann sums justified by
   monotonicity), and `grh_class_number/RESULTS.md` (2.6), which records the
   two guards of the code that bind at 1/2 and the cells where the optimiser
   stalled (valid, 1 to 2% weaker in D than Theorem B allows; the search
   range is unaffected). Code: `hunts/qrh_class_number/lbound.py` and
   `explicit.py`, imported unchanged; `bounds.py` here.
9. **Theorem C, the cutoff table.** `grh_class_number/RESULTS.md` section 3:
   2041 adjacent cells over [10^2, 10^11] with q_hi / q_lo <= 1.0198,
   Theorem B evaluated at q_hi on each, adjacency asserted in code; then 77
   log-scale cells from 10^11 to 10^50, on which h >= 12 145. Data:
   `dtable_grh.json`.
10. **The tail, q >= 10^50.** `grh_class_number/RESULTS.md` section 4, item 3
    (rederived at 1/2; compare sibling section 4, item 3): a(q) = 2 log log q,
    every piece bounded by its value at Q1 = 10^50, giving
    L(1, chi) >= 0.38571 / log log q, hence h >= 2.5 * 10^23 there. Section
    4 items 1 and 2 (the clean constant 1/3 of Theorem A) are not needed for
    the lists.
11. **The exact search.** Sibling section 5 for the reduced-form count
    (r(a) = #{b mod 2a : b^2 = D mod 4a} counts the reduced forms with first
    coefficient a when 4a^2 < |D|); `grh_class_number/RESULTS.md` section 5
    for the program used here (`cnx.c`, which includes the sibling's `cn.c`
    unchanged): below 3 * 10^9 every class number is computed by streaming
    r(a) and enumerating every reduced form with larger first coefficient;
    above, a filter whose partial count is a lower bound for h(D), then the
    sibling's exact count. No hypothesis, no floating point in a decision.
12. **Controls.** `grh_class_number/RESULTS.md` section 6 (what each control
    can and cannot detect is stated there).

## 4. Where to attack first

We name these against ourselves. Each is a place where an error would not
necessarily be visible in any control we ran.

1. **The explicit formula (2.1) was first quoted, not derived.** The
   original text cited Davenport (chapters 12, 17 and 19) and the start of
   the proof of Lemma 2.5 of Lamzouri, Li and Soundararajan. *Done:* the
   contour shift is now written out (residues, horizontal segments at
   heights avoiding ordinates, the far vertical line between trivial zeros,
   absolute convergence of the zero sum). The identity was measured as a
   defect function at seven characters against zeros from PARI `lfunzeros`
   (defect at most 7 * 10^-6, below the trivial-zero part of E, so the signs
   are resolved), and by a reviewer at three more characters
   (D = -7, -1000003, -6623767483). Measurement cannot replace the
   derivation: the written contour argument has not been read by a person.
2. **The tail argument beyond the verified cover.** For q >= 10^50 the bound
   rests on an analytic lemma, not on enclosed cells: the claim that each
   piece (the main term, both zero sums, T and 1/(b - a)) is nonincreasing in
   q, so that the Arb value at Q1 bounds every larger q, and on Rosser and
   Schoenfeld's S(t) < log log t + B + 1/(2 log^2 t) for t >= 286, which
   needs a(q) >= log 286, that is log q >= 16.92. *Done:* the lemma was
   rederived at 1/2 (a(q) = 2 log log q instead of 8 log log q); a(Q1) = 9.492
   is asserted in code and in a test; K1 = -0.259504, P2(a1) = 0.179250 and
   E~(Q1) = 0.057100 are Arb values; the Rosser-Schoenfeld inequality was
   measured at every prime from 286 to 3 * 10^6 (smallest margin 0.00112 at
   293; it fails at 283, as the threshold predicts), float grade. The
   equation number within their Theorem 5 was not confirmed against the
   paper. The bridge
   10^11 to 10^50 is enclosed cell by cell; the monotonicity in q is not, it
   is argued in prose.
3. **Completeness of the exact search for even h above 2000.** The
   78 323 558 fields with even h in (2000, 5000] have no outside table, and a
   dropped field at h = 2002, 3000 or 4998 passes every published-table
   comparison (a test pins that blindness). *Done:* mode 1 agrees with
   brute-force reduced-form counting for every fundamental |D| <= 6000 and,
   as sorted lists, with the sibling's `cn.c` on five ranges (2 946 395
   fields); 212 769 enumerated class numbers recompute equal through
   `exact_h`; 28 496 sampled streamed counts recompute with Jacobi symbols;
   PARI agrees on every fundamental |D| in 13 windows (11 856
   discriminants) and on the largest |D| of every h, and finds no class
   number <= h among the 600 fundamental |D| just above D_GRH(h) for
   h = 1, 2, 3, 10, 100, 500, 1000, 2000, 3000, 4000, 5000, 10 000. An independent full-range sweep
   (`sweep.py`, `lsieve.c`: its own sieve, truncated Euler products, PARI on
   every unlisted candidate within tolerance; it shares no code with the
   search) covered all 4 983 858 175 fundamental discriminants in a
   reviewer's run, sent 5 358 520 unlisted candidates to PARI, and found no
   missing field and no wrong class number (smallest unlisted class number
   5001); a rerun with the committed code reproduced the reviewer's rows on
   [3, 5 * 10^7] and [1.5 * 10^9, 16 396 235 837]. The sweep is a detector,
   not a proof: the truncated product has no error term, PARI is not an
   oracle of record, and a class number wrong by less than the tolerance
   passes it. What makes the list complete is the correctness of the
   reduced-form count in section 3, item 11, which is a written argument.

A fourth weakness is structural rather than local: the main numerical
control, the exact L(1, chi_D) of every listed field against the bound, has
a margin of 1.449 at worst, and it cannot see an error that moves the bound
by less than that factor, including the zero term dropped altogether
(`controls_fault.json`). The size of the zero term, which fixes the search
cutoff, is checked only by the seven-character measurement and the written
proof.

## 5. How to reproduce

From a clone of the repository, with a recent Python 3, `gcc`, and the
pinned `python-flint` and `cypari2` (`requirements.txt`):

```bash
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt && .venv/bin/pip install -e .
.venv/bin/python -c "from zeta import rigor; print(rigor.BACKEND)"   # want python-flint
.venv/bin/python -m hunts.grh_class_number.bounds dtable             # the cutoff table
.venv/bin/python -m hunts.grh_class_number.search run 5000 16396235837 OUTDIR 3
.venv/bin/python -m hunts.grh_class_number.search summarise 5000 16396235837 OUTDIR
.venv/bin/python -m pytest -q hunts/grh_class_number
```

The sweep and the list controls are run by the commands in the run
manifests of `RUNS.md`.

**Measured time** (shared cores): the cutoff cover, about 80 s in Arb; the
search, 42.6 minutes of wall clock on three workers, 1.69 CPU-hours against
an estimate of 1.81 written before launch, 194 chunks, each a checkpoint;
the sweep rerun, 536 s. Per-step timings are in `RUNS.md`.

**Hashes** (sha256). The summarise step hashes the list files in increasing
|D|, one line "|D| h" per field.

| what | sha256 |
| --- | --- |
| all fields, h <= 5000 (1.5 GB) | `7bc67e064addc52f724682806b42894e8267556a4a949b7918edfd106ae6b421` |
| h <= 2000 | `07100ea3589ab2b490122fa69b438cd5393bdcd2e547dfc29bb3b5c86f9f24c0` |
| h <= 1500 | `c373d7c67bbecb922878481c50e6273f03ed07b93fc968a458bb0bf5389ee101` |
| h <= 1000 | `075a201c8e7cce6c0b6013423a5d96c6308452afab2fa79882388fc46d8b0c45` |
| h <= 100 | `ebeaedc1d6535c8696a1317247f973592709cba1b4090aebf2c748431f94b49a` |
| `cnx.c` used for the run | `fe679c516e33b7a057de0dc7113c05f22c3ba88fec681a324cfd196244e3a1f5` |
| the sibling's `cn.c` | `21b42fa90d1b7a3c8fae4fb24b9266a6439bca5a2c24430806715f87a525edb9` |
| Molteni's file `classes-list-2000.txt` | `2900aabef20e51511cbe0cbb1c7519f6788dfbd9a17b172626dcee70b302cb12` |

The h <= 1500 and h <= 1000 hashes equal those of the sibling hunt's
independent run under the 7/8 half-plane.

**Committed:** the code (`bounds.py`, `search.py`, `cnx.c`, `sweep.py`,
`lsieve.c`, `controls.py`, `lls_route.py`, and the sibling's modules), the
cutoff table and covers (`dtable_grh.json`, `theorem_a_grh.json`), the
counts F(h), largest |D| and largest squarefree k for every h
(`search_H5000.json`), the per-chunk run record (`search_chunks.json`), and
every control's output (`controls_*.json`, `crosschecks.json`,
`holmin_kurlberg_odd_5000.json`). **Not committed:** the full lists (1.5 GB;
identified by the hashes above and regenerated by the commands), Molteni's
file (165 MB), and the run logs, whose sha256 are in `search_chunks.json`.

## 6. Who checked what

No person has read the proof or the code. Two review passes were run on
2026-11-20, each by an AI agent working separately from the one that built
the hunt: one attacked the proof (P), one the computation (C). Both returned
"holds"; neither found a wrong or missing field or a failed step. Their
eleven findings (two major, nine minor) and the disposition of each are in
`RESULTS.md` section 9:

- C1 (major): the hunt was missing from the laboratory's case log; added.
- C2 (major): the even-h gap of section 4, item 3; answered by committing
  the reviewer's full-range sweep and rerunning part of it.
- C3: Molteni's per-field file was unused; now compared, identical.
- C4: the planted sign fault was sized above the control's floor; the floor
  and two plants it misses are now stated and tested.
- C5, C6, C7: run-record accuracy (an unannotated edit to a timestamp,
  "byte-identical" that held only after sorting, run records left outside
  the repository); corrected or committed.
- P1: the explicit formula was quoted, not derived; the contour shift is now
  written out (section 4, item 1).
- P2: the cover had stalled on 514 cells; the table is valid but 1 to 2%
  weaker than Theorem B allows for about 400 < h <= 2760; described, not
  regenerated.
- P3: the numerically evaluated LLS route beats Theorem B; recorded, not
  adopted.
- P4: small inaccuracies (a cell ratio, a cover description, an unconfirmed
  equation label, the discharge condition); corrected.

The agent reviews are evidence that certain errors were looked for. They
are not a referee's reading, and nothing above should be taken as one.

## 7. What we ask of you

1. **Is Theorem B proved?** In particular: is the contour shift of (2.1)
   complete as written, and are the two monotonicity steps of (2.4),
   especially the range 1 <= sigma <= 1 + delta where G has its pole, correct
   for every zero with beta = 1/2?
2. **Is the tail lemma for q >= 10^50 correct?** Does each piece decrease in
   q as claimed, so that the value at Q1 bounds every larger q, and is the
   Rosser and Schoenfeld inequality cited in the form and range in which
   they prove it?
3. **Is the completeness argument sound?** Given the cutoff, does the
   reduced-form count (r(a) for 4a^2 < |D| and direct enumeration of the
   remaining reduced forms) give h(D) exactly for every fundamental D, and
   is there a cheaper or more standard independent check you would want to
   see for the even h above 2000 before accepting the list?

Any error found, of any size, is useful to us.

## 8. Cover note (draft for the owner; not sent)

> Dear [RECIPIENT],
>
> We have computed the complete list of imaginary quadratic fields of class
> number h for every h <= 5000, assuming GRH for the quadratic characters
> chi_D with |D| above 16 396 235 837, by an explicit Littlewood-type bound
> evaluated in ball arithmetic and an exact search below it. For h <= 2000
> it agrees field by field with the list of Garcia, Grenie, Lee and
> Molteni. No mathematician has yet reviewed the written proof, and we
> would value your view of it.
>
> The attached packet states the result, its hypothesis, the proof in
> reading order, the three places we think it most likely to fail, and three
> specific questions. Everything is reproducible from the commands it gives.
> A partial reading, or a reason to decline, would also help.
>
> With thanks,
> [SENDER]
