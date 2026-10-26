# Public follow-ups to OpenAI's 7/8 paper, read on 2026-10-21

**Hunt #136, followups lane. Nothing here is a result of this laboratory: it is a map of
other people's claims, none of them refereed.** Compiled 2026-10-21 between 14:36Z and
15:10Z from sources downloaded to `<cache>/followups/run-2026-10-21T1440Z/`
on the campaign box (outside the tree, read as data). `followups.json` carries every row
below machine-readably, with the SHA-256 of each source file and the line each quotation
sits on. An independent verifier then reviewed this page, and three repair passes followed
on the same day: a partial one (r2, 15:52Z), r3 (16:41Z), which kept r2's changes and
finished the verifier's list, and this one (r4, from 21:22Z), a re-run of the repair step on
the same list that also re-checked the tracker between 21:28Z and 21:38Z and found a newer
claim (section 1, item 4). Section 12 records what the repairs changed and section 13 what
is still open.

**How to read the numbers.** This lane has no test file. Every number on this page is one
of two kinds, and says which at the point of use:

- *cited*: quoted from the named source, by line where the source is a text file, otherwise
  a substring of the downloaded file;
- *scratch-exact*: recomputed here in exact arithmetic (fractions and sympy) by scratch
  checkers outside the tree. That is weaker than this hunt's grade *derived*, because no
  test in the tree pins it. `followups.json` lists these as identities X1 to X18 so the
  test lane can pin them.

A decimal expansion of an exact value is a truncation; a gap between two numbers is
rounded to the figures shown. Other grades used: *measured* (a hash or listing taken here)
and *inferred* (a reading no computation here checks). "Lean per tracker" means the
QuasiRiemannTracker reports that Comparator matched the statement and that Lean, NanoDa and
con-ron accepted the proof. This laboratory has not replayed any of those builds. The
tracker adds a result "After review and merge" (cited, tracker README line 107) without
saying what that review covers, and no check of the mathematics of a tracker proof by a
person is reported in anything read here.

## 1. The headline: the mission's frontier is out of date

`MISSION.md` names 0.8748867 (Xu and Sang) as the best public abscissa. Smaller abscissae
were already claimed on the public record before this hunt opened (commit 9c1f21c5,
2026-10-21T14:57Z), and a smaller one still was posted in an open draft after it opened
(item 4). None of these claims is refereed and none was replayed here:

1. **Smallest claimed in a paper outside the tracker.** B_flat = 0.874886647039964..., the
   root near 0.8749 of 133488B^4 - 376596B^3 + 384534B^2 - 167541B + 26231 (cited, Liu
   arXiv:2610.26835 lines 122 to 123), claimed for every finite-order Hecke L-function over
   every number field (cited, line 128). It lies 5.30e-8 below Xu and Sang's 8748867/10^7
   (scratch-exact). The same algebraic number appeared nine days earlier as Hailey Collet's
   quartic boundary on the tracker (PR 9, 2026-10-10; identity X4, scratch-exact), for which
   the tracker reports Comparator verification of the exact quartic bound and of the
   rational 683505193/781250000 just above it (cited, catalogue lines 494 and 520).
2. **Not a record: Newton's geometry refinement.** Newton (Zenodo, 2026-10-16) states
   43744332481/50000000000 = 0.87488664962, conditional on Xu and Sang's analytic inputs
   (cited, PDF page 1). It is a re-choice of geometry inside Xu and Sang's system and lies
   2.58e-9 above B_flat (X11, scratch-exact), which the tracker had on 2026-10-10, so it was
   never the smallest claimed abscissa.
3. **Smallest merged on the tracker for every Dirichlet L-function: 8748087/10000000 =
   0.8748087** (cited, tracker catalogue `as_of` 2026-10-21, record
   gao-five-step-affine-20261020, PR 68 by Zhongpai Gao, merged 2026-10-21T07:16:31Z).
   Lean per tracker, against the canonical Mathlib statement
   `DirichletCharacter.LFunction χ s ≠ 0` (cited, `verifier/upstream-challenge.lean` lines
   10 to 11), "with the submitted bound substituted for $7/8$" (cited, tracker README lines
   105 to 106). It sits 39/500000 below Xu and Sang, 1913/10^7 below 7/8, and 0.0081420
   above 13/15 (scratch-exact). It comes with a four-page paper (cited, catalogue line
   1674) and is not refereed. In the pull list saved at 14:50Z the only open bound PR on
   the tracker was PR 52 (2187109/2500000, above the current best), which declares explicit
   `sorry` and does not count (cited, PR 52 body); by 21:28Z a second one was open (item 4).
4. **Claimed after this hunt opened, in an open draft: 8747729897/10000000000 =
   0.8747729897** (cited, tracker PR 69 by GitHub user HaileyStorm, whose body names
   Hailey Collet as sole human author, opened as a draft at 2026-10-21T19:58:25Z; body,
   metadata and check list fetched between 21:28Z and 21:38Z). It is the smallest
   abscissa found that is claimed without an unproved extra hypothesis (Guo's conditional
   328/375, section 2, assumes one). Its body says "verification pending" and "Local
   verification is incomplete." (cited, PR 69 body), and it builds on "the accepted PR67
   input" (cited). It is not merged and not in the catalogue: the catalogue fetched at
   21:28:09Z is byte-identical to the copy saved at 14:49Z (measured, SHA-256), and the
   tracker's verify check on the PR head, which the README says runs on drafts too (cited,
   README line 103), was still in progress at 21:38Z (measured, check-runs API). It sits
   357103/10^10 below PR 68 and 0.0081063 above 13/15 (X15, scratch-exact). Only its
   pull-request text was read; its Lean sources and paper were not.

Three consequences for this hunt (inferred):

- The kill condition "a claimed improvement is matched or beaten by a public follow-up
  already on record" must be read against **0.8748087**, the smallest bound merged on the
  tracker, not 0.8748867. A candidate between 0.8747729897 and 0.8748087 would sit above
  PR 69's open draft claim, so PR 69's state has to be checked again before either number
  is used (section 13).
- Part (a) asks for the smallest abscissa inside OpenAI's Part II assembly with stronger
  row-count inputs, and hunt #134 puts that assembly's ceiling with perfect row counts at
  13/15. A part (a) result therefore escapes the kill condition only if it lands between
  13/15 and the public bar: a window 0.0081420 wide below 0.8748087, or 0.0081063 wide if
  PR 69 is verified (X15). The window does not depend on what the tracker's own entries
  assume. The assembly keeps the paper's pointwise reflected numerator, and the smallest public
  abscissa found that keeps it is B_new (Guo; Liu v2, which claims it is the infimum of a
  comparison system that holds the paper's counts fixed with kappa in [13/18, 1], section
  3). So a part (a) result has to gain more than B_new - 0.8748087 = 1.48e-4 (X16,
  scratch-exact) over B_new by row counts alone.
- The tracker line from PR 26 to PR 68 (section 4) is the closest public analogue of part
  (a), not part (a) itself. It strengthened row-count and moment inputs and moved the
  claimed bound from B_flat down by 7.79e-5 (X13, scratch-exact) to 0.8748087, but every
  entry in it has Levy's weighted numerator in its `builds_on` closure (measured, from the
  catalogue; that each entry uses it is inferred), which changes the high-exponent form of
  hunt #134's assembly (section 2), and PR 63, 66, 67 and 68 also change what the tracker
  calls LOW-side source handling and normalization. Whether the line itself is bounded by
  13/15 depends on whether those entries stay inside the model in which tomoto0, Watson
  and hunt #134 place that floor (M + l = 1, the h/6 signal, rows near the line counted in
  full); the tracker says of the floor "This barrier applies to that model" (cited,
  milestones line 36). That is not established (section 5, I9; section 13).

## 2. Improvements to the Dirichlet abscissa in the papers

All entries: unrefereed preprints or repositories. "Inside" means inside hunt #134's
Part II assembly (its low side 5/6 + (M - 2l)/12 and its endpoint inequality with the
paper's row counts); "inside, extended moment range" means the same assembly with the
capacity coefficient c = 1/(3 kappa) moved by a wider range of the paper's Lemma 18.1.

| date (UTC) | who and where | abscissa (cited) | what changed, from and to (cited) | relation to the assembly | Lean |
|---|---|---|---|---|---|
| 2026-10-07 (draft date) | Z. Gao, GitHub draft at commit 309a757e | 20999/24000 | l: 1/6 to 1001/6000; b = 1/8 and kappa = 3/4 kept | inside, geometry only | not inspected; the README calls it an unsubmitted draft with mathematical review pending |
| 2026-10-08 05:02 (commit cacbab49) | J. Guo, GitHub aster2024/openai-math-followups | sigma_dagger in (0.8749570194, 0.8749570195), root of 7884s^3 - 18819s^2 + 14643s - 3686; also 349999/400000, 20999/24000, (1507 - 2 sqrt 921)/1653 | geometry optimised; Lemma 18.1 kappa range [3/4, 1] to [37/50, 1] with kappa = 2 sigma - 1; low estimate rederived for 0 <= l <= 1/5 | inside, extended moment range | none (Python exact scripts) |
| 2026-10-08 16:18 | B. Liu, arXiv:2610.12234v1 | B_r = 34999/40000; B_alg = (1507 - 2 sqrt 921)/1653 = 0.874957069799... | (b, l): (1/8, 1/6) to (1/8, 1/6 + 1/10000), then to (-4/29 + 230 sqrt(921)/26709, (33 + 8 sqrt 921)/1653); kappa = 3/4 | inside, geometry only | Lean per tracker (the exact B_alg) |
| 2026-10-08 | Argonaut Math, GitHub | 3499999/4000000 | l: 1/6 to 1/6 + 10^-6 | inside, geometry only | Lean per tracker |
| 2026-10-08 | GitHub user LW56e2 | 4374785349/5000000000 | rational point beside B_alg (8.3e-13 above it, scratch-exact) | inside, geometry only | README reports standard axioms; not on the tracker |
| 2026-10-09 | ProofCouncil (T. Gehrunger), nielstron; tracker | 874957019421/10^12, then the exact cubic 11/12 - e/4 with 657e^3 - 954e^2 + 21e + 20 = 0 (= B_new) | "Extends the actual masked moment and detector range" (catalogue) | inside, extended moment range (inferred) | Lean per tracker (the rational and the exact cubic) |
| 2026-10-10 | A. Levy, tracker PR 6 | 10499/12000 | high side: pointwise reflected numerator to a weighted fourth moment of the reflected numerator; kappa = 3/4; l = 167/1000 | changes structure (high-exponent form) | Lean per tracker; the PR reports "no external human peer review" |
| 2026-10-10 | H. Collet, tracker PR 9 | 11/12 - l/4, l the root in [1/6, 1/5] of 927l^4 - 3135l^3 + 2433l^2 + 275l - 100 (= B_flat); rational 683505193/781250000 | variable-kappa moment plus Levy's weighted numerator | changes structure | Lean per tracker (the exact quartic and the rational) |
| 2026-10-11, v2 10-15 | H. Sang (v1); Y. Xu and H. Sang (v2), arXiv:2610.15291 | 8748867/10^7 via 69991/80000 | low estimate keeps the decay of rescaled prime tuples (allows l > 1/6); numerator: pointwise to an amplified first moment, sum over the class of abs L(1/2 + theta + it) << U^((3R+1)/4 - theta/2); kappa range to [13/18, 1]; (kappa, b, l) = (3/4, 173/2000, 10027/60000) then (29991/40000, 17307/200000, 1253399/7500000) | changes structure (high-exponent form), counts R_kappa kept | none |
| 2026-10-12 | B. Liu, arXiv:2610.12234v2 | B_new = (18 xi + 7)/(18 xi + 9) = 0.874957019420098946..., xi the root in (0.38858, 0.38859) of 1188xi^3 - 2160xi^2 + 171xi + 190 | Lemma 18.1 kappa range to [13/18, 1], iterated to kappa = 2B_new - 1 = 0.7499140388; an optimality theorem claimed with proof (section 3) | inside, extended moment range | author reports Lean; repository scope not inspected |
| 2026-10-16 | T. Newton, Zenodo 10.5281/zenodo.23414581 | 43744332481/50000000000 | (b, l) at Xu and Sang's stage-two kappa = 29991/40000: l from 1253399/7500000 to 6267002557/37500000000 | geometry only, inside Xu and Sang's system; barrier B_lim = 0.8748866496166314... for that system (cited); 2.58e-9 above B_flat (scratch-exact) | none |
| 2026-10-19 | B. Liu, arXiv:2610.26835v1 | B_flat = 0.874886647039964..., every number field | Xu and Sang's averaged numerator carried to F containing mu_12; varying kappa in one limiting step, kappa_flat = 2B_flat - 1 = 0.749773294; base field K(zeta_12) and class-field descent | changes structure | the paper states its Lean files do not yet cover the complete analytic argument (line 1725) |

Three identifications, scratch-exact: Guo's sigma_dagger, Liu's B_new and nielstron's cubic
are one algebraic number (X1, X2; Guo's and Liu's formulas for the limiting b agree modulo
the cubic, X3); Collet's quartic boundary and Liu's B_flat are one algebraic number (X4);
the order is B_flat < Newton's B_lim < Newton's rational < 8748867/10^7 < B_new < B_alg < 7/8
(X5). ProofCouncil's rational 874957019421/10^12 is a different number, 9.0e-13 above B_new
(X14, scratch-exact). Guo also states a **conditional** 328/375 from an unproved mean-square
Hypothesis 11.1 for H >= D^(99/100), which would change the sixth-power amplification
exponent to max{1, 1/6 + 33r/40} (cited, Guo section 11, lines 39, 51 and 63).

Guo's date is the commit time of cacbab49 in the saved commit list (cited, `guo_commits`
lines 2627 and 2633), and his README at that commit, as re-fetched by the verifier, already
states sigma_dagger and its cubic (cited, `guo_readme_cacbab49` lines 6 and 8).

The five follow-ups whose low estimate was read at source level all take l above 1/6 and
rederive the direct estimate by charging the rescaled tuples their own decay. Liu v1's loss
is (d_J + 5l - 1)_+/4 and its net exponent -d + [d + 5l - 1]_+/8 (cited, arXiv:2610.12234v1
lines 370, 2227 and 2309); Liu v2 bounds the same net exponent by -7d/8 (cited,
arXiv:2610.12234v2 lines 3003 and 3004); Liu's number-field paper restates that loss and
the -7d/8 bound (cited, arXiv:2610.26835 lines 968 and 969); Guo's completed-row loss is
[5l + d_J - 1]_+/4, with the same net exponent (cited, Guo section 3, lines 41 and 161); and
Xu and Sang's first refinement says the same in words (cited, arXiv:2610.15291v2 line 248).
Newton works inside Xu and Sang's system, conditional on their analytic inputs, so he
inherits their low estimate (inferred). Gao's draft, Argonaut and LW56e2 also take l above
1/6 but were read at README level only, and the tracker's Lean sources were not read, so for
them this is inferred. This is the "total accounting" door that hunt #134 recorded as
inferred.

## 3. What Liu's optimality claims hold fixed

**B_new (arXiv:2610.12234v2, Theorem 34.4, lines 5774 to 5861).** Over an admissible set
of parameter choices with all losses set to zero, the infimum is B_new (cited, line 5810).
Held fixed: the direct estimate (exponent l_x/2 + b/12, signal C_b(s) = s - (4 + b)/6, free
total length allowed); the pointwise reflected-numerator high exponent E_B(d) <= 0 at every
permitted zero and amplitude class, including classes whose nonemptiness is unknown; the
counting exponents from the separate moment estimates (Lemma 17.1, Lemma 17.6 with slope
5/6, Lemma 18.1 with kappa in [13/18, 1] and capacity 6 kappa z); the detector cutoffs
t in [1, 3/2] and the contour and norm-range choices of his Lemma iv-necessary-branches;
and the compatibility B <= (1 + kappa)/2 with each moment licensed by a previously proved
bound (cited, line 5789). Liu names what would change the system: "An estimate excluding a
critical class, a relation between the large values arising from different detector
choices, or a stronger analytic estimate" (cited, lines 5860 to 5861).

**B_flat (arXiv:2610.26835v1, "refined comparison system", lines 9877 to 9998).** Held
fixed: balanced lengths with b > 0 and 0 < l <= 1/5; the direct majorant matched at
B(l) = 11/12 - l/4; the counts R_kappa of the pointwise system; Xu and Sang's averaged
numerator at every class with delta >= 1/8, shift 0 <= theta <= g/(6 kappa), evaluated at
d = h; the endpoint exponent <= 0 on 1/8 <= delta <= 2B(l) - 1, 0 <= x <= 1/2, the formal
class x = 1/2 included; kappa in [13/18, 1] licensed by a previous bound (cited, lines 9886
to 9902). Stated as outside: a class-by-class mix of averaged and pointwise numerators,
unequal lengths, and "stronger analytic inputs (a smaller count at the critical class, a
larger admissible prime length in M2, a sharper Gram or reflected-energy estimate, a smaller
amplification exponent)" (cited, lines 9989 to 9991). The claim is that B_flat is the exact
infimum and is not attained by finite chains starting above it (cited, line 9914).

So the "claimed optimal" B_flat (0.874887 in `MISSION.md`) holds the row counts fixed. The
tracker results below it change inputs that this system holds fixed (the counts R_kappa,
through moment capacity, density, detector and marked counts; from PR 63 on, also the
normalization and the LOW side), so they do not contradict it (inferred).

## 4. The tracker records below B_flat (row-count inputs)

QuasiRiemannTracker (`gtimg.github.io/QuasiRiemannTracker`) admits a bound when Comparator
checks the submitted statement and its axioms against the canonical target with the bound
substituted for 7/8, and Lean, NanoDa and con-ron all accept the proof; the result is then
added "After review and merge" (cited, README lines 103 to 107). The table lists all 17
catalogue records below B_flat (X12, scratch-exact), each "framework-verified" in the
deployed catalogue of 2026-10-21 (cited, `catalogue.json`, SHA-256 in `followups.json`)
and merged between 2026-10-13 and 2026-10-21. Through its `builds_on` chain each one builds
on OpenAI's baseline, Levy's weighted numerator and Collet's Cycle25 framework (measured,
from the catalogue). They are not all records: PR 48 and PR 53 were merged after a lower
bound had already been merged (X12). Mechanisms are paraphrased from the metadata and the
papers read; the Lean sources were not read.

| PR | bound (cited) | author | what changed (cited, metadata or paper) | kind of input |
|---|---|---|---|---|
| 26 | 87487/100000 | nielstron | local fourth moment with prime cost 22/5 in place of 9/2 = 6 kappa (explanation.md lines 10 to 11), used above h - 1/1000 with 6 kappa below that junction (lines 21 to 22) | moment capacity |
| 37, 38 | 4374347/5000000, 87486797/10^8 | K. Roegnvaldsson | affine local-moment capacity; defect allowance 1/250; PR 37: "The LOW architecture remains unchanged; this does not cross its 13/15 barrier." | moment capacity |
| 41 | 8748673/10^7 | Z. Gao | defect 1/241, asymmetric LOW reserves | moment capacity |
| 42 | 874861/1000000 | H. Collet | fixed-dictionary density: rows with a zero of real part >= a number at most Y^(rho(2a - 1)), rho(delta) = 1 - 10 delta/(3(5 - 2 delta)), for 33/40 <= a <= 7/8; interior affine moment n1 + n2 + Lambda z <= B with Lambda = 19312/4787 and B = 14200/14361 - 10^-5 on 0.41 <= n_i <= 0.44, 0.034 <= z <= 0.04 (Cycle61 paper lines 276 to 278, 397, 415 to 416) | density count and moment capacity |
| 43 | 4374299/5000000 | Z. Gao | Cycle61 parameters coupled, exact reserves | parameters |
| 48, 50 | 437429/500000, 8748559/10^7 | timbalud | high-zero counting keeps slot amplitudes; separate inverse and plain slot selections with the common-radical penalty | marked counts |
| 53 | 10935831/12500000 | D. Watson | defect 1/250 to 429/100000; Lean module B127 states a hard-limit hierarchy including "the universal 13/15 low-side LP floor" (catalogue method text; PR 53 body) | moment capacity, formal ceiling |
| 56 | 437423/500000 | DaysSky | detector per-fiber count: capacity (1 - 2m)/(6 kappa) becomes (B - 2m)/Lambda for m in [0.4137, 0.4235] | detector count |
| 60, 62, 63 | 21871/25000, 218709/250000, 87483/100000 | Z. Gao | combinations of the above; marked HIGH width; "balanced common-geometry normalization" and density-adaptive caps | counts and LOW normalization |
| 64 | 874835173/10^9 | ArviFoxy | marked-ledger constants computed in Lean from their constraints, with a Lean statement that no other admitted split does better | parameters, with an optimality claim |
| 66 | 874828524351/10^12 | Sil | saturated marked capacities, retained sixth-root weights, short-width moment bootstrap, "clipped uneven normalization with common-factor cost 2/5" | counts and normalization |
| 67 | 174963413/200000000 | ArviFoxy | second affine step for the LOW children | changes LOW-side structure |
| 68 | 8748087/10^7 | Z. Gao | five affine stages; uniform root moment m1 + m2 + lambda s <= B with lambda = 3.741331371862391 and B = 0.982029506308942 as printed, input price kappa_0 = 4499/6000 (paper page 1) | changes LOW-side structure; moment capacity |

Not in the table: the open draft PR 69 (section 1, item 4), which is not a catalogue record;
its metadata lists openai-baseline, Levy's weighted numerator and two-level-affine-20261019
(PR 67) among the records it builds on (cited, PR 69 body).

Scratch-exact comparisons for the two inputs that are now numbers: Collet's density minus
the paper's no-slot count is rho(delta) - (1 - 2 delta/3) = 4 delta^2/(3(2 delta - 5)) < 0
for 0 < delta < 5/2 (X10); the prime cost 22/5 equals 6 kappa at kappa = 11/15.

## 5. Row-count and moment inputs: which were improved, which were not

Paper lines refer to the pinned `paper.tex` (16,677 lines, SHA-256 `42a5ee0f...a6a3`); every
line listed below carries a quotation in `followups.json`. Its `build/paper.tex` is
byte-identical at the later `openai/math` commits fd4aeeb2 and 1581d4cb (measured, SHA-256).

| input | paper lines | value (cited) | status |
|---|---|---|---|
| I1 marked inverse moment, Lemma 17.1 | 9250, 9254 | r + 2z <= m - c1, 2r + 8z <= 3m - c2 | **not improved as a lemma**; its use in counting changed (PR 48, 50, 66) (inferred) |
| I2 sixth-power amplification, Lemma 17.6 | 12362, 12383, 15101 to 15104 | e(r) = max{1, (1+5r)/6}, alpha = 5/6 | **not improved unconditionally** by anything read (absence inferred); only Guo's unproved Hypothesis 11.1 (cited); Liu lists it as outside both systems (cited) |
| I3 plain fourth moment, Lemma 18.1 | 12531 to 12581 | kappa in [3/4, 1], n1 + n2 + 6 kappa z <= M, premise beta_* <= (1 + kappa)/2 | **improved**: range [37/50, 1] (Guo), [13/18, 1] (Liu, Xu and Sang); local and affine capacities (PR 26 to 68) (cited) |
| I4 two saturated witnesses, Proposition 8.3 | 4510 to 4530 | t in [1, 3/2], r <= t, r + m >= t, 0 <= m <= 1/2 | **not improved** as stated by anything read; counts built on it changed (inferred) |
| I5 no-slot count, Proposition 19.2 | 15185, 15215 | U^(1 - 2 delta/3) | **improved** on 33/40 <= a <= 7/8 by Collet's density (cited) |
| I6 selected-slot count R_short with D_x, P_x | 15192 to 15206 | D_x = 3 - 17x/9, P_x = (2 - 8x/9)(1 - x) | **improved** through c = 1/(3 kappa) and the tracker counts (cited) |
| I7 floor bin a = 51/100, counted in full | 15843, 15847 | R = 1, E(h) <= -7/1200 | **not improved** (absence inferred from what was read); any count of these rows, even the density-hypothesis count R = 1 - delta, tends to R = 1 as the floor approaches 1/2, which forces 13/15 in the model with M + l = 1 and the h/6 signal (cited, section 6); its reach over PR 63, 66, 67 and 68, and the draft PR 69, is open (I9) |
| I8 pointwise reflected numerator, section 20 | 15726 to 15801 | reflected to Re w = 1 - a - 6e, cost U^(delta/2 + O(e)) | **improved** (structure): averaged numerator (Levy, Xu and Sang, Liu) (cited) |
| I9 direct estimate, Lemma 14.3 and Proposition 15.2, combined in the compensated low estimate | 7747, 8340, 8564 to 8642 | Z^(l_x/2 + b/12), signal with h/6 | **open**: exponent and h/6 signal kept by Liu v1 and v2, Guo, and Xu and Sang (cited), and by Liu's number-field paper, whose direct majorant 11/12 - l/4 on balanced lengths (cited, section 3) is the same target 1 - h/6 + b/12 (X18, scratch-exact), with per-summand losslessness replaced by total accounting; tracker PR 63, 66, 67 and 68 change the LOW side (the draft PR 69 builds on PR 67), and whether they keep the exponent, the signal and M + l = 1 is not established |
| I10 bin ceiling delta <= alpha, prime supply above 7/37 | 15100 to 15101, 15195 | from the 11/12 input; lower bound on l/h | **not improved** (not changed), not binding (inferred) |

**Inputs no follow-up read here has improved**: I1 as a lemma, I2 unconditionally, I4, I7
and I10. **Open**: I9. I7, the h/6 signal of I9 and M + l = 1 are what fix the 13/15 floor,
so the floor bounds the tracker line only under the I9 caveat. I2 is the input hunt #134's
doors table already marked "genuine, outside this assembly". The status column for the
tracker entries is inferred from metadata and papers; it is a statement about what was
read, not a proof that nobody changed a lemma.

## 6. Ceilings and barriers stated by others

- **13/15, tomoto0 (GitHub, commit b83a73c6, 2026-10-07T20:30Z).** The saved commit record
  gives that time and shows that the commit added `reports/barrier_analysis.md` (cited,
  `tomoto_commit` lines 2, 8, 214 and 215). In the cubic-theta exponent model with
  M + l = 1, near-line rows counted in full force target > 13/15 even with
  density-hypothesis counts R = 1 - delta, optimum l_x = 2/5, b = 0; with the 51/100 floor,
  the floor alone gives 0.86979 (cited, barrier_analysis.md lines 32, 34, 35). Its
  condition 1 - (5/2) l_x - (13/12) b < 0 is hunt #134's floor condition C_0 <= 0 rewritten
  on M = 1 - l (X7, scratch-exact), and the 51/100 floor gives 167/192 = 0.8697916 (X8,
  scratch-exact). The tracker's 13/15 milestone ("Limit of OpenAI’s method") rests on it,
  says the normalization M + l = 1 and the row count R(0) = 1 near the critical line force
  the bound above 13/15, says "This barrier applies to that model", and notes that the
  analysis assumes some exponent formulas hold "beyond the ranges proved in the paper"
  (cited, milestones lines 34 to 36).
- **tomoto0's 0.87451 and "fixed point near 0.8745"** (lines 45 to 47) lower the bin
  ceiling and the amplification slope together. Hunt #134's RUNS.md records the same
  scratch error and discards its 0.8745: alpha = 5/6 is the sextic amplification slope
  (paper lines 15101 to 15104), not the 11/12 input (inferred assessment).
- **Watson, Lean module B127 (tracker PR 53, opened 2026-10-14, merged 2026-10-15):** "the
  universal 13/15 low-side LP floor" and an interior envelope down to 328/375 (cited,
  catalogue method text for certb-local-20261013, line 1035; the PR 53 body says
  "universal 13/15 LP floor"); the module was not read.
- **Tracker PR 37 (2026-10-13):** "The LOW architecture remains unchanged; this does not
  cross its 13/15 barrier." (cited, PR 37 body).
- **3/4, Acer (X post, 2026-10-06):** "a further obstruction" in the method, cited at second
  hand from the tracker's milestones (the post was not read).
- **Guo, section 11.1:** sigma_dagger is the limit of his stated envelope, geometry allowed
  to depend on beta; "A different mean value, correlation, signed cancellation, or low-side
  estimate lies outside this model" (cited, line 30).
- **Liu, Newton:** the optimality statements of section 3, and Newton's barrier B_lim for
  Xu and Sang's system with 29991/40000 <= kappa <= 3/4 (cited).
- **Xu and Sang, arXiv:2610.17675:** a matching lower bound of size A^(5/6) B^(1/3) for the
  squarefree sextic residue-character matrix in B^(16/11 + delta) <= A <= B^(2 - delta);
  they state it does not establish optimality of the zero-free boundary (cited, via
  arXiv:2610.15291v2 introduction).

No follow-up found claims a route toward real part 1/2, and none reaches below 7/8 with a
probe whose constants are not tied to the sextic pole (inferred from the searched set,
section 11; PR 69 was read only at the level of its pull-request text). Collet's
single-compensating-prime construction (tracker PR 8) is a different probe and stops at
29/33, above 7/8 (cited, catalogue line 435).

## 7. Prior art for hunt #134 (searched, found)

Hunt #134's RESULTS.md section 10 says "Not searched". The search is now done:

| hunt #134 statement | public antecedent |
|---|---|
| sigma_0 = 1 - h/6 + b/12, and 11/12 - l/4 on M + l = 1 | tomoto0, 2026-10-07, section 1; Liu v1, 2026-10-08 (cited) |
| floor ceiling 13/15 at l = 1/5, M = 4/5, b = 0 | tomoto0, 2026-10-07 (same condition, X7); Watson's B127, PR 53 opened 2026-10-14 (cited) |
| geometry optimum about 0.874958 (float), exact lower bounds 5655673/6464057 and 44117/50422, printed there as 0.8749417 and 0.8749554 (rounded; hunt #134 RESULTS.md lines 165 to 167 at commit 9456b4da) | exact optimum B_alg = 0.8749570697 (Guo, Liu, 2026-10-08), lying between 44117/50422 and 0.874958 (X9, scratch-exact) |
| only the unrescaled summand must be lossless (inferred there) | claimed with proof in unrefereed preprints by Liu (v1, v2 and the number-field paper), Guo, and Xu and Sang (cited, section 2) |

Hunt #134's numbers stand as an independent reading (original as provenance); they are not
first on the record.

## 8. Scope extensions, the 11/12 companion and the Siegel exclusion

- **Cureton and Thorner** (hexagon:2610.00200 v2; the page dates v2 Oct 12, 2026, its
  history lists v2 as current from Oct 14): zeta_K(s) != 0 for Re s > 31/32 for every
  number field K, Hecke corollary (cited, report line 172). The authors write "These
  results were proved and formalized in Lean using AxiomProver" (cited, report line 63), and
  the AxiomMath/DedekindZetaZeroFree README says the formal proof uses only Lean's three
  standard axioms (cited, AxiomMath README line 24; not replayed here). It runs OpenAI's
  Primitive-roots comparison over K(zeta_12), not the Part II assembly, and calls the 7/8
  refinement "less suited" there (cited, report line 293). It does not improve the Dirichlet
  abscissa.
- **Others, at fixed abscissa** (cited, abstracts): Hu, 7/8 for unitary Weil L-functions over
  every number field, Hecke characters of infinite order included (hexagon:2610.00216);
  Rubinstein and Restrepo Borrero (hexagon:2610.00220), Part I adapting 11/12 to give
  L(E_d, s) != 0 for Re s > 17/12, and Part II adapting 7/8 to give L(s, conj(alpha) eta) != 0
  for Re s > 7/8 and hence L(E_d, s) != 0 for Re s > 11/8, which are 11/12 and 7/8 in the
  analytic normalization; they "do not claim that the complete proof has been independently
  checked and understood by a human mathematician" (cited, page lines 10 to 16 and 24);
  Guo, 11/12 for Hecke characters of nonzero angular type over Q(sqrt(-3)) and 17/12 for
  y^2 = x^3 + D.
- **OpenAI's companion of 2026-10-05**, "The Quasi-Riemann Hypothesis" (paper2.pdf): the
  weaker Re s > 11/12 by a shorter argument; its README says "This paper was written with
  human assistance" (cited); Quanta reports it is "not yet formally verified" and that it
  is the only one of the papers released on October 6 edited by a person (cited, lines 124
  and 141). Its Proposition 3.1 mean square for H = D^(1 + theta), 0 < theta <= 1/10, is what
  Guo's Hypothesis 11.1 asks to extend (cited, Guo section 11 line 33, whose citation is the
  5 October preprint, references.bib line 13).
- **Siegel exclusion write-ups** (cited, abstracts and pages): Banks, arXiv:2610.15483
  (2026-10-11), (1 - beta) log q >= 3.0e-3 for q >= 10^10, and for every q >= 3 with a
  computation of Lu, Zaman and Zhao; Kerr, arXiv:2610.21099 (2026-10-15), a simpler proof
  through a pigeonhole construction and Masser's degree bound, constant not explicit; Green,
  hexagon:2610.00311 (v1 2026-10-17, v2 2026-10-18), the bound "sum over p <= X = q^C with
  chi(p) = -1 of (log p)/p <= (1/2 + O(1/C)) log X + O_C(1)", arguments attributed to
  ChatGPT, text human-written. **Tao's sketch** (blog, 2026-10-19) presents Green's
  formulation and says the quasi-Riemann papers "are still in the process of being fully
  digested, and I will not be discussing them further here" (cited).

## 9. Commentary

Quanta (Konstantin Kakaes, 2026-10-19): mathematicians "have set aside the 7/8 paper to
focus on the 11/12 one" (cited, line 125). The experts' write-ups of seven to 13 pages
concern that 11/12 paper, and those experts "largely agree that the result is correct"
(cited, line 142); Sarnak will not call it a theorem "until humans check and understand all
the details" (cited, line 150). So the agreement Quanta reports is about the 11/12 paper,
not the 7/8 argument this hunt reads (inferred from lines 125 and 141 to 142). Statements
quoted there and on Tao's blog about how far these methods are from RH itself are out of
this hunt's scope (`MISSION.md`) and are not recorded here.

## 10. Checks run on this page's data, and the planted faults

Every checker named here lives outside the tree, in session scratch storage; none of them is
a test of this tree.

- **Repair r4's pair.** `check_followups_r3p.py` is repair r3's checker with three patches
  only: a source may name its own root, the numbers r4 added join its recomputed list, and
  r4's withdrawn wording joins its ban list. On the shipped files it rehashes all 44 sources
  and the pinned paper; checks all 222 quotations, 210 by line and 12 by substring; and runs
  everything else r3's checker ran: the roots and full decimals of B_alg, B_new and B_flat,
  Newton's B_lim against his printed digits, X1 to X14, each record against its section 2
  row, each tracker row and the section 4 table against the catalogue, the Part II inputs
  and the section 5 table, the page's numbers, fractions and gaps, the stated counts, the
  reserved stem, dashes and withdrawn wording. `check_followups_r4.py` is new and shares no
  code with the earlier checkers. It re-reads every source and quotation; checks PR 69
  against the fetched pull list and check runs and the live catalogue copy; recomputes X15
  to X18 and the part (a) numbers; and audits the page at every occurrence: each decimal is
  a truncation of a known value or appears in a hashed source, each e-notation gap is
  recomputed, each prose line reference points at a quoted line of the source named nearest
  before it, each stated gap has the right direction, and the X10 sign, the refereed flags,
  the grade fields, the identity claims, the section 4 cells, the Lean column, the dates,
  pinned grade phrases and the section 5 value cells agree with the JSON and the sources.
  Both report GREEN on the shipped files.
- **Earlier checkers.** Repair r2's checker (`check_followups_r2.py`) reports GREEN on the
  shipped files. Repair r3's unpatched checker and the lane's original checker
  (`check_followups.py`) stop with a file-not-found error at the first source kept outside
  the download root, because they look for every source there and r4 keeps four sources in
  session scratch storage. On the r3 files, which they were written for, r3's checker was
  GREEN and the original checker failed only on 167/192 written as a truncation (measured
  again here). The adversarial verifier's twenty plants on prose, grades, dates and signs
  (`my_plants.py`), rerun here against r3's checker on the r3 files, left it GREEN in 19 of
  20 cases (measured); only the edited I9 line list went RED. That is why r4 wrote a second
  checker rather than only patching r3's.

**Planted faults (measured).** Thirty-two faults were planted in copies of the two files
(harness `plant_r4.py`; both checkers run on every copy): the adversarial verifier's twenty,
adapted where the r4 text moved, and twelve aimed at what r4 added (PR 69's bound, gap,
status, direction and check-run hash; Liu v2's limiting ell; the -7d/8 citation; the gain
over B_new; I7's absence grade; an em dash inside a PR 69 quotation; an e-mail address in
the JSON; the withdrawn part (a) framing). All 32 go RED: 6 under both checkers, 25 under
the r4 checker alone, and 1, the edited I9 line list, under r3p alone, so of the adversarial
verifier's twenty the r4 checker catches 19 and r3p the last one. The unplanted files are
GREEN under both. Several faults in the r4 checker's own first draft showed up on the
unplanted files and were fixed before the plant run, among them: it read e-notation gaps
with their sign, so it rejected the correct 5.30e-8; it looked for a source name only
before the word "lines", so it missed the one in "Cycle61 paper lines"; and it took
"Quanta reports" for a citation of Cureton and Thorner's report.

## 11. Not found, and limits of this reading

- No follow-up is refereed. None is presented here as established.
- No follow-up improves the sixth-power amplification slope unconditionally, and none
  claims a route toward 1/2.
- No report was found, in what was read, of a person checking the mathematics of a tracker
  proof or of the 7/8 argument.
- The tracker's Lean sources, the papers of PR 37 to PR 67 other than Cycle61, PR 69's
  sources and paper, the Watson B127 module, Acer's post, the Liu v2 Lean repository and
  Newton's 294-page record were not read; their rows rest on metadata and abstracts.
- Searches covered: arXiv (API queries for "quasi-Riemann", "zero-free half-plane", OpenAI
  in math.NT), Hexagon search, the QuasiRiemannTracker catalogue and all 63 of its pull
  requests, the GitHub repositories named above, Zenodo, Tao's blog and Quanta, all by
  15:00Z on 2026-10-21. Repair r4 re-fetched the tracker catalogue, its ten newest pull
  requests and PR 69's check runs between 21:28Z and 21:38Z, and reran the arXiv query for
  "quasi-Riemann" at 21:30Z, which returned the same 15 entries as at 14:50Z (measured).
  Hexagon, Zenodo and the GitHub repositories were not searched again, and anything else
  posted after 15:00Z is not covered.

## 12. What the repairs changed

The verifier's pass found no fatal or major issue and ten minor ones. Repair r2 (15:52Z)
made part of the changes; repair r3 kept them and made the rest; repair r4, a re-run of the
repair step on the same list, found each of the ten handled and made the further changes
listed last. Withdrawn wording is not repeated here; what replaced it, in r2 and r3:

- v1 called the mission's number beaten and superseded; it now says smaller abscissae were
  claimed before the hunt opened. Newton's rational is no longer called a record, because
  it lies above B_flat (X11).
- v1 put everything the tracker gained between 0.8748087 and the 13/15 floor. That is
  withdrawn: the tracker's gains run from B_flat to 0.8748087. r3 then made the 13/15 room
  below that conditional on the later tracker entries staying inside the floor model; r4
  separated the two questions (below). I9 moved from the inputs not improved to the open
  ones.
- v1 said Liu, Guo, and Xu and Sang had proved the total-accounting step in print; it now
  says they claim it with proof in unrefereed preprints.
- v1 said every printed improvement below 7/8 rederives the direct estimate; that is now
  restricted to the follow-ups read at source level, with Liu v1 and Guo section 3 quoted.
- v1 said no person was reported to have reviewed the tracker's proofs; it now says the
  tracker merges after a review of unstated scope and that no check of the mathematics by a
  person is reported.
- Citations repointed: Watson's floor (catalogue line 1035 and the PR 53 body), PR 26
  (explanation.md lines 10, 11, 21 and 22), the substituted bound (tracker README lines 103
  to 107, now hashed), I8 (paper lines 15726 to 15801), the sixth-power slope (15101 to
  15104), I9 (the openings of Lemma 14.3 and Proposition 15.2 at 7747 and 8340). Guo's page
  count, which came from an unsaved README, was dropped.
- The URL containing the reserved stem was replaced by the owner's URL and the commit, and
  the stem is now banned in both files outright. The commentary on RH itself was dropped as
  out of scope.
- Rubinstein and Restrepo Borrero's 11/8 consequence was added; ProofCouncil's rational was
  separated from B_new; Levy's and B_lim's decimals were made truncations; empty evidence
  lists were filled for ProofCouncil, nielstron, Levy, Collet, Rubinstein, the
  primitive-roots base and tracker PR 8, PR 15 and PR 52.
- The tracker rows keep their JSON key `tracker_frontier_records`, but the JSON now says
  they are all records below B_flat, not only record-setting ones (X12).

Repair r4 (from 21:22Z):

- The open draft PR 69 (0.8747729897, verification pending) is recorded in section 1 (item
  4), under section 4's table and in the JSON's frontier block and other tracker records;
  item 3 now says smallest merged on the tracker, and the kill-condition reading names both
  numbers.
- Part (a) is reframed. Its window, between 13/15 and the public bar, does not depend on
  the tracker's floor model; the tracker line is the closest public analogue of part (a),
  not part (a) itself, because it builds on Levy's weighted numerator; and the strict
  setting's best public number is B_new, so a part (a) result must gain more than 1.48e-4
  over it (X16). Only the tracker line's own bound depends on the floor model.
- Liu v2's -7d/8 is now cited at arXiv:2610.12234v2 lines 3003 and 3004 (it sits on line
  3004); Liu's number-field paper joins the total-accounting citations (arXiv:2610.26835
  lines 968 and 969); the sentence on follow-ups read at source level now names the five
  quoted and says Newton inherits Xu and Sang's step (inferred).
- Liu v2's limiting ell in the JSON is now the truncation 0.1668385889 of his printed digits
  (X17), with arXiv:2610.12234v2 lines 329 and 332 quoted; Gao's PR 68 constants are given
  as printed, not rounded; hunt #134's two exact lower bounds are given as fractions beside
  their rounded printed forms.
- Grades: I2 and I7 say their absence of an improvement is inferred; section 6's last
  paragraph is graded; section 3 says the tracker changes inputs that Liu's system holds
  fixed, without claiming an exact match to his list.
- Provenance: Guo's commit time and his README at cacbab49, tomoto0's commit record, the
  arXiv page that dates Liu's B_flat, the opening dates of PR 9 and PR 53 and the Quanta date
  are now quoted from hashed sources; section 8's back-references name the report and the
  AxiomMath README.
- Closed: the ROWCOUNTS.md wording issue (that file now says claimed with proof in
  unrefereed preprints, read at 21:43Z), and v1's question about Bhargava's N = 6000, which
  the verifier showed is no conflict: a half-plane Re s > 31/32 contains Re s > 1 - 1/6000
  (Bhargava's page was not read here).

## 13. Open issues

- The cited sources live outside the tree, under the download root above, and repair r4's
  re-fetches and the verifier's copy of Guo's README at cacbab49 sit in session scratch
  storage that is swept when idle (`followups.json`, `source_root_override_note`). No tree
  test can replay the hashes or quotations until they are vendored or re-fetched by URL,
  commit and hash.
- Identities X1 to X18 and the numbers on this page are scratch-exact only; no test in the
  tree pins them. The scratch checkers pin numbers, hashes, quotations and selected prose;
  most prose-level grades are pinned by nothing that can fail. The test lane should pin
  them from `followups.json`, which carries the polynomials, isolating intervals,
  identities, catalogue rows and table keys.
- The tracker's Lean sources were not read. Whether PR 63, 66, 67 and 68, and the draft PR
  69, keep the low exponent l_x/2 + b/12, the h/6 signal and M + l = 1, and so stay inside
  the 13/15 floor model, is not established.
- PR 69 was read only at the level of its pull-request text, metadata and check list. It may
  be verified and merged, changed or closed after 21:38Z, so whoever uses 0.8748087 or
  0.8747729897 as the bar should check it again.
- `MISSION.md` (question, frontier, huntspec) and the `hunts/README.md` case-log entry still
  name 0.8748867. The smallest bound merged on the tracker is 0.8748087, B_flat is the
  smallest in a paper outside it, and the open draft PR 69 claims 0.8747729897. This lane
  may not edit those files.
- This hunt's `probe_table.py`, `rowcounts.py` and `amplification/price.py` use 8748087/10^7
  as the record. That is right for merged bounds; they do not weigh PR 69.
- Not read first-hand: Acer's 3/4 post, Watson's B127 module, Liu's v2 Lean repository,
  Newton's full record, and PR 69's Lean sources and paper.
- Repair passes r2 and r3 edited these two files without coordinating; r3 merged r2's
  changes, and r4 checked before writing that the files were still r3's.
