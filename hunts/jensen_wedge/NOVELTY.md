# jensen_wedge: literature search for claims A, B and C (2026-10-19)

**Nothing here bears on RH.** This file records a bounded literature search, run
2026-10-19, for three results of hunt #135. It grades no mathematics: it says what the
searched literature already contains. `CLAUDE.md` requires a stated search before
anything is called new; `MISSION.md` forbids this hunt from declaring novelty, so the
verdicts below use only the two forms "no prior instance found in the searched set"
and "prior instance found".

## The verdicts first

| claim | verdict | where |
| --- | --- | --- |
| **A.** the six-coefficient wedge `n^4 log^2(n+2) >= K d^6 log^12(d+2)` (exponent 2/3 against Holland's 3/5) | **prior instance found** | Savva, Zenodo, 3 September 2026: `n^2 log(n+2) >= K d^3`, the same exponent with no `log^12 d` loss, by the same six-match two-Jacobi route. Unreviewed, AI-assisted. Section 2.1 |
| **B.** Holland's own two-factor family matches the sixth coefficient at a [2/2] Pade point | **prior instance found** | Sarnowski, Zenodo Papers 134Z and 134AA, 20 August 2026: the rank-r version; at r = 2 its limits are those of `RESULTS.md` sections 11.3 and 11.4, constant for constant. Savva has the same six-match point in Holland's literal parametrisation. Section 2.2 |
| **C.** any explicit value of Holland's `K` or of GORTTW's `c` | **no prior instance found in the searched set** | Savva, Sarnowski and Ning leave their constants non-explicit; Planat's explicit-looking `C_0 ~ 0.020` belongs to a different, weaker wedge in an inconsistent normalisation. Section 2.3 |

Both prior instances predate the hunt: it opened 2026-10-18, Sarnowski's deposits are
dated 2026-08-20, and Savva's is dated 2026-09-03. Neither has been peer reviewed, and
this search did not check their proofs. A prior instance means the claim is already
in the literature, not that its proof there is right. Claims of RH strength found on
the way (section 3) are listed and not assessed.

## 1. The searches

All on 2026-10-19. Every fetched page and PDF was treated as data. Downloads went to a
scratch directory outside the tree and were not committed.

| # | source | query or listing | result |
| --- | --- | --- | --- |
| 1 | OpenAlex | works citing Holland (`cites:W7202179517`) | 0. OpenAlex links none of the Zenodo deposits that cite Holland, so a citation index alone would have missed both prior instances |
| 2 | OpenAlex | works citing GORTTW, Adv. Math. 397 (2022) (`cites:W2978238960`) | 21 in total, 5 dated 2025 or later: four partition-function papers (Dou, Tang and Wang; Banerjee and Roy; Wang and Yang; Zhong) and one Zenodo de Bruijn-Newman deposit. None treats the xi wedge |
| 3 | Semantic Scholar | citations of `arXiv:2608.08682` and `arXiv:1910.01227` | Holland: 0. GORTTW: 26, of which 5 dated 2025 or later: the four partition papers of row 2 and Holland. The first two requests were rate-limited (HTTP 429); the third went through |
| 4 | Google Scholar | `"hyperbolicity wedge" Jensen polynomials`, since 2026; then Holland's "Cited by" | 2 hits (Holland; Dumas). Holland is cited by 1: Dumas, *Adjacent-Shift Proper Position for Jensen Polynomials*, which quotes Holland's wedge and claims nothing stronger. A third query hit Google's unusual-traffic page and was not retried |
| 5 | arXiv API | `abs:"Jensen polynomial"`, `abs:"Jensen polynomials"`, `ti:Jensen AND abs:hyperbolic`, `abs:"hyperbolicity wedge"`, `abs:Jensen AND abs:"xi-function"`, sorted by date, 2025 onward | 25, 25, 9, 0 and 6 hits. From 2025 on: Banerjee, Bringmann and Rolen 2609.14295; Dimitrov and Shapiro 2606.17864; Campbell and Jalowy 2605.31356; Shapiro 2605.29991; Ono 2511.02628; Holland 2608.08682. The full text of 2609.14295v2 cites neither Holland nor GORTTW. None reaches past Holland |
| 6 | arXiv full text | no full-text endpoint exists | approximated by rows 4 and 9, which index arXiv full text. This leg is therefore thin |
| 7 | zbMATH Open API | `ti:Jensen & ti:polynomial & py:2019-2026`; `Jensen polynomials Riemann xi`; `ab:"Jensen polynomials" & ab:hyperbolic & py:2022-2026` | 6, 12 and 4 documents. Relevant: GORTTW (Zbl 1490.11086), O'Sullivan (Zbl 1479.11146), Kim and Lee (Zbl 1494.30013), Wagner (2020, 2022), Griffin and South (2023). Nothing from 2026 on the xi wedge, and Holland is not indexed. A `ci:` citation query returned no result set, so the zbMATH citation leg did not run |
| 8 | OpenAlex | `title.search:Jensen polynomial` from 2025-01-01, plus abstract searches since 2026-08-01 for `Holland Jensen`, `Jensen hyperbolicity xi`, `explicit constant Jensen hyperbolic` and `Jensen polynomials wedge` | 19 title hits outside Sarnowski's series; section 3 lists them. This is the search that found Savva, Ning and the Sarnowski series |
| 9 | OpenAlex | author `Sarnowski`, `Jensen`, from 2026-08-01 | 45 Zenodo deposits, 2026-08-18 to 2026-08-28 (Papers 134H to 134DG, 140A, 140B). Abstracts read for 134O, 134Y, 134Z, 134AA, 134AB, 134AC, 134AE, 134AF, 134AT, 134BR and 140A; the full text of 134AA was read |
| 10 | web search | `Holland "hyperbolicity wedge" Jensen polynomials xi improvement`; `Planat Jensen polynomials preprints.org asymptotic hyperbolicity 2026` | Holland, GORTTW, O'Sullivan and the two Planat articles. No preprints.org version of Planat's Jensen articles |
| 11 | OpenAlex | author `Planat`, 2026 | 35 works. The preprints.org items (202601.2003, 202604.0442, 202606.1957, 202608.1692) are, by title, about Painleve or theta-kernel positivity, not Jensen thresholds. The title *Asymptotic Hyperbolicity of Jensen Polynomials ...* is the MDPI article Mathematics 14 (2026) 1884, not a preprint |
| 12 | MDPI, in a browser | both Planat articles read in full (curl and WebFetch got HTTP 403) | section 4 |
| 13 | GitHub, `gh` | `the-omega-institute/trureturing` PRs matching `Holland`, `wedge`, `Savva`, `two-thirds`, `hyperbolicity`, `2608.08682` | only #15294 (merged 2026-10-10) cites Holland, and it is citation-only. The later Jensen PRs read (#15316, #16194, #16633, #17294) claim no wedge improvement. #15316 records the `d <= 9e24` all-shift range from GORTTW Theorem 1.2 with Platt-Trudgian, the figure `MISSION.md` derives |
| 14 | GitHub and Zenodo | Savva's repository `aimathpapers/Jensen-2-Thirds` (README, main paper source); Ning's PDF; O'Sullivan arXiv:2007.13582 | sections 2 and 3 |

**What the set does not cover.** It includes no journal full-text search beyond MDPI and
no MathSciNet. Zenodo was reached only through OpenAlex's index (its own API refused
scripted requests), and only through titles and abstracts that OpenAlex holds.
Sarnowski's other 33 deposits were not opened. Savva's Lean development and technical
supplement were not read.

## 2. What was found, claim by claim

### 2.1 Claim A: Savva's two-thirds wedge

John Savva, *A Two-Thirds Hyperbolicity Wedge for Jensen Polynomials of Riemann's
Xi-Function*, Version 1.1, 3 September 2026, Zenodo `10.5281/zenodo.22293642` (OpenAlex
lists `10.5281/zenodo.22293641`); repository `github.com/aimathpapers/Jensen-2-Thirds`.
Its Theorem 1.1, in GORTTW's normalisation `xi(1/2 + w) = sum gamma(n) w^(2n)/n!`, states
(paraphrased): for an absolute `K > 0` and all `d >= 1`, `n >= 0`, the condition
`n^2 log(n+2) >= K d^3` implies that `J^{d,n}` has exactly d distinct negative real zeros.

Squared, the condition reads `n^4 log^2(n+2) >= K^2 d^6`. That is claim A without the
`log^12(d+2)` factor, so Savva's statement, if correct, implies claim A. The route is
the one `RESULTS.md` sections 11 and 12 follow:

- Holland's `3F2(-d, A, C; B, D)` model with D free, fixed by four quotient coordinates
  and two normalisations so that six coefficients match;
- the limiting zero `(alpha, t, w, delta) = (3, 2, 16/3, 1/3)` of its matching map, that
  is `A ~ 3nL`, `C ~ 2n`, `B - C ~ 16n/(3L)` and `D ~ n(1 + 1/(3L))`, which are the
  leading-order values of section 11.3;
- a Banach contraction around that point (`det DF = -1/144` in Savva's coordinates), the
  role H1 plays in `H1_H3.md` section 4;
- the observation that Holland's localisation hypothesis `(C - D)/D <= 1/4` fails on this
  branch, where the ratio tends to 1 (section 11.3 has `(C - D)/D -> 1`), and a
  replacement through a shifted `3F2` recurrence where section 12 uses Lemmas A to C;
- a six-node complex Hermite-Genocchi remainder at radius `sqrt(nd)`, giving
  `d^3/(n^2 log n)`, the role of Proposition 2.2_6 in section 12.1.

Status as Savva states it: written with substantial AI assistance, mainly from one named
OpenAI model, and with no human mathematical review or peer review claimed. The Lean
development is conditional on literature inputs entered as typed records (Jacobi,
Martinez-Finkelshtein-Morales-Perales, Marcus-Spielman-Srivastava). This search did not
check the proof.

A second, weaker prior instance concerns the exponent heuristic only. Sarnowski's Paper
134Y (20 August 2026) shows that five matches plus a fifth-derivative bound on a
`sqrt(nd)` disk reproduce Holland's 3/5, and Paper 134Z's conditional 3/4 and 4/5 wedges
are the rule `d <~ n^(1 - 2/m)` at m = 8 and 10. This is the
heuristic `MISSION.md` derives under Q1, there marked as derived in-tree.

### 2.2 Claim B: Sarnowski's diagonal Pade spines

Michael Sarnowski, *Paper 134Z: Multi-Jacobi Protected Spines and Higher-Order Matching
in the Riemann xi Jensen Hierarchy*, Zenodo `10.5281/zenodo.22023893`, 20 August 2026;
and *Paper 134AA: Jacobi Cancellation Skeletons and All-Large-Shift Geometry of
Multi-Jacobi Protected Spines*, Zenodo `10.5281/zenodo.22025447`, 20 August 2026. Read:
134AA in full, 134Z in abstract.

134Z builds a rank-r rational quotient spine by diagonal rational interpolation of the
adjacent normalised coefficient ratios. It matches 2r + 2 coefficients and factors into
Jacobi strands joined by finite-free convolution. A model `3F2(-d, A, C; B, D)` has
adjacent coefficient ratio `(A + j)(C + j)/((B + j)(D + j))`, a [2/2] rational function
of j, so the rank-2 spine is Holland's two-factor family with D free. That identification
is read from 134AA's definitions; 134Z's rank-2 text was not read. 134AA proves, for
every fixed r and all large shifts N:

- the rescaled spine tends to the diagonal [r/r] Pade approximant of `(1 + y)^alpha_N`,
  with `alpha_N = 1 - eps_N` and `eps_N ~ 2/L_N`. This is section 11.1's statement that
  matching is Pade agreement with the binomial `f_eps`;
- at `alpha = 1` numerator and denominator share the Jacobi factor `P^(1,1)_(r-1)`, which
  134AA calls the cancellation skeleton. At r = 2 its single zero gives the interior node
  `lambda = 2`, which is section 11.3's Lobatto (Simpson) limit with nodes at 0, 1/2
  and 1 in the variable `w = n/p`;
- one escaping pole with `eps_N A_(r,N)/N -> r(r + 1)`: 6 at r = 2, so `A ~ 3NL`, as in
  section 11.3; and `B_1/N -> 1`, section 11.3's `D ~ n`;
- the first unprotected derivative obeys `N^(2r+1) E^(2r+2)(0)/eps_N -> -C_r` with
  `C_r = (r+1)(r!)^4/(r (2r)!)`. At r = 2, `C_2 = 1`, so `E^(6)(0) ~ -2/(N^5 L)`: section
  11.4's leading-order R_6 defect `E_S(6) ~ -2/(n^5 L)`, sign and constant included.

Sarnowski's Paper 134AE (`10.5281/zenodo.22026880`, 20 August 2026; abstract read) adds
section 11.3's Stieltjes argument: an exact positive Beta-Stieltjes representation of the
binomial comparison, the diagonal Pade approximant as a Gaussian quadrature, and
pole-zero interlacing. Savva (section 2.1) reaches the same six-match point in Holland's
literal parametrisation, without the Pade language.

Not found in what was read, and therefore still without a located prior instance: that
phase 0's bisected `theta_star` (the sign change of `E_F(5)` along Holland's D-fixed
family) is this Pade point (section 11.3); the measured reflection symmetry
`a1 + b2 = b1 + a2 = 1`; the restricted-class obstruction of section 11.5; and the
Davenport-Heilbronn gate of section 15. They are details of claim B, not claim B itself.
Sarnowski states that his own deposits have mixed-precision, non-interval diagnostics,
no effective starting shift, and no new hyperbolicity region.

### 2.3 Claim C: explicit constants

No searched source gives a number for Holland's K, for GORTTW's c, or for the constant of
any wedge at exponent 3/5 or 2/3.

- **Savva** makes one part explicit: `K_geometry = 522255954073519803473068032000000000000000001`
  (about 5.2e44). The final constant is `max{K_geometry, C_mult C_B6, K_finite}` with
  `N_0 = max{N_analytic, N_explicit}`. `C_B6` and `N_analytic` come from the sectorial
  saddle proof and are not computed, so the K of his wedge is not explicit.
- **Sarnowski** says 134Y does not determine Holland's constants and 134AA gives no
  effective starting shift.
- **Ning**, *An Effective d^3-Scale Criterion for the Hyperbolicity of Jensen Polynomials
  Associated with the Riemann xi-Function*, Zenodo `10.5281/zenodo.19891455`, 29 April
  2026, Theorem 9.4: an absolute `C_0` with `n + d >= C_0 d^3` sufficient. It is a
  polynomial wedge (`d <~ n^(1/3)`) that predates Holland, but `C_0` is only taken large
  enough, never computed. Holland's eight references (read in arXiv:2608.08682v1) include
  O'Sullivan but not Ning or Planat.
- **Planat**, Mathematics 14 (2026) 1884, prints `C_0 ~ 0.020` for `n >= C_0 d^4`. That is
  not Holland's K or GORTTW's c, and section 4 explains why it is not an explicit
  constant for the standard family either.

A remark derived here, unreviewed, and recorded because it bears on how much claim C is
worth: GORTTW's c is the cheap half. GORTTW Corollary 1.3 covers every `d <= 9.36e20` at
all n. For larger d and `n >= e^(d/2)`, `n^3 log^2(n+2) >= e^(3d/2) (d/2)^2`, which exceeds
`K d^5` whenever `K <= e^(3d/2)/(4 d^3)`, a quantity far above `e^(1e21)` at
`d = 9.36e20` and increasing from there. So any proved explicit bound `K <= e^(1e21)` on
Holland's K would make `c = 1` admissible in GORTTW Theorem 1.1, in both its v3 form
`c e^(d/2)` and its published form `c e^d`. The substantive explicit target is K.

## 3. Other 2026 work met on the way

None of these is a prior instance of A, B or C. The last three claim results of RH strength,
or close to it, that would subsume Holland's wedge if correct. All four are unreviewed
deposits, and this search did not assess them.

| date | deposit | relation to the claims |
| --- | --- | --- |
| 2026-04-10 | Sporyshev, Zenodo 10.5281/zenodo.19497341 | discriminant formula in the model normalisation `gamma_k = k!`; unrelated |
| 2026-05-13, 2026-09-17 | Dumas, Zenodo 10.5281/zenodo.20172307 and 10.5281/zenodo.22812117 | proper-position reformulations; the second quotes Holland's wedge and transfers it, with no stronger wedge |
| 2026-05-31 | Grant, figshare 10.6084/m9.figshare.32525328 | Wronskian identity; reduces full hyperbolicity to log-concavity |
| 2026-06-04 | Hayden, Zenodo 10.5281/zenodo.20544075 | claims d = 4 for all n, already inside GORTTW Corollary 1.3 |
| 2026-07-07 | Torregrosa, Zenodo 10.5281/zenodo.21242285 | reformulation: shift-zero hyperbolicity for infinitely many d is equivalent to RH |
| 2026-08-18 to 08-28 | Sarnowski, 45 deposits (Papers 134H to 134DG, 140A, 140B) | 134Y, 134Z, 134AA and 134AE in section 2. 134AC: a conditional near-linear degree envelope from growing rank, consistent with `MISSION.md`'s conjectured stall of this method class near `d ~ n`. 134BR and 140A: consolidations stating that RH is not proved |
| 2026-09-24 | Schieber, Zenodo 10.5281/zenodo.22936341 | Marchenko-Pastur and semicircle limits conditional on hyperbolicity; neighbours Holland's semicircle theorem, not the wedge |
| 2026-05-24 | Hayden, Zenodo 10.5281/zenodo.20366857 | claims every `J^{d,n}` with `n >= 1` is hyperbolic; would subsume the wedge; not assessed |
| 2026-09-25 | Chen, Zenodo 10.5281/zenodo.22951676 | claims all n >= 0 and all d, hence RH; not assessed |
| 2026-10-15 | Chung, Zenodo 10.5281/zenodo.23405056 | claims all d and all shifts; not assessed |

Older work checked for claim C: O'Sullivan, Res. Math. Sci. 8 (2021) 46 (arXiv:2007.13582).
His Theorem 1.3 makes a Hermite-modified family `P_{d,n}`, not `J^{d,n}`, hyperbolic for
`n/log^2 n >= d^(3/4)/2` once d is large enough. There is no explicit threshold.
Kim and Lee, J. Korean Math. Soc. 59 (2022) 775 (Zbl 1494.30013): by its review, an
improvement of GORZ for derivatives; no explicit wedge was found in the review.

## 4. Planat 2026, read critically

Two articles by Michel Planat, both in MDPI *Mathematics*: *Asymptotic Hyperbolicity of
Jensen Polynomials and the Finite-Strip Obstruction to the Riemann Hypothesis*, 14 (2026)
1884, 28 May 2026, doi 10.3390/math14111884; and *Parity Bifurcation, PIII(D6) Topology,
and a Stieltjes Framework to Jensen Polynomial Hyperbolicity*, 14 (2026) 2240, 23 June
2026, doi 10.3390/math14132240. Both were read in full in a browser.

**What 1884 states.** Theorem 3 (paraphrased): there is a constant `C_0^inf > 0` such that
`J^gamma_{d,n}` is hyperbolic for all `d >= 1` and `n >= C_0^inf d^4`, with
`C_0^inf ~ 0.020` given numerically. Theorem 4 bounds the onset index by
`n*(d) <= C_0^inf d^4` and gives the formula
`C_0^inf = (6/pi)(C_2^eff + C^tail + C^bulk) ~ 0.0195`.

**Is it uniform in d?** One constant serves every d, but the threshold grows like `d^4`.
That is a wedge `d <~ n^(1/4)`, weaker than Holland's `n^(3/5)`, and GORTTW Corollary 1.3
already covers every `d <= 9.36e20` at all n. It is not "for all n >= C" independent of
d. The summary that credited such a statement misread `n >= C_0^inf d^4`.

**What is proved and what is asserted.**

- The `d^4` exponent is chosen, not derived. Remark 5 notes that a cruder estimate gives
  `d^(5/2)` and sets it aside because it disagrees with the observed onset scaling. In
  Step 3 of the proof the bulk constants `C_{d,k}` depend on d and k and are summed
  without a uniform bound.
- `C_0^inf` uses an effective `K_tau ~ 0.62` fitted on `n <= 23` (the paper's own
  analytic limit is `K_tau = 1`), and components evaluated at the single reference point
  `(d, n) = (8, 4)`.
- Proposition 2(iii)'s bound `|eps_n| < 2.9/(n+1)`, on which Lemma 1 rests for
  `n >= 10`, is checked numerically for `n = 10..50` and asserted beyond.

**Normalisation.** The paper sets `M_n = int_0^inf Phi_1(u) u^(2n) du`, where `Phi_1` is
twice the first term of the theta series, and identifies `gamma(n) = M_n` although its own
definition of `gamma(n)` carries a `1/(2n)!`. Constant factors and a rescaling `t -> 2t`
do not matter for hyperbolicity, but the dropped `(2n)!` does, and so, slightly, do the
dropped `k >= 2` terms. The family is then used two ways:

- Lemma 1's `b_n > (2n+1)/(2n+3)`, with `b_n = M_(n+1)^2/(M_n M_(n+2))`, is exactly the
  Turan inequality for GORTTW's `gamma(n)`, which is proportional to `n! M_n/(2n)!`
  (derived here: `gamma(n+1)^2/(gamma(n) gamma(n+2)) = b_n (2n+3)/(2n+1)`).
- Remark 2 computes the `d = 2` discriminant from raw `M_n`, finds it negative because
  moments are log-convex (`b_n < 1`), and concludes that `J_{2,n}` has no real zeros at
  any n.

Measured here, once, by mpmath quadrature at 25 digits on one route (not pinned by a
test): with the full kernel, `b_n` is 0.35828, 0.63765, 0.75307 and 0.81515 at n = 0..3,
so `b_n < 1`, and the Turan ratio of the standard `gamma(n)` is 1.0748, 1.0627, 1.0543 and
1.0481. The standard `J_{2,n}` is hyperbolic at those n, so Remark 2 holds for the
raw-moment family and fails for the standard one. Keeping only the first theta term moves
`M_0` by a relative 3.5e-4. The paper also places a positive onset at every `d >= 9`,
which for the standard family contradicts GORTTW Corollary 1.3 (`n*(d) = 0` for
`d <= 9.36e20`) and Chasse (`d <= 2e17`). So the family on which its onset numbers were
measured is not the standard `J^{d,n}`, and Theorem 3 does not transfer to Holland's or
GORTTW's polynomials as written.

**Comparison with Holland or GORTTW.** None. 1884 has 12 references, and the only Jensen
work among them is GORZ 2019. Holland postdates both articles. 2240 cites GORZ and
Planat 1884.

**2240.** A numerical study of an onset for `5 <= d <= 16`, again positive where the
standard family is hyperbolic at every n. It offers conjectures only (Conjectures 1 and
2), no hyperbolicity theorem. Its Pade approximants belong to a cumulant generating
function `B(w)`, with poles near the squared zero ordinates. That is unrelated to claim
B's comparison family.

## 5. What this changes for the hunt

Claims A and B already have prior instances, so the hunt's phase 1 result is an
independent re-derivation of results deposited 6 to 9 weeks earlier, not a delta against
Holland that the lab could claim. Two parts of it still differ from what was found:
- it is conditional where Savva states an unconditional theorem;
- it carries a `log^12 d` loss that Savva's statement does not.

Phase 2 (MISSION Q2, explicit constants) has no located prior instance and is the open
target. Savva's `K_final` structure is the nearest prior work and could serve as a
comparison: an explicit K for Holland's wedge or for Savva's wedge would be a delta
against both. Per section 2.3, an explicit bound on K also settles GORTTW's c at once.
Whether to redirect phase 2 is the owner's decision, and this file does not make it.
