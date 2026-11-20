> **Landing note (2026-11-20).** These are one reader's literature notes, written inside a working
> session on the day a Lean proof of RH and of GRH for Dirichlet L-functions was posted, and landed
> here unedited except for three things: a machine-local path was replaced, section 6 (press relay
> of social-media posts that were not opened at their source) was cut to a summary, and this note
> was added. They are the source the regrade board beside this file cites as `literature.md`.
> The labels VERIFIED TODAY, SECONDARY and RECALLED are the reader's own and mean what the method
> paragraph says. Four table rows of Garcia, Grenie, Lee and Molteni (h0 = 500, 1000, 1500, 2000)
> were re-read from the arXiv PDF by the session that landed this file. Nothing here is a result
> of this laboratory. Per this directory's contract, the tree decides and the memo proposes.

# literature: what is already published under GRH / RH, for the lab's delta statements

Reader label: literature. Date of reading: 2026-11-20. Region: the published literature (web), no archive reading.

Method. arXiv PDFs were downloaded to
session scratch storage (not kept)
and converted with `pdftotext`. Statements marked VERIFIED TODAY were read in that text layer. Prose
quotes are verbatim; displayed formulas are re-typeset by me from the text layer (the layer scrambles
two-dimensional layout), so a formula is "verbatim in content, re-typeset in form". Statements marked
RECALLED were not read from a primary source today. Statements marked SECONDARY were read today, but in
another paper quoting the original. The AMS journal site (Math. Comp.) returned HTTP 403 / a bot wall to
both curl and the fetch tool, so Watkins 2004, Bach 1990 and Schoenfeld 1976 could only be read
through other primary papers quoting them.

Float evaluations labelled "my evaluation" are measured (one route, Python floats), not enclosure-carrying.

---------------------------------------------------------------------------------------------------

## 0. The headline for the builders (read this first)

**H1. A complete GRH list of imaginary quadratic fields for every h <= 2000 is already public, and it
was posted one day after this lab's October 8 results.**
S. R. Garcia, L. Grenie, E. S. Lee, G. Molteni, "Bounds for the residue of Dedekind zeta functions under
GRH and applications", arXiv:2610.14257v1, submitted Fri 9 Oct 2026 19:21:41 UTC, 15 pages (the PDF's
own date line reads "Date: October 14, 2026"). Abstract, verbatim: "The new lower bound enables all
imaginary quadratic fields with class number <= 2000 to be detected (assuming GRH)." Data:
https://sites.unimi.it/molteni/research/class_numbers/class_numbers.html (file
`classes-list-2000.txt`, 162 MB, one line per class number).

Their Table 1, verbatim numbers (h0, number of fields with h_K <= h0, max |disc|):

| h0 | # fields | max disc | h0 | # fields | max disc |
|---|---|---|---|---|---|
| 100 | 42272 | 2383747 | 1100 | 4972445 | 283506787 |
| 200 | 167157 | 8377363 | 1200 | 5941733 | 351036667 |
| 300 | 372393 | 19225243 | 1300 | 6960178 | 398158363 |
| 400 | 665008 | 35723227 | 1400 | 8061896 | 480668203 |
| 500 | 1028749 | 55171603 | 1500 | 9245562 | 562394347 |
| 600 | 1488496 | 81792547 | 1600 | 10553429 | 643541347 |
| 700 | 2014583 | 114148483 | 1700 | 11881764 | 707327707 |
| 800 | 2645480 | 138731107 | 1800 | 13348410 | 805169467 |
| 900 | 3342720 | 199362403 | 1900 | 14824012 | 898772323 |
| 1000 | 4115897 | 227932027 | 2000 | 16453493 | 1062350083 |

Cross-check against this lab's `docs/39`: the lab reports for h <= 1500 "9,245,562 fields, the largest
with q = 562,394,347". GGLM's h0 = 1500 row is 9245562 fields, max disc 562394347. **Exact agreement on
both numbers**, from a different hypothesis (GRH versus the 7/8 half-plane), different lower bound,
different software (PARI/GP on PlaFRIM versus the lab's reduced-form sieve). Their h0 = 1000 row
(4115897, 227932027) also equals Cremona-Sutherland's count and largest |D|. The lab's repo does not
cite this paper or the Molteni page (rg for "molteni", "2610.14257" in docs/, hunts/qrh_class_number,
references/ returned nothing).

Consequence for the delta. If GRH for Dirichlet L-functions becomes a theorem:
- the lab's h <= 1500 list is no longer an extension of anything: h <= 2000 is published (preprint +
  data) under GRH, and under a GRH theorem it becomes unconditional by citation;
- what stays the lab's own is (i) the list under the weaker 7/8 hypothesis (which a GRH theorem makes
  moot), (ii) the independent agreement with GGLM at h <= 1500, which is now a two-route check of their
  table, and (iii) anything above h = 2000.

**H2. Above 2000 the door is open and cheap.** Cremona-Sutherland (arXiv:2301.11169v4, section 5),
verbatim: "one could use the same approach for h(D) <= 24416, but we did not attempt this." The approach
is: GRH lower bound, then read class numbers off the Jacobson-Mosunov unconditional table |D0| < 2^40.
With the sharper Languasco-Trudgian form (valid for every q >= 5), my evaluation of the lower bound at
q = 2^40 is 30175.3, so under GRH every fundamental discriminant with |D| >= 2^40 has h >= 30176, and
the unconditional 2^40 table covers every h <= 30175. At the lab's own existing cutoff
D(1500) = 12,409,254,457 the same bound evaluates to 3169.8: the lab's already-run sieve range covers
every h <= 3169 under GRH (if class numbers above 2000 were kept or the 39 CPU-minute sieve is re-run
with a higher h cap). I found no published or announced complete list (all h, even and odd) above
h = 2000. For odd h only, Holmin et al. give counts F(h) for all odd h < 10^6 under GRH.

**H3. Under RH, primes between consecutive cubes for every n is a 2005 result, and exponent 2.25 is a
February 2026 result.** The lab's seventh and ninth power results have no GRH-grade counterpart to
claim: Caldwell-Cheng (2005) give k = 3 for all n under RH; Chamberland-Straub (arXiv:2602.22502,
Theorem 1.2(a)) give [x^(2+delta), (x+1)^(2+delta)] for all x >= 1 and delta >= 1/4, with a remark that
0.2253 is reachable. Legendre (exponent 2) is open even under RH.

**H4. Under GRH the least-nonresidue, Miller-witness and Linnik statements are all already explicit at
exponent 2**: n_p < (log p)^2 for prime p >= 5 (LLS Cor. 1.1), P(a,q) <= (phi(q) log q)^2 for q > 3
(LLS Cor. 1.2), Miller witness < 2 (log n)^2 (Bach 1990). The asymptotic constants are 0.7615
(nonresidue) and 8/9 (least prime in AP) by Carneiro, Milinovich, Quesada-Herrera, Ramos.

**H5. If RH is a theorem, the de Bruijn-Newman constant is exactly 0**: RH <=> Lambda <= 0 (Newman),
and Lambda >= 0 (Rodgers-Tao). The Platt-Trudgian bound Lambda <= 0.2 is then superseded.

---------------------------------------------------------------------------------------------------

## 1. Explicit GRH bounds for L(1, chi) and for h(D)

### 1.1 Littlewood 1928 (asymptotic)
J. E. Littlewood, "On the class number of the corpus P(sqrt(-k))", Proc. London Math. Soc. 27 (1928),
358-372. NOT read today (primary). SECONDARY, read today in Languasco-Trudgian arXiv:2011.08348 eq. (1):
under RH for L(s, chi_d), chi_d quadratic, d not a square,

    ( (12 e^gamma / pi^2) (1 + o(1)) log log d )^(-1)  <  L(1, chi_d)  <  2 e^gamma (1 + o(1)) log log d.

GGLM (arXiv:2610.14257 section 1) say the same in the form c_- = zeta(2)/(2 e^gamma) + o(1),
c_+ = 2 e^gamma + o(1), and add, verbatim: "Under the same hypothesis, Littlewood also proved that these
bounds are optimal up to a factor 1/2."

### 1.2 Lamzouri, Li, Soundararajan 2015 (explicit, q >= 10^10)
Y. Lamzouri, X. Li, K. Soundararajan, "Conditional bounds for the least quadratic non-residue and
related problems", Math. Comp. 84 (2015), no. 295, 2391-2412; Corrigendum Math. Comp. 86 (2017), no.
307, 2551-2554. arXiv:1309.3595 (v1 13 Sep 2013, v2 28 Sep 2016, v3 8 Dec 2016). VERIFIED TODAY from
arXiv v3 (which incorporates the corrigendum: the arXiv comment says an error in Lemma 6.1 "affects the
asymptotic bounds in Theorems 1.2 and 1.3"). URL read: https://arxiv.org/pdf/1309.3595

Theorem 1.5, verbatim prose: "Assume GRH. Let q be a positive integer and chi be a primitive character
modulo q. For q >= 10^10 we have"

    |L(1, chi)| <= 2 e^gamma ( log log q - log 2 + 1/2 + 1/log log q ),
    1/|L(1, chi)| <= (12 e^gamma / pi^2) ( log log q - log 2 + 1/2 + 1/log log q + 14 log log q / log q ).

Corollary 1.3, verbatim prose: "Assume GRH. Let -q be a fundamental discriminant, and let h(-q) denote
the class number of Q(sqrt(-q)). If q >= 10^10 then"

    h(-q) >= (pi / (12 e^gamma)) sqrt(q) ( log log q - log 2 + 1/2 + 1/log log q + 14 log log q / log q )^(-1),
    h(-q) <= (2 e^gamma / pi) sqrt(q) ( log log q - log 2 + 1/2 + 1/log log q ).

Followed, verbatim, by: "The work of [12] computes class numbers and class groups for all imaginary
quadratic fields with absolute discriminant below 10^11. From our corollary it follows that on GRH
h(-q) >= 9053 when q >= 10^11." My evaluation of the lower bound at q = 10^11: 9052.74, consistent.

Same shape for zeta, verbatim prose: "for real numbers t >= 10^10 we have (assuming RH)"
|zeta(1+it)| <= 2 e^gamma (log log t - log 2 + 1/2 + 1/log log t), and 1/|zeta(1+it)| <=
(12 e^gamma/pi^2)(log log t - log 2 + 1/2 + 1/log log t + 14 log log t/log t).

### 1.3 Languasco, Trudgian 2022 (same inequalities, every q >= 3; class number for every q >= 5)
A. Languasco, T. S. Trudgian, "Uniform effective estimates for |L(1, chi)|", J. Number Theory 236
(2022), 245-260 (journal data as given in Cremona-Sutherland's bibliography), arXiv:2011.08348v1 (17 Nov
2020). VERIFIED TODAY. URL read: https://arxiv.org/pdf/2011.08348

Theorem 1, verbatim: "Assume the Generalised Riemann Hypothesis. Then, for q >= 3 both (2) and (3) hold
for every non-principal primitive Dirichlet character mod q." Here (2), (3) are the two LLS inequalities
of Theorem 1.5 above.

Corollary 1, verbatim prose: "Assume the Generalised Riemann Hypothesis. Let -q be a discriminant and
let h(-q) denote the class number of Q(sqrt(-q)). For every q >= 5 we have that"

    h(-q) <= (2 e^gamma / pi) sqrt(q) ( log log q - log 2 + 1/2 + 1/log log q ),
    h(-q) >= (pi / (12 e^gamma)) sqrt(q) ( log log q - log 2 + 1/2 + 1/log log q + 14 log log q / log q )^(-1).

Proof route stated: extend the LLS proof from q >= 10^10 to q >= 404, machine check for composite
3 <= q <= 1000, plus Languasco's check (arXiv:2005.04664) for every prime 3 <= q <= 10^7.

This is the strongest published explicit GRH lower bound for h(-q) valid for all discriminants that I
found. It is the bound Cremona-Sutherland use (their reference [28], "Corollary 1").

### 1.4 Garcia, Grenie, Lee, Molteni 2026 (general number fields; slightly weaker for quadratic, no range restriction)
arXiv:2610.14257v1 (9 Oct 2026). VERIFIED TODAY. URL read: https://arxiv.org/pdf/2610.14257

Theorem 1, verbatim prose: "Let K != Q be a number field. Assume GRH for the Dedekind zeta functions of
K and Q. Then the residue kappa_K of the Dedekind zeta function zeta_K of K at 1 satisfies"

    c_- / ln ln |Delta_K|  <=  kappa_K  <=  c_+ (ln ln |Delta_K|)^(n_K - 1),
    c_- = (zeta(n_K) / (2 e^gamma)) exp( -3 / ln ln |Delta_K| ),
    c_+ = (2 e^gamma)^(n_K - 1) exp( (11 - 3 n_K) / (4 ln ln |Delta_K|) ).

Corollary, verbatim prose: "Let K be any imaginary quadratic field. Assume GRH for the Dedekind zeta
function of K. Then the class number h_K satisfies the inequality"

    h_K >= (pi / (12 e^gamma)) ( sqrt(|Delta_K|) / ln ln |Delta_K| ) e^( -3 / ln ln |Delta_K| ).

Then, verbatim: "Using the corollary we see that if h_K <= h0, then |Delta_K| <= Delta0 for each pairing
(h0, Delta0) in {(1, 3 552), (100, 30 864 538), (2 000, 12 338 970 045)}. These bounds can be further
improved to (10) (h0, Delta0) in {(1, 1 592), (100, 19 124 734), (2 000, 8 213 527 466)} with a variation
of the formula that we will show during the proof of (8). A similar lower bound is proved in [15],
Corollary 1.3. Its conclusion is actually stronger than our corollary but it assumes that
|Delta_K| >= 10^10 while in our case all values are admitted." ([15] is LLS. Note GGLM do not cite
Languasco-Trudgian, which removes the 10^10 restriction from LLS.)

My evaluation: GGLM bound at 12,338,970,045 gives 2000.0 and at 30,864,538 gives 100.0 (reproduces
their pairs). For comparison the lab's 7/8-hypothesis cutoffs are D(100) = 48,611,613 and
D(1500) = 12,409,254,457; the GRH cutoffs are of course smaller.

Earlier paper by the same authors: "Explicit conditional bounds for the residue of a Dedekind
zeta-function at s=1", arXiv:2506.17416 (search result says to appear in J. Number Theory 2026; I
downloaded it but did not read it; GGLM cite it as [7] with c_- = (zeta(n_K)/(2 e^gamma))
(ln ln |Delta_K|)^(-19(n_K-1)/ln ln |Delta_K|) under GRH plus zeta_K/zeta entire).

### 1.5 Which bound to use for a GRH cutoff table
Ranking for imaginary quadratic fields, largest lower bound first (my evaluation, floats):

| q | LLS / L-T Cor. 1 | GGLM Cor. |
|---|---|---|
| 30,864,538 | 153.58 | 100.00 |
| 48,611,613 | 193.32 | 125.55 |
| 1,629,085,093 | 1139.86 | 727.40 |
| 8,213,527,466 | 2575.26 | 1632.16 |
| 10^10 | 2843.47 | 1800.72 |
| 12,338,970,045 | 3160.76 | 2000.00 |
| 12,409,254,457 | 3169.80 | 2005.68 |
| 10^11 | 9052.74 | 5684.56 |
| 2^40 | 30175.31 | 18805.47 |
| 1.1881e15 | 1000018.87 | 613100.10 |

(GGLM say a "variation of the formula" gives the better pairs in their (10); that variation was not
transcribed here.) The L-T Corollary 1 bound needs monotonicity in q to turn "h <= H" into "q <= Q(H)":
Holmin et al. state, verbatim, "It is easy to verify that the right-hand side above is monotonic for
q >= 10^10." Below 10^10 a builder must check monotonicity or use an interval table as the lab's hunt
#124 already does.

---------------------------------------------------------------------------------------------------

## 2. State of the class number problem

### 2.1 Watkins 2004: h <= 100, unconditional
M. Watkins, "Class numbers of imaginary quadratic fields", Math. Comp. 73 (2004), no. 246, 907-938.
Primary NOT readable today (AMS 403). SECONDARY, read today in three primary papers:
- Holmin et al. abstract: "The unconditional computation of F(h) for h <= 100 was completed by M.
  Watkins, using ideas of Goldfeld and Gross-Zagier".
- GGLM: "Watkins [33] determined all such fields with class number <= 100. These results are
  unconditional, that is, they are proved without assuming any unproved hypotheses."
- Cremona-Sutherland: "For h <= 100 the complete list of discriminants D < 0 with h(D) = h is known."
Count and largest discriminant for h <= 100: 42,272 fundamental discriminants (Cremona-Sutherland),
max |disc| 2,383,747 (GGLM Table 1 and the Molteni page).

### 2.2 Klaise: nonmaximal orders, h <= 100
J. Klaise, "Orders in quadratic imaginary fields of small class number", University of Warwick
undergraduate Masters thesis, unpublished (2012 per Cremona-Sutherland's bibliography). VERIFIED TODAY
(abstract). URL read:
https://warwick.ac.uk/fac/cross_fac/complexity/people/students/dtc/students2013/klaise/janis_klaise_ug_report.pdf
Abstract, verbatim extract: "In 2003 M. Watkins [Wat03] solved the Gauss Class Number Problem for class
numbers up to 100 [...] In this project we extend the problem by including non-maximal orders [...] We
then describe a different algorithm that was suggested and implemented during the writing of this
project and succesfully finds all orders of class number up to 100." Cremona-Sutherland give the total:
"There are a total of 66,758 such discriminants, of which 42,272 are fundamental." Unconditional (built
on Watkins plus the class number formula for orders).

### 2.3 Cremona, Sutherland 2023: all h <= 1000 (fields and orders), under GRH
J. E. Cremona, A. V. Sutherland, "Computing the endomorphism ring of an elliptic curve over a number
field", arXiv:2301.11169v4 (15 Dec 2023; PDF header "Contemporary Mathematics"). VERIFIED TODAY. URL
read: https://arxiv.org/pdf/2301.11169

Proposition 19 (GRH), verbatim prose: "Assume GRH, let D < 0 be a discriminant and let h = h(D). If D is
fundamental then"

    |D| <= (12 e^gamma / pi)^2 h^2 ( llog(h+1) + 4 )^2,
    and for any D:  |D| <= (12 e^(2 gamma) / pi)^2 h^2 ( llog(h+1) + 4 )^4,

with llog = log log. Proof source, verbatim: "Under GRH we may apply [28, Corollary 1]" where [28] is
Languasco-Trudgian. They simplify to (2.3): h >= (pi/(12 e^gamma)) sqrt(|D|) (llog|D| + 2.3)^(-1) for
|D| >= 2^28, and check smaller |D| against the Jacobson-Mosunov data.

Section 5, verbatim: "using the dataset computed by Klaise [24], which we extended to h(D) <= 1000 by
assuming the GRH. Under this assumption, there are 6,450,424 discriminants D < 0 with h(D) <= 1000;
these can be found in the file cmdiscs1000.txt in [13]. The largest is |D| = 227932027 with h(D) = 996.
Proposition 19 implies that every fundamental D0 < 0 with h(D0) <= 1000 satisfies |D0| <= 1629085093.
Class numbers for all such D0 can be found in the dataset computed by Jacobson and Mosunov [20], which
covers |D0| < 2^40 and can be downloaded from [30]. There are 4,115,897 fundamental discriminants
|D0| <= 1629085093 with h(D0) <= 1000, and one can use (2.1) to compute the 6,450,424 discriminants
D < 0 with h(D) <= 1000; one could use the same approach for h(D) <= 24416, but we did not attempt
this." ([13] = EndECNF repository, https://github.com/AndrewVSutherland/EndECNF; [30] = LMFDB.)

So: which h: every h <= 1000, even and odd, fields and nonmaximal orders. Which hypothesis: GRH, used
only for the cutoff (Prop. 19); the class numbers below the cutoff come from an unconditional table.
My evaluation of Prop. 19 at h = 1000 gives 1,629,085,093.03 (reproduces their number). My evaluation
at h = 24416 gives 1.09957e12, slightly above 2^40 = 1.09951e12, so with plain floats the crossing is at
24415, not 24416; they presumably used (2.3) or a slightly different rounding. Minor, flagged.

### 2.4 Jacobson, Mosunov 2016: unconditional tabulation to |Delta| < 2^40
A. S. Mosunov, M. J. Jacobson Jr., "Unconditional class group tabulation of imaginary quadratic fields
to |Delta| < 2^40", Math. Comp. 85 (2016), 1983-2009 (pages recalled), arXiv:1502.07953v1 (27 Feb 2015).
VERIFIED TODAY (abstract). URL read: https://arxiv.org/pdf/1502.07953
Abstract, verbatim extract: "Our method uses classical class number formulas involving theta-series to
compute the group orders unconditionally for all Delta not congruent to 1 (mod 8). [...] The 1 mod 8
case was handled using the methods of [JRW06], including the batch verification method based on the
Eichler-Selberg trace formula to remove dependence on the Extended Riemann Hypothesis. Our new method
enabled us to extend the previous bound of |Delta| < 2 * 10^11 to 2^40."
Data availability is described inconsistently by two sources read today: Cremona-Sutherland say the
dataset "can be downloaded from [30]" (LMFDB); GGLM say "only aggregated tables of values are explicitly
given, and the raw values of h_K are not made available." A builder should check LMFDB directly.

### 2.5 Holmin, Jones, Kurlberg, McLeman, Petersen: odd h < 10^6 under GRH (counts)
S. Holmin, N. Jones, P. Kurlberg, C. McLeman, K. Petersen, "Missing class groups and class number
statistics for imaginary quadratic fields", Experimental Mathematics 28 (2019), no. 2, 233-254 (journal
data from a search result, not from the publisher page), arXiv:1510.04387v1 (15 Oct 2015). VERIFIED
TODAY. URL read: https://arxiv.org/pdf/1510.04387
Abstract, verbatim: "conditionally on the Generalized Riemann Hypothesis, we extend Watkins' data,
tabulating F(h) for odd h <= 10^6 and F(G) for G a p-group of odd order with |G| <= 10^6." Body (section
6), verbatim: "With the aid of a supercomputer and assuming GRH, we have computed F(h) and F(G) for all
odd h < 10^6 and all p-groups G of odd size at most 10^6."
Range and method, verbatim: "by genus theory, if -q < -8 is a fundamental discriminant, then h(-q) is
odd precisely when q is prime. Corollary 1.3 in [22] states that under GRH, [the LLS lower bound] if -q
is a fundamental discriminant such that q >= 10^10. [...] This implies that if q >= 1.1881 * 10^15 then
h(-q) > 10^6. Thus it suffices to consider only discriminants in D0(1.1881 * 10^15)." And: "We use the
procedure quadclassunit0 in the computer package PARI 2.7.3 to compute the class groups H(d); this
procedure guarantees correct results assuming GRH".
So GRH enters twice: the cutoff, and the correctness of each class group computation. Note the abstract
says "odd h <= 10^6" and the body "odd h < 10^6"; the lab's papers.md says "< 10^6", matching the body.
They publish counts F(h) and lists for noncyclic p-groups (people.kth.se/~kurlberg/class_group_data/),
not a full list of discriminants per h as far as the text read says.
My evaluation of the LLS bound at 1.1881e15: 1000018.87, consistent with their cutoff.

### 2.6 Garcia, Grenie, Lee, Molteni 2026: all h <= 2000 under GRH
See H1 and 1.4. This is the current published frontier for complete lists (all h, even and odd) that I
found. Verbatim: "we have classified the imaginary quadratic fields up to our bound for 2 000, i.e. up
to 8 213 527 466 (slightly better than what is necessary if we use the bound in [15])." Software: PARI/GP
(per the Molteni page; the algorithm's own dependence on GRH is not discussed in the passage read;
PARI's quadclassunit is GRH-conditional, which matters if a builder wants an unconditional-below-cutoff
list: the lab's exact reduced-form sieve does not have that dependence).
The Molteni page title still reads "Imaginary quadratic fields with class number up to 1000 (assuming
GRH)" while the body and table go to 2000.

### 2.7 Complete list for all h above 1000 under GRH: summary
- h <= 2000: GGLM (arXiv:2610.14257, Oct 2026, preprint, with data). FOUND.
- h <= 24416: stated as feasible, explicitly not attempted, by Cremona-Sutherland. No list.
- Odd h < 10^6: counts by Holmin et al. (GRH, twice).
- Nothing found above 2000 for all h. Searches run: one extended web search for tabulations above 2000;
  it surfaced the Molteni page and nothing larger. zbMATH and OEIS were NOT searched today.

---------------------------------------------------------------------------------------------------

## 3. Least quadratic nonresidue, least prime in an arithmetic progression, Miller witnesses (GRH)

### 3.1 Bach 1990
E. Bach, "Explicit bounds for primality testing and related problems", Math. Comp. 55 (1990), no. 191,
355-380. Primary NOT readable today (AMS 403). SECONDARY, read today in LLS arXiv:1309.3595 section 1.1,
verbatim: "Assuming GRH, Ankeny [1] established that the least prime lying outside a proper subgroup H
of (Z/qZ)* is O((log q)^2). Ankeny's work was refined by Bach [2], who gave explicit as well as
asymptotic bounds for the least such prime. Thus Bach showed, on GRH, that the least prime p that does
not lie in H is less than 2(log q)^2, and if the additional natural requirement that p does not divide q
is imposed then p is less than 3(log q)^2. He further established that the least prime p not dividing q
with p not lying in H satisfies the asymptotic bound p <= (1 + o(1))(log q)^2."
Miller test consequence (RECALLED, and consistent with Wikipedia's Miller-Rabin page read today, which
says the O((ln n)^2) constant "was reduced to 2 by Eric Bach" and gives the test range
2 <= a <= min(n-2, floor(2 (ln n)^2))): under GRH every odd composite n has a Miller witness
a < 2 (log n)^2. Wikipedia adds (citing Schoof 2004) that GRH is only needed for quadratic Dirichlet
characters. Wikipedia names no later improvement of the Miller bound.

### 3.2 Wedeniwski
S. Wedeniwski, "Primality Tests on Commutator Curves", Dissertation, Tuebingen, Germany, 2001. Primary
NOT read. SECONDARY, read today in LLS section 1.1, verbatim: "In the special case when H consists of
the square residue classes (mod q), Wedeniwski [16] has recently given the improved explicit bound
(3/2)(log q)^2 - (44/5) log q + 13." (Under GRH; range of q not stated in the LLS sentence.)

### 3.3 Lamzouri, Li, Soundararajan 2015 (VERIFIED TODAY, arXiv v3)
Theorem 1.1, verbatim: "Assume GRH. Let q >= 3000 be an integer, and let H be a proper subgroup of
G = (Z/qZ)*. (1) Let A(q) = max(0, 2 log log q - 8/5 - sum_{p|q} (log p)/(p-1)), and put
B(q) = max(0, 2 log log q + 3 + 2 omega(q)(log log q)^2 / log q - 2A(q)). The least prime l with l not
dividing q and l not lying in the subgroup H satisfies the bound l <= (log q + B(q))^2. (2) Suppose q is
not divisible by any prime below (log q)^2. Then there is a prime l <= (log q)^2 with l not lying in the
subgroup H."
Corollary 1.1, verbatim: "Assume GRH. If q >= 5 is prime, the least quadratic non-residue (mod q) lies
below (log q)^2."
Theorem 1.2 (corrected version), verbatim: "Assume GRH. Let q be a large integer and let H be a subgroup
of G = (Z/qZ)* with index h = [G : H] > 1. Then the least prime p not in H satisfies
p < (alpha(h) + o(1))(log q)^2, where alpha(2) = 0.8, alpha(3) = 0.7 and in general alpha(h) = 0.66 for
all h > 3." (CMQR cite the corrected LLS quadratic constant as 0.794.)
Theorem 1.3: for h >= 4, p < (1/4 + o(1)) (1 - 1/h)^2 ( log(2h) / (log(2h) - 4) )^2 (log q)^2.
Theorem 1.4, verbatim prose: "Assume GRH. Let q >= 20000 and let H be a subgroup of G = (Z/qZ)* with
index h = [G : H] > 1. Let p be the smallest prime lying in a given coset aH. Then either p <= 10^9, or"
p <= ( (h-1) log q + 3(h+1) + (5/2)(log log q)^2 )^2.
Corollary 1.2, verbatim: "Assume GRH. Let q > 3, and let a (mod q) be a reduced residue class. The least
prime in the arithmetic progression a (mod q) satisfies P(a, q) <= (phi(q) log q)^2."
Prior explicit AP bounds quoted there (Bach-Sorenson, Math. Comp. 65 (1996), 1717-1735): (1.1)
P(a, q) <= (1 + o(1))(phi(q) log q)^2 and (1.2) P(a, q) <= 2 (q log q)^2.
The LLS paper contains no Miller-test statement. A Miller-witness bound of size (log n)^2 from Theorem
1.1(2) needs "n has no prime factor below (log n)^2", i.e. trial division first; that is my inference,
not a statement in the paper.

### 3.4 Carneiro, Milinovich, Quesada-Herrera, Ramos (asymptotic constants)
"Fourier optimization, the least quadratic non-residue, and the least prime in an arithmetic
progression", arXiv:2404.08380v2 (12 Aug 2025). VERIFIED TODAY. URL read: https://arxiv.org/pdf/2404.08380
Theorem 1, verbatim: "Assume GRH. Let n_p be the least quadratic non-residue modulo a prime p. Then
limsup_{p -> infinity} n_p / log^2 p <= C(1)^(-2) < 0.7615." With the remark C(1)^(-2) > 0.7596 ("we have
essentially arrived at the limit of this method"), and "assuming GRH, we prove that
n_p < (380/499) log^2 p when p is sufficiently large".
Theorem 2: the same bound for the least prime quadratic residue r_p.
Theorem 3, verbatim: "Assume GRH. Let q in N and a in Z with gcd(a, q) = 1. The least prime P(a, q) that
is congruent to a modulo q verifies limsup_{q -> infinity} P(a, q) / (phi(q) log q)^2 <= C(3)^(-2) < 8/9."
With C(3)^(-2) > 0.8859.
History line read there: Ankeny n_p << log^2 p; Bach n_p <= (1 + o(1)) log^2 p; LLS
n_p <= (0.794 + o(1)) log^2 p.
Beyond GRH: Kandhil, Languasco, Moree, arXiv:2607.14515v1 (16 Jul 2026), "Beyond the Riemann Hypothesis
bounds: A pair-correlation approach to the least prime in arithmetic progression and the smallest
quadratic non-residue": sharper estimates "under GRH and specific pair-correlation hypotheses". Abstract
read only.

### 3.5 Delta for the lab
Lab (given 7/8): least n with chi(n) not in {0,1} at most (log q)^8 for every nonprincipal chi mod q >= 3;
Miller-Rabin witness at most (0.7 log n)^8; P(a,q) <= C(eps) q^(7/3 + eps).
GRH, published: exponent 2 everywhere with explicit constants 1 (LLS, prime q >= 5; or general q with
the B(q) correction, q >= 3000), 2 and 3 (Bach, all q), and (phi(q) log q)^2 for q > 3. A GRH-grade
counterpart of these three hunts would be a reproduction of published results, not a delta, unless it
closes a named gap: e.g. an explicit bound with constant below 1 valid for all q (the constants 0.7615
and 8/9 are only asymptotic), or the general-character statement with no q >= 3000 and no B(q).

---------------------------------------------------------------------------------------------------

## 4. Explicit RH results on primes

### 4.1 Schoenfeld 1976
L. Schoenfeld, "Sharper bounds for the Chebyshev functions theta(x) and psi(x). II", Math. Comp. 30
(1976), no. 134, 337-360. Primary NOT readable today (AMS 403; it is a scan in any case). RECALLED:
Theorem 10: under RH, |psi(x) - x| < (1/(8 pi)) sqrt(x) log^2 x for x >= 73.2 and
|theta(x) - x| < (1/(8 pi)) sqrt(x) log^2 x for x >= 599; Corollary 1: |pi(x) - li(x)| <
(1/(8 pi)) sqrt(x) log x for x >= 2657.
SECONDARY read today:
- Wikipedia "Riemann hypothesis": |pi(x) - li(x)| < (1/(8 pi)) sqrt(x) log x for x >= 2657, and
  |psi(x) - x| < (1/(8 pi)) sqrt(x) log^2 x for x >= 73.2 (both attributed to Schoenfeld 1976).
- Platt-Trudgian arXiv:2004.09765v1, verbatim: "Schoenfeld [29] proved that |psi(x) - x| <=
  (1/(8 pi)) x^(1/2) log^2 x, (x > 59)." DISCREPANCY: 59 versus 73.2 for the psi threshold. Their
  Corollary 1 (unconditional, in ranges): |psi(x) - x| <= (sqrt(x)/(8 pi)) log^2 x for
  59 < x <= 2.169 * 10^25; |theta - x| <= same for 599 < x <= 2.169 * 10^25; |pi(x) - li(x)| <=
  (sqrt(x)/(8 pi)) log^2 x for 2657 < x <= 2.169 * 10^25. Note the arXiv v1 text layer prints log^2 x in
  the pi(x) line where Schoenfeld's corollary has log x; either a typo in v1 or a deliberately weaker
  statement. A builder must take thresholds from Schoenfeld's paper itself, not from this note.
- Dudek arXiv:1402.6417, verbatim: "von Koch [12] proved that there exists a constant k such that the
  interval (x - k sqrt(x) log^2 x, x) contains a prime for all x >= x0. Schoenfeld [8] made this result
  precise, showing that one can take K = 1/(4 pi) and x0 = 599."
The psi threshold (59 vs 73.2) is cheap for the lab to settle by direct computation of psi(x) on
[59, 100], given RH is only needed above the checked range.

### 4.2 Cramer 1920
H. Cramer, "Some theorems concerning prime numbers", Ark. Mat. Astron. Fysik 15 (5) (1920), 1-32.
Primary NOT read. SECONDARY (CMS, verbatim): "Assuming the Riemann hypothesis (RH), a classical result of
Cramer [14] yields the bound limsup (p_{n+1} - p_n) / (sqrt(p_n) log p_n) <= c, where c is a universal
constant." Dudek's Theorem 1 restates it: under RH, pi(x + c sqrt(x) log x) - pi(x) > sqrt(x) for a
constant c, hence p_{n+1} - p_n = O(sqrt(p_n) log p_n).

### 4.3 Dudek 2015
A. W. Dudek, "On the Riemann hypothesis and the difference between primes", Int. J. Number Theory 11
(2015), no. 3, 771-778; arXiv:1402.6417v2 (20 May 2014). VERIFIED TODAY (abstract and theorem
statements). URL read: https://arxiv.org/pdf/1402.6417
Abstract, verbatim: "We prove some results concerning the distribution of primes on the Riemann
hypothesis. First, we prove the explicit result that there exists a prime in the interval
(x - (4/pi) sqrt(x) log x, x] for all x >= 2; this improves a result of Ramare and Saouter. We then show
that the constant 4/pi may be reduced to (1 + eps) provided that x is taken to be sufficiently large.
From this we get an immediate estimate for a well-known theorem of Cramer, in that we show the number of
primes in the interval (x, x + c sqrt(x) log x] is greater than sqrt(x) for c = 3 + eps and all
sufficiently large x." Ramare-Saouter's earlier constant: 8/5.
Dudek, Grenie, Molteni, "Primes in explicit short intervals on RH", Int. J. Number Theory 12 (2016), no.
5, 1391-1407: SECONDARY (CMS): c(x) = 1 + 4/log x in place of 22/25.

### 4.4 Carneiro, Milinovich, Soundararajan 2019
E. Carneiro, M. B. Milinovich, K. Soundararajan, "Fourier optimization and prime gaps", Comment. Math.
Helv. 94 (2019), no. 3, 533-568; arXiv:1708.04122v2 (14 Sep 2018). VERIFIED TODAY. URL read:
https://arxiv.org/pdf/1708.04122
Theorem 5, verbatim: "Assume the Riemann hypothesis. Then, for x >= 4, there is always a prime number in
the interval [x, x + (22/25) sqrt(x) log x]." Also, verbatim: "assuming the Riemann hypothesis, prove
that p_{n+1} - p_n <= (22/25) sqrt(p_n) log p_n for all primes p_n > 3."
Corollary 4: limsup (p_{n+1} - p_n)/(sqrt(p_n) log p_n) <= 1/C^+(B) < 21/25. Theorem 3 (alpha = 1):
c = 3/C^+(B) < 63/25 for "more than sqrt(x) primes". Stated limit of the method: constant 1/2.
Proof structure of Theorem 5: (1.15) p_{n+1} - p_n < log^2 p_n verified for 11 <= p_n <= 4 * 10^18
(Oliveira e Silva, Herzog, Pardi) covers 4 <= x <= 4 * 10^18; analysis for x >= 4 * 10^18.

### 4.5 Primes between consecutive cubes and powers
Under RH, all n (VERIFIED TODAY in Chamberland-Straub arXiv:2602.22502v1, 26 Feb 2026, URL
https://arxiv.org/pdf/2602.22502; the underlying Caldwell-Cheng paper NOT read):
- Verbatim: "there is always a prime between n^3 and (n + 1)^3 for all sufficiently large n. By the
  special case delta = 1 of Theorem 1.2, which was previously proved by Chris Caldwell and Yuanyou Cheng
  [CC05], this is in fact true for all positive integers n if we are willing to assume the Riemann
  hypothesis." [CC05] = C. K. Caldwell, Y. Cheng, "Determining Mills' constant and a note on Honaker's
  problem", J. Integer Sequences 8(4), #05.4.1, 2005.
- Theorem 1.2, verbatim: "Suppose the Riemann hypothesis is true, and let delta > 0. (a) If
  delta >= 1/4, then the interval [x^(2+delta), (x+1)^(2+delta)] contains a prime for all x >= 1. (b) If
  delta < 1/4, then the interval [x^(2+delta), (x+1)^(2+delta)] contains a prime for all
  x >= [beta (log(beta) + log(log(beta)))]^beta, beta = 2/delta." Remark: "the bound for delta in part
  (a) can be improved to 0.2253. On the other hand, obtaining a result like delta >= 1/5 in part (a)
  seems out of reach with the current state of computation and theory." Inputs: CMS Theorem 5 plus the
  Sorenson-Webster verification of Legendre's conjecture up to 7 * 10^13 (Res. Number Theory 11(4), 2025).
Unconditional (same source): cubes for n >= exp(exp(32.537)) (Cully-Hugill, PhD thesis UNSW Canberra
2023, Theorem 4.3), improving Dudek. Dudek's paper (arXiv:1401.4233v1, "An explicit result for primes
between cubes", Funct. Approx. Comment. Math. 55(2) (2016), 177-197), abstract VERIFIED TODAY: "there is
a prime between n^3 and (n + 1)^3 for all n >= exp(exp(33.217)) [...] there is a prime between any two
consecutive mth powers for m >= 4.971 * 10^9." Then Mattner (alpha >= 1,438,989), Cully-Hugill-Johnston
(alpha = 155, 140, 90). The lab's docs/39 cites Lee arXiv:2602.14340 for k = 86 (not re-read today).

---------------------------------------------------------------------------------------------------

## 5. The de Bruijn-Newman constant

### 5.1 Rodgers, Tao
B. Rodgers, T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020),
e6 (volume and article number RECALLED; the arXiv v5 header, dated 3 Jul 2020, carries placeholder
journal data "Forum of Mathematics, Pi (2021), vol. ???, e1, 61 pages"). arXiv:1801.05914. VERIFIED
TODAY (abstract). URL read: https://arxiv.org/pdf/1801.05914
Abstract, verbatim extract: "Newman showed that there exists a finite constant Lambda (the de
Bruijn-Newman constant) such that the zeroes of H_t are all real precisely when t >= Lambda. The Riemann
hypothesis is the equivalent to the assertion Lambda <= 0, and Newman conjectured the complementary
bound Lambda >= 0. In this paper we establish Newman's conjecture."
Normalisation in the paper: H_0(z) = (1/8) xi(1/2 + iz/2), matching this lab's
H_0(z) = (1/8) Xi(z/2) (AGENTS.md traps section).

### 5.2 Platt, Trudgian
D. Platt, T. Trudgian, "The Riemann hypothesis is true up to 3 * 10^12", Bull. London Math. Soc. 53
(2021), 792-797 (pages RECALLED), arXiv:2004.09765v1 (21 Apr 2020). VERIFIED TODAY. URL read:
https://arxiv.org/pdf/2004.09765
Theorem 1, verbatim: "The Riemann hypothesis is true up to height 3 000 175 332 800. That is, the lowest
12 363 153 437 138 non-trivial zeroes rho have Re rho = 1/2."
Section 3.4, verbatim: "The 15th Polymath Project [24] contains some calculations with the de
Bruijn-Newman constant: the authors prove that Lambda <= 0.22. We note that we can make an instant, but
very mild, improvement on this. The second row in Table 1 on page 65 of [24] shows that one may take
Lambda <= 0.2 provided one has shown H > 2.51 * 10^12. This leads to the following. Corollary 2. We have
Lambda <= 0.2. The next entry in Table 1 of [24] is conditional on taking H a little higher than 10^13,
which of course, is not achieved by Theorem 1. This would enable one to prove Lambda < 0.19."

### 5.3 Consequence
RH as a theorem gives Lambda <= 0; with Rodgers-Tao, Lambda = 0. Every upper-bound computation
(Polymath15's 0.22, Platt-Trudgian's 0.2) is then superseded, and Polymath15's Table 1 (height H versus
bound on Lambda) becomes a consistency check rather than a frontier.

---------------------------------------------------------------------------------------------------

## 6. Public reaction to the Alpoge claim (dated 2026-11-20)

No primary reaction source was read directly. The press read on the day (Scientific American,
20 November 2026, marked as breaking news to be updated, and one aggregator relaying social-media
posts) reports no completed build, no completed kernel replay, no axiom printout and no defect.
The relayed posts are not reproduced here: they were not opened at their source.

---------------------------------------------------------------------------------------------------

## 7. Verified-today versus recalled, in one table

| Item | Status | URL read today |
|---|---|---|
| Littlewood 1928 | SECONDARY (in L-T, GGLM) | https://arxiv.org/pdf/2011.08348 |
| LLS 2015, Thm 1.1-1.5, Cor 1.1-1.3 | VERIFIED (arXiv v3) | https://arxiv.org/pdf/1309.3595 |
| LLS corrigendum 2017 | bibliographic only (in CMQR, L-T) | https://arxiv.org/pdf/2404.08380 |
| Languasco-Trudgian 2022 | VERIFIED | https://arxiv.org/pdf/2011.08348 |
| GGLM 2026 (h <= 2000) | VERIFIED | https://arxiv.org/pdf/2610.14257 ; https://arxiv.org/abs/2610.14257 ; https://sites.unimi.it/molteni/research/class_numbers/class_numbers.html |
| Watkins 2004 | SECONDARY (AMS 403) | via the three papers in 2.1 |
| Klaise 2012 | VERIFIED (abstract) | warwick.ac.uk URL in 2.2 |
| Cremona-Sutherland 2023 | VERIFIED | https://arxiv.org/pdf/2301.11169 |
| Jacobson-Mosunov 2016 | VERIFIED (abstract) | https://arxiv.org/pdf/1502.07953 |
| Holmin et al. | VERIFIED | https://arxiv.org/pdf/1510.04387 |
| Bach 1990 | SECONDARY (in LLS; Wikipedia) | https://arxiv.org/pdf/1309.3595 ; https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test |
| Bach-Sorenson 1996 | SECONDARY (in LLS, CMQR) | same |
| Wedeniwski 2001 | SECONDARY (in LLS) | same |
| CMQR 2024/25 | VERIFIED | https://arxiv.org/pdf/2404.08380 |
| Schoenfeld 1976 | RECALLED + SECONDARY, with a 59 vs 73.2 discrepancy | https://arxiv.org/pdf/2004.09765 ; https://en.wikipedia.org/wiki/Riemann_hypothesis |
| Cramer 1920 | SECONDARY | https://arxiv.org/pdf/1708.04122 |
| Dudek 2015 (4/pi) | VERIFIED | https://arxiv.org/pdf/1402.6417 |
| CMS 2019 (22/25) | VERIFIED | https://arxiv.org/pdf/1708.04122 |
| Caldwell-Cheng 2005 (cubes, RH) | SECONDARY (in Chamberland-Straub) | https://arxiv.org/pdf/2602.22502 |
| Chamberland-Straub 2026 | VERIFIED | https://arxiv.org/pdf/2602.22502 |
| Dudek 2016 (cubes, unconditional) | VERIFIED (abstract) | https://arxiv.org/pdf/1401.4233 |
| Rodgers-Tao | VERIFIED (abstract) | https://arxiv.org/pdf/1801.05914 |
| Platt-Trudgian | VERIFIED | https://arxiv.org/pdf/2004.09765 |
| Alpoge reaction | press only | URLs in section 6 |

## 8. Not resolved

1. Watkins 2004, Bach 1990, Schoenfeld 1976 primary texts (AMS bot wall). Thresholds for Schoenfeld's
   psi bound disagree between sources (59 vs 73.2).
2. Whether the Jacobson-Mosunov raw class numbers to 2^40 are downloadable (Cremona-Sutherland say yes,
   via LMFDB; GGLM say raw values are not available).
3. Whether GGLM's list below their cutoff is unconditional or inherits PARI's GRH dependence.
4. The "variation of the formula" behind GGLM's improved pairs (10); not transcribed.
5. No zbMATH or OEIS search was run; "nothing above h = 2000" rests on one extended web search.
6. The Lean Zulip thread and the X posts on the Alpoge archive were not read directly.
7. Lee arXiv:2602.14340 (k = 86), Caldwell-Cheng 2005, Wedeniwski 2001, Littlewood 1928, Cramer 1920:
   not opened.
