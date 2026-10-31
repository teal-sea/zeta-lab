# CHAIN: Lambda <= 0.2 from Polymath 15 Table 1, row 2

Chain lane of hunt #147, written 2026-10-21 and repaired the same day after an
adversarial review. Reading and sourcing only: nothing here recomputes H_t,
and no bound on Lambda is stated by this lane.

**How to read this file.** `[Q:ID]` cites a quotation in `chain.json`. Each
quotation is an exact substring of a source whose URL, SHA-256 and retrieval
time are in `sources.json`, at a locator: a TeX line, a file at a git commit,
a blog comment anchor (whose author, date and parent are read from the page),
a GitHub comment id, or a bundle member by basename and digest.
`test_chain.py` re-reads every quotation from the hashed bytes and re-derives
every identity below in exact rationals and in two interval backends. It also
ties the prose to the evidence: every number in this file must occur in a
quotation or a structured field of `chain.json`, and every date, named person
and count sits inside a registered fact (`chain.json`, `facts`) that the test
checks against the source. Three items were read in the session's PDF or image
reader and cannot be re-read by the test; each is marked where it is used.
Grades are this tree's: *measured*, *hardened*, *kernel-checked*. A statement
read in a source carries the grade of what that source shows.
Added at landing, 2026-10-31: the re-reading runs only where the download
cache exists, and no CI runner has it. There the tests that read a source
skip, and what is checked is that this file agrees with `chain.json` and that
its arithmetic holds; every quotation, date, name and count below is tied to
its source only by a run on a machine that holds the cache (`RESULTS.md`,
section 6).

## Verdict

**Row 2's asymptotic-region hypothesis was evaluated in the Polymath record only at N = N0 = 630783 and y = y0 = 0.16733, never over all N >= N0 or over its y-range.**
Table 1's last column is the Euler-2 lower bound at those two values, the paper
says it expects the rest to be verifiable, and the project repository holds no
sweep at row 2's parameters at any of its commits. On 2019-04-15 Terence Tao
wrote in issue #131 that the calculation at N0 is not quite enough, that this
"should not be a problem" because the bounds get easier as N grows and the
safety margin is conservative, and that he was not concerned about verifying
it carefully [Q:I1] [Q:I10]. That reason is a heuristic, not a verification.
On 22 April 2020 Tao wrote on the blog that the Platt-Trudgian height
"immediately improves" the paper's 0.22 to 0.20, without that qualification
[Q:B9]. The only report found of a sweep over all N >= N0 at row 2's
parameters is a blog comment of 5 July 2024 by Fabrice Imparato, a reader
outside the project, with unpublished code, no stated precision or y-range,
and no stated threshold for the bounded range [Q:B1]. It postdates the
Platt-Trudgian corollary, and it assumed the barrier's winding number instead
of recomputing it [Q:B14].

So the published chain behind Lambda <= 0.2, in which Platt and Trudgian read
Table 1 row 2, contains one step that its cited source did not carry out. In
the terms of `ALIGNMENT.md` section 5 this is an *attempt unresolved*, not a
refutation: nothing found suggests the hypothesis is false, and the margins
reported at N0 are large. The step is at most *measured* (one route, third
party, unpublished, precision not stated).

**Two unpublished 2018 routes have a different gap profile (section 2a).** The
repository also holds a barrier run with winding number zero and a finite sweep
at y = y0 for (t0, y0) = (0.17, 0.2) at row 2's own X, which gives 0.19, and
for (t0, y0) = (0.18, 0.2) at X = 10^12 + 46880, which gives 0.20. The
tenth-thread post announced the first as Lambda <= 0.19 under the RH height
claimed by Gourdon and Demichel [Q:T1], which Platt and Trudgian's verification
now covers. Neither route entered the paper. Their open steps are the
y-direction above y0 (the sweeps rest on a monotonicity in y [Q:T2] that the
project found false in April 2019, at the 0.22 parameters [Q:I12]) and the
region beyond the last swept N (the post says an analytic bound takes over
there [Q:T3]; no file in the history carries it). They are not complete
either, but closing those two
steps at either point would give 0.19 or 0.20 at Platt and Trudgian's height
without row 2.

## 1. The step Platt and Trudgian take

Their Theorem 1: "The Riemann hypothesis is true up to height
$3\,000\,175\,332\,800$." [Q:PT1] (arXiv TeX line 62). The de Bruijn-Newman
paragraph, verbatim (line 144):

> The second row in Table 1 on page 65 of \cite{Poly} shows\footnote{Note that
> the $X$ in Table 1 corresponds to $2H$. } that one may take
> $\Lambda \leq 0.2$ provided one has shown $H> 2.51\cdot 10^{12}$. This leads
> to the following. [Q:PT3]

followed by the corollary "We have $\Lambda \leq 0.2.$" [Q:PT4] (line 146),
and on line 149 the remark that the next row needs H a little higher than
10^13 [Q:PT5] and that extra decimals at their height were "not pursued"
[Q:PT6]. arXiv holds a single version (`sources.json`, ABS_PT); the published
text (Bull. London Math. Soc. 53, 2021) is closed access and was not read
(`chain.json`, `not_accessed`).

What they read is Polymath 15's Theorem 1.2 (TeX label `ubc-0`, v2 lines
145 to 151) [Q:P1]:

- (i) no zeros of zeta with (1+y0)/2 <= sigma <= 1 and 0 <= T <= X/2 [Q:P2];
- (ii) (asymptotic zero-free region at final time t0) no zeros of H_t0 with
  x >= X + sqrt(1 - y0^2) and y0 <= y <= sqrt(1 - 2 t0) [Q:P3];
- (iii) (barrier at intermediate times) no zeros of H_t in the barrier slab for
  0 <= t <= t0 [Q:P4];
- then Lambda <= t0 + y0^2/2 [Q:P5].

Table 1, row 2 (v2 line 1950), under the header of line 1947 [Q:P8]:

    $5 \times 10^{12} + 194858$ & 0.186 & 0.16733 & 0.20 & 0 & 630783 & 0.0376\\   [Q:P9]

The arithmetic, re-derived by the test: t0 + y0^2/2 = 3999993289/20000000000
= 0.19999966445 <= 1/5; X/2 = 2500000097429, and the height exceeds it by
500175235371, so the printed sufficient threshold 2.51e12 lies between X/2 and
the height; and N = floor(sqrt(x/(4 pi) + t/16)) = 630783 on the whole slab
x in [X, X+1], t in [0, 0.186] (interval arithmetic, two backends).

Hypothesis (i) is supplied by [Q:PT1], a refereed theorem. Hypothesis (iii),
the barrier, was computed by the project: the repository's output file reports
the barrier at X = 5000000194858 with N = 630783, y0 = 0.16733, t up to 0.186
[Q:R3] and "Overall winding number: 0.000000" [Q:R4], and the paper says all
barrier runs gave winding number zero [Q:P14]. This lane does not re-grade that
computation. The question is hypothesis (ii).

## 2. Hypothesis (ii) at row 2: only at N = N0 and y = y0

**The paper.** Section 10 says how the table was made: parameters were chosen
"for which one could obtain a good lower bound for $f_{t_0}(x+iy_0)$ when
$x=N_0$" with a target of 0.03 [Q:P10] (line 1965), and the Euler-2 lemma
(`trib2`) "yields a lower bound on $|f_{t_0}(x+iy_0)|$ when $N=N_0$." [Q:P11]
(line 1994). Both statements fix y = y0 as well as N = N0. The next sentence,
in full (line 2002):

> By working in intervals $N \in [N_-,N_+]$ for some finite number of intervals
> $[N_-,N_+]$ covering $[N_0,N_1]$ for some large $N_1$ as in Section
> \ref{b-bound}, and then using a crude triangle inequality bound for
> $N \geq N_1$ as in Section \ref{c-bound}, we thus (in view of the
> conservative safety margin in our lower bounds for $|f_{t_0}(x+iy_0)|$)
> expect to be able to verify the hypothesis in Theorem \ref{ubc-0}(iii) for
> any choice of parameters $t_0, y_0, N_0$ as above. [Q:P12]

The same section's first sentence says the table collects "results verifying
the second two hypotheses" [Q:P7]; the specific statements are [Q:P11] and
[Q:P12], and they evaluate at N0 and y0 only. For comparison, the unconditional
Lambda <= 0.22 of the same paper does sweep its right region, from N0 = 69098
to N1 = 1.5e6 [Q:P17], and covers the y-direction there by an argument that
needs the other three sides of the rectangle, adopted in April 2019 [Q:I13].

**The repository, at every commit.** The text of [Q:P12] entered the writeup in
commit `4a460d9` (2019-04-14) [Q:R2]. In the commit before it, `7eff611`
(2019-04-13), the column was the "Moll2 bound" with "$N_a$ the initial value of
$N$ at the point $X$" [Q:R1]. The repository's sweeps of the right region live
in `output/eulerbounds/`; in all 778 commits on all refs (768 on master) every
file there is at y = 0.2, and the only one starting at N = 630783 is at
t = 0.17, y = 0.2 [Q:R5], the 2018 point of section 2a, which does not imply
the hypothesis at (t0, y0) = (0.186, 0.16733). The test lists every file that
path has ever held and checks both statements. A search of the whole history
for the string 0.16733 touches only the writeup, row 2's barrier output and
y = 0.2 sweep files where the digits sit inside other numbers; the test pins
that too.

**The issue threads.** Issue #131 (opened 2019-01-25) proposed that for the
conditional rows the mollified triangle bound "can be made positive already at
the location of the Barrier" so that nothing further is needed [Q:I6]. The
pattern was older: on 2018-10-10, for two other conditional cases, Rudolph
Dwars wrote that the triangle bound was already positive at the barrier, "so no
further numerical work is required beyond the verification that no zeros have
passed the Barrier itself" [Q:I15]. On 2018-12-20 Tao asked whether the step
can be skipped for some parameters but not for 0.22 [Q:I16], and Rudolph Dwars
replied the same day that for 0.22 "we unfortunately can't skip" it [Q:I17].
On 2019-04-13 Rudolph Dwars confirmed that the table's bound is the fast
triangle bound and that barrier locations were chosen so that "no further
verification work beyond the Barrier would be required." [Q:I3]. On 2019-04-14
he asked whether that is actually correct [Q:I4]. Tao answered on 2019-04-15
(comment 483072037), in full:

> It is technically true that in order to properly clear out the region to the
> right of the barrier, it's not quite enough to do the calculation at N_0; one
> should start clearing out intervals as in what we now do in Section 8.5, then
> do an analytic calculation past some extremely large cutoff N_1, but given
> how the bounds always get easier as N increases, and the conservative safety
> margin we have in the lower bound for f_t, this should not be a problem and I
> am not really concerned about verifying this carefully  (though it would not
> be too difficult to do if, say, a referee insists on it). [Q:I1]

The stated reason [Q:I10] is that the bounds get easier with N and the margin
is conservative: a heuristic about N, silent on y. Two days earlier, on
2019-04-13, Tao had written that the extra checks on the other sides of the
region might be skipped "if we just want to give a tentative indication of
what conditional results ought to be possible with our approach" [Q:I11],
while expecting that "all the conditional results you've obtained would also
go through" [Q:I14]. The selection table that produced row 2 is in issue #81,
posted by Kalpesh Muchhal on 2018-09-08: "5E+12 | 630783 | 0.20 | 0.186 |
0.167332 | 0.037612" [Q:I7]. Tao's plans treated the
conditional section as secondary: on 4 July 2018 he wrote that it might not
need as many details [Q:B7], and on 12 April 2019 that it was the part still
unfinished [Q:B8].

**The author's later public statement.** On 22 April 2020 Tao wrote that the
Platt-Trudgian verification "immediately improves the upper bound \Lambda \leq
0.22 in the Polymath15 paper to \Lambda \leq 0.20" [Q:B9]. That is the
contrary-leaning record: the paper's author read the corollary as immediate. It
adds no computation, and the 2019-04-15 comment above says what the immediacy
rests on.

**The counter-claim, examined.** On 2019-01-06 Kalpesh Muchhal wrote that "the
triangle bound we calculate always stays positive since it is an asymptotic
estimate and is guaranteed to be positive by a lemma" [Q:I8], pointing to the
wiki page *Estimating a sum*. That page's Euler-2 lemma is stated "in the toy
model" [Q:W4], and its uniformity step is the toy-model sentence "The summand
is monotone decreasing in N so we can majorise it by N/2 times the value at
N/2" [Q:W3]. It is not a computation for f_t with its error terms at row 2's
parameters, and the later answer [Q:I1] supersedes it.

**The wiki.** The live wiki returns 404; the archived *Zero-free regions* page
"was last edited on 10 May 2018" [Q:W1] and has no conditional rows. The main
page's last edit says Lambda <= 0.22 "may be improved to" 0.20 after
Platt-Trudgian [Q:W2]. The GitHub wiki has no pages [Q:W5].

**The one reported sweep.** On the tenth thread, comment 685281 of 5 July 2024,
Fabrice Imparato wrote "We checked the calculations using parameters N0=630783
N1=5000000, t0=0.186, y0=0.16733 as per the paper." [Q:B1], in intervals up to
N1 "using Lemma 10.1 based on Euler 2 mollifier" [Q:B2], and for N > N1 "we
checked" the paper's Lemma 8.2 bound against 1.25e-3 [Q:B12]. That threshold is
the error budget the paper derives for its own 0.22 proof [Q:P21], whose
regions have y >= 0.2 [Q:P22], not y0 = 0.16733; the threshold for the bounded
range and the y-range are not stated. The comment states no precision, and it
covers hypothesis (ii) only: it proceeds "assuming a winding number of zero at
the barrier location" [Q:B14]. His name occurs nowhere in the project's issue
records read here (every issue and pull-request body, and the comments of six
issues), and no blog comment under it predates 2024; his first, in the threads
read here, is of 28 June 2024. The day before comment 685281, a comment about
the Lemma 8.5 calculation of the 0.22 proof [Q:B13], posted as Anonymous on
4 July 2024 in reply to Tao, said "we used Python code on
orderai.azurewebsites.net with 15 to 17 digits float" [Q:B3]. That it speaks
for the same group is an inference from where it sits in the thread, so
floating point is the likely tooling, not
a stated fact about the row-2 check. The thanks for "this detailed
verification" [Q:B5] was Rudolph Dwars's reply of 7 July 2024 to Fabrice
Imparato's comment of 6 July 2024 resolving the Lemma 8.5 discrepancy ("We got
what went wrong with our calculation." [Q:B15]), not to comment 685281. Tao's
reply of 7 July 2024 to the same comment closed the exchange [Q:B16]. No
project member replied to comment 685281. The check is not published, not
deposited, and its code is not public. The y-range matters: on 2019-04-08 Tao
reported that the Lemma bound "is in fact not monotone in y as previously
thought" [Q:I5], and a later package needed a separate lemma because sweeps at
y = y0 alone do not give hypothesis (ii) [Q:Z15]. (The exchange began with a
query about claim (93) of the 0.22 proof [Q:B6], which the thread records as
resolved; it is outside this question.)

**The referee reports.** On 25 July 2019 Tao linked two referee reports on the
paper [Q:B17]. Both were read in the session's PDF reader (hashed in
`sources.json`; not re-read by the test). The first recommends acceptance after
minor edits and lists eight small corrections, none in the conditional section.
The second has a numbered list of corrections; its item at page 15, line 17
asks for hypothesis (iii) instead of (ii), which matches the proof-label fix of
section 3 (the page-to-line match is an inference), and another item cites
page 65, inside Section 10. Neither asks for the region
N >= N0 of the conditional rows to be verified, and neither mentions the
Section 10 label swap. (One item swaps the expressions N = N0 and N >= N0 in
the text of the 0.22 proof; it is not about the conditional rows.)

**Margins, as others report them.** Row 2's bound at N0 is 0.0376 [Q:P9];
the 0.1875 bundle's error-terms audit puts e_A + e_B + e_C0 at the row-2
barrier corner near 1.03e-7 [Q:Z19]. These make the hypothesis plausible.
They are not a sweep.

**Downstream.** The 0.1875 bundle (Zenodo 21175533) restates the 0.2 row as an
instance of the criterion and attributes its right region to a "Polymath 15
Lemma-bound sweep, Table 1 row 2" [Q:Z11], a sweep the Polymath record does
not contain; its scope note leaves these hypotheses to the "Polymath artifacts"
[Q:Z13]. Its own bound is at another site (REDUCTION.md, part A) and uses row 2
only for arithmetic anchors, so it does not inherit the gap. The 0.172422 row
does not inherit it either, in the version the catalogue cites: its first
record stated the published 0.2 as its anchor [Q:K1] [Q:K2], but its
version 1.1, the one the catalogue cites [Q:C12], derives its own Lambda <= 0.2
(an unrefereed claim) from its separator, its tail theorem and Platt and
Trudgian's height [Q:K4], and says the published bound is no longer a logical
dependency [Q:K5] [Q:K6] (REDUCTION.md, part C).

**Not accessed.** The published Res. Math. Sci. full text (the PDF URL returned
a client challenge; the article page is a preview). The arXiv v2 comment field
says v2 is the final version with referee corrections [Q:ABS1]. Broughan's
book chapter, described in the 2024 exchange as "a rewrite and verification of
the Polymath15 work" [Q:B11], is closed access; whether it treats row 2's right
region is unknown. Both are listed in `chain.json` under `not_accessed`.

## 2a. The 2018 routes: a barrier and a finite sweep at y = y0

The tenth-thread post of September 2018 states the bound "depends on the
height to which one is willing to assume the Riemann hypothesis" [Q:T4] and,
at the Gourdon-Demichel height, "this improves slightly to \Lambda \leq 0.19"
[Q:T1].
Its results table is an image; read in the session's image reader (hashed in
`sources.json`; not re-read by the test), it lists the 0.19 row at row 2's X
with t0 = 0.17 and y0 = 0.20, and a 0.20 row at X = 10^12 + 46880 with
t0 = 0.18 and y0 = 0.20, both with winding number 0 and the RH input marked
tentative. The repository holds, for each point:

| point | barrier (winding 0) | sweep at y = y0 | lowest bound in the sweep |
|---|---|---|---|
| (0.17, 0.2) at X = 5000000194858, Lambda 0.19 | commit `e8cd27b`, N = 630783, t up to 0.17 [Q:R7] [Q:R8] | commit `ae36498`, N from 630783 to 15000000 [Q:R5] | 0.03028099814 at N = 1650000, error column at most 1.740023267e-05 |
| (0.18, 0.2) at X = 1000000046880, Lambda 0.20 | commit `97a8088`, N = 282094, t up to 0.18 [Q:R9] [Q:R10] | commit `6b9a1e8`, N from 282094 to 13000000 [Q:R11] | 0.03005127217 at N = 400000, error column at most 7.461781092e-05 |

The test recomputes the last column from the files, checks that every row's
error bound is below its lower bound, re-derives 0.17 + 0.2^2/2 = 0.19 and
0.18 + 0.2^2/2 = 1/5, the heights X/2 = 2500000097429 and 500000023440 (both
below 3000175332800), and N constant on both barrier slabs, and lists every file
in the history that names either point: barrier summaries, stored sums and the
one sweep each, nothing else.

What the routes lack:

- **The y-direction.** Each sweep is at y = y0 only. The post justifies this by
  "the Lemma bound monotonically increases when y goes to 1" [Q:T2]. On
  2019-04-08 Tao reported a "somewhat serious issue" in the 0.22 proof's sweep
  because the Lemma bound "is in fact not monotone in y as previously thought"
  [Q:I12]. The fix adopted for 0.22 needs the other three sides of the
  rectangle [Q:I13]. No file at the 2018 points carries such an argument;
  whether their barrier runs already supply the side at the barrier was not
  examined.
- **The region beyond the last swept N.** The post says that past N_b
  "analytical proof takes over" [Q:T3]. No file in the history carries that
  analytic step at either point.
- **The paper.** Neither point is in Table 1 or anywhere in the TeX.

So the 2018 routes are not a verification of a 0.2 bound either. They move the
open work from a whole range of N to two smaller steps, and they are the
nearest existing material to a completed 0.20 or 0.19 at Platt and Trudgian's
height.

## 3. Section 10 swaps the hypothesis labels of Theorem 1.2

Theorem 1.2 numbers its hypotheses (i) RH height, (ii) asymptotic region,
(iii) barrier [Q:P2] [Q:P3] [Q:P4]. Section 10 (v2 line 2002) calls the
asymptotic region "(iii)" [Q:P12] and the barrier "(ii)": "The main remaining
difficulty is then to verify the barrier hypothesis (Theorem
\ref{ubc-0}(ii))." [Q:P13]. The rest of v2 uses the theorem's labels: the
introduction says (iii) "can be done quite quickly compared to (ii)" [Q:P6],
and Section 10's own first paragraph calls the asymptotic region the "second
hypothesis" [Q:P16].

The swap was already in v1 (line 2004) [Q:V1A], under the same theorem labels
[Q:V1C]. Between versions the proof of the zero-free-region proposition was
corrected from "(ii)" [Q:V1B] to "(iii)" [Q:P15] for the barrier side x = X,
apparently at the second referee's request (section 2), but Section 10 was
not. The swap travels: the 0.1875 bundle's criterion file keeps the theorem's labels in
its Theorem 1.1 [Q:Z32] [Q:Z14] and swaps them in its Theorem 2.1 [Q:Z33] at
the 0.2 row [Q:Z12] [Q:Z11], and its README records that its writeups use "the
OPPOSITE numbering" from each other [Q:Z16]. Only labels move; the displayed
regions are unambiguous.

## 4. What was searched

| where | what it shows about row 2 |
|---|---|
| arXiv TeX, 1904.12438 v1 and v2; 2004.09765 v1 | bound at N0 and y0 only; the expect-to-verify sentence in both versions; no 2018 point |
| `km-git-acc/dbn_upper_bound`: 778 commits on all refs, 151 issues and pull requests, comments of issues 81, 107, 113, 118, 126, 131 | no row-2 sweep at any commit; the 2018 points of section 2a; the 2019-04-15 statement |
| the project wiki (live 404; archived snapshots) and the empty GitHub wiki | no conditional rows |
| the blog: ninth, tenth and eleventh threads and the 2019 paper post, with comments, and the tenth-thread results table | the 2024 check; the 0.19 announcement of 2018; the plan to give the conditional section fewer details |
| the two 2019 referee reports linked from the paper post | neither raises N >= N0 or the Section 10 swap |
| `teorth/optimizationproblems` `constants/21a.md`, PRs 208 and 210 | rows and anchors (REDUCTION.md) |
| Zenodo 21175533 and the fork commits `6baae4c`, `cc81078` | attribution of row 2's right region to a sweep the Polymath record does not contain [Q:Z11] |
| Zenodo 22337308 and 22658444 (the 0.172422 records) and the TeX of version 1.1 | the 0.172422 anchor (REDUCTION.md, part C) |
| arXiv API, newest 60 de Bruijn-Newman abstracts; author search | six 2024 to 2026 papers, none about row 2 in its abstract (abstracts only were read); no paper by the 2024 commenter |
| Crossref, OpenAlex | published Polymath text blocked; published Platt-Trudgian closed |

## 5. What would change this

A deposited or published sweep of row 2's right region over all N >= N0 with
error terms and the full y-range, which this file missed, rewrites the verdict
around it (MISSION.md, kill conditions). A ball-arithmetic rerun of the 2024
method at row 2's parameters, with a y-direction argument and a tail, would
supply the missing step; that is the evaluator lane's milestone, gated on
refusing Davenport-Heilbronn first. A cheaper route to the same bound is the
2018 material: an argument for the y-direction (the other three sides of the
rectangle, as in the 0.22 proof) and an analytic tail at (0.18, 0.2) would give
Lambda <= 0.20 at Platt and Trudgian's height without row 2, and the same two
steps at (0.17, 0.2) would give 0.19. Either would be a new computation, graded
as what it shows.

## 6. Open issues

- Not read: the published Res. Math. Sci. text, the published Platt-Trudgian
  text and Broughan's chapter (all closed or blocked). Any could hold a row-2
  verification that this file missed.
- The website named in the 2024 comment was not fetched, so the precision of
  the 2024 check is inferred, not stated.
- The two referee reports and the tenth-thread results table were read in the
  session's PDF and image readers; the test cannot re-read them (no PDF text
  tool in this tree's environment), so the statements made from them are at the
  grade of one reading.
- Whether the rows of the 2018 sweep files cover every N between them depends on
  the sawtooth scheme the post describes; this lane did not audit it.
- The number registry ties every number to the evidence, but a one- or
  two-digit number in running prose that no fact covers is checked only
  against a registry where small numbers occur by chance.
- The quotation tests skip where the download cache is absent, for example in
  CI; the shape, arithmetic and prose checks still run there.
- The builder scripts that resolved the quotation locators are scratchpad files
  and are not committed; `chain.json` can be re-verified but not regenerated.
- `CLAUDE.md` routes an unpursued observation like the row-2 gap to a public
  GitHub issue. None was opened: this lane may not publish or contact anyone.
