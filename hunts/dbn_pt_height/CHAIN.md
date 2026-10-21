# CHAIN: Lambda <= 0.2 from Polymath 15 Table 1, row 2

Chain lane of hunt #147, 2026-10-21. Reading and sourcing only: nothing here
recomputes H_t, and no bound on Lambda is stated by this lane.

**How to read this file.** `[Q:ID]` cites a quotation in `chain.json`. Each
quotation is an exact substring of a source whose URL, SHA-256 and retrieval
time are in `sources.json`, at a locator (TeX line, file at a git commit, blog
comment anchor, GitHub comment id, or bundle member by basename and digest).
`test_chain.py` re-reads every quotation from the hashed bytes, re-derives
every identity below in exact rationals or 256-bit interval arithmetic, and
fails if this file contains a number that `chain.json` or `sources.json` does
not carry. Grades are this tree's: *measured*, *hardened*, *kernel-checked*.
A statement read in a source carries the grade of what that source shows.

## Verdict

**Row 2's asymptotic-region hypothesis was verified in the Polymath record only
at N = N0 = 630783, never over all N >= N0.** Table 1's last column is the
Euler-2 lower bound at N = N0, the paper says it expects the rest to be
verifiable, the project repository holds no sweep at row 2's parameters at any
of its commits, and the paper's administrator wrote on 2019-04-15 that the
calculation at N0 is not quite enough and that he was not concerned about
verifying it carefully. The only report found of a sweep over all N >= N0 at
row 2's parameters is a blog comment of 5 July 2024 by an outside reader, with
unpublished code and no stated precision, y-range or threshold; the same
exchange describes the group's tooling for a neighbouring computation as 15 to
17 digit floats. It postdates the Platt-Trudgian corollary.

So the published chain behind Lambda <= 0.2 contains one step that its cited
source did not carry out. In the terms of `ALIGNMENT.md` section 5 this is an
*attempt unresolved*, not a refutation: nothing found suggests the hypothesis
is false, and the margins reported at N0 are large. The step is at most
*measured* (one route, third party, unpublished, precision not stated).

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
x in [X, X+1], t in [0, 0.186] (interval arithmetic).

Hypothesis (i) is supplied by [Q:PT1], a refereed theorem. Hypothesis (iii),
the barrier, was computed by the project: the repository's output file reports
the barrier at X = 5000000194858 with N = 630783, y0 = 0.16733, t up to 0.186
[Q:R3] and "Overall winding number: 0.000000" [Q:R4], and the paper says all
barrier runs gave winding number zero [Q:P14]. This lane does not re-grade that
computation. The question is hypothesis (ii).

## 2. Hypothesis (ii) at row 2: only at N = N0

**The paper.** Section 10 says how the table was made: parameters were chosen
"for which one could obtain a good lower bound for $f_{t_0}(x+iy_0)$ when
$x=N_0$" with a target of 0.03 [Q:P10] (line 1965), and the Euler-2 lemma
(`trib2`) "yields a lower bound on $|f_{t_0}(x+iy_0)|$ when $N=N_0$." [Q:P11]
(line 1994). The next paragraph (line 2002):

> By working in intervals $N \in [N_-,N_+]$ ... we thus (in view of the
> conservative safety margin in our lower bounds for $|f_{t_0}(x+iy_0)|$)
> expect to be able to verify the hypothesis in Theorem \ref{ubc-0}(iii) for
> any choice of parameters $t_0, y_0, N_0$ as above. [Q:P12]

(the ellipsis elides the clause about the intervals and the crude bound for
N >= N1; the quoted part is verbatim). The same section's first sentence says
the table collects "results verifying the second two hypotheses" [Q:P7]; the
specific statements are [Q:P11] and [Q:P12], and they say N0 only. For
comparison, the unconditional Lambda <= 0.22 of the same paper does sweep its
right region, from N0 = 69098 to N1 = 1.5e6 [Q:P17].

**The repository, at every commit.** The text of [Q:P12] entered the writeup
in commit `4a460d9` (2019-04-14) [Q:R2]. The day before, in commit `7eff611`,
the column was the "Moll2 bound" with "$N_a$ the initial value of $N$ at the
point $X$" [Q:R1]. The repository's sweeps of the right region live in
`output/eulerbounds/`; in all 768 commits every file there is at y = 0.2, and
the only one starting at N = 630783 is at t = 0.17, y = 0.2 [Q:R5], a
different parameter point (an earlier rung, 0.17 + 0.2^2/2 = 0.19) that does
not imply the hypothesis at (t0, y0) = (0.186, 0.16733). The test lists every
file that path has ever held and checks both statements.

**The issue threads.** Issue #131 (opened 2019-01-25) proposed that for the
conditional rows the mollified triangle bound "can be made positive already at
the location of the Barrier" so that nothing further is needed [Q:I6]. On
2019-04-13 the lead numerics contributor confirmed that the table's bound is
the fast triangle bound and that barrier locations were chosen so that "no
further verification work beyond the Barrier would be required." [Q:I3]. On
2019-04-14 he asked whether that is actually correct [Q:I4]. Tao answered on
2019-04-15 (comment 483072037):

> It is technically true that in order to properly clear out the region to the
> right of the barrier, it's not quite enough to do the calculation at N_0; one
> should start clearing out intervals as in what we now do in Section 8.5, then
> do an analytic calculation past some extremely large cutoff N_1 ... I am not
> really concerned about verifying this carefully  (though it would not be too
> difficult to do if, say, a referee insists on it). [Q:I1] [Q:I2]

The selection table that produced row 2 is in issue #81 (2018-09-08):
"5E+12 | 630783 | 0.20 | 0.186 | 0.167332 | 0.037612" [Q:I7]. Tao's plans for
the paper treated the conditional section as secondary: it would carry fewer
details [Q:B7] and was the part still unfinished in April 2019 [Q:B8].

**The counter-claim, examined.** On 2019-01-06 a project member wrote that "the
triangle bound we calculate always stays positive since it is an asymptotic
estimate and is guaranteed to be positive by a lemma" [Q:I8], pointing to the
wiki page *Estimating a sum*. That page's Euler-2 lemma is stated "in the toy
model" [Q:W4], and its uniformity step is the toy-model sentence "The summand
is monotone decreasing in N so we can majorise it by N/2 times the value at
N/2" [Q:W3]. It is not a computation for f_t with its error terms at row 2's
parameters, and the later answer [Q:I1] [Q:I2] supersedes it.

**The wiki.** The live wiki returns 404; the archived *Zero-free regions* page
"was last edited on 10 May 2018" [Q:W1] and has no conditional rows. The main
page's last edit says Lambda <= 0.22 "may be improved to" 0.20 after
Platt-Trudgian [Q:W2]. The GitHub wiki has no pages [Q:W5].

**The one reported sweep.** On the tenth thread, comment 685281, 5 July 2024,
an outside reader wrote "We checked the calculations using parameters
N0=630783 N1=5000000, t0=0.186, y0=0.16733 as per the paper." [Q:B1], in
intervals up to N1 "using Lemma 10.1 based on Euler 2 mollifier" [Q:B2]; for
N > N1 "we checked" the paper's Lemma 8.2 bound against 1.25e-3 [Q:B12]. That
threshold is the error budget the paper derives for its own 0.22 proof [Q:P21],
whose regions have y >= 0.2 [Q:P22], not y0 = 0.16733; the threshold for the
bounded range and the y-range are not stated. The comment states no precision.
The day before, in the same exchange, a comment about the Lemma 8.5
calculation of the 0.22 proof [Q:B13] said "we used Python code on
orderai.azurewebsites.net with 15 to 17 digits float" [Q:B3], so floating
point is the likely tooling, not a stated fact about this check. A project
member closed the exchange with thanks for "this detailed verification"
[Q:B5], without saying which computation he meant. Not published, not
deposited, code not public. The y-range matters: in 2019 the project found
that its Lemma bound "is in fact not monotone in y as previously thought"
[Q:I5], and a later package needed a separate lemma because sweeps at y = y0
alone do not give hypothesis (ii) [Q:Z15]. (The exchange began with a query
about claim (93) of the 0.22 proof [Q:B6], which the thread records as
resolved; it is outside this question.)

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
states Lambda <= 0.2 as its anchor [Q:K1] [Q:K2] and so does inherit it
(observation from the record and the announcement; the v1.1 PDF was hashed,
not read). The catalogue says instead that all three 0.16-range rows descend
from the 0.1875 row [Q:C2].

**Not accessed.** The published Res. Math. Sci. full text (the PDF URL returned
a client challenge; the article page is a preview). The arXiv v2 comment field
says v2 is the final version with referee corrections [Q:ABS1]. Broughan's
book chapter, described in the 2024 exchange as "a rewrite and verification of
the Polymath15 work" [Q:B11], is closed access; whether it treats row 2's right
region is unknown. Both are listed in `chain.json` under `not_accessed`.

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
but Section 10 was not. The swap travels: the 0.1875 bundle's criterion file
keeps the theorem's labels in its Theorem 1.1 [Q:Z14] and swaps them in its
Theorem 2.1 at the 0.2 row [Q:Z12] [Q:Z11], and its README records that its
writeups use "the OPPOSITE numbering" from each other [Q:Z16]. Only labels
move; the displayed regions are unambiguous.

## 4. What was searched

| where | what it shows about row 2 |
|---|---|
| arXiv TeX, 1904.12438 v1 and v2; 2004.09765 v1 | bound at N0 only; the expect-to-verify sentence in both versions |
| `km-git-acc/dbn_upper_bound`: 768 commits, 151 issues and PRs, comments of issues 81, 113, 131 | no row-2 sweep at any commit; the 2019-04-15 statement |
| the project wiki (live 404; archived snapshots) and the empty GitHub wiki | no conditional rows |
| Tao's blog: ninth, tenth and eleventh threads and the 2019 paper post, with comments | the 2024 check; the plan to give the conditional section fewer details |
| `teorth/optimizationproblems` `constants/21a.md`, PRs 208 and 210 | rows and anchors (REDUCTION.md) |
| Zenodo 21175533 and the fork commits `6baae4c`, `cc81078` | attribution of row 2's right region to a sweep the Polymath record does not contain [Q:Z11] |
| arXiv API, newest 60 de Bruijn-Newman abstracts; author search | six 2024 to 2026 papers, none about row 2; no paper by the 2024 commenter |
| Crossref, OpenAlex | published Polymath text blocked; published Platt-Trudgian closed |

## 5. What would change this

A deposited or published sweep of row 2's right region over all N >= N0 with
error terms and the full y-range, which this file missed, rewrites the verdict
around it (MISSION.md, kill conditions). A ball-arithmetic rerun of the 2024
method at row 2's parameters, with a y-transfer and a tail, would supply the
missing step; that is the evaluator lane's milestone, gated on refusing
Davenport-Heilbronn first.
