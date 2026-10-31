# Prior-art scan: place split, three-term balance, uniform gap

Scan date: 2026-10-30. Nothing here is a result about the Riemann Hypothesis.
The statements compared are the ones on `origin/main` in
`hunts/weil_split/RESULTS.md`, `hunts/arch_cover/RESULTS.md` section 4, and
`hunts/weil_gram/RESULTS.md` section 4, not the earlier framings those files
correct. Nothing below is offered as unknown to the literature. A source is cited only if it
was opened. Weil's 1952 paper and Yoshida's 1992 paper were not opened. Where
a later author quotes them, the citation is to that later author.

The three questions, with the corrected wording:

1. Is `cost_p = log p (Q_p - 1)`, `Q_p = (1 - 1/p) ||Phi_p f||^2`,
   `Phi_p f = sum_{m >= 0} p^{-m/2} f(. - m log p)`, a standard split of the
   prime side? The cost is an exact finite closed form. It carries `log p`,
   `p^{-1/2}` and `b`. It is not a rational number.
2. Is the three-term balance `W = pole + arch - sum_p cost_p >= 0`, with the
   prime side split by place, already stated, and is the margin identity
   `cover - 1 = W_zeros / sum_p cost_p` and its decay along widening test
   functions already stated? The disowned framing, that the archimedean plus
   pole term must dominate the sum of local costs, is recorded only so each
   citation can be marked against it.
3. Is the absence of a fixed `c > 0` with `W(|f^|^2) >= c ||f||^2` on the
   admissible class already stated? Separately: does the literature already
   separate a falling `lambda_min` on growing subspaces from the fact that
   nonnegativity on each subspace passes to the limit?

## Verdict 1. PARTIAL

The split of the explicit formula into one local term per place is in the
sources opened. The L2 shift-norm identity is not.

Bombieri's Clay notes, opened as the 11-page PDF "Problems of the Millennium:
the Riemann Hypothesis", state Weil's formula as a sum over `n` of
`Lambda(n)` times a test function, plus an archimedean integral, and then:
"The terms in the right-hand side of the equation can be written as a sum of
terms of local nature, associated to the absolute values of the underlying
number field, or function field in the case of curves over a field of
positive characteristic." That sentence supports a place split. It does not write
`Phi_p` or `(1 - 1/p) ||.||^2`. The same notes cite Weil, "Sur les 'formules
explicites' de la théorie des nombres premiers", Lund 1952, which was not
opened.

Connes and Consani, arXiv:2106.01715, source opened, write Weil's formula as
a sum over rational places and give the finite-place term, in their
Fourier normalization, as

    W_p(F) = (log p) sum_{m=1}^infty p^{-m/2} (F(p^m) + F(p^{-m})).

The quadratic form is

    psi(F) = F-hat(i/2) + F-hat(-i/2) - W_R(F) - sum_p W_p(F).

They label these displays as Bombieri's form of the explicit formula. This is
the prime side grouped by place, as a distribution on the multiplicative
group, not as an L2 norm of a weighted shift. It supports the place split in
question 1. It does not support `cost_p = log p (Q_p - 1)`.

Bombieri, "Remarks on Weil's quadratic functional in the theory of prime
numbers, I", Atti Accad. Naz. Lincei, Rend. Lincei Mat. Appl. (9) 11 (2000),
183-233, PDF opened, writes the same prime side as
`sum_n Lambda(n) {f(n) + f*(n)}` inside the linear functional `T[f]`, and
proves `T[f] = sum_rho f-tilde(rho)`. Again a von Mangoldt sum, not an L2
shift norm.

Burnol, arXiv:math/9810169, source opened, states Weil's local term as a
principal-value integral on `Q_nu^x`,

    W_nu(g) = PF_nu integral g_nu(1/x) / |1 - x|_nu  d^x x,

with `d^x x` assigning volume `log p` to the units at `p`. The factor
`log(p) / (1 - 1/p)` appears in the same note, as the constant in the Fourier
transform of `-log|x|` on `Q_p` (his display `(Q_p)`, quoting Vladimirov for
the computation and Haran for the comparison of local terms). That is a
different formula. It uses `(1 - 1/p)` as a Haar normalization, not as the
coefficient of `||Phi_p f||^2`.

Connes, arXiv:math/9811068, abstract and introduction opened: the explicit
formulas are interpreted as a trace formula on the adele class space. The
S-local proof was not read. The abstract supports the trace-formula setting
named in the question. It was not checked line by line for `Phi_p`.

Targeted searches for the shift-norm identity returned no external paper
whose title or abstract stated it. See the search record. The same identity
is already written in this repository, `docs/24-the-local-positivity-attempt.md`,
as a derivation checked against the explicit-formula module, with no external
citation attached. That file is not an external source.

Gap, stated exactly: grouping the prime side by place, as `W_p` or as a
von Mangoldt sum, is in the sources above. The rewriting

    ||Phi_p f||^2 = (1/b) sum_{m,n >= 0} p^{-(m+n)/2} (b - |m-n| log p)_+
    cost_p = log p ((1 - 1/p) ||Phi_p f||^2 - 1)

for the rectangle family was not found outside this repository.

## Verdict 2. PARTIAL

The three-term balance is the explicit formula. The covering-margin identity
was not found. The disowned framing is not what the opened sources say.

Connes and Consani, arXiv:2106.01715, write `psi` as pole terms minus the
archimedean distribution minus the sum of `W_p`. That is the corrected
balance: one sum, three kinds of term, required to be non-negative on
autocorrelations. Their numerical section supports the corrected sign
statement and cuts against the disowned one. Quote, from the source: the
archimedean contribution alone "ceases to be positive" on an interval of
`log(lambda^2)` around `log 2`, "while the positivity is restored by adding
the contribution of the prime 2." A later section: when `lambda^2` grows past
a prime power and that contribution is ignored, `QW_lambda` "fails to remain
positive", displayed up to `lambda^2` about 7. So a prime term can restore
positivity. It is not, in their account, a cost that the archimedean term
must dominate. The same pages do say that each new prime power has to be
included once the support crosses it. That supports completeness of the sum
as the support widens. It does not support a margin `(pole + arch) / cost`
or the identity `cover - 1 = W_zeros / sum_p cost_p`.

Connes, Consani and Moscovici, arXiv:2310.18423, introduction opened: there
is a property `P(n)` using only the Euler factors for primes smaller than
`n`, such that `P(n)` for all `n` is equivalent to RH, because Weil positivity
on test functions supported in `[1/n, n]` is that criterion, and the
semilocal trace formula supplies a Hilbert-space form of each `Q_n`. This
supports "more places enter as the support widens, and the criterion is the
whole sequence." It does not support a decaying covering margin.

Zhu, arXiv:2608.24827, source opened, studies a different quotient,
`lambda^*(L) = inf Q(f) / ||f||_2^2` for `supp f` in `[-L, L]`. He writes
that the quantitative behaviour of the criterion "appears not to have been
studied." That sentence is his claim, not a completed search. His decay law
is for `lambda^*(L)`, not for `cover - 1`. It is recorded under verdict 3.

The rectangle margin in `hunts/weil_split/RESULTS.md` section 2, including
`cover - 1 = W_zeros / sum_p cost_p` and the exponents between rows, was not
found in the sources opened or in the recorded searches. By the identity in
that file, the margin is `W` normalised by the prime cost. A citation that
said the archimedean term dominates the primes would be a citation for the
disowned framing. None of the opened sources says that.

## Verdict 3. PARTIAL

A falling window constant, and the passage of nonnegativity rather than of a
uniform constant, are in the sources opened. The Gaussian ratio, and a
geometric drop per added Gaussian, were not found.

Weil's criterion, as stated in the Clay notes opened above: RH is equivalent
to negativity of the right-hand side for every autocorrelation
`f(x) = integral g(xy) conjugate(g(y)) dy` whose `g` has vanishing integrals
against `dx/x` and against `dx`. Bombieri's 2000 memoir, abstract opened with
the rest of the PDF: the quadratic functional is positive semidefinite if and
only if RH, it attains its minimum on the unit sphere of `L2` functions
supported in a given interval, and it is positive definite for sufficiently
small support, which he attributes to Yoshida, "On Hermitian forms attached
to zeta functions", Adv. Stud. Pure Math. 21 (1992), 281-325. Yoshida was
not opened. Zhu, same preprint, quotes the classical range as
`supp f` in `[- (log 2)/2, (log 2)/2]`, attributed to Yoshida and, by a
different method, to Connes and Consani. The small-support positivity is
therefore cited here only as those two authors state it.

This is the "passes to the limit" half of question 3. Nonnegativity on every
compact window is the criterion. It does not require a constant `c > 0`
independent of the window. Bombieri's Theorem 3 is the attainment of the
infimum on each fixed window, not a uniform gap.

Connes and Consani, arXiv:2106.01715: if RH holds, `QW_lambda` is strictly
positive, so the radical on each finite window is `{0}`, and yet one can
build `g` supported in `[lambda^{-1}, lambda]` with `QW_lambda(g)` much
smaller than `||g||^2`. They report a smallest positive eigenvalue
`2.389 x 10^{-48}` at `lambda^2 = 11`. That supports a falling spectral
margin on growing support windows. It is a reported eigenvalue, not a theorem
that the infimum over the whole admissible class is 0, and it is not a
geometric drop per added basis function.

Zhu, arXiv:2608.24827, defines `lambda^*(L)` as above and states: under RH,
`lambda^*(L) <= exp(-L e^L)` for all large `L`, by an explicit construction.
He also writes that the computation turns "the folklore that positivity gets
exponentially hard" into measured constants and a barrier. The folklore
phrase is his. The conditional theorem is a citation for "no fixed `c > 0`
on the union of the windows", because every window sits inside the admissible
class and the bound tends to 0. It is conditional on RH. If RH is false, Weil's
criterion already says the form takes a negative value, so no positive `c`
exists either. That dichotomy was not found written as one lemma. Zhu's
unconditional upper bounds at specific `L` (down to `3.2 x 10^{-283}` at
`L = 2`, from the abstract in the source) show the window constant is tiny
at those `L`. They are not themselves a proof that the infimum over all `L`
is 0.

The Gaussian ratio in `hunts/arch_cover/RESULTS.md` section 4(d), about
`4 sqrt(pi a) e^{-a gamma_1^2}`, was not found. An arXiv query for Gaussian
and "Weil positivity" returned 0 hits. The geometric drop of `lambda_min` on
a growing Gaussian span, `hunts/weil_gram/RESULTS.md` section 4, was not
found. Zhu's rate is a function of window length, Landau-Widom in his
account, not a factor per added element of a Gaussian span. Shi,
arXiv:2609.04908, abstract only: assuming RH, `lambda_min` of a different
"Prime-Weil" matrix tends to 0, with zero ordinates as inputs. That is not
`W / ||f||^2`.

## Search record

Google Scholar was queried. The dispatch note said it returns 403. On this
run it returned HTTP 200. Undermind was not searched: the site answered, and
the page is a login wall. Neither is a complete literature search. zbMATH
Open and the arXiv API answered.

Times are UTC on 2026-10-30. "Inspected" means titles, and abstracts or
theorem statements where the row says so.

arXiv API, `all:"Weil positivity"`, 20:44:57 and again 20:53:30, 12 hits.
Titles inspected, both times. Abstracts read in the first response for
2006.13771, 2609.20367, 2607.24830, 2608.24827, 2607.02828, 2206.03682,
math/0101068, math/9809119, and the start of 1910.14368. Full source or PDF
then opened for 2106.01715, 2006.13771 (abstract and first page), 2608.24827,
math/9810169, math/9811068 (abstract and introduction), 2310.18423
(introduction), 1910.14368 (first page only).

arXiv API, `all:"explicit formula" AND all:"local terms" AND all:Weil`,
20:45:26, 1 hit, math/0101068, abstract inspected.

arXiv API, `all:"semi-local" AND all:Weil AND all:positivity`, 20:45:26,
2 hits: 2006.13771 and 1910.14368, both already in the list above.

arXiv API, `au:Yoshida AND all:Weil AND all:positivity`, 20:45:26, 0 hits.

arXiv API, `all:"log p" AND all:"1/p" AND all:Weil AND all:positivity`,
20:46:09, 0 hits.

arXiv API, `au:Connes AND au:Consani AND all:Weil`, 20:46:09, 9 hits, titles
inspected. Source opened for 2106.01715, 2310.18423, 2006.13771.

arXiv API, `all:"p^{-m/2}" AND all:"explicit formula"`, 20:50:50, 1 hit,
2603.04666, title inspected, not this subject.

arXiv API, `all:"log p" AND all:Weil AND all:"quadratic form"`, 20:50:50,
0 hits.

arXiv API, `all:"local distribution" AND all:Weil AND all:"explicit formula"`,
20:50:50, 0 hits.

arXiv API, `all:"no uniform" AND all:Weil AND all:positivity`, 20:50:50 and
titles again 20:51:15, 17 hits. Titles inspected. Sixteen are Weil-Petersson,
Mordell-Weil, or otherwise unrelated. One title was pursued:
arXiv:2609.04908, abstract opened 20:52:30.

arXiv API, `all:Gaussian AND all:"Weil positivity"`, 20:50:50, 0 hits.

arXiv API, `ti:"Remarks on Weil"`, 20:50:50, 1 hit, 1309.2551, title
inspected, not Bombieri's memoir.

zbMATH Open `api.zbmath.org/v1/document/_search`, 20:45:48 probe, then:

- `ti:Weil positivity`, 20:49:21, 6 hits. Titles inspected. Relevant rows
  already in the arXiv list, plus Connes, "Trace formula on the adele class
  space and Weil positivity", not opened.
- `au:Bombieri ti:Weil`, 20:50:52, 2 hits. One is the 2000 memoir, then
  opened from bdim.eu.
- `au:Yoshida ti:Hermitian forms`, 20:50:52, 2 hits. The 1992 paper is the
  first. Not opened.
- `au:Burnol ti:explicit`, 20:50:53, 4 hits. math/9810169 opened in source.
  The CRAS note math/0101068 was opened at the abstract only.
- `au:Connes ti:trace formula zeta`, 20:50:53, 2 hits, both the 1999 trace
  formula paper.
- `ti:Weil quadratic functional`, 20:50:57, 1 hit, the 2000 memoir.

Web search, 20:45:26, "Weil explicit formula local distributions per place
quadratic form positivity", 8 results inspected. The first result is this
repository's `docs/24`. The others led to 2106.01715, 2608.24827,
math/9810169, math/9809119, and 2606.09096 (abstract level only, not used
for a verdict).

Web search, 20:45:26, `"1 - 1/p" Weil positivity local factor shift`, 5
results inspected. Again `docs/24`, plus Connes notes and 2106.01715. No
external statement of `||Phi_p f||^2`.

Google Scholar, 20:51:13, query "Weil positivity explicit formula local",
HTTP 200, 10 result titles inspected. Top rows: 2609.20367, 2608.24827,
2609.04908, and several preprints whose titles do not state the L2 cost
identity. Those preprints were not opened, except 2609.04908 at the abstract.

Google Scholar, 20:52:30, query `"log p" "explicit formula" positivity local
place`, HTTP 200, 10 result titles inspected. No title stated the shift-norm
identity. Repeats of Zhu and of Suzuki-numerical abstracts already seen.

Undermind, 20:50:49: HTTP 308 to the public site, then HTTP 200 on a login
page. No query was run.

Opened in full or in source, and used above: Bombieri Clay notes; Bombieri
2000 memoir; Connes-Consani arXiv:2106.01715 source; Burnol arXiv:math/9810169
source; Zhu arXiv:2608.24827 source; Connes-Consani-Moscovici arXiv:2310.18423
introduction; Connes arXiv:math/9811068 abstract and introduction.

## For the docs page

Tied to verdict 1. Cite the place split as Weil's explicit formula in the
form already written by Connes and Consani, arXiv:2106.01715, and as the
local-nature sentence in Bombieri's Clay notes. Do not present
`cost_p = log p (Q_p - 1)` with `Q_p = (1 - 1/p) ||Phi_p f||^2` as standard
notation. If the page states that identity, say it is a rewriting of the
von Mangoldt sum for an autocorrelation, already checked in this repository
(`docs/24` and `hunts/weil_split`), and that this scan did not find it
outside the repository. Do not call the cost rational.

Tied to verdict 2. Do not write that the archimedean term must cover the
prime side. Cite Connes and Consani, arXiv:2106.01715, for the opposite
numerical fact: past `log 2` the archimedean contribution alone loses
positivity, and the prime contribution restores it. State the balance as
the explicit formula, a three-term sum that has to come out non-negative,
with either sign allowed. If the page quotes the rectangle margin, say it is
`W` divided by the prime cost, by the identity in
`hunts/weil_split/RESULTS.md` section 2, and that this scan did not find
that identity or the measured decay outside the repository. Cite
arXiv:2310.18423 for the semilocal reduction `P(n)`, which is the "more
places enter" statement that does exist.

Tied to verdict 3. Cite Bombieri 2000 for attainment of the minimum on each
window, and for the criterion itself. Cite Zhu, arXiv:2608.24827, for
`lambda^*(L)` and for the conditional bound `exp(-L e^L)`, and quote his
folklore sentence rather than inventing one. Cite Connes and Consani,
arXiv:2106.01715, for strict positivity on each finite window if RH holds,
together with a reported eigenvalue `2.389 x 10^{-48}` at `lambda^2 = 11`.
Do not cite the Gaussian ratio `4 sqrt(pi a) e^{-a gamma_1^2}` as a known
formula. Do not identify the geometric drop on Gaussian spans in
`hunts/weil_gram` with Zhu's window law: different quotient, different
parameter. Keep the two directions separate, as in `hunts/weil_gram` section
4: nonnegativity on each subspace of an exhausting sequence is the criterion
and passes to the limit; a uniform positive gap does not survive enlargement,
which under RH is Zhu's theorem for windows, and which this scan did not find
as a Gaussian-span theorem.

Do not describe any of this as new to the literature. The scan did not cover
Undermind, did not open Weil 1952 or Yoshida 1992, and used Google Scholar
only for the two result pages named above.
