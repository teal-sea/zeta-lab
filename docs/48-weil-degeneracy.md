# 48. The Weil functional's degeneracy: three measurements and a constraint on proof strategy

**Hunts #155, #156 and #157.** The records are
`hunts/arch_cover/RESULTS.md`, `hunts/weil_gram/RESULTS.md` and
`hunts/weil_split/RESULTS.md`. This page is the front door. It quotes those
records and does not recompute them. The pins that keep the records from
drifting are `hunts/arch_cover/test_arch_cover.py`,
`hunts/weil_gram/test_weil_gram.py` and `hunts/weil_split/test_weil_split.py`.

**Nothing here is evidence for the Riemann Hypothesis.** A finite computation
is not a uniform statement about RH (`docs/08`). A hunt measures. It does not
claim. This page does not promote a claim. Grade of the page: **measured**,
the grade of the weakest step below. No human has reviewed the hunts or this
page.

A prior-art scan,
[`docs/reviews/2026-10-30-weil-degeneracy-prior-art.md`](reviews/2026-10-30-weil-degeneracy-prior-art.md),
compared the landed statements with sources it opened. Its three verdicts are
PARTIAL, PARTIAL and PARTIAL. This page follows that scan's closing list. It
claims nothing as new to the literature. The scan did not cover Undermind, did
not open Weil's 1952 paper or Yoshida's 1992 paper, and used Google Scholar
only for the two result pages named in the memo.

## 1. The object

In this repository's convention (`docs/10`, implemented in `zeta/weil.py`),

```
    W(h) = pole + arch + prime,
    pole = h(i/2) + h(-i/2),
    arch = (1/2pi) int h(r) [Re psi(1/4 + ir/2) - log pi] dr,
    prime = -2 sum_n Lambda(n) n^{-1/2} g(log n),
```

and `W(h) = sum_rho h(gamma_rho)` for every admissible `h`. Conventions differ
across the literature, so the module was calibrated by comparing the two sides
(`docs/10`). This page does not re-derive that calibration.

For `h = |f^|^2` the test function is non-negative on the real line. When the
ordinates in the sum are real, the zero side is a sum of non-negative terms,
and it does not cancel. The cancellation that produces a small `W` then sits
on the arithmetic side: three terms, each typically of size O(1), adding to
that non-negative number. Off the line an ordinate is not real, `h` is no
longer a square there, and the zero side need not be non-negative. That is the
criterion, not a fact the measurements assume away. The zero table used below
places its zeros on the line only up to its height.

The criterion, in this convention, is that `W(h) >= 0` for every admissible
`h` of positive type if and only if RH (`docs/07`, `docs/10`). Bombieri's Clay
notes, as read in the scan, state the same criterion as negativity of their
right-hand side, for every autocorrelation whose test function has vanishing
integrals against `dx/x` and against `dx`. The displays are not the same, and
this page does not equate them. The admissible class differs across sources.
`docs/10` records that, and neither that document nor this one re-derives the
minimal hypotheses.

The balance is the explicit formula: one sum, three kinds of term, required to
come out non-negative on autocorrelations, with either sign allowed on each
term. It is not a requirement that the archimedean term cover the prime side.
Hunt #155 measured a comb whose prime term is `+0.0174` (two teeth at
`log 2`, `sigma = 0.01`): on that row the prime sum helps. Connes and Consani,
arXiv:2106.01715, as read in the scan, record the opposite numerical fact from
any such covering demand. Past `log 2` the archimedean contribution alone
"ceases to be positive", and "the positivity is restored by adding the
contribution of the prime 2."

Grouping the prime side by place is already in the sources the scan opened.
Connes and Consani write a local term

```
    W_p(F) = (log p) sum_{m=1}^infty p^{-m/2} (F(p^m) + F(p^{-m}))
```

and a quadratic form as pole terms minus an archimedean distribution minus
`sum_p W_p`, labeled as Bombieri's form of the explicit formula. Bombieri's
Clay notes say: "The terms in the right-hand side of the equation can be
written as a sum of terms of local nature, associated to the absolute values
of the underlying number field." That sentence supports a place split. It does
not write the shift-norm cost in section 2.3. That cost is not presented here
as standard notation.

## 2. Three measurements

### 2.1 Hunt #155 (`arch_cover`): how deep the three pieces cancel

Grade: **measured**. No proof, no review. Two families: a Gaussian
`h = e^{-a r^2}`, and a comb. The printed balance table rounds. The
digit-by-digit comparison with the closed form is in section 4(b) of the hunt
record. An enclosed scan also ran a Fejer grid. Those rows are not in the
printed table, so this page does not quote them.

Gaussian rows, quoted from section 3 of `hunts/arch_cover/RESULTS.md`:

| family | pole | arch | prime | W | depth |
| --- | --- | --- | --- | --- | --- |
| gaussian a=0.05 | +2.025 | -1.909 | -0.116 | +9.18e-5 | 4.34 |
| gaussian a=0.2 | +2.103 | -1.500 | -0.603 | +8.86e-18 | 17.38 |
| gaussian a=0.45 | +2.238 | -1.230 | -1.008 | +1.80e-39 | 39.1 |
| gaussian a=0.65 | +2.353 | -1.113 | -1.240 | +7.98e-57 from the zeros (enclosure band 7e-33) | 56.5 |

On the full table, comb rows included, the zero side and the arithmetic side
agree between 1e-22 and 1e-32. The prime term grows with `a` on the Gaussian
(0.116 at 0.05, 0.603 at 0.2, 1.240 at 0.65) while the zero sum collapses onto
the first zero. The hard regime is inside the family, not outside it.

The cancellation depth is

```
    depth = log10( max(|pole|, |arch|, |prime|) / |W| ).
```

On the Gaussian, once one zero dominates, the zero side is
`2 e^{-a gamma_1^2}` times a factor `1 + O(e^{-a(gamma_2^2 - gamma_1^2)})`, and
the largest piece is `pole = 2 e^{a/4}`. The hunt record therefore states

```
    depth = a (gamma_1^2 + 1/4) / ln 10 = 86.88 a,
```

with `gamma_1^2 = 199.79`. Measured against that form, to every digit the
hunt's `results.json` and a direct sum over the zeros carry:

| a | measured | closed form |
| --- | --- | --- |
| 0.05 | 4.344 | 4.344 |
| 0.2 | 17.375 | 17.375 |
| 0.3 | 26.063 | 26.063 |
| 0.45 | 39.094 | 39.094 |

The section 3 table prints the same rows more coarsely (4.34, 17.38, 39.1)
and does not include `a = 0.3`. The statistic carries no information beyond
`h(gamma_1)` against the pole. It measures how far the test function sits from
the first zero.

The form first written was `depth = a gamma_1^2 / ln 10`, which drops the
pole's `e^{a/4}`. The hunt's kill condition, that the closed form fail to
reproduce a measured row to the printed digits, fired against that form (17.38
measured against 17.35 at `a = 0.2`) and was not recorded until landing. The
corrected form reproduces every row. That firing is a defect of the first
write-up, recorded in section 5.

Normalized by `||f||^2 = (1/2 pi) int h = 1/(2 sqrt(pi a))`, the ratio
`W / ||f||^2` along this family is about `4 sqrt(pi a) e^{-a gamma_1^2}`, and
it tends to 0. That ratio is what the hunt wrote. The scan did not find it
outside this repository. This page does not cite it as a known formula.

The inequality this page relies on is the one the ratio tending to 0 gives:
no inequality `W(|f^|^2) >= c ||f||^2` with a fixed `c > 0` holds over the
admissible class. The hunt record reads the same family as the bottom of the
form being 0, approached rather than attained away from the zeros. A proof
must be an identity, or an inequality whose constant degenerates as the test
function concentrates away from the zeros. Section 3 keeps this separate from
the window theorems, and records what the scan did find.

The enclosed instrument has a floor near 33 digits, set by prime truncation,
not by precision. At `a = 0.65` the enclosure is `[-7.12e-33, +6.36e-34]`,
with sign 0. The binding term is `prime_tail_bound = 7.76e-33` at the
`n_max = 2e6` cap. The value from the zeros there is `7.98e-57`. A report that
the enclosure was identical at 256 and 512 bits is unpinned: only the 256-bit
run is committed (`rows.jsonl`).

### 2.2 Hunt #156 (`weil_gram`): the bottom of the form on Gaussian spans

Grade: **measured**. Eigenvalues are not enclosed in ball arithmetic.

`lambda_min` on a span is the minimum of `W(|f^|^2) / ||f||^2` over that
span, and `W(|f^|^2) = sum_rho h(gamma_rho)`. It is not a squared distance to
functions vanishing at the zeros. Reading the zero side as a sum of
`|F(gamma)|^2` presupposes that the zeros lie on the line, which the zero
table guarantees only to its height.

On a purely broad Gaussian span, refined by adding `sigma = 0.05`, then
`0.25`, then `0.30`, section 3 of `hunts/weil_gram/RESULTS.md` gives:

| k | sigmas | lambda_min |
| --- | --- | --- |
| 2 | .10 .15 | +2.404e-3 |
| 3 | + .20 | +3.574e-7 |
| 4 | + .05 | +2.223e-7 |
| 5 | + .25 | +2.649e-13 |
| 6 | + .30 | +5.029e-22 |

The arithmetic side and the zero side agree at every printed digit. Every
element is individually healthy: `W(h_jj)` at `sigma = 0.30` is `3.10e-8`, and
at `sigma = 0.05` it is `2.75`. The bottom still falls by 19 orders from
`k = 2` to `k = 6`. At `k = 6` the bottom eigenvector is concentrated on
`sigma = 0.30` with a `-0.075` admixture of `sigma = 0.25`. The hunt record
describes the descent as geometric in the dimension, roughly a factor `1e-6`
per added element at this end of the range. That geometric drop was not found
by the scan outside this repository. It is not Zhu's window law: different
quotient, different parameter (section 3).

Adding one concentrated element is a different drop, the single-element
degeneracy of hunt #155 restated on the form. From `+3.574e-7` on the broad
span the bottom falls to `+3.917e-25` once `sigma = 0.45` is included, and the
bottom eigenvector is the coordinate vector of that element.

The `plus2` row, which adds `sigma = 0.60`, is not a measurement. The
`(0.60, 0.60)` entry has `prime_tail_bound` `1.2e-33` against a value
`1.16e-31`, 1 percent truncation uncertainty, and the eigenvalue sits
below that uncertainty. The two sides disagree because the eigenvalue is far
below the entry uncertainty. What is established is only
`lambda_min(plus2) < 1e-30`. The unresolved digits are not quoted here.

A file first written as a dps 90 run was computed at dps 50: `run_base` took
its precision default from a module constant, and `main` did not pass the
requested precision. It was rerun at dps 90 at landing (3 min 45 s). No
eigenvalue changed at any printed digit. The rerun is a null test of the
arithmetic side. Entry residuals sit at the zero table's 30-digit floor, about
`1e-32`, and the check cannot confirm entries below that floor.

Consequence, scoped as the hunt record scopes it after the landing correction.
A uniform positive gap does not survive enlargement of these subspaces. An
argument that needs `lambda_min` bounded below independently of the subspace
cannot work on these spans: the gap is created by the choice of subspace and
destroyed by adding dimensions. Nonnegativity on each subspace of an exhausting
sequence does pass to the limit. That weaker route is untouched by the
measurement.

### 2.3 Hunt #157 (`weil_split`): the prime side split by place, on rectangles

Grade: **measured**, with one exact identity: the place sum against the prime
term, checked to the float-sum floor.

For `f = b^{-1/2} 1_{[-b/2, b/2]}`, so `||f||^2 = 1`, the shift
`Phi_p f = sum_{m >= 0} p^{-m/2} f(. - m log p)` has finitely many overlapping
terms. The hunt writes

```
    ||Phi_p f||^2 = (1/b) sum_{m,n >= 0} p^{-(m+n)/2} (b - |m-n| log p)_+
    Q_p = (1 - 1/p) ||Phi_p f||^2
    cost_p = log p (Q_p - 1)
```

`cost_p` is an exact finite closed form. It carries `log p`, `p^{-1/2}` and
`b`. It is not a rational number. It is not standard notation. It is a
rewriting of the von Mangoldt sum for an autocorrelation, already checked in
this repository: `docs/24` keeps the general factor `Q_p - ||f||^2`, and
`hunts/weil_split` specialises to `||f||^2 = 1`, which is why the cost is
`log p (Q_p - 1)` on this family. The scan did not find this rewriting outside
the repository.

`sum_p cost_p = -prime_term` was checked to `1e-16`, the float-sum floor, at
every `b` tested. Only primes with `log p < b` contribute, that is `p <= e^b`.

Quoted from section 2 of `hunts/weil_split/RESULTS.md`:

| b | primes contributing | sum of cost | top-3 share | cover `(pole+arch)/cost` | margin | quad-vs-zero |
| --- | --- | --- | --- | --- | --- | --- |
| 2.0 | 4 | 1.745851 | 0.977 | 1.030400439 | 3.04e-2 | 7.5e-3 |
| 3.0 | 8 | 4.085344 | 0.727 | 1.006436469 | 6.44e-3 | 5.3e-3 |
| 4.5 | 24 | 9.835248 | 0.441 | 1.001504129 | 1.50e-3 | 1.4e-3 |
| 6.0 | 79 | 20.158935 | 0.261 | 1.000791320 | 7.91e-4 | 7.8e-3 |
| 8.0 | 429 | 48.293063 | 0.126 | 1.000158833 | 1.59e-4 | 2.2e-3 |

`cover` in that table is `(pole + arch) / cost`, computed as
`(W_from_zeros - prime_term) / sum_p cost_p`, not from the archimedean
quadrature. By construction

```
    cover - 1 = W_zeros / sum_p cost_p,
```

with `W_zeros = sum h(gamma)`. On this family `h >= 0`, and the zeros in the
table are on the line, so `W_zeros >= 0` inside that table's range. The margin
is `W` normalised by the prime cost, not an independent statement about the
archimedean term. Its decay says `W` grows more slowly than the prime side.
From `b = 2` to `b = 8` the margin falls from `3.04e-2` to `1.59e-4`. The
local exponents between rows run from 2.2 to 5.6, and the overall decay is
about `b^{-3.8}`. The scan did not find this identity, or that measured decay,
outside the repository.

The cost spreads. At `b = 2` the top three places carry share 0.977 (the hunt
record names `p = 2, 3, 5` as carrying 98 percent). At `b = 8` there are 429
places and the top three carry 0.126. On this family there is no finite set of
important primes doing the work, and no bounded slack.

What does exist in the literature, and is not this margin, is the semilocal
reduction of Connes, Consani and Moscovici, arXiv:2310.18423, as read in the
scan: a property `P(n)` using only the Euler factors for primes smaller than
`n`, such that `P(n)` for all `n` is equivalent to RH, because Weil positivity
on test functions supported in `[1/n, n]` is that criterion. More places enter
as the support widens, and the criterion is the whole sequence. That is not a
decaying covering margin.

The archimedean quadrature on this family agrees with the zero side only to
between `1e-3` and `8e-3`: three digits. `h` decays like `1/r^2`, which is
what compact support of `f` costs. Anyone quoting the quadrature value of
`pole + arch` is quoting three-digit arithmetic. The cover column is printed
to nine digits because it uses the zero side and the exact prime side. The two
differ by the `quad-vs-zero` column.

## 3. What a proof through this functional would have to be

The constraint, stated so it does not outrun the records:

There is no inequality `W(|f^|^2) >= c ||f||^2` with a fixed `c > 0` over the
admissible class. On the Gaussian family the ratio tends to 0 (hunt #155). On
growing Gaussian spans a uniform positive gap does not survive enlargement
(hunt #156). A proof through this functional has to be an identity, or a
decomposition whose constant degenerates with the test function.

The weaker route is untouched. Nonnegativity on each subspace of an exhausting
sequence passes to the limit. That is the shape of the criterion. It does not
need a gap.

This is not a statement the laboratory is presenting as its own. The scan's
verdict on the question is PARTIAL.

Bombieri, "Remarks on Weil's quadratic functional in the theory of prime
numbers, I", Atti Accad. Naz. Lincei, Rend. Lincei Mat. Appl. (9) 11 (2000),
183-233, as the scan records it: the quadratic functional is positive
semidefinite if and only if RH, it attains its minimum on the unit sphere of
L2 functions supported in a given interval, and it is positive definite for
sufficiently small support. The small-support half is attributed there to
Yoshida, "On Hermitian forms attached to zeta functions", Adv. Stud. Pure Math.
21 (1992), 281-325. Yoshida's paper was not opened. Zhu, arXiv:2608.24827,
quotes the classical range as support in `[-(log 2)/2, (log 2)/2]`, attributed
to Yoshida and, by a different method, to Connes and Consani. Small-support
positivity is cited here only as Bombieri and Zhu state it. Bombieri's
attainment on each fixed window is not a uniform gap. Nonnegativity on every
compact window is the criterion. It does not require a constant `c > 0`
independent of the window.

Connes and Consani, arXiv:2106.01715, as the scan records them: if RH holds,
their window form is strictly positive, so the radical on each finite window
is `{0}`, and yet one can build a test function on that window with the form
much smaller than the square of the norm. They report a smallest positive
eigenvalue `2.389 x 10^{-48}` at `lambda^2 = 11`. That is a reported
eigenvalue, not a theorem that the infimum over the whole admissible class is
0, and it is not a geometric drop per added Gaussian.

Zhu, arXiv:2608.24827, defines `lambda^*(L)` as the infimum of
`Q(f) / ||f||_2^2` for support in `[-L, L]`. Under RH,
`lambda^*(L) <= exp(-L e^L)` for all large `L`, by an explicit construction.
He writes that the computation turns "the folklore that positivity gets
exponentially hard" into measured constants and a barrier. That folklore
sentence is his. The conditional bound is a citation for no fixed `c > 0` on
the union of the windows, because every window sits inside the admissible
class and the bound tends to 0. It is conditional on RH. If RH is false,
Weil's criterion already says the form takes a negative value, so no positive
`c` exists either. The scan did not find that dichotomy written as one lemma.
Zhu's unconditional upper bounds at specific `L`, down to `3.2 x 10^{-283}` at
`L = 2` in the abstract the scan read, show the window constant is tiny at
those `L`. They are not themselves a proof that the infimum over all `L` is 0.

Keep the two directions separate, as hunt #156 section 4 does. Nonnegativity
on each subspace of an exhausting sequence is the criterion and passes to the
limit. A uniform positive gap does not survive enlargement: under RH that is
Zhu's theorem for windows, and the scan did not find it as a theorem about
Gaussian spans. The Gaussian ratio in section 2.1 is not cited here as a known
formula.

## 4. Prior art, in the scan's own verdict words

The scan is
[`docs/reviews/2026-10-30-weil-degeneracy-prior-art.md`](reviews/2026-10-30-weil-degeneracy-prior-art.md).
Verdict words, quoted exactly:

1. PARTIAL. The split of the explicit formula into one local term per place is
   in the sources opened. The L2 shift-norm identity is not.
2. PARTIAL. The three-term balance is the explicit formula. The covering-margin
   identity was not found. The disowned framing, that the archimedean term must
   dominate the sum of local costs, is not what the opened sources say.
3. PARTIAL. A falling window constant, and the passage of nonnegativity rather
   than of a uniform constant, are in the sources opened. The Gaussian ratio,
   and a geometric drop per added Gaussian, were not found.

No verdict in that scan is KNOWN, and none is NOT FOUND. Where a statement
above is the explicit formula, a place split, a window infimum, or the passage
of nonnegativity to the limit, the citation is to the source the scan opened,
not to these hunts. Where a statement is the shift-norm cost, the rectangle
margin, the Gaussian ratio, or the geometric drop on Gaussian spans, the page
says the scan did not find it outside this repository. That is a limit of the
scan, not a claim that the statement is unknown.

The scan did not cover Undermind. The site answered, and the page was a login
wall, so no query was run. It did not open Weil 1952 or Yoshida 1992. Google
Scholar was used only for the two result pages named in the memo. Neither
Google Scholar nor the arXiv and zbMATH queries recorded there is a complete
literature search.

## 5. Scope and defects

The page takes the grade of its weakest step. The place-sum identity is a
finite check at the float-sum floor. The strategic reading also uses
eigenvalues that are not enclosed, and a cover column whose quadrature sibling
has only three digits. Grade: measured. Nothing under the three hunt
directories is a result, and this page does not make one of them.

Defects recorded on the landed hunt records, carried here rather than left in
the directories:

- Eigenvalues in hunt #156 are computed in mpmath, not enclosed. The
  generalised eigenproblem is badly conditioned by construction: entries span
  `1e-31` to 1. Nothing in that hunt is enclosed.
- The `plus2` row is unresolved. The only established bound is
  `lambda_min(plus2) < 1e-30`. The unresolved digits are not quoted on this
  page.
- The archimedean quadrature in hunt #157 agrees with the zero side only to
  between `1e-3` and `8e-3`. Three digits. The printed cover column does not
  use that quadrature. Quoting the quadrature value of `pole + arch` is quoting
  three-digit arithmetic.
- The families are narrow. Hunt #155: finite families, finite grids, no
  statement uniform in `f`. Hunt #156: Gaussians centred at the origin. Shifts
  and non-Gaussian elements were not measured. Hunt #157: one rectangle
  family. The widest member still has `h` of slow decay.
- No human has reviewed any of the three hunts, or this page.
- The enclosed instrument in hunt #155 has a floor near 33 digits, set by the
  prime-tail cap `n_max = 2e6` (`prime_tail_bound = 7.76e-33` at `a = 0.65`),
  against a value from the zeros of `7.98e-57`. Adding bits does not move that
  floor. The floor is a measured optimum at one cap, not a proved ceiling:
  candidate, the Gaussian family at `a <= 0.65`, information class the prime
  sum truncated at `n_max`, proof status none.
- A statement that the `a = 0.65` enclosure was identical at 256 and 512 bits
  is unpinned. Only the 256-bit run is committed.
- The first `results_dps90.json` in hunt #156 was computed at dps 50. It was
  rerun at dps 90 at landing. No eigenvalue changed at any printed digit. The
  arithmetic side is more accurate than the zero-table check, which cannot
  confirm entries below about `1e-32`.
- The depth law was first written as `a gamma_1^2 / ln 10`, dropping the
  pole's `e^{a/4}`. The hunt's kill condition fired against that form (17.38
  measured against 17.35 at `a = 0.2`) and was not recorded until landing. The
  corrected form is the one in section 2.1.
- The archimedean term has no second backend in this tree.
  `enclose_weil_functional` reports that a two-backend cross-check is
  unavailable, because `mpmath.iv` has no enclosed quadrature. A quadrature
  error in the archimedean term would look like `W` moving. The hunt record
  calls this the largest unmitigated risk in every enclosed number it produced.
- Hunt #157's cover uses the zero side for `W`, so it inherits the zero
  table's 30-digit accuracy and the range `gamma < 10^4`. The zero tail bound
  is reported by `explicit_formula_sides` and is negligible for these `b`, but
  it is not zero.
- `Q_p > ||f||^2` for every place measured in hunt #157, so every `cost_p > 0`
  there. That is the opposite sign to reading `Q_p` as the norm the
  local-positivity gate was about. The gate in `docs/24` applies to Toeplitz
  sections of local coefficients, not to `||Phi_p f||^2` of a fixed `f`. The
  two should not be conflated.
- `lambda_min > 0` at every measured `k` is consistent with RH and with its
  negation on other spaces. It is not evidence about RH in either direction.
