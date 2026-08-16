# SOURCE.md: pinned source texts (WP1)

This file pins the texts the hunt attacks and the literature it leans on, so
that every later step works against the served words rather than a
paraphrase. Nothing in this file is a result of this hunt. Constants that
appear here are quoted claims of the cited sources, not values decided by
this hunt; decided values belong to WP2 and are stated there with backend
and precision.

Fetch log:

- 2026-08-15: OEIS A107311 fetched as JSON (the scout's copy, kept in the
  session scratchpad as `A107311.json`).
- 2026-08-16: refetched live with curl from
  `https://oeis.org/search?q=id:A107311&fmt=json`; the two fetches are
  byte-identical (empty `diff`). The entry is unchanged between the two
  dates.
- Entry-internal provenance: revision 55, last modified
  2024-12-29T23:50:41-05:00, created 2005-07-19; the conjecture comment
  block is dated Dec 21 2024 inside the entry text.

## 1. OEIS A107311, verbatim as served

The complete JSON response body, reproduced byte for byte from the
2026-08-16 fetch (the server escapes `<` and `>` as `\u003c` and `\u003e`
inside the link fields; the indentation is the server's):

```json
[
	{
		"number": 107311,
		"data": "1,7,2,8,6,4,7,2,3,8,9,9,8,1,8,3,6,1,8,1,3,5,1,0,3,0,1,0,2,9,7,6,9,1,4,6,4,2,3,4,1,0,9,8,4,9,3,3,5,0,3,5,7,3,2,3,2,1,2,8,5,9,0,8,4,2,3,1,7,8,5,9,6,5,3,5,7,1,0,0,8,6,7,7,2,7,4,6,0,8,1,0,8,8,9,8,2,6,4,4,0,1",
		"name": "Decimal expansion of the solution to zeta(x) = 2.",
		"comment": [
			"From _Artur Jasinski_, Dec 21 2024: (Start)",
			"Borwein et al. (2007) proved (Theorem 3.1) that the real parts of the zeros of the partials sums of the Riemman zeta functions are not greater than this constant.",
			"Conjecture 1: the real parts of the zeros of the prime zeta function are not greater than this constant.",
			"Conjecture 2: the real parts of the zeros of the anyone subset of the prime zeta function are not greater than this constant. (End)"
		],
		"reference": [
			"Steven R. Finch, Mathematical Constants, Cambridge University Press, 2003, Section 5.5 Kalmar's Composition Constant, p. 293."
		],
		"link": [
			"Peter Borwein, Greg Fee, Ron Ferguson, and Alexa van der Waal, \u003ca href=\"https://projecteuclid.org/journals/experimental-mathematics/volume-16/issue-1/Zeros-of-Partial-Summs-of-the-Riemann-Zeta-Function/em/1175789799.full\"\u003eZeros of Partial Sums of the Riemann Zeta Function\u003c/a\u003e, Experiment. Math. 16(1) (2007), pp. 21-40. See p. 25.",
			"Einar Hille, \u003ca href=\"http://matwbn.icm.edu.pl/ksiazki/aa/aa2/aa215.pdf\"\u003eA problem in \"factorisatio numerorum\"\u003c/a\u003e, Acta Arithmetica, 2(1);134-144, 1936.",
			"Hsien-Kuei Hwang, \u003ca href=\"https://doi.org/10.1006/jnth.1999.2467\"\u003eDistribution of the number of factors in random ordered factorizations of integers\u003c/a\u003e, Journal of Number Theory 81:1 (2000), pp. 61-92.",
			"M. Klazar and F. Luca, \u003ca href=\"https://arxiv.org/abs/math/0505352\"\u003eOn the maximal order of numbers in the \"factorisatio numerorum\" problem\u003c/a\u003e, arXiv:math/0505352 [math.NT], 2005-2006."
		],
		"example": [
			"zeta(1.72864723899818361813510301...) = 2."
		],
		"mathematica": [
			"x /. FindRoot[ Zeta[x] == 2, {x, 2}, WorkingPrecision -\u003e 102] // RealDigits // First (* _Jean-François Alcover_, Mar 19 2013 *)"
		],
		"program": [
			"(PARI) solve(X=1.5,2,zeta(X)-2)"
		],
		"xref": [
			"Cf. A129374, A247667."
		],
		"keyword": "nonn,cons",
		"offset": "1,2",
		"author": "_Ralf Stephan_, May 20 2005",
		"references": 23,
		"revision": 55,
		"time": "2024-12-29T23:50:41-05:00",
		"created": "2005-07-19T03:00:00-04:00"
	}
]

```

Field notes, no content changed:

- **name**: "Decimal expansion of the solution to zeta(x) = 2." This is the
  entry's definition of the constant called x* throughout this hunt.
- **data**: the first 102 decimal digits of x*, beginning
  1.7286472389981836181351030102976914642341... (the entry's claim,
  quoted, not a value this hunt has decided).
- **example**: "zeta(1.72864723899818361813510301...) = 2."
- **comment**: one attribution line and two conjecture lines, all three
  from Artur Jasinski, dated Dec 21 2024; quoted verbatim in section 2.
- **reference**: Steven R. Finch, Mathematical Constants, Cambridge
  University Press, 2003, Section 5.5 (Kalmar's Composition Constant),
  p. 293. The entry's own framing of x*: it is Kalmar's composition
  constant, the growth exponent of ordered factorizations, which is what
  three of the four links (Hille 1936, Hwang 2000, Klazar-Luca 2005-2006)
  concern.
- **link**: the fourth link is the partial-sums paper behind the first
  comment line: Borwein, Fee, Ferguson, van der Waal(l), Experimental
  Mathematics 16(1) (2007), with the entry's pointer "See p. 25." The
  served Project Euclid URL and page title carry the typo "Summs"; the
  fourth author's surname is spelled "van der Waal" in the OEIS link text
  and "van der Waall" in the bibliographies quoted in section 3.
- **author** (of the entry): Ralf Stephan, May 20 2005. The conjectures
  are a 2024 addition to a 2005 entry about the constant.

## 2. The two conjectures, verbatim, and their precise reading

The comment field in full, word for word as served (spelling as served:
"partials sums", "Riemman" and "the anyone subset" are in the source):

> From _Artur Jasinski_, Dec 21 2024: (Start)
> Borwein et al. (2007) proved (Theorem 3.1) that the real parts of the zeros of the partials sums of the Riemman zeta functions are not greater than this constant.
> Conjecture 1: the real parts of the zeros of the prime zeta function are not greater than this constant.
> Conjecture 2: the real parts of the zeros of the anyone subset of the prime zeta function are not greater than this constant. (End)

### What Conjecture 1 asserts, quantified

For every s at which the prime zeta function P(s) = sum_p p^{-s} vanishes,
Re s <= x*. "Not greater than" is <=, so a refutation requires a zero with
Re s > x* strictly.

Domain of the statement. The series converges absolutely for Re s > 1. The
classical continuation (Glaisher's inversion, treated in detail by Froberg
1968) is

    P(s) = sum_{k>=1} (mu(k)/k) log zeta(ks),

analytic on Re s > 0 except at s = 1/k for squarefree k (from the pole of
zeta at 1) and at s = rho/k for nontrivial zeros rho of zeta (logarithmic
branch points); the line Re s = 0 is a natural boundary (Landau and
Walfisz 1920; Froberg 1968). The entry does not restrict the domain, and
the standard reading is: the zeros of P wherever P is defined.

Reading-independence of the planned refutation. Since x* = 1.7286... > 1,
any zero with Re s > x* found in the half-plane of absolute convergence
Re s > 1 is a zero of the defining series itself, where every branch of
every continuation agrees with the series. Zeros there are zeros under
every reading of "the prime zeta function", so a refutation built from
them refutes all readings at once. This is why the hunt's target strip
(x*, sigma_c) sits entirely inside Re s > 1 (MISSION.md).

### What Conjecture 2 asserts, quantified

For every subset S of the primes (the evident intent of "the anyone
subset"), every zero of P_S(s) = sum_{p in S} p^{-s} satisfies Re s <= x*.
For finite S this is an exponential polynomial, entire; for infinite S the
series is analytic at least on Re s > 1. The same reading-independence
holds: subset zeros with Re s > 1 refute every reading. Taking S = all
primes recovers Conjecture 1; the extra exposure of Conjecture 2 is the
universal quantifier, which must survive every S, including the tails
S = {p >= p_k}.

### Continuation sources, pinned

C.-E. Froberg, "On the prime zeta function", BIT (Nordisk Tidskr.
Informationsbehandling) 8 (1968), no. 3, pp. 187-202,
doi:10.1007/BF01933420, Zbl 0167.04201. Continuation to Re s > 0, natural
boundary at Re s = 0, numerical tables, and the remark on roots quoted in
section 4.

E. Landau and A. Walfisz, "Uber die Nichtfortsetzbarkeit einiger durch
Dirichletsche Reihen definierter Funktionen", Rend. Circ. Mat. Palermo 44
(1920), pp. 82-86. Natural boundary at Re s = 0. (The reference list of
Froberg's paper, as transcribed by zbMATH, dates it 1919; MathWorld dates
it 1920.)

## 3. The partial-sums provenance of x*

### The entry's own attribution

The first comment line (verbatim in section 2) plus the entry's link:
"Peter Borwein, Greg Fee, Ron Ferguson, and Alexa van der Waal, Zeros of
Partial Sums of the Riemann Zeta Function, Experiment. Math. 16(1) (2007),
pp. 21-40. See p. 25."

### The paper, pinned

P. Borwein, G. Fee, R. Ferguson, A. van der Waall, "Zeros of Partial Sums
of the Riemann Zeta Function", Experimental Mathematics 16 (2007), no. 1.
Pages 21-40 per the Project Euclid metadata and the OEIS link, 21-39 per
the Platt-Trudgian bibliography below. Stable URL:
https://projecteuclid.org/euclid.em/1175789799 (the served page title
carries the typo "Partial Summs").

Access note (2026-08-16): the Euclid abstract page is reachable, the PDF
is behind a bot wall (Incapsula interstitial), and no open copy was found
in this session. The opening sentence of the abstract as served by Euclid:
"The semiperiodic behavior of the zeta function zeta(s) and its partial
sums zeta_N(s) as a function of the imaginary coordinate has been long
established." (Greek transcribed to ASCII.) Theorem 3.1's exact wording is
therefore pinned through the entry's paraphrase above plus two independent
secondary statements, quoted next from peer-reviewed papers whose authors
read the original.

### Secondary statement A: Platt and Trudgian

D. J. Platt and T. S. Trudgian, "Zeroes of partial sums of the
zeta-function", arXiv:1507.01340v2 (15 Dec 2015), published in LMS J.
Comput. Math. 19 (2016). They write zeta_N(s) = sum_{n<=N} n^{-s}. Quotes
transcribed to ASCII from the typeset PDF:

> Spira [13, Thm. 1] proved that all zeroes of zeta_N(s) must have real
> part less than 1.85; this was sharpened in [3, Theorem 3.1] to 1.73.

with [3] the Borwein-Fee-Ferguson-van der Waall paper ("Experiment. Math.,
16(1):21-39, 2007" in their list) and [13] R. Spira, "Zeros of sections of
the zeta function I", Math. Comp., 20:542-550, 1966.

> Turan [16] showed that the Riemann hypothesis would follow if for all N
> sufficiently large zeta_N(s) had no zero in sigma > 1. Let psi_N be the
> supremum over all values of sigma for which zeta_N(s) = 0. Montgomery
> [9] showed that for all N sufficiently large,
>
>     psi_N = 1 + (4/pi - 1 - o(1)) (log log N / log N),
>
> where the constant 4/pi - 1 is best possible. Therefore for N
> sufficiently large, zeta_N(s) has zeroes in sigma > 1.

with [9] H. L. Montgomery, "Zeros of approximations to the zeta function",
in P. Erdos, editor, Studies in Pure Mathematics: to the Memory of Paul
Turan, pp. 497-506, Birkhauser, Basel, 1983, and [16] P. Turan, "On some
approximative Dirichlet-polynomials in the theory of the zeta-function of
Riemann", Danske Vid. Selsk. Mat.-Fys. Medd., 24(17):1-36, 1948.

### Secondary statement B: Gonek and Ledoan

S. M. Gonek and A. H. Ledoan, "Zeros of partial sums of the Riemann
zeta-function", arXiv:0807.0019v2, published in Int. Math. Res. Not.
IMRN (2010), no. 10, pp. 1775-1791 (journal data per the Platt-Trudgian
bibliography). They write F_X(s) = sum_{n<=X} n^{-s}. Their Theorem 1,
transcribed to ASCII from the typeset PDF:

> Theorem 1. The zeros of F_X(s) lie in the strip alpha < sigma < beta,
> where alpha and beta are the unique solutions of the equations
> 1 + 2^{-sigma} + ... + (X-1)^{-sigma} = X^{-sigma} and
> 2^{-sigma} + 3^{-sigma} + ... + X^{-sigma} = 1, respectively. In
> particular, alpha > -X and beta < 1.72865. For X sufficiently large
> F_X(s) has no zeros in the half-plane sigma >= 1 + 2 log log X / log X.
> Moreover, for any constant c with c > 4/pi - 1 there exists a number
> X_0(c) such that if X >= X_0(c), then F_X(s) has at most a finite
> number of zeros in the half-plane sigma > 1 + c log log X / log X.

And from their proof of Theorem 1:

> That the zeros all lie in a strip follows immediately from the fact
> that |1 + 2^{-s} + ... + X^{-s}| > 0 if 1 + 2^{-sigma} + ... +
> (X-1)^{-sigma} < X^{-sigma} or if 2^{-sigma} + ... + X^{-sigma} < 1.
> The estimates for alpha and beta may be found in Borwein et al. [1].
> The last two assertions are due to Turan [9] and Montgomery [4],
> respectively.

with their [1] the Borwein-Fee-Ferguson-van der Waall paper, their [9]
Turan 1948 and their [4] Montgomery 1983, as pinned above.

### The mechanism, and the exact sense in which x* belongs to this family

Observation (elementary, this file's own; no computation is being decided
here): beta_X in Gonek-Ledoan's Theorem 1 is the unique real root of
sum_{n=2}^X n^{-sigma} = 1, the wall past which the leading term 1
outweighs the rest of the sum by the triangle inequality. The left side
increases with X, pointwise in sigma, toward zeta(sigma) - 1; hence beta_X
increases with X and converges upward to the unique real root of
zeta(sigma) = 2, which is the entry's x*. So:

- for every X, all zeros of the partial sum satisfy Re s <= beta_X < x*;
- the thresholds beta_X approach x* as X grows;
- x* is the supremum of the walls over the whole family, and no single
  member's zeros reach it.

This is the provenance of x*: the limit of the triangle-inequality walls
for the family of partial sums of zeta.

### What approaches x*, and what does not

The walls approach x*. The zeros do not: by Montgomery's theorem quoted
above, the supremum psi_N of real parts of actual zeros of zeta_N is
1 + (4/pi - 1 - o(1)) log log N / log N, which tends to 1. The wall is
asymptotically far from sharp for partial sums; the frequencies log n for
2 <= n <= N are rationally dependent (log 4 = 2 log 2, and so on), and the
phase steering that saturates a wall needs independent frequencies. For
P(s) the frequencies log p are linearly independent over Q, which is
exactly why MISSION.md expects the corresponding wall sigma_c to be
approached by actual zeros of P. The conjecture therefore transplants a
constant from a family where the wall is never attained, and is not even
the limit of the real parts of zeros, onto a family with a different wall
that plausibly is attained. Both halves of that last sentence are the
hunt's business to establish (WP2, WP3); this file only fixes what the
sources say.

## 4. Prior literature on zeros of P(s) itself

**Corrected 2026-08-16, after the first version of this section was found to
be wrong.** The first version ended with the sentence "No source was found
naming any rightmost-zero threshold for P(s), so nothing found here trips kill
condition 2 of MISSION.md." That sentence is false. Two published sources own
the threshold and the mechanism, and both were located by a later adjudication
sweep on the same day. The false sentence is removed rather than softened, and
what replaces it is below. Everything that was *found* by the first sweep
(Froberg, the zbMATH review, the search log) is kept unchanged, because the
queries were really run and what came back is really what came back; only the
conclusion drawn from their emptiness was wrong.

### 4.0 Kill condition 2 has fired

MISSION.md's kill condition 2 reads:

> a literature source is found proving the sigma_c threshold for P, in which
> case the finding is reclassified as a rediscovery and the OEIS correction
> cites that source instead of this work

Such a source exists, was published on 3 June 2025, and states the same
constant sigma_c = 1.77954465354699... by the same triangle-inequality proof.
A second, older source owns the general theorem of which the whole hunt is a
specialization, and it is *stronger* than what the hunt proved. The condition
has fired on both counts. Consequences, applied throughout this directory:

- the hunt's Theorem A(a), Theorem B, Corollary B1, Lemma 2, Lemma 4, the
  aggregated-tail device and the value of sigma_c are **pure rediscovery**;
- the OEIS correction cites Belovas et al. for the threshold, not this work
  (`OEIS-CORRECTION.md`, rewritten);
- what survives as this hunt's own is listed in `PRIOR-ART.md` section 9 and
  restated in `RESULTS.md` section 7.1, and it is narrow.

### 4.1 The source that owns the threshold: Belovas, Cepaityte and Sabaliauskas (2025)

Full pin: Igoris Belovas, Rugile Cepaityte and Martynas Sabaliauskas, "On the
zero-free region and the distribution of zeros of the prime zeta function",
Analele Stiintifice ale Universitatii Ovidius Constanta, Seria Matematica
**33**(2) (2025), 27-44. DOI `10.2478/auom-2025-0017`. Received 07.10.2024,
accepted 28.02.2025. Open access, CC BY-NC-ND. PDF:
`https://www.anstuocmath.ro/mathematics/anale2025v2/2_Igoris_Belovas_et_al.pdf`
(2.2 MB, image-scanned; the text used here was obtained by downloading the file
and running `pdftotext`, not by fetching the page). Bibliographic note: the
PDF's own running header says 27-43 while external indexing and the last
printed folio give 27-44; cite 27-44.

Their Theorem 1, verbatim:

> **Theorem 1.** The prime zeta function has no zeros in the half-plane
> sigma > sigma_0. Here sigma_0 = 1.77954465354699... is the zero of the
> function U(sigma) = 2^{1-sigma} - zeta_P(sigma).

Their proof, verbatim, which is the hunt's Theorem A(a) argument:

> First we note that |zeta_P(s)| = |1/2^s + 1/3^s + 1/5^s + ...| >
> 1/2^sigma - 1/3^sigma - 1/5^sigma - ... = 2^{1-sigma} - zeta_P(sigma) =
> U(sigma).

Their Lemma 1, verbatim, which is the hunt's Lemma 1 (uniqueness of the root):

> **Lemma 1.** Let the function U(sigma) be defined as above and
> sigma_1 = 2.18, then U'(sigma) > 0 if 1 < sigma <= sigma_1, and
> U(sigma) > 0 if sigma >= sigma_1.

Their Remark 1 and Conjecture 1, verbatim (the printed Remark writes
`zeta_P(sigma) = 0` where it means `zeta_P(s) = 0` with s = sigma + it; the
typo is in the source and the meaning is unambiguous):

> **Remark 1.** Let M = 200000 and define
>
>     sigma_T = max_{|t| < T} { sigma | zeta_P(sigma) = 0 },        (2)
>
> then we receive sigma_M = 1.682628788045196... . Thus, the result of Theorem
> 1 can not be refined by more than Delta = 0.097.

> **Conjecture 1.** The estimate for the zero-free plane given by Theorem 1 can
> not be improved, that is, if sigma_T is defined as above (see (2)), then
>
>     lim_{T -> infinity} sigma_T = sigma_0.                        (3)

What their paper does **not** contain, established by word-level search over
the extracted text: no occurrence of `A107311`, `Jasinski` or `1.72864`, and
no occurrence of `almost period`, `Moreno`, `Sepulcre`, `Vidal`, `Kronecker`,
`Bohr`, `exponential polynomial` or `subset`. There is one incidental
`oeis.org` URL, in reference [2], hosting Cohen's Hardy-Littlewood-constants
preprint; it is not a reference to A107311. So the paper does not engage the
OEIS conjectures, does not refute them (its bound 1.7795 is *weaker* than the
conjectured 1.72864, and its numerics stop at 1.6826, below x*), and does not
treat prime subsets.

### 4.2 The source that owns the mechanism: Sepulcre and Vidal (2022, preprint 2018)

Full pin: J. M. Sepulcre and T. Vidal, "On the real projections of zeros of
analytic almost periodic functions", Carpathian Journal of Mathematics **38**
(2022), no. 2, 489-501. MSC 30B50, 30D20, 30Axx, 11J72. Preprint:
arXiv:1805.02041 [math.CV], 5 May 2018, titled "On the real projections of
zeros of almost periodic functions" (the journal title adds "analytic").
**Preprint Theorem 6 = journal Theorem 4.3**, statements word for word
identical apart from the label.

Their Theorem 4.3, verbatim from the journal text, with R_f defined at their
equation (1.4) as `R_f := closure{Re s : f(s) = 0, s in U} intersect
(alpha, beta)`:

> **Theorem 4.3.** Let f(s) be an almost periodic function in a vertical strip
> U = {s = sigma + it : alpha < sigma < beta} whose Dirichlet series is given by
> sum_{n >= 1} a_n e^{lambda_n s} with {lambda_1, lambda_2, ..., lambda_k, ...}
> Q-linearly independent and k > 2. Let sigma_0 in (alpha, beta). Then
> sigma_0 in R_f if and only if
>
>     |a_j| e^{sigma_0 lambda_j} <= sum_{i >= 1, i != j} |a_i| e^{sigma_0 lambda_i}
>                                                   (j = 1, 2, ..., k, ...).   (4.8)

Specialized to P(s) = sum_p p^{-s} (a_n = 1, lambda_n = -log p_n), condition
(4.8) becomes `2 p_j^{-sigma_0} <= P(sigma_0)`, whose binding instance is
j = 1, that is `U(sigma_0) = 2^{1-sigma_0} - P(sigma_0) <= 0`: exactly Belovas
et al.'s U. The specialization is worked out hypothesis by hypothesis in
`PRIOR-ART.md` section 6. The conclusion it yields,
`closure{Re s : P(s) = 0, Re s > 1} intersect (1, infinity) = (1, sigma_c]`,
is strictly stronger than the hunt's Theorem B.

The proof of the "if" direction also contains, in print, the hunt's
aggregated-tail device: the infinite tail is collapsed into a single polygon
side of length `r := sum_{j >= n_0} |a_j| e^{sigma_0 lambda_j}`, with the
polygon step attributed to Moreno at `[14, p.71]`.

### 4.3 Moreno (1973)

C. J. Moreno, "The zeros of exponential polynomials (I)", Compositio
Mathematica **26** (1973), no. 1, 69-78. Not fetched; cited here on the
strength of Sepulcre and Vidal's citations at `[14, p.71]` for the polygon
construction (the hunt's Lemma 2) and `[14, Lemma, p.73]` elsewhere. The
adjudication further records that Moreno himself applies the Geometric
Principle to `sum_{p <= M} p^{-s}`; that statement is accepted from the
adjudication and was not verified against the paper.

Also named by the adjudication and not checked in this directory: Sepulcre and
Vidal, "On the non-isolation of the real projections of the zeros of
exponential polynomials", J. Math. Anal. Appl. **437** (2016), no. 1, 513-525
(Proposition 5 and Corollary 6: supremum of real parts equals the balance root,
and is not attained, for finite sums), and a Math.StackExchange comment (question
3894479, K. Conrad, 2020-11-05) giving the balance equation and the
triangle-inequality argument publicly.

### 4.4 Froberg 1968, the one source the first sweep found

Full pin: C.-E. Froberg, "On the prime zeta function", BIT 8 (1968),
no. 3, pp. 187-202, doi:10.1007/BF01933420, Zbl 0167.04201. Access attempt
on 2026-08-16: the Springer landing page redirects to a login wall; the
paper text was not reachable in this session. Two independent witnesses to
its content on roots were captured instead.

The zbMATH review (Zbl 0167.04201, reviewer Edgar Karst, in German),
fetched 2026-08-16 via the zbMATH Open API, quoted verbatim including the
review's opening slip (it says "Riemanns Zeta-Funktion" while defining the
prime zeta function):

> Riemanns Zeta-Funktion sei P(s) = sum_{(p)} p^{-s}, s = sigma + i tau,
> über alle Primzahlen p. Die Schwierigkeiten der Berechnung werden
> außerordentlich groß in der Nähe der imaginären Achse. Das
> Haselgrove-Miller-Verfahren, das auf halbkonvergierenden, passend
> zugestutzten Reihen beruht, findet hier Anwendung. Sehr wenig ist über
> Lösungen von P(s) = 0 bekannt.
>
> Tafel I enthält vier davon; ziemlich weit entfernt von der imaginären
> Achse, außerdem je eine von P(s) = -1 und P(s) = 1.

(TeX markup dropped and math transcribed to ASCII; the German text and its
punctuation are kept.) Translation, this file's own: "Very little is known
about solutions of P(s) = 0. Table I contains four of them; rather far
away from the imaginary axis, in addition one each of P(s) = -1 and
P(s) = 1."

So Froberg's paper contains, besides the continuation treatment, four
numerically computed roots of P(s) = 0 in its Table I (float grade, 1968
methods), located "rather far from the imaginary axis"; the review does
not give their coordinates. Operator note: pulling the paper through a
library would recover the four roots; if any had Re s > x*, the conjecture
would contradict literature it postdates. Nothing in the review suggests
the roots sit near the right edge, and the review gives no real-part
bound either way.

MathWorld's sentence (Prime Zeta Function page, fetched 2026-08-16),
verbatim including its dropped word:

> According to Fröberg (1968), very little is known about the roots P(s).

### 4.5 Search log, first sweep

Queries run 2026-08-16 through this session's web search tool, with what
came back. This is the sweep that missed both sources in 4.1 and 4.2; it is
kept verbatim because the record of a failed search is the evidence for the
lesson in 4.6.

1. `Froberg 1968 "On the prime zeta function" BIT 8 zeros roots analytic
   continuation`: the MathWorld page, the Semantic Scholar record
   (doi:10.1007/BF01933420 confirmed; abstract withheld by the publisher),
   HandWiki's copy of the Wikipedia material. Continuation facts and the
   roots remark; nothing further on zeros.
2. `"zeros of the prime zeta function"` (exact phrase): no paper with that
   subject in the results. Hits concern zeros of zeta(s), or P on the
   critical line as a statistical object (G. Chavez and A. Allawala,
   "Prime zeta function statistics and Riemann zero-difference
   repulsion", arXiv:2102.02280, which studies P(1/2+it) distributionally
   and says nothing about zeros of P; its abstract page was checked
   directly).
3. `"prime zeta" function zeros "sigma > 1" OR "Re(s) > 1" zero-free
   region Dirichlet series over primes`: zero-free-region literature for
   zeta(s) only; nothing for P.
4. `Jasinski conjecture prime zeta function A107311 zeros 1.728647`:
   nothing engaging the conjectures; no citation of the entry's
   conjecture lines found anywhere.
5. zbMATH Open API, title search "prime zeta function" with author
   Froberg: the Zbl 0167.04201 record quoted above, whose linked OEIS
   cross-references (A008480, A143524, A341444) concern factorization
   counts, not zeros.

Adjacent but not on point, recorded so the neighborhood is visibly looked
at: a retracted note claiming results about P (M. Vassilev-Missana, Notes
on Number Theory and Discrete Mathematics 22 (2016), no. 4, retracted) and
a published refutation of it (arXiv:2103.09418) concern identities
relating P to zeta and the Riemann hypothesis, not zero locations of P.

### 4.6 Why the first sweep missed both sources

Two distinct failures, needing two distinct countermeasures. Neither is a
failure of effort, which is what makes them worth recording.

**Failure 1, the venue gap.** The hunt's exact-phrase query
`"zeros of the prime zeta function"` (query 2 above) is a *literal substring*
of the Belovas et al. title, "On the zero-free region and the distribution of
zeros of the prime zeta function". The query was re-run during the adjudication
and the failure **reproduces exactly**: ten results, MathWorld's prime zeta
page among them, and the Belovas et al. paper not among them. Contributing
causes, each of which alone defeats a standard sweep: the paper was never
preprinted on arXiv; it lives in a Sciendo/DOAJ journal that an
arXiv-plus-MathWorld-plus-zbMATH title sweep does not reach; and its PDF is
image-scanned, so a retrieval step that reads landing pages rather than
downloading and extracting files yields nothing even after finding it.

*Countermeasure*: an exact-title-substring query that returns nothing proves
nothing. Search the DOI registries and open-access aggregators (Crossref, DOAJ,
Sciendo) by title, not only the engines and arXiv, and treat an image-scanned
PDF as a document that must be downloaded and extracted.

**Failure 2, the classification gap.** Sepulcre and Vidal Theorem 4.3 is filed
under almost periodic functions, MSC 30B50 and 30D20, not number theory, and
the paper **never names a prime**. No query about prime zeta functions can
reach it. It was reachable only by searching for the *device* rather than the
application.

*Countermeasure*: when an argument's engine is a general device (here, rational
independence of frequencies plus a polygon construction), search for the device
under its own name in its own field. The hunt's own Lemma 2 and Lemma 4 were
the signposts, and a query for "real projections of zeros", "exponential
polynomials" or "almost periodic Dirichlet series" lands on the right MSC class
immediately.

The transferable corollary: `ontology/knownness.py` defaults to "the literature
was not consulted", and this episode is the argument for that default. Four
independent searches returned nothing on the core result while two published
papers owned it outright. **An unrun or unsuccessful search is not evidence of
absence.**

### 4.7 Finding, corrected

As of 2026-08-16, after the adjudication sweep:

- **The threshold sigma_c for P(s) is in the literature**: Belovas et al.
  (2025), Theorem 1, same constant, same proof (section 4.1).
- **The mechanism is in the literature and is more general**: Sepulcre and
  Vidal Theorem 4.3 (2022, preprint 2018), which subsumes the hunt's Theorems
  A(a) and B and contains the aggregated-tail device (section 4.2), standing in
  turn on Moreno (1973) for the polygon step (section 4.3).
- **Kill condition 2 has fired** (section 4.0). The hunt's core is reclassified
  as rediscovery and the OEIS correction cites Belovas et al. for the constant.
- Froberg 1968 remains the earliest source found touching zeros of P at all:
  four numerically observed roots in Table I and the remark that very little is
  known.
- Neither published source engages OEIS A107311, and neither treats prime
  subsets. That is where the hunt's remaining contribution lives, and it is
  itemized in `PRIOR-ART.md` section 9.

Even now this is a record of queries run on the dates above, not a completed
search of record: MathSciNet was not available, zbMATH full-text search was
not available beyond the single API record quoted, and the density statement
behind the hunt's Lemma 4 sits in classical almost-periodic territory (Jessen
and Tornehave) that has not been searched at all. Do not read the corrected
section as a completed audit; read it as a sweep that found what it found
after a first sweep found nothing.

## 5. What this file settles for the other work packages

- WP1 is discharged: the refutation target is the verbatim comment block
  in section 2, and every later document should quote it from here.
- WP5's calibration target is section 3: the same code path pointed at
  partial sums must reproduce beta_X rising toward x*, and at the limit
  equation zeta(sigma) = 2 the entry's digits.
- Kill condition 4 (the entry means something narrower) now has a fixed
  text to be re-read against.
- **Kill condition 2 has fired** (section 4.0, corrected 2026-08-16). Belovas
  et al. (2025) prove the sigma_c threshold for P and Sepulcre and Vidal (2022)
  own the general mechanism, so the hunt's core is rediscovery and
  `OEIS-CORRECTION.md` cites those sources for the constant rather than this
  work. WP1's transcription and WP5's calibration target are unaffected; what
  changes is the ownership of WP2, WP3 and WP4's mathematics, not its
  correctness.
