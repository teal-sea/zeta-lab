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

### Froberg 1968, the one source found

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

### Search log

Queries run 2026-08-16 through this session's web search tool, with what
came back:

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

### Finding

As of 2026-08-16 the only literature found that touches zeros of P(s) is
Froberg 1968: four numerically observed roots in Table I and the remark
that very little is known. No source was found naming any rightmost-zero
threshold for P(s), so nothing found here trips kill condition 2 of
MISSION.md (a prior source proving a sigma_c threshold would reclassify
the hunt as rediscovery). This is a record of the queries above on the
dates above, not a completed search of record: zbMATH full-text search and
MathSciNet were not available beyond the single API record quoted.

## 5. What this file settles for the other work packages

- WP1 is discharged: the refutation target is the verbatim comment block
  in section 2, and every later document should quote it from here.
- WP5's calibration target is section 3: the same code path pointed at
  partial sums must reproduce beta_X rising toward x*, and at the limit
  equation zeta(sigma) = 2 the entry's digits.
- Kill condition 4 (the entry means something narrower) now has a fixed
  text to be re-read against; kill condition 2 has, so far, nothing to
  cite.
