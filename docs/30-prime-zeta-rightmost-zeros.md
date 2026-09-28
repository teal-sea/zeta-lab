# 30. The rightmost zeros of the prime zeta function

*A reading-course page about a threshold this laboratory did not discover.
The threshold that governs the rightmost zeros of the prime zeta function is
not this laboratory's result: it is Theorem 1 of Belovas, Cepaityte and
Sabaliauskas (2025), with the same constant and the same
triangle-inequality proof, and the general statement behind it is Theorem
4.3 of Sepulcre and Vidal (2022), whose finite ancestor is Moreno's
Geometric Principle of 1973; what this laboratory adds is the connection to
OEIS A107311, the unboundedness of the subset thresholds, the constant
sigma_3, and two-backend interval enclosures. Hunt #60
(`hunts/prime_zeta_rightmost/`) computed the mathematics below before it
found the papers, and its own second kill condition fired when it did. The
page is kept because the exposition is correct and useful, and because the
way the search failed is worth more than the rediscovery was.*

The record: the adjudication and the verbatim source texts are in
`hunts/prime_zeta_rightmost/PRIOR-ART.md`, the hunt's proofs in
`THEOREM.md`, the decided enclosures in `decided.json` and
`theorem_inputs.json`, the run record in `RESULTS.md`, the OEIS transcript
and search log in `SOURCE.md`. Every number stated here is pinned by
`tests/test_prime_zeta_rightmost.py`, which recomputes the decided constants
through the hunt's own instrument at reduced precision and checks the
remaining figures against the recorded artifacts.

Vocabulary, per the hunt's contract: *measured* is one float route;
*decided* is an interval or ball enclosure whose exact endpoints settle a
sign, stated with backend and precision; *heuristic* is an order-of-magnitude
model with measured inputs, always labeled. The reserved enclosure
vocabulary of `zeta/rigor.py` appears nowhere in the hunt and nowhere on
this page.

---

## 1. Who owns what

Read this before the mathematics, so that nothing below can be mistaken for
a priority claim.

**Published, and prior to anything here:**

| statement | source |
|---|---|
| the wall: P has no zero with Re s > sigma_0 = 1.77954465354699..., where sigma_0 is the root of U(sigma) = 2^(1-sigma) - P(sigma) | Belovas, Cepaityte, Sabaliauskas, *On the zero-free region and the distribution of zeros of the prime zeta function*, An. St. Univ. Ovidius Constanta Ser. Mat. 33(2) (2025), 27-44, DOI 10.2478/auom-2025-0017, Theorem 1 |
| the unique root of U in (1, infinity) | same paper, Lemma 1 |
| the general characterization: for an almost periodic Dirichlet series with Q-linearly independent frequencies, sigma_0 lies in the closure of the real projections of the zeros exactly when the domination condition fails at every index | Sepulcre and Vidal, *On the real projections of zeros of analytic almost periodic functions*, Carpathian J. Math. 38 (2022) no. 2, 489-501 (preprint arXiv:1805.02041, 2018), Theorem 4.3 = preprint Theorem 6 |
| the aggregated-tail polygon device used in that proof | Moreno, *The zeros of exponential polynomials (I)*, Compositio Math. 26 (1973) 69-78, Geometric Principle, pp. 71-72; Moreno applies it to sum_{p <= M} p^(-s) himself |
| the finite ancestors: supremum of real parts equals the balance root, and is not attained, for exponential polynomials | Sepulcre and Vidal, JMAA 437 (2016) 513-525, Proposition 5 and Corollary 6 |
| the balance equation and the triangle-inequality argument, informally | Math.StackExchange 3894479, comment by K. Conrad, 2020-11-05 |

So: the wall theorem (section 3), the existence of zeros filling every
window below it (section 4), the polygon lemma, the phase-steering lemma,
and the value of sigma_c are **pure rediscovery**. The hunt derived them
independently and that is a fact about provenance, not a claim on the
mathematics.

**What this laboratory adds, with its grade:**

- **the OEIS connection** (section 2 and section 4): no source in the
  literature engages A107311, and the published wall does not by itself
  refute the entry's Conjecture 1, since 1.7795 is *weaker* than the
  conjectured 1.72864 and Belovas et al.'s numerics stop at 1.6826, below
  x*. Grade: new as a connection, zero new mathematics.
- **the unbounded subset walls** (section 5, Theorem C2 and Corollary C3):
  tail subsets {p >= p_k} have walls at least log2(3 p_k / (5 log p_k)),
  so no constant at all bounds the real parts across all prime subsets.
  No prior art located by four independent searches. Grade: new, small,
  an elementary corollary of the published framework plus
  Rosser-Schoenfeld.
- **sigma_3 = 1.8252259560738457...** (section 5), and the fact that a
  subset out-walls the full series by more than 0.045. Grade: new instance
  of prior-art theory.
- **the two-backend interval enclosures** (section 6). Grade: rediscovery
  in a sharper form; Belovas et al. print 15 digits and remark that any
  precision is available.
- **one literature observation** (section 9): Belovas et al.'s Conjecture
  1, left open in their paper, is a corollary of Sepulcre and Vidal
  Theorem 4.3, which neither paper cites. Grade: new as a literature
  observation, and the most publishable item on this page.

Nothing else here is claimed. A per-statement ownership map, with the
verbatim source quotations it rests on, is `PRIOR-ART.md` section 8.

## 2. The two conjectures, verbatim

OEIS A107311 is "Decimal expansion of the solution to zeta(x) = 2", an
entry created by Ralf Stephan in 2005 for the constant called x* throughout
this page: x* = 1.728647238998183618135103010297... It earns its OEIS place
as Kalmar's composition constant; that role is not in dispute. A comment
block added in 2024 is. Word for word as served (entry revision 55, fetched
2026-08-15 and refetched 2026-08-16, byte-identical; the spellings
"partials sums", "Riemman" and "the anyone subset" are in the source, and
the full JSON body is pinned in `SOURCE.md` section 1):

> From _Artur Jasinski_, Dec 21 2024: (Start)
> Borwein et al. (2007) proved (Theorem 3.1) that the real parts of the zeros of the partials sums of the Riemman zeta functions are not greater than this constant.
> Conjecture 1: the real parts of the zeros of the prime zeta function are not greater than this constant.
> Conjecture 2: the real parts of the zeros of the anyone subset of the prime zeta function are not greater than this constant. (End)

"Not greater than" is <=, so a refutation needs zeros with real part
strictly above x*. Both conjectures are false. The second is false for
every possible replacement constant, not only for x*.

## 3. The mis-port: why x* is the wrong constant for this family

x* is a correct threshold for a different family. For the partial sums
zeta_X(s) = sum_{n <= X} n^(-s), the triangle-inequality wall is the root
beta_X of sum_{n=2}^{X} n^(-sigma) = 1: past it the leading term 1 outweighs
everything else, so zeros stop. Gonek and Ledoan state exactly this bound,
with the estimate credited to Borwein, Fee, Ferguson and van der Waall
(2007, Theorem 3.1, the paper the OEIS comment cites); the quotes are
pinned in `SOURCE.md` section 3. The walls beta_X increase with X toward
the root of zeta(sigma) = 2, which is x*. Two facts make the transplant to
P(s) = sum_p p^(-s) wrong:

- **The balance is different.** P's leading term is 2^(-s), not 1, so the
  wall for P is the root sigma_c of 2^(-sigma) = sum_{p >= 3} p^(-sigma),
  equivalently P(sigma) = 2^(1-sigma). This is exactly the root of Belovas
  et al.'s U(sigma) = 2^(1-sigma) - P(sigma), and their sigma_0 is this
  page's sigma_c. Decided on both backends here:
  sigma_c = 1.779544653546994116445898786965..., which exceeds x* by more
  than 1/20 (the difference is 0.0508974145..., decided). At x* the balance
  has not yet tipped: P(x*) - 2^(1-x*) = 0.0169073772138... > 1/60
  (decided), so the triangle-inequality argument that protects the partial
  sums at x* protects nothing for P there.
- **The family shape is different.** For partial sums the wall is never
  approached by zeros: by Montgomery's theorem, as quoted in `SOURCE.md`
  section 3, the supremum of real parts of zeros of zeta_N tends to 1 as
  N grows. The frequencies log n are rationally dependent (log 4 =
  2 log 2), which blocks the phase steering that would saturate the wall.
  For P the frequencies log p are linearly independent over Q, and the
  wall is actually approached by zeros (section 4 below). The conjecture
  moved a constant from a family whose wall is slack onto a family with a
  different wall that is sharp.

The hunt made the mis-port mechanical as a control: balancing P's leading
term 2^(-s) against the zeta tail sum_{n >= 3} n^(-s) lands at 2.4241...,
decidedly equal to neither x* nor sigma_c. The template and the series fed
to it both matter (`controls_results.json`, lesion 2).

## 4. The threshold, and the zeros below it: the published statement

The two halves below are Belovas et al. Theorem 1 and (in a stronger form)
Sepulcre and Vidal Theorem 4.3. The hunt's independent proofs, with its own
labels, are in `THEOREM.md`; the labels are retained here so the record
lines up, and each is marked with its owner. Everything numeric they
consume is decided on both backends (section 6).

**The wall (hunt Theorem A; Belovas et al. Theorem 1 for q = 2; the "only
if" half of Sepulcre-Vidal Theorem 4.3 in general).** For a prime q write
P_q(s) = sum_{p >= q} p^(-s), and let sigma_c(q) be the unique root in
(1, infinity) of the balance q^(-sigma) = sum_{p > q} p^(-sigma). Then P_q
has no zero with Re s >= sigma_c(q). For Re s > sigma_c(q) the triangle
inequality leaves |P_q(s)| >= q^(-Re s) - sum_{p > q} p^(-Re s) > 0; a zero
on the line Re s = sigma_c(q) would force equality in the triangle
inequality for the whole series, hence a common phase for every p^(-s),
which the multiplicative independence of the primes (unique factorization)
forbids. The proof is exact mathematics with no numeric input; the numerics
only locate the constants. For q = 2 this is the prime zeta function and
sigma_c(2) = sigma_c above; for q = 3 the wall is
sigma_3 = 1.8252259560738457... (decided).

A precision note, recorded in `PRIOR-ART.md` section 8: the boundary line
itself, Re s = sigma_c(q), is covered by neither published statement
verbatim. Belovas et al. Theorem 1 speaks only of sigma > sigma_0, and
Sepulcre-Vidal Theorem 4.3 places sigma_c *inside* the closure without
deciding whether a zero sits on that line; their JMAA (2016) Corollary 6 is
stated for finite exponential polynomials. The short argument closing that
case for the infinite series is written out in `PRIOR-ART.md` section 8
(taking any two of p = 3, 5, 7 forces t log(5/3) and t log(7/5) to be
simultaneous multiples of 2 pi, hence t = 0, where P(sigma_c) > 0).

**Zeros fill every window below the wall (hunt Theorem B, Corollaries B1
and B2; strictly implied by Sepulcre-Vidal Theorem 4.3, which is
stronger).** For every window (sigma_1 - eps, sigma_1 + eps) inside
(1, sigma_c(q)), P_q has infinitely many zeros with |Re s - sigma_1| <
eps/2, with imaginary parts unbounded above. The hunt's proof phases the
whole series to vanish exactly at sigma_1 (a closing-polygon lemma, with
the tail aggregated as one polygon side; this is Moreno's Geometric
Principle, and the aggregation is the device Sepulcre and Vidal use in
their proof), steers a genuine vertical translate of P_q onto that phased
model over a small circle by Kronecker's approximation theorem in Weyl's
positive-density form (this is where the linear independence of the log p
enters), and transfers the model's zero to P_q by Rouche. Consequently

    sup { Re s : P_q(s) = 0, Re s > 1 } = sigma_c(q),

approached and not attained. Sepulcre and Vidal give more: the *closure* of
the set of real projections of zeros is exactly (1, sigma_c], which implies
the windowed existence statement and is not implied by it.

Instance q = 2, window (1.73, 1.77): the window sits inside (1, sigma_c)
and above x* (decided window compares), so P has infinitely many zeros with
Re s in (1.73, 1.77), every one exceeding x*. **OEIS Conjecture 1 is
false**, and the correct threshold is sigma_c, a supremum rather than a
maximum. That refutation is the connection this laboratory contributes; the
mathematics under it belongs to the sources in section 1.

## 5. The subsets: what does not follow from the published work

**The subset {p >= 3} (hunt Theorem C1).** The same pair of theorems for
q = 3: P_3(s) = sum_{p >= 3} p^(-s) has infinitely many zeros with Re s in
(1.78, 1.82), beyond x* and beyond sigma_c itself, since
sigma_3 - sigma_c > 0.0456813 (decided). Removing a prime moves the wall
right, so a subset out-walls the full series. **Conjecture 2 is false**
already for this one subset. Grade: a new instance of prior-art theory, and
the constant sigma_3 is new.

**Tail subsets have unbounded walls (hunt Theorem C2, Corollary C3).** For
the k-th prime p_k >= 23, the wall of {p >= p_k} is at least
log2(3 p_k / (5 log p_k)), which tends to infinity with k; the count input
is Rosser and Schoenfeld's inequality pi(2x) - pi(x) > 3x/(5 log x) for
x >= 20.5, re-checked against the paper's text during the hunt. Decided
instance: the wall of {p >= 23} is at least log2(69/(5 log 23)) =
2.1379035036560028... > 17/8, already beyond both x* and sigma_c. Combined
with the existence half, for every real M some tail subset has infinitely
many zeros with Re s > M: **no constant at all bounds the real parts of the
zeros over all subsets**, so Conjecture 2 fails for every possible
replacement constant. (The refuting subsets are infinite; nothing is
claimed about finite subsets, whose series are exponential polynomials with
walls of their own, and whose case is Moreno's and Sepulcre-Vidal's.)

This is the one place on the page where the mathematics itself is not in
the located literature. It is small: given the published framework, the
bound is an elementary consequence of a prime-counting inequality. Four
independent searches found no source stating it. The bound is loose in
every case checked (the true wall of {p >= 23} is 4.4875..., against the
bound's 2.1379...), which is all it needs to be.

## 6. The enclosures recomputed here

Two backends with deliberately independent code paths, both decided on
every row: **flint** = python-flint (arb balls) at 350 bits, arb zeta
direct for x*, Moebius series K = 120 with a proved tail bound for P;
**iv** = mpmath.iv at dps 40, which cannot use a library zeta (iv.zeta
raises on call in mpmath 1.3.0) and so carries its own enclosure, a finite
Dirichlet sum plus an Euler-Maclaurin tail with a decided remainder,
Moebius K = 40. Bracket bookkeeping is exact Fractions on both legs. From
`decided.json`:

| constant | defining balance | flint enclosure (350 bits) | width | iv width (dps 40) |
|---|---|---|---|---|
| x* | zeta(x) = 2 | [1.7286472389981836181351030102976660, 1.7286472389981836181351030102977450] | 7.889e-32 | 8.882e-17 |
| sigma_c | P(s) = 2^(1-s) | [1.7795446535469941164458987869654405, 1.7795446535469941164458987869655195] | 7.889e-32 | 9.095e-14 |
| sigma_3 | 3^(-s) = sum_{p>=5} p^(-s) | [1.8252259560738457623878727108889264, 1.8252259560738457623878727108890054] | 7.889e-32 | 9.313e-11 |

The sigma_c row agrees with Belovas et al.'s printed
sigma_0 = 1.77954465354699... on every digit they print, which is the
honest way to describe this row: it is a cross-check against the source,
not an independent discovery, and the source itself notes that any
precision is available from the same equation.

Cross-checks, all decided: each flint interval lies inside its iv
interval; the OEIS entry's 102-digit value interval lies inside both x*
enclosures; each constant is the unique root of a strictly decreasing
function on its bracket (termwise-exact for zeta, decided derivative
guards for the other two). The decided sign comparisons the theorems
consume, each decided on both backends:

- **separation**: sigma_c - x* > 1/20, exact rational compare of
  enclosure endpoints; the difference is 0.0508974145...
- **margin**: P(x*) - 2^(1-x*) > 1/60, evaluated over the whole x*
  enclosure; the value is 0.0169073772138...
- **D1**: h(7/4) = P(7/4) - 2^(-3/4) = 0.0094656372937... > 1/128, the
  ring margin for the q = 2 existence instance.
- **D2**: u(9/5) = sum_{p>=5} p^(-9/5) - 3^(-9/5) = 0.0043124917294... >
  1/256, the ring margin for the q = 3 instance.
- **D3**: log2(69/(5 log 23)) = 2.1379035036560028... > 17/8, the
  {p >= 23} wall instance of Theorem C2.
- **W1-W5** (window compares, exact Fractions against outward-rounded
  endpoints): hi(x*) < 1.73; lo(sigma_c) > 7/4; lo(sigma_c) > 1.77;
  hi(sigma_c) < 1.78; lo(sigma_3) > 1.82. These place the windows
  (1.73, 1.77) and (1.78, 1.82) where sections 3 to 5 need them.
- **subset gap**: sigma_3 - sigma_c > 0.0456813, exact rational compare.

## 7. Why no explicit zero is exhibited

The existence half cannot be a numerical zero-find, and the reason is the
size of the margins. Below the wall the series can reach zero only when
the phases t log p align nearly perfectly: at sigma_1 = 7/4 the entire
alignment budget is h(7/4) = 0.0094656372937... (decided), the amount by
which the fully aligned odd-prime resultant (about 0.3068) exceeds the
p = 2 term it must land on (about 0.2973). So the odd-prime phases must
give up less than about one percent of their aligned mass simultaneously.
Kronecker's theorem guarantees such times exist, with positive but tiny
density, and Rouche converts each steered near-cancellation into an actual
zero of P; that is why the proof needs exactly this pair of tools, and why
it produces infinitely many zeros without coordinates for any of them. A
heuristic model of the phase-coherence probability (labeled as such in
`witness_results.json`; von Mises tilted importance sampling, checked
against plain Monte Carlo at loose tolerance) puts the expected height of
a first zero near Re s = 7/4 at about 1.6e16 on the line budget, about
1.7e10 on the window-wide budget. The hunt's budget-capped screen of the
line sigma = 7/4 up to t = 1e8 (measured, numpy float64) found a global
minimum of |P| of about 0.010021 at t of about 5.63e7, above the budget,
with no point below the 1e-4 candidate gate; the pre-registered prediction
P4 (no explicit witness below t = 1e8) held, and an argument-principle box
counter validated on null and planted controls never had a candidate to
fire at.

Belovas et al. report the same shape of fact from the other direction:
their Remark 1 gives sigma_M = 1.682628788045196... as the largest real
part observed for |t| < 200000, so their own numerics stop 0.097 short of
their theorem's wall. Two independent numerical efforts thus agree that the
wall is not reachable by screening, which is what the phase-coherence
budget predicts.

## 8. The calibration control

Before the verdict on P was read, the same solver (the same function
object `decide.py` uses for sigma_c, asserted identical at import) was
pointed at the family x* actually belongs to: the balance of the leading
term 1 against sum_{n>=2} n^(-sigma), whose root is the root of
zeta(sigma) = 2. It reproduced the Borwein-Fee-Ferguson-van der Waall
constant: the OEIS value interval lies inside both backend enclosures, and
the flint leg reproduces 31 of the entry's digits (the enclosure width,
7.889e-32, is what caps the count; the iv leg reproduces 13). Two lesions
guard against a solver that ignores its input: dropping the p = 3 term
from the sigma_c tail moves the root by a decided 0.3502... (to 1.4293...),
and the mechanical mis-port of section 3 lands at 2.4241..., decidedly
neither constant. The precision response is monotone: the sigma_c code
path at 60, 120 and 200 bits achieves strictly shrinking widths 1.421e-15,
6.163e-34 and 1.020e-57. A rerun of `decide.py` in a subprocess reproduced
`decided.json` line for line with only timings differing. All of it is
recorded in `controls_results.json`.

The control did what a control is for, and it is worth noting what it could
not do: reproducing a literature constant on a neighbouring family tells
you the instrument works. It tells you nothing about whether the constant
you are about to compute is already in print. No numerical control can
answer that question; only a search can, and section 10 is about how that
search failed.

## 9. The observation worth keeping: a published conjecture that is already a corollary

Belovas et al. close their paper with Conjecture 1, left open there: with
sigma_T the supremum of real parts of zeros of P with |t| < T, they
conjecture that lim_{T -> infinity} sigma_T = sigma_0.

That is a corollary of Sepulcre and Vidal Theorem 4.3, published three
years earlier. Specializing their theorem to P on a fixed strip
{1 + delta < Re s < infinity} with 0 < delta < sigma_c - 1, condition
(4.8) becomes 2 p_j^(-sigma_0) <= P(sigma_0) for every j; the map
p -> 2 p^(-sigma_0) is strictly decreasing, so the index j = 1 (that is,
p = 2) binds and the whole family collapses to
U(sigma_0) = 2^(1-sigma_0) - P(sigma_0) <= 0, which is exactly Belovas et
al.'s U. The theorem's "only if" half then re-proves their Theorem 1, and
its "if" half gives closure{Re s : P(s) = 0} intersect (1, infinity) =
(1, sigma_c], which forces the monotone bounded sequence sigma_T up to
sigma_c. Their theorem and their open conjecture are the two directions of
one characterization that predates both.

Neither paper cites the other. The verification of this bridge, hypothesis
by hypothesis, including the one correction it needed (the fixed-strip
hypothesis forbids alpha = 1, but beta = infinity is allowed by their own
convention, so a single fixed strip suffices and no shrinking-delta union
is required), is `PRIOR-ART.md` sections 6 and 7. Grade: a literature
observation, no new mathematics, and the only item on this page a
specialist might want to hear about.

## 10. How the search missed it

This is the transferable part, and it reproduces on demand.

**Failure 1, the specific paper: a venue gap.** The hunt ran the
exact-phrase query "zeros of the prime zeta function". That string is a
literal substring of the Belovas et al. title, *On the zero-free region and
the distribution of zeros of the prime zeta function*. The query was re-run
during the adjudication and the failure reproduces exactly: ten results,
MathWorld and a mention of Froberg (1968) among them, and the paper not
among them. Contributing causes, each of which alone defeats a standard
sweep: the paper was never preprinted on arXiv; it lives in a Sciendo/DOAJ
journal that an arXiv-plus-MathWorld-plus-zbMATH-title sweep does not
reach; and its PDF is image-scanned, so fetching the page yields nothing
and the 2.2 MB file has to be downloaded and run through a text extractor
before a single sentence of it is readable.

**Failure 2, the general theorem: a classification gap.** Sepulcre and
Vidal Theorem 4.3 is filed under almost periodic functions, MSC 30B50 and
30D20, not number theory, and the paper never names a prime. No query about
prime zeta functions can reach it. It was reachable only by searching for
the *device*: real projections of zeros, exponential polynomials, Dirichlet
series with rationally independent frequencies.

**The two countermeasures, because one does not cover the other.**

1. *Against the venue gap*: an exact-title-substring query that returns
   nothing has proved nothing. Search the DOI registries and open-access
   aggregators (Crossref, DOAJ, Sciendo) by title, not only the engines and
   arXiv, and treat an image-scanned PDF as a document to download and
   extract rather than a page to fetch.
2. *Against the classification gap*: when the engine of an argument is a
   general device, search for the device under its own name in its own
   field, not for the application. The hunt's own lemmas were the
   signposts: a polygon construction and a Kronecker density argument point
   straight at almost periodic function theory, which is where the answer
   was.

The wider corollary is the reason `ontology/knownness.py` defaults to "the
literature was not consulted". Four independent searches returned nothing
while two published papers owned the result outright. **An unrun search and
an unsuccessful search are both compatible with a full shelf**, and a
search can be run competently and still fail for reasons that have nothing
to do with effort. What a hunt may report is what it searched and what came
back, never absence.

## 11. Honest scope

- **Priority.** Section 1 is the operative statement. The wall, its
  constant, the existence of zeros up to it, and both lemmas are prior
  art. What is claimed here is provenance (this laboratory derived them
  independently, which the git history shows) and the four small additions
  listed in section 1, of which exactly one, the unbounded subset walls,
  is mathematics not found in the located literature.
- **Reading-independence of the refutation.** The refuting zeros have
  Re s > 1, inside the half-plane of absolute convergence, where the
  defining series, Glaisher's continuation and every branch of it agree; a
  zero there is a zero under every reading of "the prime zeta function",
  so the refutation holds for all readings at once (`SOURCE.md` section
  2). Nothing is claimed about 0 < Re s <= 1, where the continuation has
  logarithmic branch points and the line Re s = 0 is a natural boundary,
  and nothing about finite subsets.
- **One residue, unverified.** The hunt's phase-steering lemma yields the
  zeros with positive lower density in t. Density statements of that kind
  are classical for almost periodic functions (Jessen and Tornehave
  territory), and that literature was not searched. The density is
  therefore carried as an unverified lead, not as a claim.
- **What is not claimed.** Nothing here bears on the Riemann Hypothesis:
  the zeros discussed are zeros of P and of subset series in Re s > 1, not
  zeros of zeta, and x* keeps its correct role as the partial-sums
  threshold of Borwein, Fee, Ferguson and van der Waall. Nothing is
  kernel-checked: no Lean formalization of any step exists, and the
  certainty ladder's top rung is untouched. The composite takes the grade
  of its weakest step: decided inequalities on both backends, glued by
  classical arguments (Kronecker, Rouche, Rosser-Schoenfeld) that are
  proved in `THEOREM.md` or cited with hypotheses checked. The heuristic
  height model of section 7 is a labeled aside that carries no claim.
- **The OEIS correction is drafted, not posted.**
  `hunts/prime_zeta_rightmost/OEIS-CORRECTION.md` holds draft texts for
  the entry comment and for a new sequence giving sigma_c's expansion.
  Both cite Belovas et al. for the threshold, which is what the hunt's own
  kill condition required; that rewrite is done. Posting anything to OEIS
  remains an operator action, explicitly outside the hunt's permissions.

## 12. Where to go next

- `hunts/prime_zeta_rightmost/PRIOR-ART.md`: the adjudication, the
  verbatim source texts, the worked specialization, the bridge
  verification, the ownership map and the search-failure record.
- `hunts/prime_zeta_rightmost/MISSION.md`: the contract, the
  pre-registered predictions P1-P4 (all held), and the kill conditions.
  Two fired: a cross-backend disjointness caught an endpoint-conversion
  defect in the instrument, fixed and re-run (`RESULTS.md` section 2), and
  the literature condition fired when the prior art was found.
- `hunts/prime_zeta_rightmost/THEOREM.md`: the hunt's own statements and
  complete proofs, with the grade of every step in its section 6. Read as
  an independent derivation, not as a priority document.
- `hunts/prime_zeta_rightmost/SOURCE.md`: the verbatim OEIS entry, the
  partial-sums provenance of x*, and the original (failed) search log.
- `hunts/prime_zeta_rightmost/RESULTS.md`: the run record.
- `tests/test_prime_zeta_rightmost.py`: the pins for every number above.
- `docs/08-why-it-is-hard.md`: the standing rule that nothing in this
  repository is evidence about RH, which this result does not bend.
