# 28: The rightmost zeros of the prime zeta function

*The reading-course record of hunt #35, `hunts/prime_zeta_rightmost/`: a
refutation of the two conjectures posted on OEIS A107311 in December 2024,
and the replacement theorem the refutation earned. The proofs live in
`hunts/prime_zeta_rightmost/THEOREM.md`, the decided enclosures in
`hunts/prime_zeta_rightmost/decided.json` and
`hunts/prime_zeta_rightmost/theorem_inputs.json`, the run record in
`hunts/prime_zeta_rightmost/RESULTS.md`, and the pinned source texts in
`hunts/prime_zeta_rightmost/SOURCE.md`. This page reads that record; it
upgrades nothing. Every number stated here is pinned by
`tests/test_prime_zeta_rightmost.py`, which recomputes the decided constants
through the hunt's own instrument at reduced precision and checks the
remaining figures against the recorded artifacts.*

Vocabulary, per the hunt's contract: *measured* is one float route;
*decided* is an interval or ball enclosure whose exact endpoints settle a
sign, stated with backend and precision; *heuristic* is an order-of-magnitude
model with measured inputs, always labeled. The reserved enclosure
vocabulary of `zeta/rigor.py` appears nowhere in the hunt and nowhere on
this page.

---

## 1. The two conjectures, verbatim

OEIS A107311 is "Decimal expansion of the solution to zeta(x) = 2", an
entry created by Ralf Stephan in 2005 for the constant called x* throughout
the hunt: x* = 1.728647238998183618135103010297... It earns its OEIS place
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

## 2. The mis-port

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
  equivalently P(sigma) = 2^(1-sigma). Decided on both backends:
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
  wall is actually approached by zeros (section 3 below). The conjecture
  moved a constant from a family whose wall is slack onto a family with a
  different wall that is sharp.

The hunt made the mis-port mechanical as a control: balancing P's leading
term 2^(-s) against the zeta tail sum_{n >= 3} n^(-s) lands at 2.4241...,
decidedly equal to neither x* nor sigma_c. The template and the series fed
to it both matter (`controls_results.json`, lesion 2).

## 3. The replacement theorem

Full statements and proofs are in `THEOREM.md`; the labels below are that
file's. Everything numeric they consume is decided on both backends
(section 4).

**The wall (Theorem A).** For a prime q write P_q(s) = sum_{p >= q} p^(-s),
and let sigma_c(q) be the unique root in (1, infinity) of the balance
q^(-sigma) = sum_{p > q} p^(-sigma). Then P_q has no zero with
Re s >= sigma_c(q). For Re s > sigma_c(q) the triangle inequality leaves
|P_q(s)| >= q^(-Re s) - sum_{p > q} p^(-Re s) > 0; a zero on the line
Re s = sigma_c(q) would force equality in the triangle inequality for the
whole series, hence a common phase for every p^(-s), which the
multiplicative independence of the primes (unique factorization) forbids.
The proof is exact mathematics with no numeric input; the numerics only
locate the constants. For q = 2 this is the prime zeta function and
sigma_c(2) = sigma_c above; for q = 3 the wall is
sigma_3 = 1.8252259560738457... (decided).

**Existence up to the wall (Theorem B, Corollaries B1 and B2).** For every
window (sigma_1 - eps, sigma_1 + eps) inside (1, sigma_c(q)), P_q has
infinitely many zeros with |Re s - sigma_1| < eps/2, with imaginary parts
unbounded above. The proof phases the whole series to vanish exactly at
sigma_1 (a closing-polygon lemma, with the tail aggregated as one polygon
side), steers a genuine vertical translate of P_q onto that phased model
over a small circle by Kronecker's approximation theorem in Weyl's
positive-density form (this is where the linear independence of the log p
enters), and transfers the model's zero to P_q by Rouche. Consequently

    sup { Re s : P_q(s) = 0, Re s > 1 } = sigma_c(q),

approached and not attained. Instance q = 2, window (1.73, 1.77): the
window sits inside (1, sigma_c) and above x* (decided window compares), so
P has infinitely many zeros with Re s in (1.73, 1.77), every one exceeding
x*. **Conjecture 1 is false**, and the correct threshold is sigma_c, a
supremum rather than a maximum.

**The subset {p >= 3} (Theorem C1).** The same pair of theorems for q = 3:
P_3(s) = sum_{p >= 3} p^(-s) has infinitely many zeros with Re s in
(1.78, 1.82), beyond x* and beyond sigma_c itself, since
sigma_3 - sigma_c > 0.0456813 (decided). Removing a prime moves the wall
right, so a subset out-walls the full series. **Conjecture 2 is false**
already for this one subset.

**Tail subsets have unbounded walls (Theorem C2, Corollary C3).** For the
k-th prime p_k >= 23, the wall of {p >= p_k} is at least
log2(3 p_k / (5 log p_k)), which tends to infinity with k; the count input
is Rosser and Schoenfeld's inequality pi(2x) - pi(x) > 3x/(5 log x) for
x >= 20.5, re-checked against the paper's text during the hunt. Decided
instance: the wall of {p >= 23} is at least log2(69/(5 log 23)) =
2.1379035036560028... > 17/8, already beyond both x* and sigma_c. Combined
with Theorem B, for every real M some tail subset has infinitely many
zeros with Re s > M: **no constant at all bounds the real parts of the
zeros over all subsets**, so Conjecture 2 fails for every possible
replacement constant. (The refuting subsets are infinite; nothing is
claimed about finite subsets, whose series are exponential polynomials
with walls of their own.)

## 4. The decided constants

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
  ring margin for Theorem B's q = 2 instance.
- **D2**: u(9/5) = sum_{p>=5} p^(-9/5) - 3^(-9/5) = 0.0043124917294... >
  1/256, the ring margin for the q = 3 instance.
- **D3**: log2(69/(5 log 23)) = 2.1379035036560028... > 17/8, the
  {p >= 23} wall instance of Theorem C2.
- **W1-W5** (window compares, exact Fractions against outward-rounded
  endpoints): hi(x*) < 1.73; lo(sigma_c) > 7/4; lo(sigma_c) > 1.77;
  hi(sigma_c) < 1.78; lo(sigma_3) > 1.82. These place the windows
  (1.73, 1.77) and (1.78, 1.82) where sections 2 and 3 need them.
- **subset gap**: sigma_3 - sigma_c > 0.0456813, exact rational compare.

## 5. Why no explicit zero is exhibited

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
fire at. None of this weakens the theorem: existence is proved, not
screened for.

## 6. The calibration control

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
and the mechanical mis-port of section 2 lands at 2.4241..., decidedly
neither constant. The precision response is monotone: the sigma_c code
path at 60, 120 and 200 bits achieves strictly shrinking widths 1.421e-15,
6.163e-34 and 1.020e-57. A rerun of `decide.py` in a subprocess reproduced
`decided.json` line for line with only timings differing. All of it is
recorded in `controls_results.json`.

## 7. Honest scope

- **Reading-independence of the refutation.** The refuting zeros have
  Re s > 1, inside the half-plane of absolute convergence, where the
  defining series, Glaisher's continuation and every branch of it agree; a
  zero there is a zero under every reading of "the prime zeta function",
  so the refutation holds for all readings at once (`SOURCE.md` section
  2). Nothing is claimed about 0 < Re s <= 1, where the continuation has
  logarithmic branch points and the line Re s = 0 is a natural boundary,
  and nothing about finite subsets.
- **Novelty caveat, as `RESULTS.md` section 7 phrases it.** The
  wall-plus-Bohr-steering mechanism is classical for general Dirichlet
  series, and a specialist may regard the sigma_c threshold as
  folklore-derivable; the searches logged in `SOURCE.md` section 4
  (2026-08-16: exact-phrase, zbMATH API, MathWorld, citation hunts) found
  no source stating any rightmost-zero threshold for P, and only Froberg
  1968 touching its zeros at all, but that is a record of queries run, not
  a completed search of record (no MathSciNet, no zbMATH full text). The
  deliverable therefore stands as: the OEIS correction, plus the first
  explicit treatment found for P specifically, with decided constants.
  Original is claimed; novel is claimed only as "no prior source found by
  the logged searches". Froberg 1968, the one prior source found on zeros
  of P, is quoted (via its zbMATH review, translated in `SOURCE.md`
  section 4) as saying: "Very little is known about solutions of
  P(s) = 0. Table I contains four of them; rather far away from the
  imaginary axis."
- **What is not claimed.** Nothing here bears on the Riemann Hypothesis:
  the zeros produced are zeros of P and of subset series in Re s > 1, not
  zeros of zeta, and x* keeps its correct role as the partial-sums
  threshold of Borwein, Fee, Ferguson and van der Waall. Nothing is
  kernel-checked: no Lean formalization of any step exists, and the
  certainty ladder's top rung is untouched (a natural later rung would be
  the polygon lemma plus the wall theorem, which are elementary). The
  replacement theorem is a composite and takes the grade of its weakest
  step: decided inequalities on both backends, glued by classical
  arguments (Kronecker, Rouche, Rosser-Schoenfeld) that are proved in
  `THEOREM.md` or cited with hypotheses checked. The heuristic height
  model of section 5 is a labeled aside that carries no claim.
- **The correction is drafted, not posted.**
  `hunts/prime_zeta_rightmost/OEIS-CORRECTION.md` holds draft texts for
  the entry comment and for a new sequence giving sigma_c's expansion;
  posting anything to OEIS is an operator action, explicitly outside the
  hunt's permissions.

## 8. Where to go next

- `hunts/prime_zeta_rightmost/MISSION.md`: the contract, the
  pre-registered predictions P1-P4 (all held), and the kill conditions
  (one fired during the run: a cross-backend disjointness caught an
  endpoint-conversion defect in the instrument, fixed and re-run;
  `RESULTS.md` section 2 tells that story).
- `hunts/prime_zeta_rightmost/THEOREM.md`: the statements and complete
  proofs, with the grade of every step in its section 6.
- `hunts/prime_zeta_rightmost/SOURCE.md`: the verbatim entry, the
  partial-sums provenance of x*, and the literature search log.
- `hunts/prime_zeta_rightmost/RESULTS.md`: the run record this page
  summarizes.
- `tests/test_prime_zeta_rightmost.py`: the pins for every number above.
- `docs/08-why-it-is-hard.md`: the standing rule that nothing in this
  repository is evidence about RH, which this result does not bend.
