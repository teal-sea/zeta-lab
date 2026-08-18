# The de Bruijn-Newman constant of the Davenport-Heilbronn function

Hunt #36 (`hunts/lambda_dh_bounds/`) produced the first quantitative bounds,
from either side, on the de Bruijn-Newman constant of the Davenport-Heilbronn
function, and one corollary that is sharper than the bracket itself: the
constant strictly exceeds zeta's, unconditionally. This page is the reading
course for that record. The evidence lives in the hunt directory; every number
here is pinned by `tests/test_lambda_dh_separation.py` or by the hunt's own
result files.

## 1. The object, and the frame trap

For zeta, the de Bruijn-Newman constant Lambda is defined through the backward
heat deformation of the Riemann Xi function, and Rodgers-Tao proved Lambda >= 0
("if RH is true, it is only barely so"), while Polymath 15 proved
Lambda <= 0.22, since sharpened to Lambda <= 0.2 by Platt and Trudgian (2021),
which is the current record `zeta.heatflow.lambda_facts()` carries. The hunt's
chain below is stated against Polymath 15's 0.22 because that is the bound it
pinned at source (`hunts/lambda_dh_bounds/POLYMATH-PIN.md`); the sharper 0.2
only widens the gap the chain needs. The Davenport-Heilbronn function F is the
canonical
counterexample: a Dirichlet series with zeta's functional equation shape and
real coefficients whose own Riemann hypothesis is false (Davenport-Heilbronn
1936; computed off-line zeros: Spira 1994, Balanzario and Sanchez-Ortiz 2007).
Its deformation

    Phi_DH(u) = 4 e^{3u/2} sum_{n>=1} n a_n exp(-pi n^2 e^{2u}/5),
    H_t(z)    = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du,

with a_n the period-5 pattern (1, kappa, -kappa, -1, 0), defines
Lambda_DH := inf{t : H_t has only real zeros}, well defined and finite by
Dobner's theorem for the extended Selberg class.

The trap, which cost this hunt a correction cycle and is now its most
transferable lesson: **the literature uses two normalizations, and the same
constant is four times larger in one than in the other.** The hunt's frame
(s = 1/2 + iz, published precedent Stopple arXiv:1301.3158) is the narrow one;
de Bruijn as usually quoted, Newman, Rodgers-Tao, Polymath 15 and Dobner all
sit at s = (1+iz)/2, the wide one. Two refereed papers quote de Bruijn's 1/2
across that frame change unconverted (neither statement is false, since the
narrow implies the wide, but the reader is not told). The conversion is derived
and numerically checked row by row in `hunts/lambda_dh_bounds/FRAME.md`.

## 2. The bracket

In the wide frame of Rodgers-Tao and Polymath 15:

    0.2304 < Lambda_DH <= 0.7696992583210755065522

and in the hunt's narrow frame the same statement reads
0.0576 < Lambda_DH <= 0.19242481458026887663805, with 0.0576 = 36/625 exactly.
The bracket ratio, which is frame-free and is the honest measure of how loose
the two sides are, is 3.341.

The lower side is an argument-principle count: at t = 36/625 the deformation
still has a zero strictly off the real axis near the deepest measured
quadruple (height about 240.4), decided by ball-arithmetic winding counts
(python-flint Arb, 420 bits) with a second witness sharing no code layer
(mpmath at dps 130), made strict by Dobner's closed half-line.

The upper side feeds a decided zero-strip constant to de Bruijn 1950 Theorem
13, whose all-zeros form was transcribed from the original text and
corroborated against two typeset restatements. That constant is where the
hunt improved on itself after the gate closed, and the two derivations are
worth seeing together because the second explains why the first was loose.
The first bounded the zeros by coefficient domination, sum |a_n| n^{-sigma} <
1, giving sigma_0 = 1.39513615823511 on both backends. That step replaces
every phase n^{-it} by an independent worst case, and the phases are not
independent: they are determined multiplicatively by their values at the
primes. Used quantitatively, that gives a strictly better criterion. Writing
f as a combination of the two Dirichlet L-functions of the odd character mod
5, a zero with Re s > 1 forces a specific total argument on their ratio, while
each prime p = 2, 3 mod 5 can supply at most 2 arctan(p^{-sigma}) radians of
it (a Moebius image of a disc, whose argument-maximising point turns out to
have modulus exactly 1, so nothing further is available from trading modulus
against phase). The abscissa where the primes run out is decided on both
backends at the exact rational sigma_0' = 1.12036249819, a factor
2.082030697360155 better in Delta^2/2, with the sum's tail closed by the Euler
products themselves so that no prime-counting estimate enters anywhere. Both
derivations are kept: `STRIP.md` for the first and `STRIP2.md` for the second.

Two honest notes on that improvement. The equation the second route solves is
Bombieri and Ghosh's Theorem 7 at their parameter values, term for term; only
its necessary half is used, and that half is derived in-tree, so the number is
theirs and the grade is the hunt's. And the obvious alternative sharpening
was tried and recorded as failing: regrouping the series into period-5 blocks
and applying the mean value theorem is correct but carries a factor |s|, so it
gives a height-restricted strip that climbs back to sigma_0 as the height
grows, and de Bruijn's theorem consumes a half-plane statement.

Grade, per the certainty ladder: the composite is a decided computation glued
to cited theorems, and it takes the weakest step's grade. The analytic lemma
inside the lower bound (the derivative bound called M2) was prose with a
measured guard and a recorded blind spot through 2026-08-17; it is now proved
in `M2-LEMMA.md`, with every constant a reported ball and every hypothesis a
decided predicate, exercised by four routes and two falsification attacks. Its
single non-elementary input is the evenness of Phi_DH, which is the functional
equation transported and was already an acknowledged citation. What survives
of the blind spot is narrower and is still disclosed: the detector cannot see
a *corrupted* M2 by itself, its own health metric moves the wrong way across
the lesion, and the lesion table is published for that reason.

## 3. The separation, which is the quotable part

Polymath 15's bound and this hunt's floor sit in the same frame, and they
cross:

    0 <= Lambda_zeta <= 0.22 < 0.2304 = 144/625 < Lambda_DH.

(Polymath 15's 0.22 is the pinned link; Platt-Trudgian's sharper 0.2 makes the
same chain hold with more room, 0.2304 > 0.2, and is not needed for it.)

So **Lambda_DH > Lambda_zeta, unconditionally**: the counterexample's failure
margin, measured in flow time, exceeds zeta's entire remaining uncertainty
window. The rational core is exact (144/625 against 11/50 cross-multiplies to
7200 > 6875) and the inequality is frame-invariant. Positivity alone could not
have given this: Lambda_DH > 0 is a two-line corollary of Dobner plus Spira
and is compatible with the whole of zeta's window, 0.22 or 0.2 alike. The
quantitative floor is what crosses the published bound. The separation rests on the floor and on the
cited zeta bound alone, so the 2026-08-18 sharpening of the upper side left it
untouched in every digit.

Scope of the novelty claim, as adversarially narrowed in
`hunts/lambda_dh_bounds/SEPARATION.md`: in the function-field analogue of the
flow, exactly determined and trivially ordered Newman constants have been in
print since 2013-2014 (Andrade-Chang-Miller; Chang-Mehrle-Miller-Reiter-
Stahl-Yott), all negative or zero because RH is a theorem there. So far as the
recorded searches reach, this is the first strict inequality between such
constants in which both are nonnegative, and the first proof that any of them
strictly exceeds zeta's.

## 4. What prior art owns

- Stopple (arXiv:1301.3158): the hunt's normalization, verbatim, and a prior
  quantitative non-zeta bound (negative side, GRH-conditional upper).
- Dobner (arXiv:2005.05142): existence, finiteness, nonnegativity, and the
  closed half-line, for the whole extended Selberg class, with no numbers.
- de Bruijn 1950 Theorem 13 (restated by Newman-Wu 2020 Theorem 7): the
  strip-to-time engine of the upper bound.
- Bombieri and Ghosh (Russian Math. Surveys 66:2, 2011), read in full during
  the gate: no de Bruijn-Newman or heat-flow content, so the bracket is not
  anticipated; but their Theorem 7 determines the exact least upper bound of
  the real parts of the zeros of this function (1.120362), so any originality
  claim for the hunt's strip abscissa is withdrawn. The hunt's second route
  now reaches that same abscissa and decides it, which changes the grade and
  not the ownership: their equation is reproduced term for term, only its
  necessary half is used, and their converse (which makes the abscissa an
  exact supremum rather than an upper bound) is neither used nor claimed. Two
  of their published numbers serve as controls on the new instrument: the
  finite claim that the smallest set of primes p = 2, 3 mod 5 with
  sum arctan(1/p) > pi/2 ends at 6323 with 420 elements, and the sibling
  abscissa 2.3822861089 to all ten digits they print, neither of which the
  instrument was built around. Their tau_+ equals the lab's kappa, and the
  gate's check
  of their golden closed form (kappa = sqrt(1 + phi^2) - phi, phi the golden
  ratio, from the quadratic kappa^2 + 2 phi kappa - 1 = 0) is decided on both
  backends in `hunts/lambda_dh_bounds/KAPPA-CLOSED-FORM.md`, tying the
  counterexample's mixing constant to the conductor-5 golden-field story of
  `hunts/golden_control/`.
- Newman-Wu (Bull. AMS 2020): a strictly positive constant of this type,
  computed exactly, for a three-atom measure; orderings against a measure's
  constant are not frame-invariant and are not claimed.

## 5. Honest scope

Nothing here is evidence about RH. The separation distinguishes the
counterexample from zeta only through its already-known off-line zeros, which
is gate-3 framing, not a mechanism. The zeta side of the chain rests on
Polymath 15's refereed computer-assisted bound, not re-verified in this tree.
The preprint that once stood as the unread risk (academia.edu 166936409) has
since been traced to an open-access deposit and read in full: it contains no
de Bruijn-Newman constant for this function and no bound on one. What is left
unread is smaller and named in the gate: the full text of Bombieri and Mueller
2008, behind a publisher wall, and one Dobner-citing preprint behind
Cloudflare. The novelty language is conditioned on the recorded searches by
standing instruction.

What a skeptical referee should attack first has changed as the record
hardened, and the gate re-ranks it honestly rather than declaring the work
finished. It is no longer M2 and no longer the looseness of the upper side,
because both were spent. It is the citations, which are now unambiguously the
weakest steps: de Bruijn's Theorem 13 in its all-zeros form, transcribed from
an image-only scan; Dobner's Theorem 1; the evenness of Phi_DH; and, for the
separation, Polymath 15's Theorem 1.1. After them comes the plainest caveat
this page can offer: the hunt's two pieces of new mathematics, the phase
obstruction and Lemma M2, are prose plus decided arithmetic at the *hardened*
rung, written by agent sessions, attacked by scripts from the same sessions,
and read by no human. The full record is `hunts/lambda_dh_bounds/GATE.md`; the
verdict there is a publication candidate pending external verification, which
is not ours to award.

## 6. Where to read

`hunts/lambda_dh_bounds/`: `MISSION.md` (preregistration), `GATE.md` (the
adjudication), `SEPARATION.md` (the corollary with per-link grades),
`FRAME.md` (the two normalizations), `RESULTS.md` and `results.json` (all
claims, keyed and graded), `STRIP.md` and `STRIP2.md` (the two strip
derivations, weaker and sharper), `M2-LEMMA.md` (the derivative bound, proved),
`THEOREM13.md` (the engine, transcribed), `NOVELTY.md` (the search record and
the sanctioned sentence), `BOMBIERI-GHOSH.md`, `KAPPA-CLOSED-FORM.md`,
`POLYMATH-PIN.md` (verbatim sources), `INDEPENDENCE.md` (measured route
independence), and the four adversary write-ups. Reproduction is one command
per instrument, listed in `GATE.md`.
