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
Lambda <= 0.22. The Davenport-Heilbronn function F is the canonical
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

    0.2304 < Lambda_DH <= 1.6025374835598228

and in the hunt's narrow frame the same statement reads
0.0576 < Lambda_DH <= 0.4006343708899557, with 0.0576 = 36/625 exactly.

The lower side is an argument-principle count: at t = 36/625 the deformation
still has a zero strictly off the real axis near the deepest measured
quadruple (height about 240.4), decided by ball-arithmetic winding counts
(python-flint Arb, 420 bits) with a second witness sharing no code layer
(mpmath at dps 130), made strict by Dobner's closed half-line. The upper side
feeds a decided zero-strip constant (sigma_0 = 1.39513615823511, both
backends) to de Bruijn 1950 Theorem 13, whose all-zeros form was transcribed
from the original text and corroborated against two typeset restatements.

Grade, per the certainty ladder: the composite is a decided computation glued
to cited theorems, and it takes the weakest step's grade. One analytic lemma
inside the lower bound (the derivative bound called M2) is prose with a
measured guard and a recorded blind spot; the artifacts disclose it at every
headline that depends on it, together with the lesion table showing where the
guard fails.

## 3. The separation, which is the quotable part

Polymath 15's bound and this hunt's floor sit in the same frame, and they
cross:

    0 <= Lambda_zeta <= 0.22 < 0.2304 = 144/625 < Lambda_DH.

So **Lambda_DH > Lambda_zeta, unconditionally**: the counterexample's failure
margin, measured in flow time, exceeds zeta's entire remaining uncertainty
window. The rational core is exact (144/625 against 11/50 cross-multiplies to
7200 > 6875) and the inequality is frame-invariant. Positivity alone could not
have given this: Lambda_DH > 0 is a two-line corollary of Dobner plus Spira
and is compatible with Lambda_DH <= 0.22. The quantitative floor is what
crosses the published bound.

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
  the real parts of the zeros of this function (1.120362), so the hunt's
  sigma_0 is a weaker bound on a known quantity and any originality claim for
  it is withdrawn. Their tau_+ equals the lab's kappa, and the gate's check
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
One preprint co-mentioning the flow and the function remains unread
(academia.edu 166936409, HTTP 403 to every fetch); the novelty language is
conditioned on the recorded searches by standing instruction. The full gate
record, including what a skeptical referee should attack first and in what
order, is `hunts/lambda_dh_bounds/GATE.md`; the verdict there is a
publication candidate pending external verification, which is not ours to
award.

## 6. Where to read

`hunts/lambda_dh_bounds/`: `MISSION.md` (preregistration), `GATE.md` (the
adjudication), `SEPARATION.md` (the corollary with per-link grades),
`FRAME.md` (the two normalizations), `RESULTS.md` and `results.json` (all
claims, keyed and graded), `NOVELTY.md` (the search record and the sanctioned
sentence), `BOMBIERI-GHOSH.md`, `KAPPA-CLOSED-FORM.md`, `POLYMATH-PIN.md`
(verbatim sources), `INDEPENDENCE.md` (measured route independence), and the
four adversary write-ups. Reproduction is one command per instrument, listed
in `GATE.md`.
