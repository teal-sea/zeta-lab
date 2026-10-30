# RESULTS: hunt #148 `ff_probe`, the 7/8 probe's local identity over F_q[T]

**Status: closed 2026-10-26. Disposition: candidate refuted at the stated parameters (the
biquadratic probe over F_13[T] has no scalar local identity); the transfer of that verdict to
S4 over Q(i) is an inference, so S4 itself stays an unresolved attempt.** Files produced on
branch `hunt/ff-probe` (draft PR #355), landed on main 2026-10-30; nothing here is reviewed by a person. Grades as
in `MISSION.md`. Nothing here bears on RH over Q (`docs/08`).

## The question, and the answer

> Does a biquadratic-theta probe with quartic averaging over F_q[T] have a scalar local
> Euler identity like Lemma 7.1 of OpenAI's 7/8 paper, and what abscissa would the 7/8
> template price for it?

**No, and the template prices nothing for it** (`S4.md`). Over F_13[T] the theta
coefficients at squarefree indices of degree 3 are not multiplicative up to phases: on the
286 squarefree products of three linear primes, abs(H)^2 is 0 at 234 and 52 at the other 52,
while every coefficient at fewer primes has a modulus fixed by the degree and component.
In the probe's principal row, abs(K(A)) is abs(theta(A)) up to a factor depending on the
degree, so a scalar Euler identity fails first at the coefficient of X^3, at
A = (T-1)(T-2)(T-lambda), which vanishes for eight of the ten lambda. Hunt #136's order-k
template prices k = 4 at 7/8, 13/16 and 4/5 only under its inputs L1 to L3. L1 (closed-form
squarefree coefficients with a pairing) fails here, so none of the three prices applies.
Grade: derived (exact cyclotomic arithmetic at q = 13, one embedding eps, components read by
degree), hardened where the PARI second implementation reproduces it (`VERIFICATION.md`,
item `s4`).

## What else the hunt established

| finding | where | grade |
|---|---|---|
| The cited function-field theta formulas hold at q = 7, n = 3 (and n = 6, and q = 13, n = 4 where stated), with errata: the 2014 Hecke relation at infinity fails as printed, the 2007 Theorem 2.1 holds only in the 2007 note's own additive character, and one degree-4 relation of 2007 page 252 has q^2 for q | `SOURCES.md` | derived, hardened by PARI |
| The control: the F_7[T] transplant of Lemma 7.1 (cubic theta, sextic averaging) holds exactly at the checked primes, rows and degrees, and the probe's original, Poisson and Euler representations agree at every checked triple of total degree at most 6 (step2 and step2b) | `LOCAL_IDENTITY.md` sections 2 and 3, `RUNS.md` | derived, hardened by PARI |
| The correction product converges absolutely from Re x = 2/3, not the 7/8 the paper uses | `LOCAL_IDENTITY.md` section 4 | derived |
| The template overcharges the Poisson coefficient by a square root (abs(F)^2 = 7 q_A exactly) and prices the cubic case at 7/8 where the truth is 1/2 | `LOCAL_IDENTITY.md` section 4 | derived; the 1/2 is Weil's theorem |
| A Davenport-Heilbronn rival over F_7[T]: 66 of 210 characters give zeros off the circle (Arb enclosures), and the local identity refuses the rival at X^2 while it holds for the single character to X^3 W | `RIVAL.md` | hardened |

The rival gate is passed in the mission's sense: the rival's zeros are not all on
abs(u) = 7^(-1/2), and its local identity fails where the single L-function's holds.

## Kill conditions

None was met. Brute force agrees with the corrected formulas; the cubic probe's
representations agree at every checked degree; every planted fault turns at least one check
red (`VERIFICATION.md` section 3); the second implementation reproduced every exact number it
recomputes, 15 items run on 2026-10-26 (`VERIFICATION.md` section 2); the rival fails as
stated above.

## What transfers to Q(i) (inferred)

The forced zeros of `S4.md` section 2 come from the infinite place of F_q(T) and do not
transfer. The degree-3 failure of section 3 is a statement about finite places and matches
the number-field picture, where Hecke theory stops determining squarefree coefficients of
degree-n theta functions for n >= 4. This is evidence, not proof, that S4's input L1 fails
over Q(i). S4 over Q(i) is therefore an **attempt unresolved** in ALIGNMENT.md section 5's
terms, with this hunt's verdict as the function-field datum.

## Limitations

One q per case (7 and 13), one embedding eps, one target eta. The quartic probe itself is
not built: the obstruction is located in its theta input. The reflected (low-side)
representation of the cubic probe was not built (`LOCAL_IDENTITY.md` section 6). The
general form of the function-field Lemma 7.1 is derived by the paper's argument and checked
at finite ranges, not proved here.

## The doors

The hunt priced a ceiling in one case: the 7/8 template applied to the cubic control over
F_7[T]. Candidate: the template's 7/8 at k = 6 (11/12 balanced, 13/15 at perfect row
counts), against a truth of 1/2. Parameter range: q = 7, the probe triples and local ranges
of `LOCAL_IDENTITY.md` section 2. Information class: the data the paper's high side reads.
Proof status: exact computation plus the paper's algebra, unreviewed. For the biquadratic
case there is no optimum to analyse, because the template's input L1 fails.

- **Active constraints at the optimum.** Ranked by hunt #136's shadow prices: the pole 1/k
  (price -3/4 per unit of 1/k at the paper's geometry), then the low estimate's exponent
  1/4. The local identity is not a binding constraint: it is exact here, and its region
  (from Re x = 2/3) is slack against 7/8. The correction is already within 0.199 of 1 on
  Re x = 7/8 with S = {T}.
- **Frozen-constant inventory.** The twist order k = 6, fixed by the cubic theta's Gauss
  pairing. The door that would move it, k = 4 through the biquadratic theta, is the one this
  hunt closed in F_13[T]. The auxiliary character xi = chi_T^xi_j, which selects the degree
  classes the probe sees and moves the balanced point at no cost to the identity: a genuine
  trade. The target's conductor T^2, a free choice. The excluded set S = {T}: enlarging it
  trades a smaller correction for nothing at this target. The base field size q, fixed at 7
  and 13: a different q changes eps(chi(-1)) and so the signs, but not the degree-3
  mechanism of `S4.md` section 3 (inferred, not run).
- **Information class.** Every door in the cubic case stays inside the data the probe already
  reads. Lowering k means reading a different theta. That is reading more, and the only such
  door tested (n = 4) fails at its input. A probe whose principal row isolates 1/L without
  being an Euler product would be a different mechanism; none is proposed here.

The latest door gets no automatic priority. Allocation is the owner's decision.
