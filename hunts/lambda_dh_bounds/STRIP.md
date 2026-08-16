# The zero strip of the completed Davenport-Heilbronn function

Section draft for WP2 (2026-08-16). Instrument: `strip.py`; decided values
in `strip_results.json`. Vocabulary per `MISSION.md`: *decided* means an
interval or ball whose exact endpoints settle a sign, stated with backend
and precision; *measured* means one float route.

## 1. Statement

Let f(s) = sum_{n>=1} a_n n^{-s} with the period-5 Davenport-Heilbronn
coefficients a_n given by the pattern (1, kappa, -kappa, -1, 0) on
n = 1, 2, 3, 4, 0 (mod 5), where kappa is the functional-equation constant,
decided by the Arb linear solve of `instrument.kappa_ball` (backend
python-flint, 500 bits, ball width 3.1e-148) to lie in

    kappa in [0.284079043840412296028291832393126169091088088,
              0.284079043840412296028291832393126169091088089],

inside the pinned 40-digit reference KAPPA_REF +/- 1e-39 of
`zeta/epstein.py` (exact rational comparison; the ball also decides
0 < kappa < 1, which several bounds below use). Let

    gamma(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2),      F(s) = gamma(s) f(s),

the completed function, which is entire and satisfies F(s) = F(1-s)
(structurally: F = c Lambda(s, chi) + conj(c) Lambda(s, chibar) for the odd
primitive character chi mod 5, each completed L entire; in-tree: the defect
`zeta.epstein.dh_functional_equation_defect` is measured ~1e-50 at dps 50
and test-pinned). Define

    g(sigma) = sum_{n>=2} |a_n| n^{-sigma} - 1        (sigma > 1).

**Claim (decided constant, exact argument).** g has a unique root
sigma_0 > 1, and every zero of F lies in the open strip

    1 - sigma_0 < Re s < sigma_0.

Decided enclosures for sigma_0 (section 4):

    backend python-flint (Arb), 192 bits, bisection width < 1e-25:
        sigma_0 in [1.3951361582351097210613588712,
                    1.3951361582351097210613589375]
    backend mpmath.iv, dps 40, bisection width < 1e-15:
        sigma_0 in [1.395136158235109178, 1.395136158235109747]

The intervals overlap, and both lie inside the scouted value
1.39513615823511 +/- 5e-15 (half an ulp of the scout's last digit; the
scout is a 14-decimal rounding, so containment runs in that direction).

Consequently every zero of Xi_DH (equivalently H_0 in the flow_repair
normalisation, where Xi_DH(z) = F(1/2 + iz); `validate.py` check 1 pins the
identification at four points) satisfies

    |Im z| < Delta = sigma_0 - 1/2,

with Delta in [0.8951361582351097210613588712, 0.8951361582351097210613589375]
(flint endpoints, outward). This is the strip that de Bruijn's Theorem 13
converts into the upper bound Lambda_DH <= Delta^2/2 in WP2.

## 2. The identity behind g, verified before use

Splitting the absolutely convergent sum (Re s > 1) over residue classes
mod 5, with |a_n| equal to 1 on n = 1, 4 (mod 5), kappa on n = 2, 3
(mod 5), and 0 on n = 0 (mod 5), and using
5^{-s} zeta(s, c/5) = sum_{j>=0} (5j + c)^{-s}:

    sum_{n>=1} |a_n| n^{-s} = 5^{-s} [zeta(s, 1/5) + zeta(s, 4/5)]
                            + kappa 5^{-s} [zeta(s, 2/5) + zeta(s, 3/5)].

The n = 1 term (j = 0 of the c = 1 class) contributes 1, so
g(sigma) = (right side) - 2. The identity was not trusted on derivation
alone: `check_identity` compares the Hurwitz-form full sum (flint midpoint,
192 bits) against a direct float64 sum over n <= 10^6 at sigma = 1.5, 2, 3.
Measured differences 1.03e-3, 5.14e-7, 2.57e-13, each positive and below
the integral-test tail bound N^{1-sigma}/(sigma-1) (2e-3, 1e-6, 5e-13):
exactly the discarded tail, as the identity requires. A wrong residue split
or a wrong n = 1 accounting would miss at order one.

## 3. The argument

**(a) Uniqueness of the root.** Each term |a_n| n^{-sigma} with a_n != 0 is
strictly decreasing in sigma (kappa > 0 is decided by the ball), so g is
strictly decreasing and continuous on (1, inf). As sigma -> 1+ the
n = 1 (mod 5) subsum alone diverges, so g -> +inf; as sigma -> inf,
g -> -1. Hence exactly one root sigma_0, and any decided sign bracket
encloses it.

**(b) No zeros of f in the open half-plane Re s > sigma_0.** For
Re s = sigma > sigma_0, strict monotonicity gives
sum_{n>=2} |a_n| n^{-sigma} < sum_{n>=2} |a_n| n^{-sigma_0} = 1, so

    |f(s)| >= 1 - sum_{n>=2} |a_n| n^{-sigma} > 0.

**(c) No zeros of f on the line Re s = sigma_0 (exact phase argument).**
Suppose f(sigma_0 + it) = 0. Then W := sum_{n>=2} a_n n^{-s} = -1, and
since |W| = 1 = sum_{n>=2} |a_n| n^{-sigma_0}, the triangle inequality is
an equality: every nonzero term a_n n^{-s} is a nonnegative multiple of a
common unit vector, and the sum being -1 makes each term strictly negative
real, i.e. n^{-it} = -1 when a_n > 0 and n^{-it} = +1 when a_n < 0. Take
n = 3 (a_3 = -kappa < 0): 3^{-it} = 1. Take n = 4 (a_4 = -1 < 0):
4^{-it} = 1. Take n = 12 (12 = 2 mod 5, a_12 = kappa > 0): 12^{-it} = -1.
But 12^{-it} = 3^{-it} 4^{-it} = 1. Contradiction; the case t = 0 fails the
same constraints (2^{0} = 1 != -1). So f has no zero with Re s >= sigma_0.

**(d) The gamma factor and the reflection.** (pi/5)^{-(s+1)/2} is entire
and never zero; Gamma((s+1)/2) is never zero and is analytic except for
simple poles at s = -1, -3, -5, .... All those poles have Re s = -1 or
less, so on Re s >= sigma_0 > 1 the factor gamma is analytic and
nonvanishing, and F = gamma f has no zero with Re s >= sigma_0 by (b), (c).
Since F is entire with F(s) = F(1-s), F also has no zero with
Re s <= 1 - sigma_0. Every zero of F therefore lies in the open strip
1 - sigma_0 < Re s < sigma_0.

**(e) Trivial zeros: why the claim is about F, not about f.** F is entire
while gamma has a simple pole at each s_m = -(2m+1), m >= 0. Writing
f = F / gamma = F * (1/gamma), the function 1/gamma has a simple zero at
s_m, so f vanishes there to order 1 + ord_F(s_m) >= 1: f has "trivial"
zeros at s = -1, -3, -5, ..., forced by the functional equation exactly as
zeta's trivial zeros are, shifted to the odd negative integers because chi
is odd (the in-tree statement is in the `zeta.epstein.completed_dh`
docstring). These lie outside the strip, so "all zeros of *f* lie in the
strip" would be false. The decided statement is: all zeros of *F* lie in
the strip. Away from the points s_m the zeros of F and of f coincide with
multiplicity (gamma is finite and nonzero there); at s_m,
ord_F = ord_f - 1. So the zeros of F are exactly the nontrivial zeros of
f, and it is those that the map z -> s = 1/2 + iz carries to the zeros of
Xi_DH, giving |Im z| < Delta in section 1.

**(f) What is decided versus what is exact.** Steps (a), (b), (c) are exact
elementary analysis given the coefficient pattern and 0 < kappa < 1
(decided); step (d) uses the classical nonvanishing of Gamma and the
structural facts that F is entire with F(s) = F(1-s), measured in-tree to
defect ~1e-50 and test-pinned, with the classical derivation cited above.
The numerics enter only to locate sigma_0. A fully decided rational form,
with no reference to sigma_0 at all, is: g(sigma*) < 0 is decided at the
rational sigma* = 1.3951361582351097210613589375 (the flint upper
endpoint), hence every zero of F has 1 - sigma* < Re s < sigma*.

## 4. Decided numbers

All intervals are outward-rounded decimal strings; the printed interval
contains the exact rational endpoints (which are dyadic-over-100 bisection
points, exact by construction). Full detail in `strip_results.json`.

| quantity | backend python-flint (Arb), 192 bits | backend mpmath.iv, dps 40 |
|---|---|---|
| sigma_0 | [1.3951361582351097210613588712, 1.3951361582351097210613589375] | [1.395136158235109178, 1.395136158235109747] |
| Delta = sigma_0 - 1/2 | [0.8951361582351097210613588712, 0.8951361582351097210613589375] | [0.895136158235109178, 0.895136158235109747] |
| Delta^2/2 | [0.4006343708899556944469547527, 0.4006343708899556944469548120] | [0.400634370889955208, 0.400634370889955718] |
| g(2) | [-0.7333360538690251425955054390, -0.7333360538690251425955054389] | [-0.733336053869025143, -0.733336053869025142] |

Decided inequalities, both backends, by exact rational comparison of the
outward endpoints:

- **Delta^2/2 < 0.4007** (against 4007/10000; flint margin ~6.6e-5). This
  is the number WP2's upper bound runs through: with de Bruijn 1950
  Theorem 13 (hypotheses per `NOVELTY.md`, confirmation against the
  original text still a standing task and a kill condition), all zeros of
  H_0 in |Im z| <= Delta implies H_t real-rooted for t >= Delta^2/2, so
  Lambda_DH <= Delta^2/2 < 0.4007.
- **g(2) < 0**: the in-tree coarse strip re-derived as a decided
  inequality. `zeta/epstein.py` pins f away from 0 for Re s >= 2 by
  sum_{n>=2} |a_n| n^{-2} = 0.2666... < 1 (numerically verified in the
  tests); here that becomes a two-backend enclosure of g(2) with a decided
  sign, and with the reflection of section 3(d) it gives the coarse strip
  -1 < Re s < 2 for the zeros of F. The present sigma_0 tightens that to
  width 2 sigma_0 - 1, about 1.79.

kappa (section 1) is decided at 500 bits on flint; the iv leg consumes the
interval KAPPA_REF +/- 1e-39, which is an enclosure because the flint ball
is decided to lie inside it (same construction as `validate.py` check 2).

Sign decisions: 79 (flint bisection, bracket [1.39, 1.40]) and 46 (iv).
Every bisection endpoint is an exact rational; every sign was decided by an
enclosure excluding 0, with an undecided sign a loud abort, never a guess.
Timings (`strip_results.json`): the whole run is about 1 s.

## 5. Method note on the iv backend

mpmath's iv context has no Hurwitz zeta. The plain integral-test tail
enclosure [0, N^{1-sigma}/(sigma-1) + N^{-sigma}] is valid but its width
decays like N^{-0.395} near sigma_0: about 1.7e-3 at N = 1e8, hopeless for
a 1e-15 bisection target at any feasible N. The iv leg therefore keeps the
integral-test skeleton and adds Euler-Maclaurin correction terms: each
residue-class sum sum_{j>=0} (5j+c)^{-sigma} is a finite sum (M = 100
terms) plus the tail

    (5M+c)^{1-sigma}/(5(sigma-1)) + (5M+c)^{-sigma}/2
      + sum_{j=1}^{8} B_{2j}/(2j)! (sigma)_{2j-1} 5^{2j-1} (5M+c)^{-sigma-2j+1}
      + R,

with |R| enclosed symmetrically by twice the first omitted correction term.
That remainder statement holds when the relevant derivative of the
integrand keeps one sign (DLMF 2.10(i)); x^{-sigma} is completely monotone,
so it applies. Per the house rule the convention was not recalled but
checked: `check_em_tail` requires each iv class-sum enclosure to contain an
independent `mpmath.mp` Hurwitz-zeta reference at dps 60, over all four
classes and five sigma values spanning the bracket (20/20 contained,
enclosure widths ~1e-36). The two-backend overlap of the sigma_0 intervals
is a second, independent check of the same arithmetic.

## 6. Honest scope

- The strip argument conditions on: the period-5 coefficient pattern with
  0 < kappa < 1 (decided, flint, 500 bits); absolute convergence for
  Re s > 1; F entire with F(s) = F(1-s) (classical structure, in-tree
  measured defect, test-pinned); and the classical nonvanishing of Gamma.
  It uses no Euler product and no positivity, which is why it applies to an
  RH-violating function at all.
- The strip is not vacuous padding. The literature records DH zeros with
  Re s > 1 (discussed in Ferry et al., arXiv:1602.06328; see `NOVELTY.md`),
  and by the present result any such zero has Re s < sigma_0, so the
  shoulder region (1, sigma_0) is genuinely occupied territory, not slack:
  no argument can shrink the strip to Re s <= 1.
- Nothing here says anything about RH or about zeta. DH violates RH inside
  this strip (the pinned off-line zero of `zeta/epstein.py` has
  Re s ~ 0.8085, comfortably interior); the strip merely caps how far off
  the line its zeros can sit, which is what de Bruijn's theorem consumes.
- Grades, per the vocabulary contract: sigma_0, Delta, Delta^2/2 < 0.4007,
  g(2) < 0, and kappa are decided (backends and precisions above). The
  strip statement itself is exact analysis on top of the decided constants
  plus the cited structural facts; the composite claim
  "Lambda_DH <= Delta^2/2" additionally rides on de Bruijn 1950 Theorem 13
  and is withdrawn if the pinning of that theorem's exact form fails (kill
  condition in `MISSION.md`). The identity and remainder checks of
  sections 2 and 5 are measured cross-checks, and say so.
