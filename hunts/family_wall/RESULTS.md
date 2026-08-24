# Results: where the n-point pressure family stops

> Bounded outcome of the `family_wall` hunt. The analysis is `FAMILY-LIMIT.md`; this page
> is the one-page verdict and the labels. Labels: VERIFIED means recomputed here from first
> principles; MEASURED means float optimisation, an upper bound on an infimum; DERIVED means
> algebra checked numerically; INFERRED means extrapolation with the gap stated; AUDIT means
> established by the independent adversarial audit in `audit/` and says how.
>
> Nothing here is a proof and nothing here is machine-checked.

## 1. The verdict

    lim_{n -> infinity} Phi_n  =  H  =  0.6725007036794116                    DERIVED, exact
    sup_n Phi_n  <=  0.675142509660254                                        AUDIT, VERIFIED here
    configuration ceiling        0.6818286874638
    deficit at the family's best   >= 0.0066862 — 71.7% of the H-to-ceiling distance

The n-point pressure certificate family, at any `n`, any pressure, and with any valid floor
`c`, cannot reach the configuration ceiling. Increasing `n` does not help: the family climbs
a little above `H`, turns over, and returns to `H`.

The mechanism is one identity. `Phi_n <= H + H c - (n-1)/p`, and a witness configuration of
total length at most `(n-1)/H` makes the pressure term cancel itself, leaving `H(1 + W)` with
`W` an energy per point of order `10^-3`. Reaching the ceiling would need `W >= 0.0138706`
for every admissible witness simultaneously. It is not close.

## 2. Coverage of every n

| range | instrument | bound | label |
|---|---|---|---|
| n = 3 .. 11 | audit's interval-checked witnesses | max 0.673403910507391537 (n=5) | AUDIT |
| n >= 12 | period-37 word + closed-form tail estimate, uniform | 0.675142509660253902 | AUDIT, VERIFIED here |

Redundantly, and from this hunt's own computations alone: witness envelope over `n = 3..36`
(max 0.6735202493), tiled witness over `n = 36..401` (max 0.6751676068 at n=56), trivial leg
`Phi_n <= H(n-1)/(n-2)` for `n >= 402` (max 0.6741861691) — giving the weaker
`sup_n Phi_n <= 0.6751676068`, which is what this hunt supported before the audit and which
still stands. MEASURED.

The period-37 word is `g_i = 1 + floor(18i/37) - floor(18(i-1)/37)`, nineteen `1`s and
eighteen `2`s per period, with `S_k = k + floor(18k/37) <= (55/37) k` and
`55/37 < 1/H`, so the length constraint holds for every `k` in closed form. Evaluated at
every `n` from 8 to 401 with this hunt's own `famlib`, its worst bound is `0.6750627723649344`
at `n = 9`; the headline `0.675142509660254` is fixed by the coarseness of the uniform tail
estimate, not by any evaluated witness. VERIFIED here (`period37_check.py`).

## 3. What the audit changed

A different model, in an isolated directory outside this repository, from a brief committed
before any work began, with no access to this repository or any prior implementation.
Provenance: `audit/PROVENANCE.md`. Report: `audit/results/REPORT.md`.

**It broke the argument.** Two steps of the inequality chain were invalid as written: the
step that replaces the denominator reverses when the numerator is negative, and the step that
evaluates at the largest admissible `m` was never given a monotonicity argument. Both were
exhibited with admissible counterexamples at `n = 3`. Section 2.1a of `FAMILY-LIMIT.md` is
the case split that repairs them, re-derived and re-checked here
(`chain_repair_check.py`: 6,475 increment-sign checks and 5,729 admissible triples with
`Phi_n > H`, zero violations).

**It did not break the claim.** No numerical counterexample at any `n`. Its largest
best-found constrained `W` was at `n = 100`: `W < 0.001404828486362211`, giving
`H(1+W) < 0.673445451825039116`. AUDIT, interval-checked there.

**It sharpened the result** to `0.675142509660254` and replaced a 367-value scan plus a
bolted-on trivial tail with one explicit word.

## 4. The open items

1. **The chain's remaining load-bearing assumption is untested here.** It rests on `m` being
   capped at `(n-1) + floor(1/c)` and on `c` being a floor for `F_{n-1}` on *all* nonnegative
   gap vectors. That should be checked against `n_point_bound` line by line, and has not been.
2. **`inf F_{7,3000}` has no global certificate.** The audit's value,
   `0.003826231211304474248285482857707954213`, rests on 562 broad local starts, four
   differential-evolution runs and 1,710 integer-lobe starts producing 953 distinct local
   minima, with the next stationary value `4.20e-5` higher and all six Hessian eigenvalues
   positive. That is evidence, not a lower bound over the domain. It sits `2.0e-13` below the
   `0.0038262312115073` this laboratory quotes, and section 3 of `FAMILY-LIMIT.md` shows why:
   the quoted figure is an Arb evaluation at an argmin rounded to six decimals, so an upper
   bound on the infimum. `hunts/ainta_seven_point/RESULTS.md` states it that way correctly;
   this hunt had been calling it a floor.
3. **Nothing here was run in exact arithmetic on this side.** The audit's witnesses carry
   directed interval bounds in the unsafe direction from its own `mpmath.iv` runs at 100
   digits; this hunt's own numbers are float, with the direction-of-error analysis in section
   4 of `FAMILY-LIMIT.md`.
