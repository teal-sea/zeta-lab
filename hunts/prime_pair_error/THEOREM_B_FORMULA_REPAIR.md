# Repair of the sharp-cutoff character-weighted explicit formula

Status: **useful intermediate lemma, plus a conditional strengthening of Theorem B.**
Grade: *measured and derived*, reviewed by nobody but its author. The derivations below
are ordinary analytic number theory with their hypotheses stated; the numerical checks in
section 9 are floating-point sanity checks and are **not proof**. Nothing here is
kernel-checked. An independent reviewer owns the attack on this argument; this file does
not claim review.

Date: 2026-09-20. Base commit: `f402358c6c3f3c838605e71dd97cb6401a6963f0`.

---

## 0. Scope

This file repairs **one object**: the zero expansion of

    I(x) = sum_{m <= x} Lambda(m) chi(m) (x/2 - m),      chi = chi_3,

asserted at THEOREM_B_SEQUENCE.md section 3 as an absolutely convergent sum over the
nontrivial zeros of L(s, chi_3), and identified as defective by FAREY_BASELINE_REPAIR.md
Appendix B (2026-09-12).

It does **not**:

- prove RH, or bear on RH at all (`docs/08`);
- re-derive or modify Theorem B of RESULTS.md section 18, which is settled and stands
  unchanged;
- modify THEOREM_B_SEQUENCE.md, which is left as the record of the failed argument;
- reopen the hunt's completed numerical passes.

The only new files are this one, `formula_repair_checks.py` and its results JSON.

What is claimed, in one sentence: **the defective expansion is replaced by a truncated
formula with an explicit two-parameter remainder, derived from facts the hunt has already
inherited; that formula supports the resonance argument under an explicitly stated
isolation hypothesis, and the exact inequality still missing in the unconditional case is
written down in section 10.**

---

## 1. Setup and conventions

`chi` is the primitive real character mod 3, `chi(1) = 1`, `chi(2) = -1`, `chi(0 mod 3) = 0`.
It is **odd**: `chi(-1) = chi(2) = -1`. `Lambda` is von Mangoldt.

    psi(x, chi)  = sum_{m <= x} Lambda(m) chi(m)
    psi_1(x, chi) = sum_{m <= x} Lambda(m) chi(m) (x - m) = integral_0^x psi(t, chi) dt
    I(x)          = sum_{m <= x} Lambda(m) chi(m) (x/2 - m)

**Endpoint convention.** Every sum `sum_{m <= x}` is closed at `x`. Hence `psi(., chi)` and
`I` are right-continuous, and `I` jumps by `-Lambda(x) chi(x) x / 2` at each prime power
`x`. This matters: the inherited fact (F1) below is quoted in RESULTS.md in its
right-continuous form, which differs from Montgomery and Vaughan's midpoint statement by
`Lambda(x) chi(x) / 2` at prime powers. No half-jump correction is therefore needed
anywhere in this file, and none is silently applied.

`rho' = beta' + i gamma'` runs over the nontrivial zeros of `L(s, chi)`, with multiplicity
`m(rho')`. `Theta_chi = sup beta'`. By the functional equation zeros pair as
`rho' <-> 1 - conj(rho')`, so `Theta_chi >= 1/2`. `Theta = sup Re rho` over the zeros of
`zeta`.

Write

    c(rho') = (rho' - 1) / (2 rho' (rho' + 1)).

This is exactly the coefficient appearing in the defective formula (*), which is why the
repair below is a repair of that formula rather than a replacement of it.

---

## 2. The defect, stated precisely

THEOREM_B_SEQUENCE.md section 3 asserts an absolutely convergent expansion

    (*)   I(x) = sum_{rho'} m(rho') c(rho') x^{rho' + 1} + (polar terms),

justifying absolute convergence by a dyadic count of zeros. Appendix B of
FAREY_BASELINE_REPAIR.md records this as defective. Two distinct things are wrong, and it
is worth separating them, because only one is fatal.

**Defect 1 (fatal): the coefficient decays like 1/|gamma'|, not 1/|gamma'|^2.**

For `|gamma'| >= 1`, using `|rho' - 1| >= |gamma'|`, `|rho'| <= sqrt(2) |gamma'|`,
`|rho' + 1| <= sqrt(5) |gamma'|`,

    |c(rho')| >= |gamma'| / (2 sqrt(10) |gamma'|^2) >= 1 / (7 |gamma'|),

and by Riemann and von Mangoldt for `L(s, chi)` (inherited fact (F2) below) the zeros in
`[T, 2T]` number `asymptotically T log T`, so dyadic summation gives

    sum_{0 < |gamma'| <= T} 1 / |gamma'|  >>  log^2 T  ->  infinity.

Hence `sum_{rho'} |c(rho')| = infinity` and (*) is **not** absolutely convergent. This is
the load-bearing error. The numerator `rho' - 1` was dropped when the size of the
coefficient was estimated; `|c(rho')| ~ 1/(2|gamma'|)`, not `~ 1/|gamma'|^2`.

**Defect 2 (a real misstatement, but not the fatal one).** The dyadic zero count is also
misstated in that section. However, the conclusion it was invoked to support, namely
`sum_{rho'} 1 / |rho'(rho' + 1)| < infinity`, is in fact **true** by (F2), so repairing the
count alone does not rescue (*). Appendix B lumps these two; separating them is a
refinement, and it identifies which one the repair must route around.

Consequence: the sum over zeros must be **truncated**, and truncation forces an error term
that depends on both `x` and the height `T`. The whole content of the repair is that the
error term can be made small relative to the resonance term, and under what conditions.

**Defect 3 (a second, independent failure in the downstream argument).** Even granted a
truncated formula, THEOREM_B_SEQUENCE.md takes `T = x^delta` for a small fixed `delta`. The
truncation error below is of size `x^2 T^{-1} log^2(xT)`, which beats the witness term
`x^{1 + beta_0}` only when `T >> x^{1 - beta_0 + epsilon}`. A fixed small `delta` fails
whenever `delta < 1 - beta_0`, which is the generic case. The admissible range of `T` is
stated explicitly in Proposition 3 and used in Theorem 4; check C6 in section 9 exhibits
the crossover numerically.

---

## 3. FROZEN candidate proposition and hypotheses

*Frozen before the derivations in sections 4 to 7. Nothing below this line was adjusted to
make a later step work; where a derivation forced a change, that is recorded as a
correction note rather than a silent edit. No such note was needed.*

### Hypotheses

**(H-ISO).** There is a nontrivial zero `rho_0 = beta_0 + i gamma_0` of `L(s, chi_3)` with
`gamma_0 > 0` and multiplicity `m_0 >= 1` such that

    beta_c := sup { Re rho' : rho' nontrivial, rho' not in {rho_0, conj(rho_0)} } < beta_0.

Write `g := beta_0 - beta_c > 0`. Necessarily `beta_0 = Theta_chi` and the supremum is
attained.

*(H-ISO) implies GRH fails for `L(s, chi_3)`.* Under GRH every nontrivial zero has
`Re = 1/2`, so `beta_c = beta_0` and `g = 0`. This is not a defect of the hypothesis; it is
the same regime in which Theorem B is informative at all (RESULTS.md section 18: Theorem B
is unconditional but says nothing new unless RH fails for `L(s, chi)`).

**(H-TRANSFER).** `Theta < Theta_chi`. This is the regime in which Theorem A's transfer
from `I(N)` to `T(N)` has room, and is the same regime RESULTS.md section 18 works in.

### Proposition 3 (repaired truncated explicit formula) [candidate]

*For all real `x >= 4` and all real `T >= 4`,*

    I(x) = sum_{0 < |gamma'| <= T} m(rho') c(rho') x^{rho' + 1} + E(x, T),

    c(rho') = (rho' - 1) / (2 rho' (rho' + 1)),

*with*

    |E(x, T)| <= C_1 x^2 T^{-1} log^2(xT) + 2 C_1 x log x + C_2,

*where `C_1` is the absolute implied constant of (F1) at modulus 3 and*

    C_2 = sum_{rho'} 4 / |rho' (rho' + 1)| < infinity.

*The sum is over nontrivial zeros with multiplicity, in conjugate pairs, so it is real.
`T` is unrestricted above 4: no admissible-height condition is needed, because (F1) as
inherited holds for arbitrary `T`. All polar contributions (the `mu_1 x` term at `s = 0`,
the `log x + nu` term at the `s = -1` pole/trivial-zero collision, and the trivial-zero
tail) are of size `O(x)` and are absorbed into the `O(x log x)` remainder rather than
dropped; they are derived separately in section 5 and are available explicitly for any use
that needs them.*

### Theorem 4 (conditional constructive oscillation) [candidate]

*Assume (H-ISO) and (H-TRANSFER). Put `c_0 = c(rho_0)`, `phi_0 = arg c_0`, and*

    x_n = exp( (2 pi n - phi_0) / gamma_0 ),     N_n = floor(x_n).

*Then*

    I(x_n) = 2 m_0 |c_0| x_n^{1 + beta_0} ( 1 + O( x_n^{-g/2} log^2 x_n ) ),

*and consequently*

    E(N_n) >> N_n^{1 + 2 Theta_chi}

*along that sequence, with no epsilon loss, where `x_{n+1} / x_n = exp(2 pi / gamma_0)`.*

*This is strictly stronger than Theorem B (`Omega(N^{1 + 2 Theta_chi - eps})` along an
unspecified sequence) in two ways: the epsilon is removed, and the sequence is explicit.
It is strictly weaker in one: Theorem B is unconditional and this is not.*

---

## 4. Lemma 0: the decomposition

**Lemma 0.** For all `x >= 0`,  `I(x) = psi_1(x, chi) - (x/2) psi(x, chi)`.

*Proof.* Both sides are finite sums over `m <= x`. Writing `S(x) = sum_{m <= x} Lambda chi(m) m`,

    I(x)   = (x/2) psi(x, chi) - S(x),
    psi_1(x, chi) = x psi(x, chi) - S(x).

Subtract: `psi_1 - (x/2) psi = x psi - S - (x/2) psi = (x/2) psi - S = I`. QED

This identity is exact, carries no error, and respects the endpoint convention of section 1
since every term is the same closed sum. It is the whole reason the repair is cheap: `I` is
a fixed linear combination of the first Riesz mean and the sharp sum, and (F1) covers both.

Check C1 in section 9 verifies it at every integer `x <= 200` to `2.4e-58`.

---

## 5. Polar structure, including the s = -1 collision

This section derives, rather than inherits, the polar terms. They do not enter the bound in
Proposition 3 beyond `O(x log x)`, but the brief requires them derived and they correct a
specific error in the source document.

For `Re s > 1`, RESULTS.md section 18 and REFEREE.md (R7) give

    integral_1^infinity I(x) x^{-s-2} dx = G(s) := -(L'/L)(s, chi) (1 - s) / (2 s (s + 1)).

The Mellin pair sends this to residues of `G(s) x^{s+1}`.

**s = 1: no pole.** `L(1, chi) != 0` and `L` has no pole at 1 for non-principal `chi`, so
`L'/L` is analytic there; the kernel factor `(1 - s)` vanishes. There is no `x^2` main term,
consistent with `psi(x, chi)` having no main term.

**s = 0: simple pole.** `L(0, chi_3) = 1/3 != 0`, so `L'/L` is analytic at 0 and the pole
comes from the kernel's `1/s`. Residue `= mu_1 x` with

    mu_1 = -(1/2) (L'/L)(0, chi_3) = -0.474099413336...

(check C4, gap `2.6e-30` against the closed form).

**s = -1: a DOUBLE pole, not a simple one.** This is the correction. Because `chi` is odd,
the completed function carries `Gamma((s+1)/2)`, whose poles at `s = -1, -3, -5, ...` force
**trivial zeros of `L(s, chi)` at the odd negative integers**, not the even ones. At
`s = -1` that simple trivial zero of `L` meets the kernel's own `1/(s+1)`, and `L'/L`
contributes a further simple pole. The result is a double pole, so the residue is not a
constant but

    log x + nu.

*Derivation.* Put `u = s + 1` and `h(-1) = lim_{s -> -1} [ (L'/L)(s, chi) - 1/(s+1) ]`, so
`(L'/L)(s, chi) = 1/u + h(-1) + O(u)`. The kernel expands as

    (1 - s) / (2 s (s + 1)) = (2 - u) / (2 u (u - 1)) = ( -1 - u/2 + O(u^2) ) / u,

and `x^{s+1} = x^u = 1 + u log x + O(u^2)`. Multiplying,

    G(s) x^{s+1} = 1/u^2 + ( log x + 1/2 + h(-1) ) / u + O(1),

so the double-pole coefficient is `1` and

    nu = 1/2 + h(-1).

*Closed form for `nu`.* For `chi_3` (real, primitive, odd, `q = 3`, root number 1) the
completed function `Lambda(s) = (q/pi)^{(s+1)/2} Gamma((s+1)/2) L(s, chi)` satisfies
`Lambda(s) = Lambda(1-s)`. Logarithmic differentiation and the reflection give

    (L'/L)(s, chi) = -log(q/pi) - (1/2) digamma((s+1)/2) - (1/2) digamma(1 - s/2) - (L'/L)(1-s, chi).

At `s -> -1`, `digamma(u/2) = -2/u - euler + O(u)` supplies the `1/u`, and
`digamma(3/2) = 2 - euler - 2 log 2`, so

    h(-1) = euler + log(2 pi / 3) - 1 - (L'/L)(2, chi_3),
    nu    = euler + log(2 pi / 3) - 1/2 - (L'/L)(2, chi_3)  =  0.643831644563...

Check C3 confirms the double-pole coefficient is `1` to `2.7e-31`, the residue linear term
equals the closed-form `nu` to `6.4e-31`, and the numeric `h(-1)` agrees with the
functional-equation closed form to `3.0e-16`.

The source document records this polar contribution as `mu_1 x + mu_0`, a constant. That is
wrong: the `s = -1` term is `log x + nu`, not a constant. It is harmless to the resonance
argument (both are `o(x)`), but it is inherited elsewhere and should not be.

**s = -(2k+1), k >= 1: simple poles at the remaining trivial zeros.** Residue

    -(k+1) x^{-2k} / (2 k (2k + 1)),

so the whole tail is `O(x^{-2})` for `x >= 2`.

Check C2 confirms the parity: `|L(-1)| = 1.5e-62`, `|L(-3)| = 3.3e-62`, while
`|L(-2)| = 0.2222`, and `L(0) = 1/3` exactly. Trivial zeros at the odd negatives only, as
an odd character requires.

**Nontrivial zeros.** `-L'/L` has residue `-m(rho')` at `rho'`, so the residue of
`G(s) x^{s+1}` there is

    m(rho') (1 - rho') / (2 rho' (rho' + 1)) . (-1) . x^{rho'+1}  =  m(rho') c(rho') x^{rho'+1},

which is the coefficient named in section 1. Multiplicity is carried through unchanged.

---

## 6. Proof of Proposition 3

Inherited fact (F1), at modulus 3, right-continuous form, arbitrary `T >= 2`, absolute
constant `C_1`:

    psi(x, chi) = - sum_{|gamma'| <= T} x^{rho'} / rho' + E_0(x, T),
    |E_0(x, T)| <= C_1 ( x T^{-1} log^2(xT) + log x ).

*Step 1: integrate.* `psi(t, chi) = 0` for `t < 2`, so `psi_1(x, chi) = integral_2^x psi(t, chi) dt`.
Integrating the truncated sum term by term (a finite sum),

    integral_2^x t^{rho'} dt / rho' = ( x^{rho'+1} - 2^{rho'+1} ) / ( rho' (rho' + 1) ),

hence

    psi_1(x, chi) = - sum_{|gamma'| <= T} ( x^{rho'+1} - 2^{rho'+1} ) / ( rho'(rho'+1) ) + E_1,
    |E_1| <= C_1 ( x^2 log^2(xT) / (2T) + x log x ).

*Step 2: the sharp term.* Multiply (F1) by `-x/2`:

    -(x/2) psi(x, chi) = (x/2) sum_{|gamma'| <= T} x^{rho'} / rho' + E_2,    E_2 = -(x/2) E_0(x, T),

so that `|E_2| <= (x/2) C_1 ( x T^{-1} log^2(xT) + log x ) = C_1 ( x^2 log^2(xT) / (2T) + (x log x)/2 )`.

*Step 3: add, using Lemma 0.* The coefficient of `x^{rho'+1}` is

    1/(2 rho') - 1/( rho'(rho'+1) ) = ( (rho'+1) - 2 ) / ( 2 rho'(rho'+1) ) = (rho' - 1) / ( 2 rho'(rho'+1) ) = c(rho').

This is the identity that makes the repair a repair: the two routes recombine into exactly
the coefficient the defective formula named. (Check C5 verifies the identity at 21 located
zeros to `1.2e-63`.)

The leftover constant from Step 1 is

    B(T) = sum_{|gamma'| <= T} m(rho') 2^{rho'+1} / ( rho'(rho'+1) ),

and since `0 < beta' < 1` gives `|2^{rho'+1}| = 2^{beta'+1} <= 4`,

    |B(T)| <= sum_{rho'} 4 / |rho'(rho'+1)| = C_2 < infinity,

uniformly in `T`. Finiteness: for `|gamma'| >= 1`, `|rho'| >= |gamma'|` and
`|rho' + 1| >= |gamma'|`, so the terms are `<= 4/gamma'^2`, and (F2) gives convergence by
dyadic summation. For `|gamma'| < 1` there are finitely many zeros (F2), each with
`|rho'| >= delta_0 > 0` because `L(0, chi_3) = 1/3 != 0` and `L` is analytic near 0.

Collecting, with `E = E_1 + E_2 + B(T)`,

    |E(x, T)| <= C_1 x^2 T^{-1} log^2(xT) + 2 C_1 x log x + C_2.

QED (Proposition 3).

**Reality.** `c(conj(rho')) = conj(c(rho'))` and `x^{conj(rho')+1} = conj(x^{rho'+1})`, and
the truncation `|gamma'| <= T` is symmetric, so the sum is real, as `I(x)` must be.

**Where the polar terms went.** They are all `O(x)` or smaller (section 5) and are absorbed
in the `2 C_1 x log x` slack. Proposition 3 could instead be stated with `mu_1 x`,
`log x + nu` and the trivial-zero tail written out and a correspondingly smaller remainder;
nothing below needs that, and stating it this way keeps the constant honest.

---

## 7. Proof of Theorem 4

Assume (H-ISO). Set `epsilon_1 = g/2` and, for each `x`, the height

    T = T(x) = x^{1 - beta_0 + epsilon_1}.

Note `beta_0 >= 1/2` (functional equation), so `T <= x` and `log(xT) <= 2 log x` for `x >= 4`.

*(a) Truncation error.* From Proposition 3,

    C_1 x^2 T^{-1} log^2(xT) <= 4 C_1 x^{1 + beta_0 - epsilon_1} log^2 x,

and `2C_1 x log x + C_2 = o(x^{1+beta_0})` since `beta_0 > 0`.

*(b) Competitor sum.* For `|gamma'| >= 1`,

    |c(rho')| <= ( |1 - beta'| + |gamma'| ) / ( 2 |gamma'|^2 ) <= 1 / |gamma'|,

and the finitely many zeros with `|gamma'| < 1` contribute a bounded amount. So by (F2)

    sum_{|gamma'| <= T} m(rho') |c(rho')| << log^2 T << log^2 x.

Therefore

    | sum_{rho' not in {rho_0, conj(rho_0)}, |gamma'| <= T} m(rho') c(rho') x^{rho'+1} |
        <= x^{1 + beta_c} sum_{|gamma'| <= T} m(rho') |c(rho')|
        << x^{1 + beta_0 - g} log^2 x.

*Note, and it is the reason the unconditional case is hard.* That competitor bound used
`beta_c < beta_0` and nothing else. The weighted mass `sum_{|gamma'| <= T} |c(rho')|` is
`asymptotically log^2 T`, which **grows with x**. The set of zeros that can compete with the
witness is not finite and does not stay finite as `x -> infinity`. Section 10 returns to this.

*(c) Witness.* The conjugate pair `rho_0, conj(rho_0)` contributes

    2 Re [ m_0 c_0 x^{1 + rho_0} ] = 2 m_0 |c_0| x^{1 + beta_0} cos( gamma_0 log x + phi_0 ).

At `x = x_n = exp( (2 pi n - phi_0)/gamma_0 )` the cosine is exactly 1. Hence

    I(x_n) = 2 m_0 |c_0| x_n^{1+beta_0} + O( x_n^{1+beta_0-g} log^2 x_n ) + O( x_n^{1+beta_0-g/2} log^2 x_n )
           = 2 m_0 |c_0| x_n^{1+beta_0} ( 1 + O( x_n^{-g/2} log^2 x_n ) ),

using `epsilon_1 = g/2 <= g`. The successive ratio is `x_{n+1}/x_n = exp(2 pi / gamma_0)`.
Also `c_0 != 0`, since `c(rho') = 0` only at `rho' = 1`, which is not a zero.

*(d) Integer transfer.* For `N <= x < N+1` no new prime power enters, so
`I(x) - I(N) = (x - N) psi(N, chi)/2 = O(N)`, negligible against `N^{1+beta_0}` since
`beta_0 > 0`. This is the same step RESULTS.md section 18 uses.

*(e) To E(N).* Theorem A (RESULTS.md section 17, unconditional):

    T(N) = I(N) + O( N^{Theta + Theta_chi} log^4 N + N log N ).

Under (H-TRANSFER), `Theta < Theta_chi = beta_0 <= 1`, so `Theta < 1` and
`Theta + Theta_chi < 1 + beta_0` with margin `1 - Theta > 0`. Hence
`|T(N_n)| >= (1 + o(1)) 2 m_0 |c_0| N_n^{1+beta_0}`, and Cauchy-Schwarz as in section 18
(`E(N) >= 2 T(N)^2 / N`, using `sum_{k <= N} chi(k)^2 <= N`) gives

    E(N_n) >= (1 + o(1)) 8 m_0^2 |c_0|^2 N_n^{1 + 2 beta_0}  >>  N_n^{1 + 2 Theta_chi}.

QED (Theorem 4).

**What Theorem 4 does not say.** It is conditional on (H-ISO), which implies GRH fails for
`chi_3`, and on (H-TRANSFER). It is not evidence for or against either. It does not improve
the unconditional Theorem B. It says nothing about the upper bound `E(N) = O(N^2 log^2 N)`,
which is the direction the hunt's original objective needed.

---

## 8. External inputs

Used as published; not re-derived here.

- **(F1)** Montgomery and Vaughan, *Multiplicative Number Theory I*, Theorems 12.5 and
  12.10, in the right-continuous form quoted at RESULTS.md section 17. Arbitrary `T >= 2`.
  This is the only nontrivial analytic input to Proposition 3.
- **(F2)** Riemann and von Mangoldt zero-counting for `L(s, chi)`: the number of zeros with
  ordinate in `[t, t+1]` is `O(log(|t|+2))`; hence
  `sum_{0 < |gamma'| <= T} 1/|gamma'| << log^2 T`. RESULTS.md section 17. Used for both the
  convergence of `C_2` and the competitor bound, and (in the reverse direction, via dyadic
  summation) for the divergence in section 2.
- **Theorem A**, RESULTS.md section 17: `T(N) = I(N) + O(N^{Theta+Theta_chi} log^4 N)`.
  Unconditional. Used only in step (e).
- **Theorem B**, RESULTS.md section 18. Quoted for comparison. Unchanged.
- **(R7)**, REFEREE.md section 4: independent re-derivation of the Mellin transform
  `G(s)`. The transform is used as the starting point of section 5 only.
- **Landau's oscillation theorem**, in the direction not requiring a sign condition
  (Ingham ch. V; Montgomery and Vaughan section 15.1). Cited in section 10 as the classical
  substitute for the missing inequality; not used in any proof above.
- Functional equation for a primitive odd real character (`Gamma((s+1)/2)`, root number 1
  for `chi_3`), used in section 5 to derive `h(-1)` in closed form.

`chi_3` zero ordinates used in the numerical checks come from
`results_landau_zero_probe.json` (21 zeros to height about 60), produced by an earlier pass
of this hunt. They are used only to test identities, never as evidence for a claim.

---

## 9. Reproducible checks. NOT PROOF.

`hunts/prime_pair_error/formula_repair_checks.py`, results in
`hunts/prime_pair_error/results_formula_repair_checks.json`. Six checks, `mp.dps = 60`,
about half a second total. Every check is a finite floating-point evaluation of an identity
at finitely many points; none of them proves anything, and the script says so in its header.

| # | what | result |
|---|---|---|
| C1 | Lemma 0, `I = psi_1 - (x/2) psi`, at all integers `x <= 200` | max residual `2.39e-58` |
| C2 | parity of the trivial zeros | `L(0)=1/3` exactly; `|L(-1)|=1.5e-62`, `|L(-3)|=3.3e-62`, `|L(-2)|=0.2222` |
| C3 | `s=-1` double pole, `u^2 G(u-1) = A + Bu + ...` | `A = 1` (gap `2.70e-31`); `B = nu = 0.643831644563` (gap `6.40e-31`); `h(-1)` numeric vs functional-equation closed form, gap `3.02e-16` |
| C4 | `mu_1 = -(1/2)(L'/L)(0, chi_3)` | `-0.474099413336`, gap `2.60e-30` |
| C5 | `1/(2 rho) - 1/(rho(rho+1)) = c(rho)` at 21 located zeros; size of `|c|` | residual `1.22e-63`; `|c(rho)| . gamma` runs `0.4915 -> 0.4998`, i.e. `-> 1/2`, confirming `|c| ~ 1/(2 gamma)` and **not** `~ 1/gamma^2` |
| C6 | truncation-error ratio `x^2 log^2(xT)/T` against `x^{1+beta_0}`, `beta_0 = 0.6` | with `T = x^{0.1}`: `1.6e3 -> 2.6e43` (diverges). With `T = x^{0.45} = x^{1-beta_0+0.05}`: `112 -> 0.073` (decays) |

C5 is the direct numerical statement of Defect 1. C6 is the direct numerical statement of
Defect 3: the source document's choice of height makes the error term beat the signal, and
the admissible range fixes it.

---

## 10. The exact remaining gap

Theorem 4 is conditional. What is missing for an unconditional constructive statement is
one inequality, and it can be written down exactly.

**(MISSING).** *There exist `epsilon_1 > 0`, `delta in (0, 1)`, a nontrivial zero
`rho_0 = beta_0 + i gamma_0` with `beta_0 > Theta_chi - eta` for a given small `eta > 0`,
and an unbounded sequence `x_n` with `cos(gamma_0 log x_n + phi_0) >= 1 - delta/4`, such
that with `T_n = x_n^{1 - beta_0 + epsilon_1}`*

    | sum_{0 < |gamma'| <= T_n,  rho' not in {rho_0, conj(rho_0)}} m(rho') c(rho') x_n^{1 + rho'} |
        <=  (1 - delta) . 2 m_0 |c_0| x_n^{1 + beta_0}

*for infinitely many n.*

Given (MISSING), sections 7(a), 7(d) and 7(e) go through verbatim and yield
`E(N_n) >> N_n^{1 + 2 Theta_chi - 2 eta}` along an explicit sequence, unconditionally.
(H-ISO) implies (MISSING) with `delta` close to 1 for all large `n`, which is precisely how
Theorem 4 is proved.

**Why (MISSING) is hard, stated honestly.**

1. The competing set grows. Section 7(b) established
   `sum_{|gamma'| <= T} |c(rho')| asymptotically log^2 T`, so the number of zeros that can
   interfere with the witness at height `T_n` is unbounded as `n -> infinity`. This is a
   direct consequence of Defect 1: because `|c| ~ 1/(2|gamma'|)` rather than
   `1/|gamma'|^2`, the weighted mass diverges. THEOREM_B_SEQUENCE.md treats the
   competitors as a fixed finite obstruction; they are not.
2. Kronecker or Weyl simultaneous approximation controls the phases of any **fixed finite**
   set of ordinates `{gamma'_1, ..., gamma'_k}` along a sequence of `x`. It does not control
   a set whose size grows with `x`, and no uniformity in `k` is available from that
   direction without further input.
3. Without (H-ISO) there may be zeros with `beta'` arbitrarily close to `beta_0` at
   arbitrarily large height, so no fixed power saving `x^{-g}` separates witness from
   competitors.
4. The classical way past exactly this obstruction is Landau's oscillation theorem, or an
   Ingham-type positive-kernel argument: instead of controlling the competitors, one
   contradicts analyticity of the Mellin transform in a half-plane. That is what
   RESULTS.md section 18 already does, and it is why Theorem B carries an epsilon and an
   unspecified sequence. **The non-constructivity is not an accident of the write-up; it is
   what that method yields.** Recovering constructiveness appears to need either (H-ISO) or
   a genuinely new mechanism, and I do not have one.

**Claims from the source document that remain unproved and are not asserted here.** The
"any `delta > 0`" aside on the truncation height (refuted as stated; see Defect 3 and C6);
the existence of an isolated witness zero (assumed as (H-ISO), not proved); effective phase
alignment against the full competitor set (this is exactly (MISSING)).

---

## 11. Disposition

**Proposition 3 is a useful intermediate lemma and I believe it is correct as stated.** It
replaces a divergent formula with a convergent one carrying an explicit two-parameter
remainder, it recovers the same zero coefficients `c(rho')`, it needs only (F1) and (F2)
which this hunt already inherits, and it fixes the admissible height range that the source
argument got wrong.

**It is not a complete repair of the sequence argument.** The payoff standard in the brief
asks for a usable error regime *with all competitors handled*. Proposition 3 supplies the
error regime; the competitors are handled only under (H-ISO). By the brief's own standard
this is therefore "a formula with valid error but insufficient for resonance", which is a
useful intermediate lemma, not a complete sequence repair. Theorem 4 is the best justified
intermediate result I can support, and it is explicitly conditional.

Grades, per the repository's certainty ladder:

- Lemma 0, section 5 polar structure, Proposition 3, Theorem 4: *derived, hypotheses stated,
  reviewed by nobody*. The composite grade of Theorem 4 is that of its weakest step, which
  is its hypothesis (H-ISO): it is a conditional theorem and is called one.
- Section 9: *measured*, float grade, one route, small finite ranges.
- Nothing here is enclosure-carrying or kernel-checked.

No novelty is claimed. No literature search for prior art on this specific repair was run;
the ingredients are standard and the write-up makes no originality claim beyond "this hunt
produced this".

---

## 12. Reproducibility note

The worktree `theorem-b-formula-repair` has no `.venv` (it is gitignored and was never
created here), so the repository rule "always `.venv/bin/python` from the repo root" could
not be followed literally. The checks were run with the **main checkout's** interpreter:

    /Users/thomas/zeta-lab/.venv/bin/python hunts/prime_pair_error/formula_repair_checks.py

Python 3.13.14, mpmath 1.3.0. (The worktree's system `python3` is 3.10 with mpmath 1.4.1;
it was not used.) Anyone reproducing in a fresh clone should create the venv per
`CLAUDE.md` Setup and run the script from the repository root. The script takes about 0.5 s,
touches no network, writes only its own results JSON, and needs no ball-arithmetic backend.
