# Repair of the sharp-cutoff character-weighted explicit formula

Status: **useful intermediate lemma with exact hypotheses, plus a conditional
strengthening of Theorem B.**
Grade: *measured and derived*, with hypotheses stated. The derivations below are ordinary
analytic number theory; the numerical checks in section 9 are floating-point sanity checks
and are **not proof**. Nothing here is kernel-checked and nothing here claims to be.

**Review status.** The first version of this file (commit `95ae36b`) was attacked by an
independent reviewer, whose findings are recorded verbatim in
`THEOREM_B_FORMULA_REVIEW.md`. Five substantive objections (R1 to R5) were raised. This
revision responds to all five; `AUTHOR_RESPONSE.md` lists each one, whether it was accepted
or rejected, the mathematical reason, and the exact change made. The revision (commit
`3006ef2`) then received a targeted follow-up review, appended to the same file, which
cleared the core formula (Proposition 3) and the conditional Theorem 4 and raised three
residual findings F1 to F3, all in section 10. Those three exact edits were made afterwards
and checked by the coordinator; **no further reviewer run has occurred on them.**

Date: 2026-09-20. Original commit: `95ae36b9c09c0cf28844e40e50f7fceac2f95cfb`
(base `f402358c6c3f3c838605e71dd97cb6401a6963f0`). Revised the same day after review.

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

The only new files are this one, `formula_repair_checks.py` and its results JSON, plus
`AUTHOR_RESPONSE.md`.

What is claimed, in one sentence: **the defective expansion is replaced by a truncated
formula whose remainder is shape-explicit in `x` and `T` up to one absolute constant
inherited from (F1), derived from a primary source checked for this revision; that formula
supports the resonance argument under an explicitly stated isolation hypothesis, and the
exact inequality still missing in the unconditional case is written down in section 10.**

"Shape-explicit" is deliberate. `C_1` below is the implied constant of Montgomery and
Vaughan's Theorem 12.10 at `q = 3`; it is absolute and finite but no numerical value for it
is computed or claimed here, so no bound in this file is numerically effective.

---

## 1. Setup and conventions

`chi` is the primitive real character mod 3, `chi(1) = 1`, `chi(2) = -1`, `chi(0 mod 3) = 0`.
It is **odd**: `chi(-1) = chi(2) = -1`. `Lambda` is von Mangoldt.

    psi(x, chi)  = sum_{m <= x} Lambda(m) chi(m)
    psi_1(x, chi) = sum_{m <= x} Lambda(m) chi(m) (x - m) = integral_0^x psi(t, chi) dt
    I(x)          = sum_{m <= x} Lambda(m) chi(m) (x/2 - m)

**Endpoint convention.** Every sum `sum_{m <= x}` is closed at `x`. Hence `psi(., chi)` and
`I` are right-continuous, and `I` jumps by `-Lambda(x) chi(x) x / 2` at each prime power
`x`. Montgomery and Vaughan state the explicit formula for the **midpoint** normalization
`psi_0(x, chi) = (psi(x^+, chi) + psi(x^-, chi))/2` (verified against the primary source;
see section 8). The two differ by `Lambda(x) chi(x) / 2` at prime powers and nowhere else,
and `|Lambda(x) chi(x)/2| <= (log x)/2`, which is inside the `C_1 log x` term of (F1). The
right-continuous form used here is therefore legitimate as an **upper bound** of the stated
shape, which is all Proposition 3 uses. No half-jump correction is applied anywhere in this
file, and none is needed. (Step 1 of section 6 integrates `psi`, and the two normalizations
differ on a finite set in any bounded range, so the integral does not see the difference at
all; only Step 2 does.)

`rho' = beta' + i gamma'` runs over the nontrivial zeros of `L(s, chi)`, with multiplicity
`m(rho')`. `Theta_chi = sup beta'`. By the functional equation zeros pair as
`rho' <-> 1 - conj(rho')`, so `Theta_chi >= 1/2`. `Theta = sup Re rho` over the zeros of
`zeta`.

**Lemma 1 (no real zeros).** *`L(s, chi_3) > 0` for every real `s > 0`. In particular
`L(s, chi_3)` has no zero in `(0, 1)`, and every nontrivial zero has `gamma' != 0`.*

*Proof.* For real `s > 0` the partial sums of `chi_3(n)` are bounded by 1 and `n^{-s}`
decreases to 0, so `sum_{n >= 1} chi_3(n) n^{-s}` converges by Dirichlet's test; it
converges locally uniformly on `Re s > 0` and so agrees there with the entire function
`L(s, chi_3)` by analytic continuation from `Re s > 1`. Because the series converges, any
subsequence of its partial sums has the same limit; taking `S_{3k}` and using
`chi_3(3k) = 0` gives the grouped form

    L(s, chi_3) = sum_{k >= 0} [ (3k+1)^{-s} - (3k+2)^{-s} ].

Each bracket is positive for `s > 0` since `t -> t^{-s}` is strictly decreasing, and the
`k = 0` bracket equals `1 - 2^{-s}`. Hence `L(s, chi_3) >= 1 - 2^{-s} > 0`. QED

This is used in exactly one place: it lets the truncation `|gamma'| <= T` in Proposition 3
be written inclusively without ambiguity, because for `chi_3` the index sets
`{|gamma'| <= T}` and `{0 < |gamma'| <= T}` coincide. The reviewer was right that the first
version of this file used the two notations interchangeably without saying why they agree.
Check C7 in section 9 exhibits the grouped identity numerically. Lemma 1 is **not** needed
for Proposition 3 itself: Proposition 3 is stated with the inclusive index set, which is
what (F1) supplies whether or not a real zero exists.

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

and by the Riemann and von Mangoldt zero count for `L(s, chi)` in its **two-sided** form
(fact (F2-low) below, Montgomery and Vaughan Corollary 14.6 together with the classical
bound on `S(T, chi)`),

    N(2T, chi) - N(T, chi) = (T / 2 pi) log(2 q T / pi e) + O(log qT) >> T log T

for `T` large. Each of those `>> T log T` zeros has `|gamma'| <= 2T`, so contributes at
least `1/(14T)` to `sum |c(rho')|`, and the dyadic block `[T, 2T]` contributes `>> log T`.
Summing over `log_2 T` dyadic blocks,

    sum_{0 < |gamma'| <= T} |c(rho')|  >>  log^2 T  ->  infinity.

Hence `sum_{rho'} |c(rho')| = infinity` and (*) is **not** absolutely convergent. This is
the load-bearing error. The numerator `rho' - 1` was dropped when the size of the
coefficient was estimated; `|c(rho')| ~ 1/(2|gamma'|)`, not `~ 1/|gamma'|^2`.

**Defect 2 (a real misstatement, but not the fatal one).** The dyadic zero count is also
misstated in that section. However, the conclusion it was invoked to support, namely
`sum_{rho'} 1 / |rho'(rho' + 1)| < infinity`, is in fact **true** by the upper bound
(F2-up) alone, so repairing the count does not rescue (*). Appendix B lumps these two; separating them is a
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

    I(x) = sum_{|gamma'| <= T} m(rho') c(rho') x^{rho' + 1} + E(x, T),

    c(rho') = (rho' - 1) / (2 rho' (rho' + 1)),

*with*

    |E(x, T)| <= C_1 x^2 T^{-1} log^2(xT) + 2 C_1 x log x + C_2,

*where `C_1` is the absolute implied constant of (F1) at modulus 3 and*

    C_2 = sum_{rho'} 4 m(rho') / |rho' (rho' + 1)| < infinity.

*The index set is inclusive: **every** nontrivial zero with `|gamma'| <= T` is summed,
counted with its multiplicity `m(rho')`, which is exactly what the residue computation
behind (F1) produces. For `chi_3` this set contains no real zero, by Lemma 1, so it
coincides with `{0 < |gamma'| <= T}`; the proposition does not depend on that. Zeros occur
in conjugate pairs and the truncation is symmetric, so the sum is real.*

*`T` is unrestricted above 4: no admissible-height condition is needed, because (F1) as
verified in section 8 holds for every `T >= 2` (Montgomery and Vaughan obtain this by
choosing a nearby good height `T_1` in `[T, T+1]` and bounding the intervening zeros; the
statement the reader gets is uniform in `T`). All polar contributions (the `mu_1 x` term at `s = 0`,
the `log x + nu` term at the `s = -1` pole/trivial-zero collision, and the trivial-zero
tail) are of size `O(x)` and are absorbed into the `O(x log x)` remainder rather than
dropped; they are derived separately in section 5 and are available explicitly for any use
that needs them.*

### Theorem 4 (conditional oscillation along a closed-form sequence) [candidate]

*Assume (H-ISO) and (H-TRANSFER). Put `c_0 = c(rho_0)`, `phi_0 = arg c_0`, and*

    x_n = exp( (2 pi n - phi_0) / gamma_0 ),     N_n = floor(x_n).

*Then, for all sufficiently large `n`,*

    I(x_n) = 2 m_0 |c_0| x_n^{1 + beta_0} ( 1 + O( x_n^{-g/2} log^2 x_n ) ),

*and consequently*

    E(N_n) >> N_n^{1 + 2 Theta_chi}

*along that sequence, with no epsilon loss, where `x_{n+1} / x_n = exp(2 pi / gamma_0)`.*

*"Sufficiently large" is not decoration: the proof needs `x_n >= 4` and needs the height
`T(x_n) = x_n^{1 - beta_0 + g/2}` to satisfy `T(x_n) >= max(4, |gamma_0|)`, so that
Proposition 3 applies and the witness pair lies inside the truncation. Both hold for every
`n >= n_0(beta_0, gamma_0, g)`, and `n_0` is computable from those three numbers.*

*This is stronger than Theorem B (`Omega(N^{1 + 2 Theta_chi - eps})` along an unspecified
sequence) in two ways: the epsilon is removed, and the sequence is written down. It is
weaker in one, and the weakness is decisive: Theorem B is unconditional and this is not.
The sequence is explicit **only as a function of the hypothetical witness zero `rho_0`**
supplied by (H-ISO); since (H-ISO) is an existence hypothesis and no zero is exhibited, no
sequence of real numbers is exhibited either. Section 10 keeps that distinction.*

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

Fact (F1), at modulus 3, right-continuous form, every `T >= 2` and every `x >= 4`, absolute
constant `C_1`, with the index set inclusive and zeros counted with multiplicity:

    psi(x, chi) = - sum_{|gamma'| <= T} m(rho') x^{rho'} / rho' + E_0(x, T),
    |E_0(x, T)| <= C_1 ( x T^{-1} log^2(xT) + log x ).

Section 8 derives this from the primary source (Montgomery and Vaughan Theorem 12.10),
which was inspected for this revision; the derivation is three crude majorizations and is
written out there rather than assumed. Multiplicity is written explicitly here because the
first version of this file carried it in Proposition 3 but suppressed it in this step.

*Step 1: integrate.* `psi(t, chi) = 0` for `t < 2`, so `psi_1(x, chi) = integral_2^x psi(t, chi) dt`.
Integrating the truncated sum term by term (a finite sum),

    integral_2^x t^{rho'} dt / rho' = ( x^{rho'+1} - 2^{rho'+1} ) / ( rho' (rho' + 1) ),

hence

    psi_1(x, chi) = - sum_{|gamma'| <= T} m(rho') ( x^{rho'+1} - 2^{rho'+1} ) / ( rho'(rho'+1) ) + E_1,
    |E_1| <= C_1 ( x^2 log^2(xT) / (2T) + x log x ).

*Step 2: the sharp term.* Multiply (F1) by `-x/2`:

    -(x/2) psi(x, chi) = (x/2) sum_{|gamma'| <= T} m(rho') x^{rho'} / rho' + E_2,    E_2 = -(x/2) E_0(x, T),

so that `|E_2| <= (x/2) C_1 ( x T^{-1} log^2(xT) + log x ) = C_1 ( x^2 log^2(xT) / (2T) + (x log x)/2 )`.

*Step 3: add, using Lemma 0.* The coefficient of `x^{rho'+1}` is

    1/(2 rho') - 1/( rho'(rho'+1) ) = ( (rho'+1) - 2 ) / ( 2 rho'(rho'+1) ) = (rho' - 1) / ( 2 rho'(rho'+1) ) = c(rho').

This is the identity that makes the repair a repair: the two routes recombine into exactly
the coefficient the defective formula named. (Check C5 verifies the identity at 21 located
zeros to `1.2e-63`.)

The leftover constant from Step 1 is

    B(T) = sum_{|gamma'| <= T} m(rho') 2^{rho'+1} / ( rho'(rho'+1) ),

and since `0 < beta' < 1` gives `|2^{rho'+1}| = 2^{beta'+1} <= 4`,

    |B(T)| <= sum_{rho'} 4 m(rho') / |rho'(rho'+1)| = C_2 < infinity,

uniformly in `T`. Finiteness: for `|gamma'| >= 1`, `|rho'| >= |gamma'|` and
`|rho' + 1| >= |gamma'|`, so the terms are `<= 4 m(rho')/gamma'^2`, and (F2-up) gives
convergence by dyadic summation. For `|gamma'| < 1` there are finitely many zeros (F2-up), each with
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

*Threshold.* Proposition 3 needs `x >= 4` and `T(x) >= 4`, and step (c) needs the witness
pair inside the truncation, that is `T(x) >= |gamma_0|`. Since `1 - beta_0 + g/2 > 0`, both
hold for all `x >= x_0` with `x_0 = x_0(beta_0, gamma_0, g)` explicit. Everything below is
asserted for `x >= x_0` only, and "for all sufficiently large `n`" in Theorem 4 means
`x_n >= x_0`.

*(a) Truncation error.* From Proposition 3,

    C_1 x^2 T^{-1} log^2(xT) <= 4 C_1 x^{1 + beta_0 - epsilon_1} log^2 x,

and `2C_1 x log x + C_2 = o(x^{1+beta_0})` since `beta_0 > 0`.

*(b) Competitor sum.* For `|gamma'| >= 1`,

    |c(rho')| <= ( |1 - beta'| + |gamma'| ) / ( 2 |gamma'|^2 ) <= 1 / |gamma'|,

and the finitely many zeros with `|gamma'| < 1` contribute a bounded amount. So by (F2-up),
counting with multiplicity,

    sum_{|gamma'| <= T} m(rho') |c(rho')| << log^2 T << log^2 x.

Therefore

    | sum_{rho' not in {rho_0, conj(rho_0)}, |gamma'| <= T} m(rho') c(rho') x^{rho'+1} |
        <= x^{1 + beta_c} sum_{|gamma'| <= T} m(rho') |c(rho')|
        << x^{1 + beta_0 - g} log^2 x.

*Note, and it is the reason the unconditional case is hard.* That competitor bound used
`beta_c < beta_0` and nothing else. The weighted mass `sum_{|gamma'| <= T} m(rho') |c(rho')|`
is of order `log^2 T`: at most, by (F2-up), and at least, by (F2-low) and the computation in
Defect 1. So it **grows with x** and the growth is not an artifact of a lossy upper bound.
The set of zeros that can compete with the
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

*(e) To E(N).* Theorem A (RESULTS.md section 17, unconditional) reads

    T(N) = I(N) + O( N^{Theta + Theta_chi} log^4 N ).

The `+ N log N` that the first version of this file attached to Theorem A is not part of
Theorem A; it appears in RESULTS.md section 18, where Theorem A is combined with the
section 15 estimate (E3). Adding it only weakens the statement, so nothing downstream
breaks, but the attribution was wrong and is corrected here. Step (e) needs only Theorem
A's own error term.

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

Used as published. (F1) and (F2-low) were checked against the primary source for this
revision, because the reviewer could not reach it and the first version of this file relied
on an inherited paraphrase.

**(F1) Montgomery and Vaughan, *Multiplicative Number Theory I*, Theorem 12.10.** Verified
2026-09-20 against the author-hosted chapter (R. C. Vaughan, Penn State, chapter 12,
"Explicit formulae", pp. 397 to 418). The theorem as printed: let `c > 1` be a constant;
suppose `x >= c`, `T >= 2`, and `chi` is a primitive character mod `q > 1`. Then

    psi_0(x, chi) = - sum_{rho, |gamma| <= T} x^rho / rho
                    - (1/2) log(x - 1) - (chi(-1)/2) log(x + 1) + C(chi) + R(x, T; chi),
    C(chi) = (L'/L)(1, chi) + log(q / 2 pi) - C_0,
    R(x, T; chi) << (log x) min(1, x / (T <x>)) + (x/T) log^2(q x T),

where `<x>` is the distance from `x` to the nearest prime power other than `x` itself, and
`psi_0` is the midpoint normalization. Five things needed checking and all five check out
for `chi_3`:

1. *Hypotheses.* `x >= c > 1` and `T >= 2`, nothing more. Take `c = 2`. There is **no**
   restriction `T <= x` and no admissible-height condition; Lemma 12.7 (a nearby `T_1` in
   `[T, T+1]` with `L'/L(sigma +- i T_1, chi) << log^2 qT` uniformly for `-1 <= sigma <= 2`)
   is what buys that, and it is internal to the proof.
2. *Normalization.* `psi_0` is the midpoint form, as section 1 says; the half-jump is
   `<= (log x)/2`.
3. *Index set.* `|gamma| <= T`, inclusive, over all nontrivial zeros; multiplicity enters
   intrinsically because the sum arises as residues of `-(L'/L)(s, chi) x^s / s`. Montgomery
   and Vaughan's proof of Theorem 14.5 explicitly guards against a real zero in `(0,1)`, so
   a real zero is a live possibility in general and the inclusive index set is the honest
   one. Lemma 1 above settles the question for `chi_3` specifically.
4. *Trivial zeros.* The same proof carries `kappa = 0` or `1` as `chi(-1) = 1` or `-1`, and
   the trivial-zero tail `sum_{1 <= k < (K+kappa)/2} x^{kappa-2k}/(2k-kappa)`. For odd
   `chi` this puts the trivial zeros at the **odd** negative integers, independently
   confirming section 5.
5. *Error shape.* `min(1, x/(T<x>)) <= 1` always, so the first term is `<= log x` uniformly
   in `x`, **including at prime powers** where `<x>` could otherwise be small. For `q = 3`
   and `x, T >= 2`, `log(3xT) <= 2 log(xT)`, so `log^2(qxT) <= 4 log^2(xT)`. For odd `chi`
   the two logarithms collapse: `-(1/2)log(x-1) + (1/2)log(x+1) = (1/2) log((x+1)/(x-1))`,
   which is `<= (1/2) log 3` for `x >= 2`, and `C(chi_3)` is an absolute constant. Both are
   `<= const . log x` for `x >= 2`.

Collecting 2 and 5 gives (F1) as used in section 6, with an absolute `C_1`, for `x >= 2`
and `T >= 2`. The load-bearing conclusion: **Proposition 3 does not need to be made
conditional, and neither its coefficient nor the shape of its remainder changes.** What
changed is the index set, the multiplicity notation, and this provenance.

- **(F2-up)** Zero counting, upper bound: the number of zeros of `L(s, chi)` with ordinate
  in `[t, t+1]` is `O(log(|t|+2))`; hence `sum_{0 < |gamma'| <= T} m(rho')/|gamma'| << log^2 T`.
  RESULTS.md section 17. Used for the convergence of `C_2` and for the competitor bound in
  section 7(b). An upper bound suffices for both.
- **(F2-low)** Zero counting, two-sided: Montgomery and Vaughan, *MNT I*, Theorem 14.5 and
  Corollary 14.6 (verified 2026-09-20 against chapter 14, "Zeros", pp. 452 to 462):
  `N(T, chi) = (T/2 pi) log(qT / 2 pi) - T/2 pi + S(T, chi) - S(0, chi) - chi(-1)/8 + O(1/(T+1))`
  for primitive `chi` mod `q > 1`, where `S(T, chi) = (1/pi) arg L(1/2 + iT, chi)`, and
  zeros with `gamma = 0` or `gamma = T` are counted with weight `1/2`. Combined with the
  classical `S(T, chi) << log(q(T+2))` this gives
  `N(2T, chi) - N(T, chi) >> T log T`. **Caveat, stated because it is the one gap in this
  verification:** Corollary 14.6 was read in the primary source, but the bound on
  `S(T, chi)` was not located in the extracted chapter text and is cited from the standard
  literature rather than from an inspected page. The divergence in Defect 1 rests on that
  citation. Nothing else in this file uses (F2-low).
- **Theorem A**, RESULTS.md section 17: `T(N) = I(N) + O(N^{Theta+Theta_chi} log^4 N)`.
  Unconditional. Used only in step (e). The additional `N log N` term seen in RESULTS.md
  section 18 comes from (E3) of section 15, not from Theorem A.
- **Theorem B**, RESULTS.md section 18. Quoted for comparison. Unchanged.
- **(R7)**, REFEREE.md section 4: independent re-derivation of the Mellin transform
  `G(s)`. The transform is used as the starting point of section 5 only.
- **Landau's oscillation theorem**, in the direction not requiring a sign condition
  (Ingham ch. V; Montgomery and Vaughan section 15.1). Cited in section 10 as the classical
  substitute for the missing inequality; not used in any proof above.
- Functional equation for a primitive odd real character (`Gamma((s+1)/2)`, root number 1
  for `chi_3`), used in section 5 to derive `h(-1)` in closed form.

`chi_3` zero ordinates used in the numerical checks come from
`results_landau_zero_probe.json` (21 ordinates in `(0, 60]`, from a sign-change scan of step
0.25), produced by an earlier pass of this hunt. They are used only to test identities,
never as evidence for a claim. The reviewer noted that their provenance had not been
audited. Check C8 audits it two ways: it re-evaluates `|L(1/2 + i gamma)|` at each listed
ordinate, and it compares the count to what (F2-low) predicts. Neither is a completeness
proof. A scan of step 0.25 can miss a close pair, and C8 cannot detect that; it establishes
only that the listed ordinates are near genuine zeros and that the list is not obviously
short. No claim in this file depends on the list being complete.

---

## 9. Reproducible checks. NOT PROOF.

`hunts/prime_pair_error/formula_repair_checks.py`, results in
`hunts/prime_pair_error/results_formula_repair_checks.json`. Eight checks, `mp.dps = 60`,
about three seconds total. Every check is a finite floating-point evaluation of an identity
at finitely many points; none of them proves anything, and the script says so in its header.

| # | what | result |
|---|---|---|
| C1 | Lemma 0, `I = psi_1 - (x/2) psi`, at all integers `x <= 200` | max residual `2.39e-58` |
| C2 | parity of the trivial zeros | `L(0)=1/3` exactly; `|L(-1)|=1.5e-62`, `|L(-3)|=3.3e-62`, `|L(-2)|=0.2222` |
| C3 | `s=-1` double pole, `u^2 G(u-1) = A + Bu + ...` | `A = 1` (gap `2.70e-31`); `B = nu = 0.643831644563` (gap `6.40e-31`); `h(-1)` numeric vs functional-equation closed form, gap `3.02e-16` |
| C4 | `mu_1 = -(1/2)(L'/L)(0, chi_3)` | `-0.474099413336`, gap `2.60e-30` |
| C5 | `1/(2 rho) - 1/(rho(rho+1)) = c(rho)` at 21 located zeros; size of `|c|` | residual `1.22e-63`; `|c(rho)| . gamma` runs `0.4915 -> 0.4998`, i.e. `-> 1/2`, confirming `|c| ~ 1/(2 gamma)` and **not** `~ 1/gamma^2` |
| C6 | truncation-error ratio `x^2 log^2(xT)/T` against `x^{1+beta_0}`, `beta_0 = 0.6` | with `T = x^{0.1}`: `1.6e3 -> 2.6e43` (diverges). With `T = x^{0.45} = x^{1-beta_0+0.05}`: `112 -> 0.073` (decays) |
| C7 | Lemma 1: grouped series vs continuation, bracket positivity, `L(s) >= 1 - 2^{-s}` at `s = 0.05, ..., 1.5` | no negative bracket in 20000 terms at any `s`; every gap inside the provable tail bound `(3N-2)^{-s}/3` (at `s = 0.5`, gap `1.361e-3` vs bound `1.361e-3`); lower bound holds at all six `s` |
| C8 | provenance audit of the 21 inherited ordinates | `max |L(1/2 + i gamma)| = 1.57e-14` over the list; count 21 against the Riemann and von Mangoldt prediction `22.61` to height 60, difference `-1.61`. **Completeness not proved** |

C5 illustrates the size estimate behind Defect 1 at 21 ordinates (taken on the critical
line) and nothing more; the divergence itself is the analytic argument of section 2, which
rests on the two-sided count (F2-low). C6 illustrates Defect 3: with the source document's
height the error *bound* exceeds the signal, so that estimate cannot establish resonance,
and the admissible range removes the obstruction. It says nothing about the size of the
actual error. C7 illustrates Lemma 1 and does not prove it; note in
particular that the grouped series converges slowly for small `s`, so C7 asks only that the
truncation gap stay inside a tail bound proved on the spot, not that it be tiny. C8 answers
the reviewer's provenance question in the two directions a cheap check can answer it, and
records in the results JSON that it does not establish completeness.

---

## 10. The exact remaining gap

Theorem 4 is conditional. What is missing for an unconditional statement of the same shape
is one inequality, and it can be written down exactly.

**(MISSING).** *There exist `epsilon_1 > 0`, `delta in (0, 1)`, a nontrivial zero
`rho_0 = beta_0 + i gamma_0` with `beta_0 > Theta_chi - eta` for a given small `eta > 0`,
and a sequence `x_{n_k} -> infinity` (as `k -> infinity`) along which, for every `k`, BOTH
the phase condition `cos(gamma_0 log x_{n_k} + phi_0) >= 1 - delta/4` AND, with
`T_{n_k} = x_{n_k}^{1 - beta_0 + epsilon_1}`, the competitor bound*

    | sum_{0 < |gamma'| <= T_{n_k},  rho' not in {rho_0, conj(rho_0)}} m(rho') c(rho') x_{n_k}^{1 + rho'} |
        <=  (1 - delta) . 2 m_0 |c_0| x_{n_k}^{1 + beta_0}

*hold.*

The earlier wording (an unbounded sequence `x_n` with the competitor bound for infinitely
many `n`) was insufficient: the unboundedness could come entirely from indices where the
bound fails, so the good indices need not escape to infinity. The form above requires the
good subsequence itself to tend to infinity, which is what the `o(1)` terms, the growth of
`T_{n_k}` and the integer transfer below all use.

**What (MISSING) buys, and at what cost.** The first version of this file said sections
7(a), 7(d) and 7(e) then "go through verbatim". They do not, and the reviewer was right to
stop there. Two adaptations are needed, and neither is free.

*Adaptation 1, the truncation error (7a).* Section 7 fixes `epsilon_1 = g/2`, a quantity
defined by (H-ISO), which is absent here. Use instead the `epsilon_1 > 0` that (MISSING)
supplies. With `T_{n_k} = x_{n_k}^{1 - beta_0 + epsilon_1}` one has exactly
`log(x_{n_k} T_{n_k}) = (2 - beta_0 + epsilon_1) log x_{n_k}`, so for every `k` with
`x_{n_k} >= 4` and `T_{n_k} >= 4` (all large `k`)

    C_1 x_{n_k}^2 T_{n_k}^{-1} log^2(x_{n_k} T_{n_k})
        = C_1 (2 - beta_0 + epsilon_1)^2 x_{n_k}^{1 + beta_0 - epsilon_1} log^2 x_{n_k}
        = o( x_{n_k}^{1 + beta_0} )

for each fixed `epsilon_1 > 0`. The factor 4 of section 7 is not inherited: there it came
from `T <= x`, which the (H-ISO) gap supplies, and `(2 - beta_0 + epsilon_1)^2` exceeds 4
whenever `epsilon_1 > beta_0`. Combining with the `(1 - delta)` competitor bound and the
`(1 - delta/4)` phase bound leaves a surviving main term

    |I(x_{n_k})| >= (3 delta / 4) . 2 m_0 |c_0| x_{n_k}^{1 + beta_0} (1 + o(1)).

So 7(a) adapts in two lines, but it does so with (MISSING)'s `epsilon_1`, not 7's.

*Adaptation 2, the transfer (7e), and this one is a genuine restriction.* Step (e) needs

    1 + beta_0 > Theta + Theta_chi

and nothing weaker: that is the exact margin at which Theorem A's error
`N^{Theta + Theta_chi} log^4 N` stays below the signal `N^{1 + beta_0}`. Section 7 gets it
from `beta_0 = Theta_chi` exactly, which is (H-ISO)'s doing. Here `beta_0` is only known to
exceed `Theta_chi - eta`, so the margin is implied by

    1 + Theta_chi - eta >= Theta + Theta_chi,   that is,   eta <= 1 - Theta.

**(H-TRANSFER) does not supply this for arbitrary `eta`.** `Theta < Theta_chi` gives
`Theta < 1`, hence `1 - Theta > 0` and the permissible range of `eta` is non-empty; but
`eta` is quantified before `Theta` in the statement of (MISSING), and for `eta > 1 - Theta`
the transfer step fails even though (H-TRANSFER) holds. So either

- state the margin `1 + beta_0 > Theta + Theta_chi` as an additional hypothesis of the
  unconditional statement, or
- restrict to `eta <= 1 - Theta` (equivalently, `Theta <= 1 - eta`), which is sufficient and
  which `Theta < 1` makes non-vacuous for every `Theta`, without making it checkable for a
  given `eta`.

With either, and keeping the strict margin `1 + beta_0 > Theta + Theta_chi`, (MISSING)
yields `E(N_{n_k}) >> N_{n_k}^{1 + 2 Theta_chi - 2 eta}` along the corresponding floor
integers `N_{n_k} = floor(x_{n_k})`, unconditionally on (H-ISO). This is a conditional
implication from the unproved (MISSING); no stronger unconditional result is inferred. (H-ISO) implies (MISSING) with `delta` close to 1 for
all large `n`, which is precisely how Theorem 4 is proved, and in that case `beta_0`
**equals** `Theta_chi`, so `eta` may be taken to be 0 and Adaptation 2 is vacuous.

**(MISSING) is an existence statement.** It asserts that some zero, some `epsilon_1`, some
`delta` and some unbounded sequence exist. It exhibits none of them. Any statement derived
from it is therefore existential too. Only the phase condition is explicit in `gamma_0` and
`phi_0` (which are not known numbers); the sequence `x_{n_k}` satisfying it is purely
existential, and no closed form is supplied under (MISSING). The closed form
`x_n = exp((2 pi n - phi_0)/gamma_0)` belongs to Theorem 4's conditional construction under
(H-ISO), not to (MISSING). No constructive or effective claim is made here.

**Why (MISSING) is hard, stated honestly.**

1. The competing set grows. Section 7(b) and Defect 1 together establish
   that `sum_{|gamma'| <= T} m(rho') |c(rho')|` is bounded above and below by constant
   multiples of `log^2 T`, so the number of zeros that can
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
   what that method yields.** An actually exhibited sequence would need an exhibited
   witness zero (which (H-ISO) only posits) or a genuinely new mechanism, and I do not have
   one.

**Claims from the source document that remain unproved and are not asserted here.** The
"any `delta > 0`" aside on the truncation height (refuted as stated; see Defect 3 and C6);
the existence of an isolated witness zero (assumed as (H-ISO), not proved); effective phase
alignment against the full competitor set (this is exactly (MISSING)).

---

## 11. Disposition

**Proposition 3 is a useful intermediate lemma with exact hypotheses, and I believe it is
correct as stated.** Its hypotheses are: `x >= 4`, `T >= 4`, `chi = chi_3`, and (F1) in the
form verified against Montgomery and Vaughan Theorem 12.10 in section 8. Its conclusion is
the displayed identity with the remainder bound, `C_1` absolute but not numerically
evaluated here and `C_2` finite by (F2-up). It replaces a divergent formula with a
convergent one carrying a remainder of explicit shape in `x` and `T`, it recovers the same
zero coefficients `c(rho')`, and it fixes the admissible height range that the source
argument got wrong.

The one place a reviewer should look hardest is section 8's reduction of Montgomery and
Vaughan's error term to `C_1(x T^{-1} log^2(xT) + log x)`. That reduction is crude by
design (it throws away `min(1, x/(T<x>))` entirely), and if it is wrong, Proposition 3's
remainder is wrong with it. Everything else in the proof is elementary.

**It is not a complete repair of the sequence argument.** The payoff standard in the brief
asks for a usable error regime *with all competitors handled*. Proposition 3 supplies the
error regime; the competitors are handled only under (H-ISO). By the brief's own standard
this is therefore "a formula with valid error but insufficient for resonance", which is a
useful intermediate lemma, not a complete sequence repair. Theorem 4 is the best justified
intermediate result I can support, and it is explicitly conditional.

**The rest of the sequence argument is an unresolved attempt, and the missing input is
analytic, not bookkeeping.** Section 10 names it: an inequality bounding the full competitor
sum at height `T_n` against the witness term, for infinitely many `n`, without an isolation
hypothesis. The obstruction is that the competing set grows like `log^2 T` in weighted mass
(both bounds now established), so no fixed finite phase-approximation argument reaches it. I
do not have that input and do not claim a route to it.

Grades, per the repository's certainty ladder:

- Lemma 0, Lemma 1, section 5 polar structure, Proposition 3: *derived*, hypotheses stated,
  reviewed at `95ae36b` and again, targeted, at `3006ef2`; the follow-up cleared them.
- Theorem 4: *derived and conditional*. Its composite grade is that of its weakest step,
  which is its hypothesis (H-ISO); it is a conditional theorem and is called one.
- Section 10's unconditional variant: *unresolved attempt*, with the missing analytic input
  written out and the margin `1 + beta_0 > Theta + Theta_chi` stated exactly.
- Section 9: *measured*, float grade, one route, small finite ranges.
- Nothing here is enclosure-carrying or kernel-checked, and no claim in this file is
  numerically effective.

No novelty is claimed. No literature search for prior art on this specific repair was run;
the ingredients are standard and the write-up makes no originality claim beyond "this hunt
produced this". The only literature contact made for this revision was to the primary
source for (F1) and (F2-low), recorded in section 8.

**Review record.** Reviewed once, in the `95ae36b` form, by an independent reviewer
(`THEOREM_B_FORMULA_REVIEW.md`). That review cleared Lemma 0, the section 5 residue
computations (re-derived by an independent contour method), the structure of Theorem 4's
steps (a) to (e), the Defect 3 framing, and the attribution spot-checks it ran. It raised
five substantive objections. All five are answered in `AUTHOR_RESPONSE.md`: four were
accepted and the artifact changed; the fifth was accepted in part, with the part rejected
argued there rather than quietly dropped. The review's own open item, that the primary
source for (F1) had not been reached, is closed in section 8. The revision at `3006ef2`
received a targeted follow-up review (appended to the same file), which confirmed the
primary (F1) reduction and cleared Proposition 3 and the conditional Theorem 4, and raised
three residual findings F1 to F3 in section 10. The three exact edits answering them
(exact truncation constant, subsequence quantifiers in (MISSING), explicitness wording) were
made afterwards and checked by the coordinator; **no further reviewer run has occurred.**
The classical bound `S(T, chi) << log(q(T+2))` (used only for (F2-low), the divergence
claim) remains cited, not inspected, as stated in section 8; it is not needed for the core
formula.

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
