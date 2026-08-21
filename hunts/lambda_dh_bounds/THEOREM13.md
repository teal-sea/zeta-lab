# Theorem 13 (de Bruijn 1950) and Dobner (2020), pinned

Source pinning for WP2 (upper bound) and for the Dobner half-line structure the
lower bound leans on. Everything quoted below was read from the sources named;
the de Bruijn quotes are transcribed from the image-only publisher scan
(https://pure.tue.nl/ws/files/1769368/597490.pdf, DOI
10.1215/S0012-7094-50-01720-0) by visual page reads, as close as a visual read
allows, with math ASCII-normalized. Page numbers are the printed journal pages
(Duke Math. J. 17 (1950), 197-226). All numbers in section 6 are measured,
with backend and precision stated; nothing in this file is an enclosure.

> **Corrected 2026-08-16** (`GATE.md` closure item (a)). Section 6 asserted
> that this hunt's deformation and Dobner's "share Lambda exactly". They
> differ by a factor of exactly 4. The false sentence is preserved inside the
> correction box in section 6, together with the derivation that replaces it
> and a record of what it was routed into. Every Lambda number in this
> directory now carries its frame: this hunt sits at `s = 1/2 + iz`
> (Stopple, arXiv:1301.3158), the Newman line sits at `s = (1+iz)/2`, and
> `Lambda(that frame) = 4 Lambda(this one)`. Conversion table: `FRAME.md`.

## 1. Verbatim statements, with page numbers

### de Bruijn's standing hypotheses: condition (1.4), p. 197

> Suppose that the function F(t) of the real variable t satisfies
>
> (1.4)  F(t) integrable over -inf < t < inf; F(t) = (F(-t))*,
>        -inf < t < inf; F(t) = O(e^{-|t|^b}) for t -> +-inf, b > 2.
>
> (The * indicates the conjugate imaginary.)

### Properties (alpha) and (beta) of a strong universal factor, p. 199

> A function S(t) of the real variable t, satisfying S(t) = (S(-t))* will be
> called a strong universal factor if it joins properties (alpha) and (beta)
> below, for any function F(t) satisfying (1.4).
>
> (alpha) If the roots of (1.5) lie in a strip |Im z| <= Delta (Delta > 0),
> then those of int_{-inf}^{inf} F(t)S(t)e^{izt} dt lie in a strip
> |Im z| <= Delta_1, where Delta_1 < Delta, Delta_1 independent of F(t).
>
> (beta) If F(t) is such that, for any eps > 0, all but a finite number of
> roots of (1.5) lie in the strip |Im z| <= eps, then the function
> int_{-inf}^{inf} F(t)S(t)e^{izt} dt has only a finite number of non-real
> zeros.

(Here (1.5) is int_{-inf}^{inf} F(t)e^{izt} dt, p. 197.) Also on p. 199:

> The functions e^{gamma t^2}, gamma > 0, also turn out to have property
> (alpha), but it is doubtful whether they have property (beta).

### Theorem 10, p. 204 (the class conditions Theorem 13 references)

> THEOREM 10. Let b be a number > 2, and let the real or complex function
> F(t) be integrable over -inf < t < inf and satisfy
>
> (3.4)  F(t) = (F(-t))*  for all real values of t,
>
> (3.5)  F(t) = O(e^{-|t|^b})  (t -> +-inf).
>
> Then the trigonometric integral
>
> (3.6)  f(z) = int_{-inf}^{inf} F(t)e^{izt} dt
>
> represents a real integral function of order < 2.

### Theorem 11, p. 204 (exponential-sum factors; both zero-count forms)

> THEOREM 11. Let F(t) satisfy the conditions of the preceding theorem and
> suppose that the roots of the function S(t) = sum_{-M}^{M} a_k e^{k lambda t},
> a_k* = a_{-k}, a_M != 0, lambda > 0, lie on the imaginary axis. Then we
> have: If the roots (all but a finite number of the roots) of (3.6) lie in
> the strip |Im z| <= Delta then the roots (all but a finite number of the
> roots) of the real integral function
>
> (3.7)  int_{-inf}^{inf} F(t)S(t)e^{izt} dt
>
> lie in the strip |Im z| <= {Delta^2 - (1/2)M lambda^2}^{1/2} if
> Delta > lambda((1/2)M)^{1/2}, and are real if
> Delta <= lambda((1/2)M)^{1/2}.

### Theorem 12, p. 205

> THEOREM 12. If S(t) = prod_1^N (xi_k e^{lambda_k t} + xi_k* e^{-lambda_k t}),
> where |xi_k| = 1, lambda_k > 0, k = 1, 2, ..., N, and the roots (all but a
> finite number of the roots) of (3.6) lie in the strip |Im z| <= Delta, then
> the roots (all but a finite number of the roots) of (3.7) lie in the strip
> |Im z| <= {Max (Delta^2 - sum_1^N lambda_k^2, 0)}^{1/2}.

### The bridge sentence before Theorem 13, p. 205

> Theorem 11 proves the statements (alpha) and (beta) made in the introduction
> concerning strong universal factors. Although it will not be used in this
> paper, we shall prove here that also the functions e^{(1/2)lambda^2 t^2},
> lambda^2 > 0, have property (alpha). We do not yet know whether they have
> or have not property (beta).

### Theorem 13, p. 205 (the statement WP2 leans on)

> THEOREM 13. If F(t) satisfies the conditions of Theorem 10, and if all the
> roots of (3.6) lie in the strip |Im z| <= Delta, then all the roots of
> g(z) = int_{-inf}^{inf} F(t)e^{(1/2)lambda^2 t^2} e^{izt} dt lie in the
> strip
>
> (3.8)  |Im z| <= {Max (Delta^2 - lambda^2, 0)}^{1/2}.
>
> Proof. By Theorem 12, the roots of g_N(z) = int_{-inf}^{inf} F(t)
> (cosh lambda t/N)^{N^2} e^{izt} dt lie in the strip (3.8). Owing to
> Theorem 7 it is now sufficient to prove that g_N(z) -> g(z) uniformly in
> any finite region. Now this follows from (3.5) and from the fact that for
> mu^2 > lambda^2 we have
>
> (3.9)  e^{-(1/2)mu^2 t^2} (cosh lambda t/N)^{N^2} -> e^{-(1/2)mu^2 t^2 + (1/2)lambda^2 t^2},
>
> uniformly in -inf < t < inf. (3.9) results from the inequality
> cosh y <= e^{(1/2)y^2}, -inf < y < inf, whence
> (cosh lambda t/N)^{N^2} <= e^{(1/2)lambda^2 t^2}.

Internal consistency check on the transcription: each factor
xi e^{lambda t} + xi* e^{-lambda t} in Theorem 12 contracts the squared strip
by lambda^2, and (cosh lambda t/N)^{N^2} is N^2 such factors with parameter
lambda/N, total contraction N^2 (lambda/N)^2 = lambda^2, matching (3.8); and
(cosh(lambda t/N))^{N^2} -> e^{(1/2)lambda^2 t^2} matches the multiplier in
the statement. The transcribed exponent (1/2)lambda^2 t^2 is therefore forced
by the surrounding mathematics, not just by the visual read.

### Theorem 14, p. 205 (context: the Delta = 0 Polya case)

> THEOREM 14. Let F(t) satisfy the conditions of Theorem 10 and suppose that
> the roots of (3.6) lie in the strip |Im z| <= Delta. Let phi(z) be a real
> integral function of genus 0 or 1 (that is, a function of the type (3.1)),
> with real roots only. Then the roots of
>
> (3.10)  int_{-inf}^{inf} F(t)phi(it)e^{izt} dt
>
> lie in the strip |Im z| <= Delta also.

### Dobner, arXiv:2005.05142v2, "A proof of Newman's conjecture for the extended Selberg class"

Theorems 1 and 2 (from the paper's Section 1; text extracted from the arXiv
PDF):

> Theorem 1. For every F in S#, there is a real number Lambda_F such that all
> the zeros of xi_t^F lie on the critical line if and only if t >= Lambda_F.
>
> Theorem 2. Lambda_F >= 0 for every F in S#.

His deformation (his equations (5)-(6)): Phi_F(u) := (1/2pi)
int_{-inf}^{inf} xi^F((1+ix)/2) e^{-ixu} dx and
xi_t^F((1+iz)/2) := int_{-inf}^{inf} e^{t u^2} Phi_F(u) e^{izu} du.

Dobner's restatement of de Bruijn's Theorem 13 (his Theorem 3, Section 2):

> Theorem 3 (De Bruijn [9, Thm. 13], cf. Polya [16, Thm. 1]). Let
> phi: R -> C be an integrable function satisfying phi(u) = conj(phi(-u)) and
> phi(u) = O(e^{-|u|^b}) for some b > 2, and let
> G(z) := int_{-inf}^{inf} phi(u)e^{izu} du. For any t > 0, let
> G_t(z) := int_{-inf}^{inf} e^{tu^2} phi(u)e^{izu} du. If all the roots of
> G lie in the strip |Im z| <= Delta, then all the roots of G_t lie in the
> strip
>
> |Im z| <= max(Delta^2 - 2t, 0)^{1/2}.

S# membership conditions as Dobner states them (his Section 2): F not
identically zero and

> (i) (Dirichlet series) F has a Dirichlet series representation
> F(s) = sum_{n=1}^{inf} a_n / n^s which converges absolutely for all s with
> Re s > 1.
>
> (ii) (Meromorphic continuation) (s-1)^m F(s) is an entire function of
> finite order for some nonnegative integer m.
>
> (iii) (Functional Equation) Let m be the order of the pole of F at s = 1
> (or let m = 0 in the case where F has no pole). There exists a function
> gamma(s) of the form gamma(s) := alpha s^m (s-1)^m Q^s
> prod_{i=1}^{k} Gamma(omega_i s + mu_i) where alpha in C \ {0}, Q > 0,
> omega_i > 0, and mu_i in C with Re mu_i >= 0 such that
> xi^F(s) := gamma(s) F(s) satisfies xi^F(s) = xi^F(1-s).

No Euler product appears anywhere in (i)-(iii).

## 2. Class conditions, summarized

Theorem 13's full hypothesis set is exactly Theorem 10's conditions plus the
strip condition:

1. F integrable over the real line.
2. Hermitian symmetry F(t) = (F(-t))* (equivalently: the transform f is real
   on the real axis). For a real F this is evenness.
3. Decay F(t) = O(e^{-|t|^b}) for some b > 2.
4. All roots of f(z) = int F(t)e^{izt} dt lie in |Im z| <= Delta.

There is no positivity condition, no monotonicity condition, no condition on
the sign or shape of F beyond (1)-(3), and F is allowed to be complex-valued.
Order and genus are conclusions, not hypotheses: Theorem 10 concludes order
< 2, which is what feeds Theorems 6-9 inside the proofs.

## 3. Restatements consulted

- **Dobner 2020** (arXiv:2005.05142v2, his Theorem 3, quoted above): the
  all-zeros form, for the class "integrable, hermitian, O(e^{-|u|^b}) with
  b > 2", multiplier e^{tu^2}, contraction Delta^2 -> Delta^2 - 2t. This is
  the restatement in the hunt's own normalization.
- **Ki-Kim 2003** (J. Anal. Math. 91, 369-387; from the MathSciNet review
  MR2037415, scratchpad kikim.txt): their Theorem 2.2 is the
  all-but-finitely-many weakening for genus 1* functions:
  > Theorem 2.2. Let f(z) be a real entire function of genus 1* having order
  > not greater than 2, and, if the order is 2, let f have type alpha for
  > some alpha < inf. Let Delta >= 0 and lambda > 0 be constants such that
  > lambda alpha < 1/4. If, for each eps > 0 all but a finite number of the
  > zeros of f lie in the strip |Im z| <= Delta + eps, then e^{-lambda D^2}
  > f(z) is also of genus 1* and all but a finite number of its zeros lie in
  > the strip |Im z| < sqrt(max{Delta^2 - 2 lambda, 0}) + eps. Further, if
  > Delta^2 < 2 lambda, then all but a finite number of the zeros of
  > e^{-lambda D^2} f(z) are real and simple.
  Same contraction constant (their lambda is the hunt's t), weaker hypothesis,
  weaker conclusion. This is a separate, later theorem; it is not what
  de Bruijn's Theorem 13 says.
- **Rodgers-Tao** (arXiv:1801.05914, published intro text): with their
  H_t(z) = int_0^inf e^{tu^2} Phi(u) cos(zu) du and H_0(z) = (1/8)Xi(z/2):
  > From results of Polya [22] it is known that Ht has purely real zeroes for
  > some t then Ht' has purely real zeroes for all t' > t. De Bruijn showed
  > that the zeroes of Ht are purely real for t >= 1/2.
  (Quoted as printed, including the elided "if".) The 1/2 here is exactly
  Delta^2/2 for Delta = 1, the strip of H_0(z) = (1/8)Xi(z/2) after the z/2
  rescaling doubles Xi's strip of 1/2; see section 5.
- **Csordas-Norfolk-Varga 1988** (Numer. Math. 52, 483-497): not reachable
  through this session's proxy (Springer paywall; GDZ and EuDML lookups came
  back empty), and Ki-Kim-Lee 2009 (Adv. Math. 222) is not on arXiv. Not
  quoted; the three restatements above triangulate the same statement, one of
  them (Dobner) being the exact theorem the hunt cites for the half-line
  structure anyway.

## 4. The three questions, answered

### (a) All zeros, or all but finitely many?

**All zeros, in both hypothesis and conclusion.** Theorem 13 reads "if all
the roots of (3.6) lie in the strip |Im z| <= Delta, then all the roots of
g(z) ... lie in the strip (3.8)". The parenthetical "(all but a finite number
of the roots)" variants appear in Theorems 11 and 12 (exponential-sum
factors) but are absent from Theorem 13 as printed; the all-but-finitely-many
Gaussian-multiplier statement is Ki-Kim 2003 Theorem 2.2 (genus 1*), a
separate and later result. Dobner's Theorem 3 restates de Bruijn's Theorem 13
in the all-zeros form.

Normalization and conversion: de Bruijn's multiplier is e^{(1/2)lambda^2 t^2}
and his conclusion strip is {Max(Delta^2 - lambda^2, 0)}^{1/2}, so all zeros
are real as soon as lambda >= Delta. Writing the multiplier as e^{t u^2}
(the hunt's and Dobner's normalization) sets t = lambda^2/2, the contraction
becomes sqrt(max(Delta^2 - 2t, 0)), and the all-real threshold is

    t >= Delta^2 / 2.

**Consequence for the hunt: kill condition 1 of MISSION.md is not triggered.
The upper bound route Lambda_DH <= Delta^2/2 stands**, conditional on WP2
deciding that all zeros of H_0 = Xi_DH lie in |Im z| <= Delta (that is
WP2's strip computation, not this file's claim).

### (b) Positivity of Phi?

**No positivity is required anywhere.** The complete hypothesis list is
quoted in section 1: integrability, hermitian symmetry (3.4), decay (3.5)
with b > 2, and the strip. F may even be complex-valued. This matches the
expectation recorded in the mission: realness/evenness plus O(e^{-|t|^b})
decay with b > 2 plus integrability suffice.

### (c) Monotonicity: once real, always real?

de Bruijn states no numbered monotonicity theorem, but the Delta = 0 case of
Theorem 13 delivers it immediately, and the hypotheses survive the
deformation. Concretely: suppose all zeros of
H_{t0}(z) = int e^{t0 u^2} Phi(u) e^{izu} du are real, with Phi satisfying
Theorem 10's conditions for some b > 2. The deformed integrand
Phi_{t0}(u) = e^{t0 u^2} Phi(u) is still integrable, still hermitian, and
still O(e^{-|u|^{b'}}) for any 2 < b' < b (for |u| large,
t0 u^2 - |u|^b <= -|u|^{b'}), so Theorem 13 applies to Phi_{t0} with
Delta = 0 and gives: all zeros of H_t real for every t > t0, since
{Max(0 - lambda^2, 0)}^{1/2} = 0. Rodgers-Tao attribute the same
monotonicity to Polya (their [22]; quote in section 3); either attribution
suffices and both predate Dobner.

What this buys the lower-bound logic: an off-line zero of H_{t1} plus
Theorem-13 monotonicity alone already gives the weak bound
Lambda_DH >= t1 (no t <= t1 can be real-rooted, else t1 would be), with no
appeal to Dobner. The strict inequality Lambda_DH > t1 still uses Dobner's
Theorem 1, because his half-line {t : all zeros real} = [Lambda_F, inf) is
closed at the left end: without closedness the real-rooted set could be
(t1, inf) and Lambda_DH would equal t1. So: weak lower bound independent of
Dobner, strictness via Dobner, exactly as the vocabulary contract's
"decided modulo Dobner's Theorem 1" phrasing anticipated.

**How Dobner's theorem reaches this frame** (added 2026-08-16; the earlier
route ran through section 6's false sentence and is corrected there). His
Theorem 1 is a statement in *his* frame: {t : xi_t^F all real} =
[Lambda_F, inf), closed at the left. Section 6 derives
xi_t^F((1+iz)/2) = H_{t/4}(z/2), and t -> t/4 is an increasing bijection of
the real line, so it carries closed half-lines to closed half-lines. Hence
{t : H_t all real} = [Lambda_F/4, inf), also closed at the left, which is
everything the strictness argument needs. What does *not* transfer is the
value: Lambda_F = 4 Lambda_DH. The strictness of the lower bound was never at
risk from the error; only the number's label was.

## 5. Hypothesis check for Phi_DH

Phi_DH(u) = 4 e^{3u/2} sum_{n>=1} n a_n exp(-pi n^2 e^{2u}/5), with a_n the
period-5 coefficients (1, kappa, -kappa, -1, 0) and kappa real, derived in
zeta/epstein.py by a linear solve on every call (kappa = 0.2840790438...,
pinned by tests/test_epstein.py::test_kappa_matches_pinned_reference and
re-derived independently at four base points).

1. **Realness.** Every term is real (kappa real, exponentials real), so
   Phi_DH: R -> R. Hermitian symmetry (3.4) therefore reduces to evenness.
2. **Evenness = the functional equation in disguise.** Three lines: the
   completed function F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s) satisfies
   F(s) = F(1-s) (that identity is what defines kappa in zeta/epstein.py;
   measured defect < 1e-25 in
   tests/test_epstein.py::test_functional_equation_defect_below_1e25).
   Setting Xi_DH(z) = F(1/2 + iz) gives
   Xi_DH(-z) = F(1/2 - iz) = F(1 - (1/2 + iz)) = F(1/2 + iz) = Xi_DH(z),
   so Xi_DH is even. Phi_DH is (1/(2pi) times) the Fourier transform of
   Xi_DH restricted to the real line, and the Fourier transform of an even
   function is even; conversely Phi even forces Xi even, which at
   s = 1/2 + iz is exactly F(s) = F(1-s). Measured in-tree:
   hunts/flow_repair/NOTES.md records the raw-series evenness defect,
   relative <= 4.2e-51 for |u| <= 0.5 at dps 50.
3. **Decay, dominated explicitly.** For u >= 0,
   |Phi_DH(u)| <= 4 e^{3u/2} e^{-(pi/5)e^{2u}} S(u) with
   S(u) = sum_n n exp(-pi(n^2-1)e^{2u}/5) (using |a_n| <= 1), and
   S(u) <= S(0) = 1.3237 (measured, mpmath dps 30). The margin
   g(u) = (pi/5)e^{2u} - (3/2)u - u^3 is >= 23.30 at u = 2 and increasing on
   [2, 30] (measured on a 201-point grid, dps 30; calibration.json,
   phi_dh_decay_domination), so |Phi_DH(u)| = O(e^{-|u|^3}): condition (3.5)
   holds with b = 3 > 2, and by evenness on both tails.
4. **Integrability.** Continuous on R plus the b = 3 tail bound: integrable.
5. **Order/genus.** Not hypotheses; Theorem 10 concludes order < 2 for
   H_0 = Xi_DH. No positivity claim is made or needed (see 4b).

### S# membership of DH (for Dobner's Theorems 1-2)

- (i) Absolute convergence for Re s > 1: |a_n| is periodic
  (1, kappa, kappa, 1, 0) and bounded by 1, so
  sum |a_n| n^{-sigma} <= zeta(sigma) < inf for sigma > 1; measured partial
  sums (mpmath nsum, dps 30): 1.7809 at sigma = 1.05, 1.4131 at 1.5,
  1.2154 at 2.0 (calibration.json, sharp_class_dirichlet_sum).
- (ii) Entire of finite order, m = 0: the period-5 coefficient sum is
  1 + kappa - kappa - 1 + 0 = 0, so f has no pole at s = 1
  (tests/test_epstein.py::test_dh_f_is_entire_no_pole_at_1).
- (iii) Functional equation of the S# shape: gamma(s) =
  (pi/5)^{-(s+1)/2} Gamma((s+1)/2) = alpha Q^s Gamma(omega s + mu) with
  alpha = (pi/5)^{-1/2}, Q = (5/pi)^{1/2} > 0, omega = 1/2, mu = 1/2
  (Re mu >= 0), m = 0, and F(s) = gamma(s) f(s) = F(1-s). The gamma factor
  is derived and pinned in zeta/epstein.py (the docstring records that the
  completing factor is Gamma((s+1)/2), not Gamma(s/2)) and exercised by
  tests/test_epstein.py (functional-equation and completed-function tests).
- No Euler product is required by S#, and DH genuinely has none:
  a_6 = a_1 = 1 while a_2 a_3 = -kappa^2
  (tests/test_epstein.py::test_no_euler_product_coefficients_not_multiplicative).

So Dobner's Theorems 1-2 apply to DH: Lambda_DH exists, the real-rooted set
is the closed half-line [Lambda_DH, inf), and Lambda_DH >= 0.

## 6. Normalization dictionary and numeric calibration

### Dictionary

| Frame | Multiplier | Contraction | All-real threshold |
|---|---|---|---|
| de Bruijn Thm 13 | e^{(1/2)lambda^2 t^2} | Delta^2 -> Delta^2 - lambda^2 | lambda >= Delta |
| Dobner Thm 3 / hunt H_t | e^{t u^2} (t = lambda^2/2) | Delta^2 -> Delta^2 - 2t | t >= Delta^2/2 |
| Ki-Kim 2003 Thm 2.2 | e^{-lambda D^2} operator (their lambda = t) | Delta^2 -> Delta^2 - 2 lambda | all-but-finitely-many only |
| Newman-Wu 2020 Thm 7 | e^{lambda u^2 / 2} (lambda = 2t) | Delta^2 -> Delta^2 - lambda | lambda >= Delta^2, i.e. t >= Delta^2/2 |

**This table is about the multiplier, and only about the multiplier.** All
four rows say the same thing once the kernels are matched, and all four are
frame-free: the threshold t >= Delta^2/2 is a statement about the ratio
t/Delta^2, which the z-rescaling below leaves invariant. The *other* axis of
normalization, where the critical line is parameterised, is a separate
question and is the subject of the next two subsections and of `FRAME.md`.
Confusing the two axes is what produced the correction below.

### Dobner's frame is not this frame: the factor is 4

> **Correction, 2026-08-16** (`GATE.md` closure item (a)). This section
> previously ended its dictionary with the sentence
>
> > Dobner's deformation xi_t^F((1+iz)/2) = int e^{tu^2} Phi_F(u) e^{izu} du
> > is the hunt's H_t up to the constant factor 2 (Phi even turns the
> > full-line integral into 2 int_0^inf ... cos(zu) du), so the two share
> > zeros and share Lambda exactly.
>
> **The factor 2 is right and the conclusion is false.** The substitution
> also carries z -> z/2, which the z-rescaling paragraph of this same
> section (kept unchanged, at the end) already said moves t quadratically:
> the false sentence contradicted the paragraph it sat next to. The correct
> statement is Phi_F(u) = Phi_DH(2u) and xi_t^F((1+iz)/2) = H_{t/4}(z/2), so
> Lambda(Dobner) = 4 Lambda(hunt). The sentence is kept here rather than
> deleted because two claims in this directory were routed through it and a
> reader is entitled to see what they were routed through.
>
> **What it would have caused, and what it did cause.** It did *not* damage
> the strictness of the lower bound: t -> t/4 is an increasing bijection of
> the time axis, so Dobner's closed half-line {t : all zeros real} =
> [Lambda_F, inf) transfers to this frame as a closed half-line, and section
> 4c's use of it stands unaltered. What it would have licensed is quoting
> Dobner's Lambda_F for DH as this hunt's number, which is four times too
> large. What it did cause is one file down: `NOVELTY.md` calibrated the
> upper bound 0.4006 against the zeta record 0.22 and 1/2 with no
> conversion, which are 0.055 and 1/8 here, so the comparison flattered the
> hunt by exactly that factor and, worse, concealed that in the common frame
> the DH lower bound 0.2304 sits *above* the best published upper bound for
> zeta. Both are repaired; the full conversion table is `FRAME.md`.

**The derivation.** Dobner's (5) and (6), quoted in section 1, are

    Phi_F(u) := (1/2pi) int_{-inf}^{inf} xi^F((1+ix)/2) e^{-ixu} dx,
    xi_t^F((1+iz)/2) := int_{-inf}^{inf} e^{t u^2} Phi_F(u) e^{izu} du.

His argument is (1+ix)/2 = 1/2 + i x/2, while this hunt's is 1/2 + i z. So
xi^F((1+ix)/2) = Xi_DH(x/2), and by the inversion that defines Phi_DH from
Xi_DH,

    Phi_F(u) = (1/2pi) int_{-inf}^{inf} Xi_DH(x/2) e^{-ixu} dx
             = (1/pi)  int_{-inf}^{inf} Xi_DH(y) e^{-2iyu} dy   (y = x/2)
             = Phi_DH(2u).

Now substitute u = v/2 in his (6), using that Phi_F is even:

    xi_t^F((1+iz)/2) = 2 int_0^inf e^{t u^2} Phi_DH(2u) cos(zu) du
                     = int_0^inf e^{(t/4) v^2} Phi_DH(v) cos((z/2) v) dv
                     = H_{t/4}(z/2).

At matched arguments the two deformations are the *same function*; what
differs is the label on the time axis. Since t -> t/4 is an increasing
bijection,

    xi_t^F has only real zeros  <=>  H_{t/4} has only real zeros
                                <=>  t >= 4 Lambda_DH(this frame),

so

    Lambda(Dobner frame) = 4 * Lambda(this frame),
    Delta(Dobner frame)  = 2 * Delta(this frame).

**Measured, this session, by code sharing nothing with `instrument.py`**
(scratchpad `frame_check.py`, `frame_deform2.py`; kappa from a linear solve
on F(s) = F(1-s), f from Hurwitz zeta at r/5, and Dobner's Phi_F computed
only from his own (5) by direct Fourier inversion, never by substituting
Phi_DH(2u)):

| u | Phi_F(u) from Dobner (5), dps 40 | rel. vs Phi_DH(2u) | rel. vs Phi_DH(u) |
|---|---|---|---|
| 0.15 | 2.032945249046710636167 | 6.2e-24 | 0.0919 |
| 0.4 | 0.5911191932630095506773 | 2.9e-23 | 0.674 |
| 0.7 | 0.001063508494264118824889 | 7.2e-21 | 0.9988 |

and the deformation identity itself, checked end to end at four (z, t) with
Phi_F again taken only from (5):

| z | t | xi_t^F((1+iz)/2) from Dobner (5)+(6) | rel. vs H_{t/4}(z/2) | rel. vs H_t(z), which the false sentence licensed |
|---|---|---|---|---|
| 1 | 1/5 | 1.411782501208473636314 | 7.7e-15 | 0.0484 |
| 3 | 2/5 | 1.159034557111109238044 | 2.6e-15 | 0.567 |
| 7/10 | 36/625 | 1.420001737196666980069 | 7.2e-15 | 0.0280 |
| 2 + 0.3i | 1/4 | 1.314420783825719854807 - 0.040120424537588350713i | 9.1e-15 | 0.270 |

(mpmath dps 28; Phi_F on 50 composite Gauss-Legendre nodes, each value a
separate Fourier inversion of Xi_DH(x/2) out to x = 80; the node set's own
quality against the analytically known 2 int_0^inf Phi_F cos(3u) du =
Xi_DH(3/2) is 7.6e-16, which is the floor for this table. The t = 0 endpoint
xi_0^F((1+iz)/2) = Xi_DH(z/2) reproduces to 7.5e-15, 7.6e-16 and 1.6e-12 at
z = 1, 3, 9.) The correct conversion holds to 15 digits; the reading the false
sentence licensed is wrong in the second significant digit.

**Neither frame is more correct.** This one is Stopple's, published and
refereed (arXiv:1301.3158, his equation (1) and his Xi_t(x, chi) at D = 5);
that one is Dobner's, Newman's, Rodgers-Tao's and Polymath 15's. What is not
allowed is a number without its frame. See `FRAME.md`.

### z-rescaling (unchanged)

z-rescaling scales t quadratically: if Htilde_0(z) = c H_0(a z), i.e.
Phitilde(u) = (c/a) Phi(u/a), then Htilde_t(z) = c H_{a^2 t}(a z). Strips
scale by 1/a, times by a^2... so Lambda/Delta^2 is invariant. Zeta's
convention H_0(z) = (1/8) Xi(z/2) has a = 1/2: Xi's strip 1/2 becomes
Delta = 1 and the bound Delta^2/2 = 1/2 is exactly de Bruijn's classical
"real for t >= 1/2" (Rodgers-Tao quote, section 3). DH needs no conversion:
flow_repair measured H_0 = c Xi_DH(a z) with |c - 1| = 4.2e-42,
|a - 1| = 2.0e-18 (hunts/flow_repair/NOTES.md), so (c, a) = (1, 1), Delta is
taken directly as sigma_0 - 1/2 (scouted float value
sigma_0 = 1.39513615823511, giving Delta^2/2 = 0.400634; deciding that strip
is WP2's job, not this file's).

*(Read the last four words of that paragraph narrowly. "DH needs no
conversion" says only that H_0 equals Xi_DH with no constant and no
z-rescaling, so Delta may be read straight off the s-plane strip. It does
**not** say that this frame agrees with Dobner's; a = 1/2 is exactly the
rescaling that separates them, and it is the same a that turns zeta's
Delta = 1/2 into Delta = 1 two sentences earlier.)*

### Calibration of the factor Delta^2/2 (derived, never recalled)

Script: calibrate_theorem13.py in this directory; raw output:
calibration.json. All numbers measured (mpmath/numpy floats, one route each;
precision per block). Route 0 first checks the frame: the e^{tu^2} multiplier
under the integral and the finite polynomial series
sum_k (-t)^k/k! p^{(2k)} both satisfy the backward heat equation
dG/dt = -d2G/dz2 (measured residual 0 at dps 30 for the quadrature route;
4.2e-6 for float64 central differences at h = 1e-5, consistent with the h^2
truncation), which is what licenses calibrating the integral multiplier with
polynomials.

- **Route A, bare conjugate pair** p(z) = z^2 + Delta^2, evolved by the exact
  finite series, landing time by 60-iteration bisection (float64, imag
  tolerance 1e-10):

  | Delta | t* measured | Delta^2/2 | 2 t*/Delta^2 |
  |---|---|---|---|
  | 0.6 | 0.18 | 0.18 | 1.0 |
  | 0.895136 | 0.40063422924800 | 0.400634229248 | 1.0000000000000 |
  | 1.2 | 0.72 | 0.72 | 1.0 |

  The middle row is the DH strip's own Delta: the landing lands on the
  mission's scouted 0.400634 to all printed digits. The factor is 1/2
  exactly for the bare pair: a claimed factor Delta^2/8 would be violated
  (t* is four times later) and 2 Delta^2 would be slack by a factor 4.

- **Route B, cosine polynomial** H_0(z) = cos z + c, flowed to
  e^t cos z + c (dps 30; Delta measured as |Im| of the zero found by
  findroot near pi + i, not recalled; the complex pair tracked by Newton
  continuation, landing by 60-iteration bisection):

  | c | Delta measured | t* measured | Delta^2/2 | 2 t*/Delta^2 |
  |---|---|---|---|---|
  | 2.0 | 1.3169578969 | 0.7254724944 | 0.8671890511 | 0.8366 |
  | 1.05 | 0.3149247566 | 0.0487901642 | 0.0495888012 | 0.9839 |
  | 1.001 | 0.0447176336 | 0.0009995003 | 0.0009998334 | 0.99967 |

  The ratio is always <= 1 (Theorem 13 is an upper bound on the landing
  time) and climbs to 1 as c -> 1+: the constant 1/2 is sharp in this
  family, so no smaller factor (in particular Delta^2/8) can be a theorem,
  and any larger one (2 Delta^2) is not sharp.

- **Route C, pair plus distant real zeros** (z^2 + 1)(z^2 - A^2) (float64,
  bisection as in A): 2 t*/Delta^2 = 0.9329, 0.99506, 0.99980 for
  A = 5, 20, 100. Repulsion from the extra real zeros only accelerates the
  landing, and the bound is approached as the spectators recede: consistent
  with Delta^2/2 as a sharp universal threshold.

## 7. Verdict

**The upper-bound route stands.** de Bruijn (1950) Theorem 13 (p. 205) is
the all-zeros form in both hypothesis and conclusion; its only class
conditions are Theorem 10's (p. 204): integrability, hermitian symmetry,
O(e^{-|t|^b}) decay with b > 2, no positivity; Phi_DH satisfies every one of
them (section 5); the strip-to-time factor converts to t >= Delta^2/2 in the
hunt's e^{tu^2} normalization and was re-derived numerically on three
families (section 6), landing at Delta^2/2 exactly on the bare pair and
sharply in the c -> 1 cosine limit. Kill condition 1 of MISSION.md is not
triggered. The remaining load on WP2 is the strip itself: decide that all
zeros of Xi_DH lie in |Im z| <= sigma_0 - 1/2, with interval arithmetic on
both backends. The lower-bound logic gains a Dobner-independent weak form
(section 4c); strictness of Lambda_DH > t1 still cites Dobner's Theorem 1,
whose S# hypotheses DH meets (section 5), applied through the conversion
t -> t/4 derived in section 6 rather than through the frame identification
that section used to assert.

**And the verdict carries a frame.** Delta^2/2 = 0.4006343708899557 is the
threshold in the normalization s = 1/2 + iz (Stopple's, arXiv:1301.3158). In
the normalization s = (1+iz)/2 (de Bruijn as usually quoted, Newman,
Rodgers-Tao, Polymath 15, Dobner) the same threshold is
1.6025374835598228, because Delta doubles there. Neither is more correct;
a number without its frame is what is wrong. See `FRAME.md`.

> **Update 2026-08-18.** The two numbers above are the coefficient-domination
> ones and are superseded as the headline, though not as arithmetic: they are
> still what Delta = 0.895136... gives in the two frames. The strip constant
> was sharpened in-tree on 2026-08-18 to Delta = 0.62036249819, giving
> Delta^2/2 = 0.19242481458026887663805 narrow and 0.7696992583210755065522
> wide (`STRIP2.md`). **Nothing in this file changes on account of it**:
> Theorem 13 is the engine either way, its transcription and hypothesis checks
> are unaffected, and the frame point this paragraph makes is unaffected. The
> conversion t -> t/4 of section 6 is what carries the new constant between
> the frames, exactly as it carried the old one.
