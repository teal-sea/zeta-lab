# Can Theorem B's Landau-oscillation sequence be made constructive?

**Scope correction, 2026-09-12.** The proposed absolutely convergent zero
expansion in section 3 is not established: its coefficient
\((\rho-1)/(2\rho(\rho+1))\) decays as \(1/|\operatorname{Im}\rho|\),
not its square. The accompanying dyadic count also uses a unit-height
zero count outside its range. A controlled truncated or smoothed expansion
is required before the later constructive resonance steps can be used.
See `FAREY_BASELINE_REPAIR.md`, Appendix B. The nonconstructive Theorem B
in `RESULTS.md` and `REFEREE.md` does not depend on this construction.

RESULTS.md Section 18 proves Theorem B, E(N) = Omega(N^{1 + 2 Theta_chi - eps}), in the
case Theta < Theta_chi <= 1 by a pole-vs-boundedness contradiction on the Mellin
transform of I(x) = sum_{m <= x} Lambda(m) chi(m) (x/2 - m), concluding "there is an
unbounded sequence" of N with |I(N)| >= N^{1 + Theta_chi - eps'}, without exhibiting it
(REFEREE.md Section 4 re-derives the same argument independently and reaches the same
non-constructive conclusion). This note asks whether the classical machinery behind that
argument (Ingham ch. V; Montgomery-Vaughan Section 15.1) can be adapted to name the
sequence, or at least bound the gaps between its members. Short answer: yes, in a clean
special case, with an explicit and easily computed gap; no, in general, and the two
places it fails are different in kind. Nothing here bears on RH, and nothing here reopens
or changes what Section 18 already proves.

## 1. What is non-constructive about the existing proof, precisely

The proof's structure is: assume I(x) = O(x^alpha) for all x (alpha = 1 + Theta_chi -
eps'); this makes the Mellin transform integral_1^infty I(x) x^{-s-2} dx converge
absolutely and hence be holomorphic on Re(s) > alpha - 1, contradicting the known pole at
a zero rho' of L(s, chi) with Re(rho') > alpha - 1. Therefore the assumption is false:
NOT [for all x, |I(x)| <= C x^alpha], for every constant C. Negating a universally
quantified O(x^alpha) statement gives exactly an existence statement -
limsup_{x -> infty} |I(x)|/x^alpha = infinity - and nothing else: no rate, no location,
no relation between two members of the witnessing set. The step from "not O(x^alpha)" to
"an unbounded sequence" is pure real analysis and carries no information beyond what
already is in the negated statement. This is why the proof, honestly written, stops at
existence: the complex-analytic content (the pole) is used only to rule out the
possibility of the bound holding everywhere, not to build anything.

This differs from the classical Landau theorem for Dirichlet series with non-negative
coefficients, which is not what is invoked here and could not be: chi(m) changes sign, so
Lambda(m) chi(m) is not sign-definite, and RESULTS.md Section 18 says as much ("no sign
condition on the coefficients is needed"). The non-negative-coefficient theorem is
stronger - it identifies the abscissa of convergence itself as a singularity, which is
extra structure a signed series does not offer for free. What is used instead is the weak
form (call it the contradiction form): a Dirichlet-type transform that converges
absolutely on a half-plane is holomorphic there, so a known singularity to its right
bounds the abscissa of convergence from below. That is all the weak form gives, and it is
an if-then about all x, not a statement about any specific x.

## 2. Two different obstructions, not one

Turning this into a genuine construction runs into two separate difficulties. They are
worth naming apart because they have different characters and, as far as this note gets,
different prognoses.

**Obstruction A - locating a witness zero at all.** For a target eps' > 0, the proof uses
"the definition of supremum" to get some zero rho' with Re(rho') > Theta_chi - eps'; it
says nothing about the height |Im(rho')| at which this zero sits. Making this effective
would need a height T = T(eps') such that a zero with Re > Theta_chi - eps' is guaranteed
to already appear among |Im(rho')| <= T. That is an effective zero-density statement
close to the supremum itself - not a zero-free region (which bounds real parts from
above) but its converse, a guarantee that the real parts actually approach the supremum
by a certain height. No such statement is available for L(s, chi_3), and none is derived
here.

**Obstruction B - disentangling a witness from its neighbors.** Granted a specific zero
rho'_0, building an explicit sequence from it (Section 3-4 below) requires that no other
zero within the same relevant height window compete with it in size while carrying an
incompatible phase. The only tool on hand for counting nearby zeros is the O(log T)
density bound already used throughout this hunt (Theorem A's (F2)); it bounds how many
competitors there are but says nothing about how close in real part they can be. When
several zeros tie or cluster near the extremal real part within reach of a single
resonance construction, isolating any one of them needs simultaneous control of several
independent phases at once, which (Section 5) is a Kronecker-type Diophantine
approximation problem with no known effective bound.

Obstruction A is about whether a witness exists early enough to exhibit; obstruction B is
about whether, once handed a witness, its signal can be pulled out from what is around
it. Section 3-4 show obstruction B is not fatal when the witness is isolated; Section 5
shows it is real when it is not, and that resolving it is not just a matter of more work
with the tools already in this hunt.

## 3. An explicit formula for I(x), by the machinery already trusted here

The pole-contradiction step throws away the actual identity the Mellin transform carries
and only uses that it has a pole. Recovering the identity is mechanical and does not need
anything beyond what RESULTS.md already establishes for two structurally identical
objects:

- Section 15's H_chi(N): a Riesz mean with denominator s(s+1), shown there to have an
  UNCONDITIONALLY convergent zero-free asymptotic H_chi(N) = c_H N + O(N^{3/4}) via a
  contour shift, using convexity bounds on L(s, chi) and L(1+s, chi) that come straight
  from the functional equation.
- Theorem A's Step 2 (Section 17): a contour shift on -L'/L(w - rho, chi), truncated at
  height T_rho, using (F3) (the log-growth bound on L'/L(s, chi) for -1 <= sigma <= 2, and
  away from trivial zeros for sigma <= -1/4 via the functional equation) to control the
  horizontal and left vertical segments explicitly, term by term.

F(s) = integral_1^infty I(x) x^{-s-2} dx = -(L'/L)(s, chi) (1-s) / (2 s (s+1)) has exactly
the same s(s+1) denominator as H_chi's Dirichlet series, and its numerator is governed by
the same L'/L(s, chi) that (F3) already bounds on every relevant vertical line (the two
ranges -1 <= sigma <= 2 and sigma <= -1/4 together cover the whole plane away from the
trivial-zero poles, by the functional equation reflecting one range into the other). At a
simple zero rho' of L(s, chi), the residue of F(s) x^{s+1} is x^{rho'+1} (rho'-1) /
(2 rho'(rho'+1)) (matching REFEREE.md Section 4's residue computation). Because the extra
1/(s(s+1)) supplies two more powers of decay than a first Mellin transform would, and
because (F2)'s O(log T) zero density per unit height makes sum 1/|rho'(rho'+1)| converge
(each term is O(1/gamma'^2), and sum over dyadic ranges of O(log T) terms of size 1/T^2
converges), the zero-sum representation of I(x) converges absolutely, by the same
argument Section 15 already carries out for H_chi(N)'s D(s)/(s(s+1)). This gives, for
x >= 1 and away from the countable set of x where I jumps,

    I(x) = mu_1 x + mu_0 + sum_{rho'} x^{rho'+1} (rho'-1) / (2 rho'(rho'+1)),         (*)

mu_1, mu_0 the explicit residues of F(s) x^{s+1} at s = 0 and s = -1, and the sum over all
non-trivial and trivial zeros of L(s, chi_3), absolutely convergent, no truncation and no
error term. (If instead one prefers to avoid re-deriving absolute convergence in full and
stay entirely inside what Section 17 already proves rigorously, the truncated version
with an explicit O(x^{1+eta} log^2(xT)/T + ...) error term, built exactly as Theorem A's
Step 2 builds one for -L'/L(w - rho, chi), suffices for everything below; the argument
does not need (*) in its strongest form, only that the tail beyond a chosen height T is
smaller than the resonance term by a computable margin, and either route gives that.)

Either way, this is the part of "making Landau's argument constructive" that has a clean
answer: the identity behind the contradiction is recoverable in full, by machinery this
hunt already trusts elsewhere, no new estimate is required, and neither obstruction A nor
B appears yet - they appear only in how (*) gets used.

## 4. The resonance construction, and its explicit gap, when the witness is isolated

Since chi_3 is real-valued, L(s, chi_3) has real coefficients, so its non-real zeros come
in conjugate pairs rho'_0 = beta_0 + i gamma_0, conj(rho'_0) = beta_0 - i gamma_0 sharing
the same real part. Summed together their two terms in (*) combine to a real quantity:

    x^{1+rho'_0}(rho'_0-1)/(2rho'_0(rho'_0+1)) + x^{1+conj(rho'_0)}(...)
        = x^{1+beta_0} |c_0| cos(gamma_0 log x + phi_0),

writing c_0 = (rho'_0 - 1) / (rho'_0 (rho'_0 + 1)) = |c_0| e^{i phi_0}, an explicit
complex number once rho'_0 is known (elementary to bound above and below given
beta_0 in (1/2, 1], gamma_0 > 0). Choosing

    x_n = exp((2 pi n - phi_0) / gamma_0),    n = 1, 2, 3, ...

makes cos(gamma_0 log x_n + phi_0) = 1 exactly, i.e. this single term equals its own
maximum modulus x_n^{1+beta_0} |c_0|. This sequence is completely explicit given rho'_0,
and its consecutive members have an explicit, computable multiplicative gap

    x_{n+1} / x_n = exp(2 pi / gamma_0),

with no dependence on n: the higher the witness zero, the tighter this gap (for the low
zeros of L(s, chi_3) found in Section 6 below, gamma_0 ~ 8.04 gives a gap of about 2.19;
gamma_0 ~ 57.6 gives about 1.12 - see Section 6). This is the "gaps between successive
members" the task asks whether can be bounded: whenever a single witness zero is in hand
and dominates its window (next paragraph), the gap is not just bounded but named in
closed form.

For this to be a genuine lower bound on I(x_n) and not just on one term of (*), the rest
of (*) at x = x_n must not cancel it. Split (*) at x_n into the rho'_0-pair term (size
x_n^{1+beta_0}|c_0| by construction), the main term mu_1 x_n + mu_0 (linear, negligible
against x_n^{1+beta_0} once beta_0 > 0, which it is), a tail |gamma'| > T for T a growing
function of n (T = x_n^delta for small fixed delta > 0 is enough, by the convergence rate
behind (*) or by Section 17's Step-2-style truncation error, either way = o(x_n^{1+beta_0
- eps''}) for T growing like any positive power of x_n), and the zeros with |gamma'| <= T
other than rho'_0's own pair. That last group is the delicate one: by (F2) there are
O(log T) = O(log x_n) many of them, each contributing at most x_n^{1+Theta_chi} |c(rho')|
in modulus. If rho'_0 is a strict, isolated maximizer of Re(rho') among zeros with
|gamma'| <= T - meaning every other such zero has real part at most beta_0 - g for some
fixed gap g > 0 - their combined modulus is O(x_n^{1+beta_0-g} log x_n), which is
o(x_n^{1+beta_0-eps}) for eps < g. In that case (*) gives, along the explicit sequence
x_n with the explicit gap above,

    I(x_n) = |c_0| x_n^{1+beta_0} (1 + o(1)),

a genuine, fully constructive, fully explicit oscillation result, transferable to
integers N_n = round(x_n) at a cost O(N_n) (Section 18's own "I(x) - I(N) = (x-N)P(N)/2 =
O(N)" step, unchanged) which is negligible against the same power. No contradiction
argument, no appeal to a definition of supremum, and no non-constructive step remains in
this case.

## 5. Where the isolated case fails, and why it is not just more of the same work

The catch is the isolation hypothesis - "no competing zero within reach of the same
resonance window" - and it is not available in general, for two compounding reasons.

First (obstruction A, restated for this construction): rho'_0 has to actually be
produced, at a known height, with Re(rho'_0) within the target eps' of Theta_chi. Nothing
in this hunt's tools, or in the standard zero-density literature for Dirichlet
L-functions, supplies a height at which such a zero is guaranteed to appear; the
classical zero-free regions cited elsewhere in this hunt (F5, and its analogue for
L(s, chi)) bound real parts from above, which is the wrong direction for this purpose.

Second (obstruction B), even granting rho'_0: the isolation hypothesis can fail, and
nothing rules it out. If instead there are two or more zeros rho'_0, rho'_1, ... within
the truncation window whose real parts are all within the eps-margin of Theta_chi (ties
or near-ties at comparable height are not excluded by (F2), which only counts, it does
not separate), then choosing x_n to align rho'_0's phase does not control the others':
their phases gamma'_j log x_n + phi_j walk around the circle at a rate set by the ratio
gamma'_j / gamma_0, generically equidistributing rather than cooperating. Recovering a
lower bound in this case is the classical multi-zero oscillation problem (this is what
Ingham ch. V's and Landau's own fuller oscillation arguments, and the standard treatment
of Omega_{+-} results for psi(x) - x, actually spend their effort on), and the standard
tool for it is Kronecker's theorem on simultaneous Diophantine approximation: if the
ratios gamma'_j / gamma_0 (finitely many, since the window is bounded) are irrational and
suitably independent, there exist n making all the relevant phases simultaneously close
to any target - in particular close enough to not cancel the rho'_0 contribution. This
settles existence again, which is not new information (existence was already the
starting point), but it does not settle constructivity: Kronecker's theorem, in its
classical form, gives no bound on how large such n must be. An effective version would
need a simultaneous Diophantine approximation rate for the specific ordinates gamma'_j /
gamma_0, i.e. a quantitative irrationality measure for those ratios. No such measure is
known for the ordinates of any single L-function's zeros, let alone across two zeros of
L(s, chi_3) - this is the same order of difficulty as the (open, believed, unproved)
linear independence over Q of the ordinates of zeta's zeros. So in the presence of
competing zeros, the gap between successive members of any resulting sequence is
unbounded by anything this note can supply, and this is not a matter of applying the
tools already in this hunt more carefully; it needs an input (an effective simultaneous
approximation bound for L-function zero ordinates) that does not exist in the literature.

## 6. What is visible at low height for L(s, chi_3), and an illustrative gap

`landau_zero_probe.py` locates the zeros of L(s, chi_3) up to height 60 by scanning
|L(1/2 + it, chi_3)| for local minima and refining each with a complex Newton solve
(mpmath, 30 decimal digits) started on the critical line but free to move off it; results
in `results_landau_zero_probe.json`. It finds 21 zeros, at ordinates 8.04, 11.25, 15.70,
18.26, 20.46, 24.06, 26.58, 28.22, 30.75, 33.90, 35.61, 37.55, 39.49, 42.62, 44.12, 46.27,
47.51, 52.50, 54.19, 55.64, 57.58, every one landing at Re = 0.5 to the residual precision
of the solve (|L| below 10^-14 on the line, versus 0.06-0.5 moved 0.05-0.1 off it). This
is a check at low height, not a proof about all height, and it says nothing about
Theta_chi - but it means that, as of this scan, there is no computationally exhibited
witness for Theta_chi > Theta anywhere near the range this note could search, consistent
with (not evidence for or against) GRH for this L-function. Taking the lowest and
highest zeros found as stand-ins for what a witness's height might look like, the
explicit resonance gap exp(2 pi / gamma_0) from Section 4 would be about 2.19 for
gamma_0 ~ 8.04 and about 1.12 for gamma_0 ~ 57.58: the gap shrinks as the witness rises,
so a witness forced (by obstruction A) to appear only at very large height would, if one
were ever exhibited, still hand back a comparatively dense and cheaply computable
sequence - the expense is entirely in the exhibiting, not in what the exhibited zero
would deliver.

## 7. What this does and does not settle

**Achievable.** The pole-contradiction step can be replaced by an actual identity (*),
recovered from tools this hunt already trusts (Section 15's Riesz-mean argument, Section
17's contour-shift-with-truncation-error argument), with no new estimate needed. Given an
isolated witness zero - one whose real part strictly exceeds every other zero's in the
relevant height window by a fixed margin - the resulting oscillation is fully
constructive: an explicit sequence x_n = exp((2 pi n - phi_0)/gamma_0) with an explicit,
closed-form multiplicative gap exp(2 pi / gamma_0) between consecutive members,
transferable to integers at a negligible O(N) cost exactly as the existing proof already
tolerates.

**Not achievable, with what is currently known.** Two separate gaps remain, and closing
either needs an input outside this hunt: (A) no effective bound on the height at which a
witness for Theta_chi - eps' must appear (an effective zero-density statement near the
supremum, the converse direction from the zero-free regions this hunt already uses); (B)
when the witness is not isolated - which nothing available here excludes - separating it
from competing nearby zeros is a Kronecker-type simultaneous Diophantine approximation
problem, classically an existence statement only, with no known effective rate for
L-function zero ordinates. Obstruction B is not specific to L(s, chi_3): it is the same
kind of open difficulty as the (still unproved) linear independence over Q of zeta's own
zero ordinates, which the classical unconditional Omega_{+-} results for psi(x) - x carry
around rather than resolve.

**Placement.** This is an investigation of the proof technique behind Theorem B's
existential clause, not a strengthening of Theorem B itself: no new bound on E(N), on
Theta_chi, or on any zero of L(s, chi_3) is claimed, obstruction A alone already means the
constructive sub-case of Section 4 has no exhibited instance, and the low-height scan of
Section 6 finds nothing to instantiate it with. It does not touch the doors table (that
table is about rank 3's major-arc construction in UPPER_BOUND.md, a different part of
this hunt). Nothing here bears on RH.
