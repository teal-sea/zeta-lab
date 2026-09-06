# outband_certificate: a ceiling. The out-of-band positivity is worth zero to any certificate whose positivity input is the Hermitian form's, and what hunt #110 priced was the RH-conditional class

**Verdict, 2026-09-06: kill condition 2 fires, at prose grade.** Section 8 has the argument;
sections 1 to 7 are the measurements and the lemma it rests on. The question the hunt asked,
whether an inertia or isolation argument can let a finite certificate spend BGSTB's
positivity, is answered no for every argument whose positivity comes from Weil's Hermitian
form, which is every unconditional argument in the field. What hunt #110 measured as
"+0.005 to +0.009" is the worth of the information to the pointwise-positivity class, which
is the class RH grants. The two inputs that would reopen the question are named at the end of
section 8. Grade: **proved** for the edge lemma and the dichotomy, **read** for the structure
of the paper's compression, **measured** for everything numerical. Nothing kernel-checked.
Nothing here is evidence for or against RH (`docs/08`).

First session, 2026-09-05 to 06. Everything below reproduces hunt #110's numbers before it
adds to them: the in-band control at X = 40, 80, 240 and 320 and the out-of-band values at
X = 40 (A = 3) and X = 80 (A = 1.5) match `../outband_intake/RESULTS.md` to the digit.

## 1. The certificate the information supports, read off the dual

`dual.py` rebuilds the configuration LP of `../frontier_math/configuration_lp.py` and returns
what that module does not: the dual solution. In the LP's own model the dual is the
certificate: the multiplier profile on the data rows is a kernel `Khat(alpha)`, signed in band
and nonpositive on the strip, and the multipliers on `tau >= -1` are its x-space partner.
Strong duality is checked first on every case (gap `1e-13` or better); whatever argument
eventually spends the information has to produce a kernel of this shape.

| grid | case | value | `g(x)` on the tau grid | `Khat` in band | `Khat` on the strip |
|---|---|---|---|---|---|
| X=40, J=200 | control | 0.6793882 | min 0 (to 5e-16), max 0.125 | min −0.020 at α=0.985, 5 of 201 nodes negative | |
| X=40 | strip to 1.5 | 0.6911038 | min 0 (7e-16) | min −0.032 at 0.995 | active on [1.06, 1.50], peak at 1.205, mass 0.0126 |
| X=40 | strip to 3.0 | 0.6918387 | min 0 (6e-10) | min −0.030 at 0.995 | active on [1.06, 3.0], peak at 1.23, mass 0.0164 |
| X=80, J=320 | control | 0.6775676 | min 0 (1e-15) | min −0.022 at 0.991, 8 of 321 | |
| X=80 | strip to 1.5 | 0.6855095 | min 0 (3e-9) | min −0.022 at 0.991, 10 of 321 | active on [1.031, 1.50], peak at 1.119, mass 0.0112 |
| X=80 | strip to 1.05 | 0.6792132 | min 0 (1e-15) | min −0.025 at 0.991, 7 of 321 | active on [1.025, 1.05], peak at 1.028, mass 8.4e-5 |

Three things in that table.

**The kernel is pointwise nonnegative in x-space.** On every case `g` on the tau grid is
nonnegative to numerical precision. That is the positivity a certificate needs for pairs of
on-line zeros, whose differences are real. It is not the square structure.

**The strip multiplier moves toward the band edge under refinement**: active support begins at
1.06 at X = 40 and at 1.031 at X = 80, peak at 1.205 then 1.119. For the width-0.05 strip the
whole multiplier mass is `8.4e-5`, and the value still moves by `+0.0016`. That is #110's
indirect channel made visible: a sliver of negative kernel just past the edge relaxes the
adversary far more than its own weight.

**The in-band kernel is slightly negative right at the band edge**, at 5 to 10 nodes with
α ≈ 0.99 and magnitude about 0.02, in the control as well as with the strip, at both grids.
Whether that is a boundary layer of the discretised dual or a feature of the continuous one
is not resolved here; it does not change the sign of `g`.

The adversary, in every case, is simple and double zeros only: `p_3 .. p_6 = 0`.

## 2. The LP cannot tell a double zero from an off-line pair, and that locates the missing argument

In `configuration_lp.py`, the off-line pair density `q` enters `D` with weight 4 and the density
constraint with weight 2. So does `p_2`. The two columns are identical, the solver puts the
mass wherever it likes (here in `p_2`, so `q` prints as zero), and **`q = 0` is not a finding**.
It is the model's statement, taken from the paper's section 7.5(b), that a depth-zero off-line
pair costs the certificate exactly what a double zero costs.

Read against section 1 that says where the obstruction lives. A pointwise-nonnegative kernel
handles every pair of on-line zeros on its own: for real differences the off-diagonal pair sum
is a sum of nonnegative terms. The square structure `g = |k|^2`, spectral density `v >= 0`, is
what gives positivity at *complex* points, and complex differences arise only from off-line
zeros. So the value #110 measured is "what the information supports when off-line pairs cost
what double zeros cost", and the only reason the unconditional proof cannot claim it is that
the proof has to cover off-line zeros, for which pointwise positivity says nothing and the
square structure forces `Khat >= 0` everywhere.

**The missing argument, stated as sharply as this session can state it: a bound for the
off-line-zero contribution to the pair sum of a kernel that is nonnegative on the real line
but not a square.** The unconditional inputs of the right kind are zero-density estimates;
Guth and Maynard's 2024 improvement (arXiv:2405.20552, fetched and confirmed) is the current
one. This is a **reading** of the classical mechanism, not a measurement: it rests on the
two facts that nonnegative kernels give nonnegative off-diagonal sums over real differences
and that positive-definite kernels give positivity at complex points, and on the LP's
degeneracy above. Whether the off-line term can actually be bounded to within `0.0006` with
a density estimate is the research question, and it is a different question from #110's
"find an inertia count for a non-Gram kernel". It is also, presumably, what Chirre,
Gonçalves and de Laat's isolation input does with RH, where there are no off-line zeros.

## 3. How narrow a strip suffices

The record is `0.6734164909714992949` (AMTOPA), `+0.00057` over this lab's four-point
`0.6728470198` and `+0.00092` over Theorem D. If a small strip past the band were worth that,
the argument of section 2 would only have to control the off-line term on a small strip.

**One grid says yes.** At X = 80, J = 320, sweeping the strip's outer edge:

| strip to | value | gain over control |
|---|---|---|
| 1.02 | 0.6775676 | 0 |
| 1.05 | 0.6792132 | +0.00165 |
| 1.10 | 0.6801949 | +0.00263 |
| 1.15 | 0.6810415 | +0.00347 |
| 1.20 | 0.6819554 | +0.00439 |
| 1.30 | 0.6835537 | +0.00599 |
| 1.40 | 0.6847045 | +0.00714 |
| 1.50 | 0.6855095 | +0.00794 |

**The ladder says not yet.** #110's matched-ladder method, six rungs, `ladder.py` and
`pinned.py`, exponent pinned rather than fitted because four to six points do not fix three
parameters (the free fit diverged on the width-0.10 column):

| width | gain per rung, X = 40, 80, 120, 160, 240, 320 | pinned-p limit, p = 0.5 … 2 | control's own fitted excess (true 0) | limit / error |
|---|---|---|---|---|
| 0.05 | +0.00137, +0.00165, +0.00147, +0.00137, +0.00113, +0.00099 | +0.00098 … +0.00129 | +0.00107 … +0.00365 | 0.4 to 0.9× |
| 0.10 | +0.00314, +0.00263, +0.00231, +0.00203, +0.00174, +0.00153 | +0.00077 … +0.00190 | same | 0.5 to 0.7× |
| 0.20 (four rungs) | +0.00572, +0.00439, +0.00379, +0.00355 | +0.00130 … +0.00359 | same | 1.0 to 1.2× |
| #110, strip to 3.0 | | +0.0065 | +0.0018 | 3.5× |

So: **a strip of width 0.05 is worth about the record gap, and by #110's own criterion that
is inside the method error and not distinguishable from zero.** The wide strip is established;
the narrow one is not. The share of the full gain that sits inside (1, 1.05] also falls under
refinement, from 20% at X = 80 to 16% at X = 240, so the one-grid front-loading partly washes
out. The extrapolation is the only instrument short of the mathematics: a finite-X dual is not
a continuous certificate, because its cosine sum is only known nonnegative on the grid up to
X, and the adversary's room beyond X is exactly what the ladder is chasing.

What would settle it without the ladder is an explicit continuous kernel, nonnegative on the
whole line with a transform nonpositive on the strip, whose bound in the LP model exceeds the
in-band optimum by more than `0.00057`; that is a lower bound, not an extrapolation, and it is
the same object the argument of section 2 would consume. Nobody has written one.

## 4. What this changes in the mission

Nothing in the HuntSpec is withdrawn. The target stays the record. Two sharpenings:

- The argument to build is for the strip (1, 1.5], as the spec says, not for a narrow strip;
  the narrow-strip shortcut is not established and should not be assumed.
- Direction (1), the signed decomposition with a separately counted residual, and direction
  (2), the moment inequality, both answer "how do we get a non-Gram kernel into the inertia
  count". Section 2 says the sharper question is "how do we bound what off-line zeros
  contribute to a pointwise-nonnegative kernel's pair sum", and names zero-density estimates
  as the input. That is a candidate direction the spec did not list, and the first checkable
  claim under it is a statement, not a lemma: the off-line contribution at depth `delta`, for
  the X = 80 dual kernel, as an explicit expression the falsifier can evaluate.

## 5. Second pass, same session: a candidate, its death, and what killed it

**The candidate.** `stable_rank_trace` (`lean/bridge/Zeta23Ext/StableRankTrace.lean`) takes
any Hermitian `Q` with a bounded positive index. For a signed spectral profile
`u = v_plus - v_minus` the compression is `P_plus - P_minus + Q`; apply the theorem to
`V_plus` and `Q' = Q - P_minus` (subtracting a positive semidefinite matrix cannot raise the
positive index, Weyl). The Frobenius side becomes the pair sum with weight `|FT u|^2`, whose
transform `u * u` is signed and could be nonpositive outside the band, where BGSTB's
positivity drops it. The price sits on the trace side, `4 tr P_minus`, four times the negative
mass per zero. In the normalisation of `paper_pin.py` the candidate's value is
`2 - min_u [(u*u)(0) + int |alpha| (u*u) + 4 int u_minus]` over even `u` with `int u_plus = 1`
and `u*u <= 0` on the strip. `signed_window.py` is the attempt to price it.

**Its death, with proof.** No grid `u` satisfied the sign condition on the whole strip, and
that is a theorem, not an optimiser failure.

> **Edge lemma (real even factors).** Let `u` be real and even in `L^2`, supported in `[-s, s]`
> with `s` the true edge, and let `Khat = u * u`. Then `Khat` is not nonpositive on any interval
> `(2s - eta, 2s)`. Hence `Khat` cannot be nonpositive on the out-of-band part of its support,
> so a kernel of this class either has `supp Khat` inside `[-1, 1]` or fails the strip condition.
>
> *Proof.* Near the edge only the two ends of `u` meet: writing `W(v) = u(s - v)` for the edge
> profile, `Khat(2s - c) = (W * W)(c)` for small `c > 0`, where `*` is convolution on `[0, infinity)`.
> Suppose `W * W <= 0` on `(0, c_0)`. Since `s` is the true edge, `0` is in the support of `W`, so by
> Titchmarsh's convolution theorem `0` is in the support of `W * W`, and `W * W` is not zero on
> `(0, c_1)` for any `c_1 < c_0`. Take Laplace transforms at large real `lambda`:
> `(L W)(lambda)^2 = L(W * W)(lambda)`. The left side is a square of a real number. The right
> side is `int_0^{c_0} e^{-lambda c} (W * W)(c) dc + O(e^{-lambda c_0})`, and the first term is at
> most `-e^{-lambda c_1} int_0^{c_1} |W * W|`, which dominates the error for large `lambda`. So
> the right side is negative for large `lambda`, a contradiction.

So the difference-of-squares candidate is dead for every real even `u`, however signed. The
`4 int u_minus` price was never reached: the sign condition fails first.

**And the lemma is false for the class one needs, which is the finding.** Krein's
factorisation of a nonnegative kernel with compactly supported transform, `K = |k|^2` with `k`
of half the type, does not make `k` real and even. Take `k(x) = sqrt2 sinc(x) sin(2 pi x)`,
real and **odd**. Then `K = sinc^2(x) (1 - cos 4 pi x) >= 0`, and by the convolution theorem
`Khat = tri(alpha) - tri(alpha - 2)/2 - tri(alpha + 2)/2`, which is compactly supported in
`[-3, 3]` and **nonpositive on `|alpha| > 1`**. Verified on a grid of step `1e-3`: `min K = 0`,
`max Khat` on `1 < |alpha| < 3.05` equals `1.5e-6` (FFT noise), `min Khat = -0.5` there, nothing
beyond `3.05`. With `1 - c cos` in place of `1 - cos` the same holds with `K(0) = 1 - c > 0`.
For an odd factor the Laplace argument above flips sign, and the transform is nonpositive at
its support edge *automatically*.

**The dichotomy, which is #110's obstruction stated with both halves proved.** A pointwise
nonnegative kernel whose spectral factor is real even can never spend the strip (the lemma).
A pointwise nonnegative kernel that does spend the strip has an odd or complex factor (the
counterexample and its family). An odd factor is antisymmetric under the difference of two
ordinates, so it is never the kernel of a Gram matrix, and a Gram matrix is what
`stable_rank_trace` needs for the on-line block and what handles off-line zeros through
Sylvester. Even factor: Gram-able, strip-blind. Odd factor: strip-capable, not Gram-able. The
paper's `v >= 0` is the even class, and that is why "the framework never has a free ghat".

**Consequence for the LP's number, stated as a hypothesis.** The LP's dual kernels are
pointwise nonnegative and signed, which is the class the RH-conditional Montgomery argument
uses (RH is what makes the zero side "a positive sum over real ordinates", the paper's
abstract). So the class value `[0.679, 0.682]` is plausibly exactly what pointwise-positivity
certificates reach *under RH* from bandwidth-one data plus BGSTB, and Chirre, Goncalves and
de Laat's `0.6792` sits inside it. Hunt #110 withdrew that coincidence because two fits landed
on two constants; this reading gives it a mechanism. Not measured, not claimed.

## 6. The lattice and the truncation, measured

Two checks on whether the LP's gain is an artifact of its own discretisation.

**Lattice spacing.** #110 imposed pair-measure positivity at spacing `h = 1/16` and never
varied `h`. At `X = 80, J = 320`, strip to `1.5`:

| `h` | in-band | strip 1.5 | gain |
|---|---|---|---|
| 1/16 | 0.6775676 | 0.6855095 | +0.00794 |
| 1/32 | 0.6762284 | 0.6858172 | +0.00959 |
| 1/64 | 0.6761447 | 0.6855025 | +0.00936 |

The gain does not shrink as the lattice refines. It is not a spacing artifact at this `X`. At
`X = 160` the same holds and the direction is the same: gain `+0.00693` at `h = 1/16` and
`+0.00808` at `h = 1/32`; the finer lattice lowers the in-band control more than it lowers the
strip value. The `X = 320` rows at finer spacing were not obtained on this machine (`RUNS.md`).

**Truncation.** The dual kernels at `X = 80` evaluated as continuous functions: on the LP's own
lattice the minimum of `g` is `-3e-9`; off-lattice within `(0, 80)` it is `-9e-5`; **beyond
`X = 80` both kernels go negative immediately** (first negative point `80.07`), the strip
kernel to `-0.077` against a maximum of `0.125`, negative on 25% of `[80, 400]`; the in-band
control kernel to `-0.051`, negative on 24%. So every finite-`X` value, control and strip
alike, rests on the adversary being cut off at `X`, and the strip's gain is the *differential*
use of that room. The large-`X` rungs at finer `h` are in `RUNS.md` when they land; the
question the truncation leaves open is the `X -> infinity` limit at fixed `h`, which #110's
extrapolation put at `+0.0065` with the local decay exponent falling with `X`.

## 7. Dead routes added by this session

- **Zero-density estimates as the unconditional input for the off-line term** (section 2's
  reading). Dead: they are trivial for `beta < 17/30`, and the zeros between the line and that
  abscissa could be a positive proportion of all zeros. Guth and Maynard's exponent `30/13`
  (arXiv:2405.20552) does not change that.
- **A signed spectral profile that is real and even**, in any inertia-type argument. Dead by
  the edge lemma above, before any price is paid.

## 8. The ceiling, and why the LP priced the wrong class

**What the compression is.** From the paper's abstract and the Lean statement of
`stable_rank_trace`: Weil's Hermitian form is compressed to a finite basis of test functions,
and the explicit formula writes the compressed matrix as a sum over zeros. An on-line zero
contributes a rank-one positive semidefinite piece `v v^H` (with multiplicity `m`, the same
vector `m` times); an off-line pair contributes a rank-two indefinite piece with one positive
eigenvalue, which is Sylvester's law and the source of `posIndex Q <= b`. So `G = V V^H + Q`
exactly as the theorem takes it. The pair weight in the Frobenius norm is `|<v_rho, v_rho'>|^2`,
and `<v_rho, v_rho'>` is a Gram pairing in a *definite* inner product (the standard one on the
compression space). A Gram pairing of shifted windows is a positive-definite kernel by
construction: in the paper it is `FT(phi^2)`, whose transform `phi^2` is nonnegative, and that
is #110's "the framework has a free `v >= 0`, never a free `ghat`".

**Why a positive-definite kernel cannot use the strip, in two lines.** Its transform is
nonnegative everywhere, so the out-of-band term `int_{|alpha|>1} Khat F` is nonnegative and,
since `F` has no unconditional upper bound outside the band, it is unbounded above. The only
way to keep the bound is `Khat = 0` outside `[-1, 1]`. Bandwidth one is forced, and BGSTB's
positivity has nothing to act on.

**Why no other kernel can enter the argument.** A kernel with a signed transform is, by the
dichotomy of section 5, one whose spectral factor is odd or complex; equivalently it is a Gram
pairing in an *indefinite* inner product, `V S V^H` with `S` indefinite. Hunt #110 tested
exactly that weakening of the inertia inequality and refuted it with a two-by-two witness
(rank half survives, inertia half fails). The two results are the same fact from two sides.

**So the ceiling.** Every unconditional certificate in this field takes its positivity from the
Hermitian form: that is what replaces RH. Within that input the on-line block is a definite
Gram matrix, its kernel is positive-definite, its transform is nonnegative, and the strip is
worth **zero**. The unconditional room that remains is inside bandwidth one, between the
current `0.6734` and the bandwidth-one configuration ceiling `0.6818`, and it is reached by
using `(tr G, tr G^2)` better, which is the n-point family this lab already runs.

**What hunt #110 priced.** Its LP is a depth-zero model of the zeros with pointwise positivity
of the ordinate pair measure (`tau >= -1`) and Montgomery's in-band data. That is the model RH
grants: no depth, and pointwise positivity over real ordinates, which is the very thing the
paper's abstract says RH was "classically needed" for. The LP's optimal kernels are pointwise
nonnegative with signed transforms (section 1), which is the pointwise-positivity certificate
class, which is conditional. So "+0.005 to +0.009" is what the out-of-band fact is worth to
a certificate that may assume RH, and Chirre, Goncalves and de Laat's conditional `0.6792`
sits inside the measured range because it is a member of that class. #110's withdrawn
coincidence was real. In band, the conditional and unconditional values coincide at Theorem
D, which is the paper's achievement and why the LP's control converges to the right number.

**The two inputs that would reopen this.** Either would be a result far larger than the
record: an unconditional evaluation of the *ordinate* pair correlation in band (which would
make pointwise positivity usable without RH), or an unconditional upper bound on the form
factor beyond the band (which would let a positive-definite kernel carry out-of-band support).
Neither is a certificate trick, and the hunt's spec forbids presenting either as available.

**What is proved and what is read, and then checked against the paper.** The edge lemma and
the odd counterexample are proved and verified. That a positive-definite kernel cannot use
the strip is two lines. The structure of the compression was first read from the abstract,
the theorem's statement and `paper_pin.py`; it was then checked against the paper's full text
(the public PDF `hunts/wide_search/HANDOFF.md` points at, 2260 lines through `pdftotext`),
which says it in its own words:

- Remark 1.2: the family `V` is a Gabor system at the critical density and `G~` "is its Gram
  matrix against the explicit-formula kernel", "a finite compression of an operator whose full
  positivity is RH", and Theorems A to D "extract what the first two trace moments of any such
  compression can certify unconditionally".
- (Z), section 1.4: each on-line point contributes "a real rank-one nonnegative form" to `P`,
  each off-line pair "a form of signature (1, 1)" to `Q`.
- Section 1.2 and section 7.4: what RH was needed for is "the reading of the zero side, where
  without RH the zeros are complex and the diagonal terms cannot be isolated by sign", "a
  positivity that fails for zeros far from the line". BGSTB and Aryan showed the form factor
  "holds for the sum over all complex zeros".
- Section 1.2: Chirre, Goncalves and de Laat "obtained 0.6792 via semidefinite programming by
  exploiting the positivity of F outside [-1, 1]; the optimality statement in Theorem D is
  scoped to the values of F on [-1, 1] only, so such majorants operate in a different regime."
- Section 1.5 and section 7.5(a): "the restriction lambda <= 1 is essential", because beyond
  bandwidth one "the off-diagonal terms are no longer dominated by the diagonal, and their
  evaluation would require information on prime pairs (the Hardy-Littlewood conjectures)".
  That is a stronger reason than the one given above: past the band the pair sum cannot even
  be evaluated on the prime side, not merely bounded on the zero side. Both land in the same
  place. Proposition 7.4 (Cap) and 7.5(d), (e): higher moments add nothing unconditionally.
- Section 7.5(b): the extremal configuration replaces doubles "by off-line pairs of depth -> 0
  (spectrally the same)", which is the LP's `q`/`p_2` degeneracy of section 2, in the paper's
  words.

So the only sentence in this section that is not mathematics is that every unconditional
argument in the field takes its positivity from the Hermitian form. The paper says as much of
its own method, and names the CGdL route as the conditional other regime.

## 9. The neighbouring threads, placed by this verdict

Everything unconditional lives inside bandwidth one, between the record `0.6734165` and the
configuration ceiling `0.68185` of Remark 1.1, and is reached by using `(tr G~, tr G~^2)`
better. Read against that, the threads of 2026-08-24 to 09-05:

- **Hunt #90 `amtopa_ceiling` (2026-08-24)** is the live in-band thread. In the leader's own
  schema, an exact assembly at the LP optimum of their pair-weight axis gives
  `0.6734201550790580964…`, `+3.96e-6` over their `0.6734164909…`; it is conditional on the
  same unreviewed bridge as the whole ladder and its floor is a float minimum until a verifier
  accepts it, and the leader's own verifier fails closed at its repository tip (a
  reproducibility defect on their side, which blocks this candidate too). Five
  differential-evolution seeds on the window axis report `+3.07e-5` to `+3.71e-5`, best
  `0.6734536…`, and the hunt calls that "direction, not magnitude". Neither number appears in
  `README.md`, `HANDOFF.md` or `ROADMAP.md`; both are now on the Leads line of `HANDOFF.md`.
- **`four_point_pressure` (2026-09-05)**: the same pressure idea inside this lab's own
  Lean-checkable four-point bridge gives a candidate `0.6728604`, `+1.3e-5` over the
  registered `0.6728470`, complete Lean check canceled. It is `0.00056` below the record, and
  the lab's n-point family's measured ceiling is `0.6730296` (seven and eight points), also
  below the record. So the record is not reachable in this family; it needs the leader's.
- **`cycle_moments` (2026-09-05)**: bounded outcome, "does not improve the asymptotic
  proportion"; consistent with the paper's 7.5(d), (e), that higher moments add nothing
  unconditionally.
- **`wide_search` THREAD 1**: the joint-window question (every admissible window's `(tr,
  Frobenius)` constraint at once) is the one open lane inside the band; its author bets it
  collapses to the single-window value. Still open. This verdict does not touch it.
- **Hunt #115** (prior art on the LP-versus-truth gap) found the route "live, not known-dead"
  in the literature; for the unconditional case this verdict answers it: the LP's value is the
  conditional class's, and there is no unconditional certificate at it.
- **`prime_pair_error`** studies the Hardy-Littlewood pair error numerically. That is the
  input 7.5(a) names as what would extend the band, so it sits on the real wall, as numerics
  on a conjecture, not as a theorem.

## Not done, and why

- **The ceiling is not in Lean.** The edge lemma is a clean statement about `L^2` functions
  and autocorrelations (Laplace transform, Titchmarsh) and is the natural next Lean target for
  the board's root item's false side; the framework claim is not a Lean statement at all. So
  the board's check cannot fire on this verdict, and the hunt closes at prose grade.
- **No candidate survived.** One was proposed, priced, and killed by a lemma. Nothing went
  through the falsifier, which also does not exist yet (`w-tool-falsify` on the board).
- **The odd-factor class was not explored as a conditional certificate.** Under RH it is the
  class that reaches about `0.68` (the LP), and CGdL already occupy it at `0.6792`. Nothing
  unconditional lives there, by section 8.
- **No Lean.** Nothing here is a statement about `riemannZeta`.
- **The in-band edge negativity** of section 1 was not chased; it does not affect the sign of
  `g` and the value it could change is the shape of the continuous dual near α = 1.
- **The depth model.** The paper's 7.5(b) argument that depth-zero pairs are extremal was not
  re-examined for a signed kernel; that is where section 2's claim would be tested first.

## Artifacts

`artifacts/dual.json` (X = 40, three cases), `artifacts/dual-x80.json`,
`artifacts/dual-x80-a105.json`, `artifacts/ladder-narrow-strip.json` (18 solves, seconds per
solve recorded). `RUNS.md` has the timings.
