# outband_certificate: the supporting certificate is pointwise nonnegative with a signed transform, and a strip of width 0.05 is worth about the record gap but is inside the ladder's error

**Verdict so far: the hunt is open. Two things measured, one thing read, no candidate
argument yet, nothing kernel-checked.** Grade: **measured**, and only that. Nothing here is
evidence for or against RH (`docs/08`).

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

## Not done, and why

- **No candidate survived.** One was proposed, priced, and killed by a lemma. Nothing went
  through the falsifier, which also does not exist yet (`w-tool-falsify` on the board).
- **The odd-factor class was not explored as a certificate.** Whether a kernel with an odd
  factor can beat Theorem D in the Montgomery bound (under RH, the LP says the class reaches
  about `0.68`), and whether any inertia-type argument can be built around a non-Gram block,
  are the two questions the dichotomy leaves. The second is the hunt.
- **No Lean.** Nothing here is a statement about `riemannZeta`.
- **The in-band edge negativity** of section 1 was not chased; it does not affect the sign of
  `g` and the value it could change is the shape of the continuous dual near α = 1.
- **The depth model.** The paper's 7.5(b) argument that depth-zero pairs are extremal was not
  re-examined for a signed kernel; that is where section 2's claim would be tested first.

## Artifacts

`artifacts/dual.json` (X = 40, three cases), `artifacts/dual-x80.json`,
`artifacts/dual-x80-a105.json`, `artifacts/ladder-narrow-strip.json` (18 solves, seconds per
solve recorded). `RUNS.md` has the timings.
