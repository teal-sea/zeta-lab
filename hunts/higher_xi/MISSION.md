# MISSION: higher derivatives of xi

## Objective

Attack the open higher-derivative form-factor problem left by Ji Bian's 2008
thesis and exposed by the August 2026 rank-trace paper.

The Chapter 11 percentages are quarantined historical data. They may appear
only in source-forensics checks. They are never inputs, targets, priors,
normalization controls, or expected outputs.

The present obligation is to reconstruct the arithmetic coefficients of
`xi'''/xi''` from first principles, derive the corresponding form-factor
information with a controlled tail, and use completed-CUE and direct
Dirichlet recurrences only as independent falsification oracles.

`C2_PROVENANCE.md` closes the historical coefficient audit. It finds that thesis page 71
drops the factors `M(v_l)M(w_k)` when passing to equation (8.1). The corrected
system first diverges at `C[2,2]=-8`, not the printed `-4`.

`CORRECTED-F2.md` derives the infinite corrected coefficient object. It gives
the rational generating function for `q_j`, 40 exact coefficients, and a
uniform index-40 tail below `3.279e-9` on bandwidth one. The remaining
obligation is now narrower: establish a uniform analytic bridge from
`xi'''/xi''` to the actual zero form factor. The printed fixed-`B` theorem is
not that bridge, as its distinct level-1 truncation polynomials already show.

`BRIDGE-CLOSURE.md` closes the present analytic audit at Outcome C. The first
failed source estimate is the contour-tail step on thesis pages 32-33: an
integral whose kernel mass stays at least `1/2` for target heights inside the
integration range is assigned quadratic height decay. Correcting it exposes
incompatible truncation-order requirements in the geometric tail and the
fixed-order mean-square error. No fixed positive alpha band, including the
target weighted window, follows from the recorded estimates.

`RESUMMED-BRIDGE.md` changes the representation rather than patching that
argument. It derives the exact untruncated resolvent for `xi'''/xi''` and shows
that its frozen arithmetic part is exactly the corrected rational `Q(z)`
object. The replacement audit closes at Outcome D: no available source gives
the required uniform mean square for the full height-dependent convolution
inverse. The minimal new target is named `URMS2`. The same source defect is
load-bearing in the printed Farmer-Gonek-Lee level-1 proof, which is classified
as a proof gap with no located repair, not as a contradiction of the limiting
prediction.

`URMS2-ATTACK.md` attacks that named target and closes at Outcome D. The full
inverse is bounded in a weighted Wiener algebra and on its companion Dirichlet
Hilbert space. Its exact coefficient envelope converges below `alpha=1/2` at
level one and `alpha=1/4` at level two. At that stage neither threshold was a
zero-side bridge: the available resummed square sum was `x(log x)^2`, one
logarithm above the required `x log x` scale. The then-smallest package was the
early-smoothed contour estimate `RC-kappa` plus the resummed almost-prime
square asymptotic `RAMS-kappa`.

`RAMS1-ATTACK.md` resolves where the elementary extra logarithm comes from.
On squarefree support exactly one convolution depth survives, with an explicit
factorial formula. The crude `x(log x)^2` bound loses prime support density
already at depth zero. That attack left mixed repeated-prime collision strata
open after closing the all-depth squarefree and pure-prime-power pieces. Early
smoothing also turned the false Cauchy-tail step into an exact `L2`
contraction. The subsequent closure below resolves both remaining level-one
obligations.

The same attack finds the full second-moment generating object. The exact
identity `alpha_k(n)=log(n) Lambda_k(n)/k` converts the ordinary resolvent into
a Laplace transform of a multiplicative exponential-convolution family. Its
Hadamard square has an explicit two-parameter Euler product. This reduced
RAMS1 to a uniform Borel-Hadamard Tauberian problem for that product.

`URMS1-CLOSURE.md` closes that Tauberian problem by the unique
powerful-squarefree support split. The squarefree strata give the factorial
main series, while powerful corrections have finite harmonic mass and vanish
by dominated convergence. The same report rebuilds RC1 on the untouched right
contour line and establishes URMS1 on compact positive bands inside
`|alpha|<1/4`. This is
Outcome B: level one repaired, level two blocked. The exact new level-two
target is `RAMS2-Cluster`, forced by the connected `A*A` atom at the coprime
integer 6.

`RAMS2-CLUSTER.md` resolves that target on the explicit coefficient band
`0<r<=1/10`. Borel transformation turns the denominator inverse into a
rank-one monomer-dimer model. In the Hadamard square its connected components
are exactly alternating paths and even cycles. Their all-support-size
majorant has successive ratio `O(1/r)`; the powerful-squarefree split then
removes repeated-prime strata from the main term. The connected atom changes
the corrected level-two coefficient but not the `x log x` scale. Reusing the
early-smoothed right-line architecture gives the level-two bridge on compact
bands inside `|alpha|<1/100`. This reaches Outcome B on a deliberately narrow
band. It does not reach the support of the simplicity window, so no percentage
is opened.

`BANDWIDTH-FORENSICS.md` removes the artificial endpoint in that first
promotion. The unchanged parameter inequalities reach `|alpha|<1/40`.
Inserting the existing pointwise coefficient envelope before the far Hilbert
tail reaches `|alpha|<1/20`. Optimizing the powerful-core Cauchy radius extends
RAMS2 to `rho<0.1454524603...` and the full bridge to
`|alpha|<0.0727262301...`; `alpha=0.07` has an exact rational witness. Peeling
off finitely many small primes then removes the fixed-rho restriction and
extends the full bridge to every compact band inside `|alpha|<1/2`. The first
failed checkpoint is `0.50`, where the far-tail cutoff conflicts with the
finite mean-value length. Independently, the downstream window
problem has exact bounds `0.5<=beta_useful<=0.51`. Cauchy-Schwarz,
operator coercivity, and completion of squares exclude all admissible
spectral-factor windows through `0.5`; the constant window at `0.51` is
useful.

`URMS2-051.md` crosses the remaining gap. At `sigma=3/2`, the two contour
ranges form one polynomial with square weights `n/x^2` below `x` and
`x^2/n^3` above `x`. Retaining the individual `log n` spacings in the
Montgomery-Vaughan estimate makes the off-diagonal error `O(x log x)`,
independent of the far cutoff length. The old `gamma<delta` condition was a
worst-spacing loss. The rational choice `alpha=51/100`, `delta=3/4`,
`gamma=21/20`, `epsilon=1/100` has positive margins. URMS2 now contains the
closed bandwidth `0.51`, and the exact constant window gives a conditional
simple-zero proportion lower bound `0.0147728663285376...` for xi-double-prime
under RH. Bandwidth optimization stops at this first corrected theorem.

`URMS2-051-AUDIT.md` is the independent internal audit. It reconstructs the
two-range phase, maps the exact weighted Montgomery-Vaughan theorem, adds the
marked-cluster height-freezing estimate at ratio `14/5`, rebuilds the window
bound from `C2_EXTENDED.json`, and checks the multiplicity normalization.
Every internal gate passes. External mathematical review remains the next
promotion gate.

`LEAN-FRONTIER.md` records the first kernel-checked slice of this package.
`ZetaLean/HigherXi.lean` contains the exact parameter witness, logarithmic
spacing majorant, full finite Dirichlet-polynomial expansion, multiplicity
normalization, and rational output positivity. It deliberately does not state
URMS2-051: the weighted Montgomery--Vaughan inequality, RAMS2 asymptotic,
marked-cluster freezing, contour transfer, and in-Lean coefficient/tail
reconstruction remain separate formal obligations.

The completed-CUE experiment uses angular derivatives of

```text
Z_U(theta) = constant * product_j sin((theta-theta_j)/2).
```

The controls are forced:

1. derivative level 0 reproduces the CUE form factor `min(alpha,1)`;
2. derivative level 1 reproduces the Farmer-Gonek-Lee closed form;
3. derivative level 2 is compared with the independently regenerated exact
   finite coefficients under identical weighted observables;
4. matrix size and sample count ladders separate finite-size error from signal.

The desired outputs, in order, are:

1. an exact coefficient provenance table and smallest obstruction;
2. an exact full-band coefficient tail and a quantified analytic bridge;
3. independent numerical oracles for the corrected object;
4. only after the finite-height bridge closes, a zero-statistics window result.

## Scope

This hunt may write only under `hunts/higher_xi/` and `figures/`. It may read
the rest of the repository and pinned primary sources. Changes to `zeta/`,
`lean/`, `ontology/`, `harness/`, or repo-level records require a separate
promotion decision.

The exact pinned primary source is Ji Bian, *The Pair Correlation of Zeros of
Derivatives of Riemann's Xi-Function*, University of Rochester PhD thesis,
2008, repository item 5500, downloaded PDF SHA-256
`ec1143f4f6c83288b717cfd4cd0aa6cc620f8c68b892f510a2a8d1708f36bfb7`.

## Non-goals

- No claim about RH.
- No unconditional xi-double-prime constant from Bian or CUE alone. The
  off-line zero-side algebra and prime-side asymptotic would be separate gates.
- No coefficient fitting presented as a derivation.
- No trust in the eleven-term truncation near `alpha=1`.
- No historical coefficient row used outside source forensics.
- No raw characteristic-polynomial derivative substituted for the completed
  real trigonometric polynomial.

## Vocabulary and controls

This directory is exploratory. Use *exact*, *measured*, *reproduced*, and
*consistent with*. Do not use the reserved claim vocabulary banned under
`hunts/`.

Every headline number must have an exact-rational route or an independent
precision and finite-size ladder. A generated claim cannot adjudicate its own
normalization.
