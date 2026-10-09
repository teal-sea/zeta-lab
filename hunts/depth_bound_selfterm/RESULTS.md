# depth_bound_selfterm: results

Grade: **measured** throughout. Nothing here is a theorem, and nothing bears on RH (`docs/08`).

## What was computed

$S(y) = g(iy)$ for the two kernels in `hunts/outband_certificate/artifacts/dual-x80.json`, with the dual.py convention `Cin = 2h cos(2 pi a x)`:

    S(y) = sum 2h khat_in cosh(2 pi alpha y) - sum 2h z cosh(2 pi aout y),
    h = X / len(x) = 1/16.

- **data[1], "out-of-band positivity to 1.5"**: strip-signed dual, z supported on aout in (1.003125, 1.5].
- **data[0], "control, in-band only"**: same formula, z empty.

Crossings are the smallest $y > 0$ on $[0, 1.5]$ with $S(y) < r(0)$ and with $S(y) < 0$. A grid of step $0.005$ finds the first drop; bisection refines it. Numpy float64 and `mp.workdps(40)` are two routes. The trivial root of $S(y) - r(0)$ at $y = 0$ is excluded.

## The numbers

| Kernel | $r(0)$ | Smallest $y > 0$ with $S(y) < r(0)$ | Smallest $y > 0$ with $S(y) < 0$ |
|---|---|---|---|
| Dual, data[1] | 0.1250000000 | 0.9198925071 | 0.9528773510 |
| In-band control, data[0] | 0.1250000000 | None on [0, 1.5] | None on [0, 1.5] |

On a step-$0.025$ grid the dual $S$ rises from $r(0)$ to a maximum near $0.308$ at $y \approx 0.75$, then falls. At the strip edge $y = 0.5$, $S = 0.2183$, still above $r(0)$. Two-route agreement at the dual crossings is $0$ and $1.1 \times 10^{-16}$ in $y$ (numpy versus mpmath). $S(0)$ agrees to $1 \times 10^{-16}$.

The in-band control is strictly increasing on the scan: $S(0.9) = 1.0117586419$, $S(1.0) = 1.5259860866$. No drop below $r(0)$ or below $0$ on $[0, 1.5]$.

## What y is, and whether 0.92 is possible: unresolved

$g$ is the x-space pair kernel of the configuration dual (`hunts/outband_certificate/dual.py` line 37, `Cin = 2.0 * h * np.cos(2.0 * np.pi * np.outer(a, x))`). $S(y) = g(iy)$ is that kernel at a purely imaginary pair difference. Complex differences come from off-line zeros (`hunts/outband_certificate/RESULTS.md` lines 65-66).

**The frame of $x$, and so of $y$, is the unfolded one.** The LP this dual comes from states its model in its first line: *"Unfolded zero configuration at density 1"* (`hunts/frontier_math/configuration_lp.py` line 3). An off-line zero at $\beta + i\gamma$ near height $T$ then sits at unfolded depth $(\beta - 1/2)\log T / (2\pi)$ up to the convention for the mean spacing. That range is not $(0, 1/2)$: it grows with $\log T$.

**A first draft of this file got this wrong.** It took the range $(0, 1/2)$ from `hunts/frontier_math/depth_uniform.py` lines 5-6, where depth is measured in raw $s$ against a window on $[-1/2, 1/2]$, and from `hunts/outband_intake/RESULTS.md` lines 196-197, whose planted pairs `1/2 ± 0.05, 0.2, 0.5 + 20i` are also raw. Neither frame is the unfolded frame of this kernel, so the verdict "$0.92$ lies outside the physical range" did not follow and is withdrawn.

**Two things remain open.** (1) The exact unfolded depth convention, including whether the mirror-pair term reads the kernel at $iy$ or at $2iy$, as the pair budget in `depth_uniform.py` line 31 reads its own kernel at $2iy$. Under the second reading the drop sits at unfolded depth about $0.46$. (2) Whether any unconditional bound confines unfolded depth below that scale. Neither is established here. Disposition: attempt unresolved.

## Structural observation

The strip frequencies `aout` lie in $(1, 1.5]$ above every in-band `alpha` in $[0, 1]$, so any strictly positive strip mass $z$ eventually dominates cosh growth and forces a zero crossing for large enough $y$. The only content of the measurement is **where** the crossing occurs, and that location is useful only once the depth convention above is fixed and compared with a depth bound that holds unconditionally.

## What it does and does not imply

- **What it implies, at measured grade.** For this $X = 80$ dual, $S$ drops below $r(0)$ at $y \approx 0.92$ and through zero at $y \approx 0.95$. The in-band control on the same artifact does not drop on $[0, 1.5]$, so the drop is carried by the strip mass. Whether the drop lies at depths an off-line zero can reach is unresolved (see above).
- **What it does not imply.** A finite-$X$ dual is not a uniform statement in $X$. A depth bound that would make the kernel usable still has to be an argument, not this scan. Nothing here is evidence for or against RH.

## The doors

**Active constraints at the optimum.** The dual self-term is forced through zero by strip mass at frequencies above the band. What binds the usefulness of that fact is not the existence of a crossing (any $z > 0$ produces one) but its location relative to the depths off-line zeros can reach in the unfolded frame. That comparison is not yet made, so the binding constraint is the missing depth convention and depth bound, not the first root of $S$.

**Frozen-constant inventory.**

| Frozen | Chosen as | What relaxing it would trade |
|---|---|---|
| kernel | $X=80$ dual from dual-x80.json | A different $X$ or a continuous kernel could move the root. Larger LP solves ($X=240, 320$) are the check that it is stable in $X$. |
| strip reach | aout in $(1, 1.5]$ | Widening the strip raises the dominant frequency and can only pull the crossing in. Narrowing it toward $1$ delays the crossing. |
| scan | step $0.005$ on $[0, 1.5]$, then bisection | A coarser scan can miss the first drop. Extending past $1.5$ does not change the first root already found. |
| normalization | $r(0) = 0.125$ | Overall scale. Roots of $S$ and of $S - r(0)$ are invariant under a global positive factor except that $r(0)$ itself sets the first-drop line. |
| depth convention | $S(y) = g(iy)$, $y$ unfolded | Not frozen by choice but unresolved: reading the mirror pair at $2iy$ halves every crossing depth (about $0.46$ and $0.48$). Fixing it is the first door. |

**Information class.** The scan reads only the dual already sitting in hunt #118's artifact: the same $Khat$ and $z$, a different evaluation point. No new zero data, no new prime data. Whether a depth bound can spend the strip positivity is still the construction problem hunt #110 named; this measurement only locates the self-term's first drop relative to the strip.
