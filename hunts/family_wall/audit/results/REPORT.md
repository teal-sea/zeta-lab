# Independent audit of the barrier claim

## Verdict

**The supporting argument is false as written. Steps 2 and 3 both omit necessary
conditions.** Step 2 reverses direction when its numerator is negative. Step 3 moves to
the largest allowed `m` even though `Phi` is not always increasing in `m`.

This is a refutation of the stated argument, not a numerical counterexample to the final
claim. A case split repairs both defects. After that repair, I found no numerical
counterexample. In fact, an explicit gap word gives a uniform bound for every `n >= 8`,
and interval-checked witnesses handle `3 <= n <= 7`. The resulting all-`n` bound is

```text
Phi_n < 0.675142509660254 < 0.6751676068 < 0.6818286874638.
```

For the requested numerical searches, the largest best-found `W` was at `n = 100`:

```text
W < 0.001404828486362211
H(1 + W) < 0.673445451825039116.
```

Thus none of the requested dimensions breaks either threshold.

## Kernel and constants

Put `q = 1/sqrt(2)` and use `sinc(z) = sin(z)/z`, continuously extended at zero.
Product-to-sum gives

```text
K(x) = 1/2 [sinc(q - pi*x) + sinc(q + pi*x)].
```

An equivalent form, useful away from the removable singularities, is

```text
K(x) = [q sin(q) cos(pi*x) - pi*x cos(q) sin(pi*x)]
       / [q^2 - pi^2*x^2].
```

I checked the first formula against direct high-precision quadrature at seven points from
`x = 0` through `x = 19`. The largest discrepancy at 100 decimal digits was
`4.02e-102`.

My independently computed constants are

```text
K(0) = 0.9187253698655684   (16 digits)
H    = 0.6725007036794116   (16 digits)
```

More digits are

```text
K(0) = 0.91872536986556843778423152512466175181017247999457...
H    = 0.67250070367941164573437979080329518859340302862626...
```

The exact `W` levels corresponding to the two quoted barriers are

```text
0.6751676068 / H - 1
  = 0.00396565104838863604939044560637081256...

0.6818286874638 / H - 1
  = 0.01387059334414481885584355033936444273...
```

The brief's rounded `0.0138706` is consistent with the recomputed value.

## Algebraic audit

Write `q0 = n - 1 >= 2`, `d = m - q0 >= 1`, and

```text
D = m - c*d.
```

The cap gives `c*d <= 1`, hence

```text
D >= m - 1 >= 2.
```

The original denominator is at least `1 - 1/m >= 2/3`. It cannot vanish or change
sign. The numerator can be negative.

### Step 1

Valid. Multiplying numerator and denominator by the positive integer `m` gives

```text
Phi = [H*m - q0*(m-1)/p] / [m - c*(m-q0)].
```

### Step 2

**Invalid as stated.** Replacing `D` by its lower bound `m-1` is valid only when

```text
N = H*m - q0*(m-1)/p >= 0.
```

When `N < 0`, the inequality reverses.

A genuinely admissible counterexample is

```text
n = 3, c = 0.01, m = 3, p = 1.
```

For this triple,

```text
Phi                         = -0.6630427722280151...
claimed step-2 upper bound  = -0.9912489444808825...
```

so the claimed inequality is false.

The certificate `c = 0.01` is genuine for both `p = 1` and `p = 2`. For `n = 3`, if
`S >= 1/2`, then `F >= S/p >= 1/4`. If `S < 1/2`, restricting the defining integral to
`|t| <= 1/4` gives

```text
K(S) >= 15/(32*sqrt(2)),
2 w(S) >= 225/1024 > 0.01.
```

Here the integrand is nonnegative on the full integration interval and `K(0) < 1`.
Thus `F >= 0.01` for every nonnegative gap vector, and the cap is also satisfied.

The flaw does not by itself threaten a positive barrier. A negative numerator makes
`Phi < 0`.

### Step 3

**Invalid without an omitted monotonicity argument.** The cap gives only

```text
m <= q0 + floor(1/c).
```

For fixed `n,c,p`, the sign of the discrete change in `m` is the sign of

```text
p*c*H - 1 - c*(q0-1).
```

Therefore `Phi` can increase, stay constant, or decrease with `m`.

For another genuinely admissible instance, take `n = 3`, `c = 0.01`, `p = 2`.
At `m = 3`,

```text
Phi = 0.005853548842219049...
```

while step 3 would assert

```text
Phi <= H + H*c - 2/p = -0.3207742892837943...,
```

which is false. At the largest allowed `m = 102`, the actual value is
`-0.3208408735118813...`, confirming that `Phi` decreased.

The numerical inequality `m_max - 1 >= 1/c` is valid at
`m_max = q0 + floor(1/c)`. What was missing was permission to replace the original `m`
by `m_max`.

### Steps 4 and 5

Step 4 is valid once step 3 has been repaired. The certificate condition gives, for
every chosen witness,

```text
c <= S/p + W.
```

Because `H > 0`, substitution has the claimed direction. Calling `c` "the floor" is
imprecise: admissibility only says that `c` is an accepted lower bound for the floor.

Step 5 is also valid once step 4 is available. If `S <= q0/H`, then
`H*S - q0 <= 0`, and division by `p > 0` preserves that sign.

### Repair

The same final witness implication can be recovered.

If `Phi <= H`, then `W >= 0` immediately gives `Phi <= H(1+W)`. Now suppose
`Phi > H`. Direct subtraction gives

```text
Phi - H = [H*c*d - q0*(m-1)/p] / D > 0.
```

It follows that

```text
p*c*H > q0 + q0*(q0-1)/d
        >= q0 + q0*c*(q0-1)
        > 1 + c*(q0-1).
```

This is exactly the condition that makes `Phi` increase with `m`. In the only branch
that can threaten a bound above `H`, moving to `m_max` is therefore legitimate. At
`m_max`, the numerator is positive, step 2 has the correct direction, and
`m_max - 1 >= 1/c`. Steps 3 through 5 then yield

```text
Phi <= H(1+W).
```

## Requested constrained searches for W

The following values are directed interval upper bounds for the exact decimal witnesses,
rounded upward to 18 decimal places. `S` is also rounded upward and the cap downward, so
each displayed feasibility comparison is safe.

| n | W, upper | S, upper | (n-1)/H, lower | H(1+W), upper |
|---:|---:|---:|---:|---:|
| 7 | 0.001328402428066512 | 8.094250553717842001 | 8.921923749927055618 | 0.673394055247055814 |
| 8 | 0.001025210961846063 | 10.091557178131284901 | 10.408911041581564887 | 0.673190158772672970 |
| 9 | 0.001322266220468393 | 11.100807816270015201 | 11.895898333236074157 | 0.673389928643128157 |
| 10 | 0.001089515659416025 | 13.097041953685113801 | 13.382885624890583427 | 0.673233403727038661 |
| 12 | 0.001133630133668114 | 16.101706869320731501 | 16.356860208199601966 | 0.673263070742015638 |
| 14 | 0.001166057669295592 | 19.105795273792323801 | 19.330834791508620506 | 0.673284878282543706 |
| 16 | 0.001191058345222086 | 22.109449907522608801 | 22.304809374817639045 | 0.673301691254696735 |
| 20 | 0.001227382861977062 | 28.115799465983066801 | 28.252758541435676124 | 0.673326119517775271 |
| 30 | 0.001279821426190888 | 43.122631457880764401 | 43.122631457980768821 | 0.673361384489109006 |
| 56 | 0.001403227840734873 | 81.166580112404309601 | 81.784301040998009833 | 0.673444375389728390 |
| 100 | 0.001404828486362211 | 147.188232149511130901 | 147.211741873796417699 | 0.673445451825039116 |

The largest best-found `W` is the `n = 100` value. Its resulting bound is below the
stated ceiling by more than `0.001722154974960884` and below the target by more than
`0.008383235638760884`.

The complete exact decimal vectors are in [WITNESSES.md](WITNESSES.md) and the
machine-readable values are in [search-results.json](search-results.json). None of these
bounds exceeds either `0.6751676068` or `0.6818286874638`.

### Optimisation and local-minimum defenses

I used SciPy SLSQP with exact analytic gradients for the nonnegative simplex constraint,
then solved the unconstrained or equality-constrained KKT equations with the exact dense
Hessian. The search starts included:

- regular spacings at several total lengths;
- alternating and periods 3, 4, 5, and 7;
- clustered vectors with exact zero gaps;
- edge-heavy and center-heavy vectors;
- random Dirichlet vectors with concentration parameters from `0.15` to `20`;
- integer and nearby-kernel-zero skeletons;
- balanced 1/2 words, cyclic phases, and explicit low-low defects.

The base searches used 91 to 191 starts per requested `n`. For `n = 7,8,9,10`, every
cap-feasible binary 1/2 skeleton was polished. For `n = 12`, the best 300 of 1,024
skeletons were polished from both integer and nearby-zero starts. For `n = 14,16,20`,
the best 400 skeletons were selected from 4,096, 16,384, and 262,144 feasible binary
words respectively. The higher dimensions also received balanced-word and defect seeds.

Every reported point has KKT residual below `1.7e-15`. The smallest relevant Hessian or
projected-Hessian eigenvalue decreases from `0.2935` at `n = 7` to `0.01852` at
`n = 100`, but remains positive at every reported point. This proves strict local
minimality in the relevant free directions, not global minimality. Global minimality is
unnecessary for the witness direction: any feasible point gives a safe upper bound on
the minimum `W`.

The only active cap among the final requested vectors is `n = 30`. An initial solve using
the binary64 cap produced a decimal sum about `5e-15` above the true cap. The final vector
was re-solved with an explicit `1e-10` cap backoff, then interval-checked. This is why its
reported `W` is about `1.5e-14` above the mathematical equality-constrained stationary
value.

## An explicit all-n construction

There is no uncontrolled large-`n` tail. Define, for every gap index `i >= 1`,

```text
g_i = 1 + floor(18*i/37) - floor(18*(i-1)/37).
```

This is a 37-period word containing 19 ones and 18 twos. For `q0 = n-1`, its prefix
length is

```text
S_q0 = q0 + floor(18*q0/37)
     <= (55/37) q0.
```

Directed intervals give

```text
55/37 = 1.486486486486486486...
1/H   = 1.486987291654509269...
```

so every prefix satisfies the length cap.

Every window sum is a positive integer. At integer `j >= 1`, the kernel simplifies
exactly to

```text
k(j) = (-1)^(j+1) / (2*pi^2*j^2 - 1),
w(j) = 1 / (2*pi^2*j^2 - 1)^2.
```

These values decrease with `j`. For `q0 >= 11`, at least `5/12` of the prefix gaps are
twos. The scale-one contribution is therefore at most

```text
2 [(7/12) w(1) + (5/12) w(2)].
```

Every scale-`s` window has integer length at least `s`, so its whole contribution is at
most `2w(s)`. Also `w(s) <= w(1)/s^4`. Consequently, for every `n >= 12`,

```text
W <= 2 [(7/12)w(1) + (5/12)w(2)]
     + 2 w(1) [pi^4/90 - 1]
  < 0.003928331920529310,

H(1+W) < 0.675142509660253902.
```

The final margin below `0.6751676068` is more than
`0.000025097139746098`. The estimate is deliberately coarse. The computed
period-averaged energy is about `0.00317879602211`.

The same word directly handles the remaining `n = 8,9,10,11` cases:

| n | W, upper | H(1+W), upper |
|---:|---:|---:|
| 8 | 0.003527662393159108 | 0.674873059121154543 |
| 9 | 0.003809763575718264 | 0.675062772364934370 |
| 10 | 0.003430990978580423 | 0.674808047526824693 |
| 11 | 0.003666517753437888 | 0.674966439448651681 |

Separate polished witnesses close `n = 3` through `7`:

| n | W, upper | H(1+W), upper |
|---:|---:|---:|
| 3 | 0.001303187718941627 | 0.673377098337426258 |
| 4 | 0.000712388197190657 | 0.672979785243315270 |
| 5 | 0.001343057074941678 | 0.673403910507391537 |
| 6 | 0.000920639929894577 | 0.673119834680101113 |
| 7 | 0.001328402428066512 | 0.673394055247055814 |

The exact finite-prefix scan through `n = 599` in
[periodic-certificate.json](periodic-certificate.json) agrees: this simple word fails the
claimed threshold only at `n = 3,4,5,7`, precisely the cases replaced above. Together
with the repaired algebra, these witnesses establish the stated ceiling for every
`n >= 3`.

## F_7,3000

The best-supported numerical value is

```text
F_7,3000 = 0.00382623121130447424828548285770795421241114973478...
```

at

```text
(1.04608035577143543724508620334,
 1.98913202062119593163024512345,
 1.98641493610882775469506115045,
 1.04160329372111326218470199081,
 1.97702352233741593883693409703,
 1.04500209461784484467937259671).
```

Its reversal is a second minimizer by symmetry. At this point,

```text
S = 9.08525622317783316927140116178...
W = 0.000797812470245196525195015804...
```

An 80-digit Newton solve reduced the gradient residual below `5e-102`. The Hessian
eigenvalues are

```text
0.2008115114, 0.2906542995, 0.4030075399,
0.6826625458, 0.7330771658, 1.3114628294.
```

The point is therefore a well-conditioned strict local minimum.

The global search used 562 broad local starts, four differential-evolution runs with
120 population members and up to 800 generations, and 1,710 integer-lobe starts. The latter
produced 953 distinct local minima up to numerical clustering. The next stationary value
found was `0.0038681976920066`, about `4.20e-5` higher.

There is also a strong compact-domain reduction. With the exact rational incumbent
`U = 0.003826231211305`, any better point must satisfy

```text
S <= 3000 U = 11.478693633915
```

and every singleton term forces `w(g_i) <= 3U`. This sharply restricts each coordinate
to the low regions surrounding the kernel zeros.

**I do not claim a rigorous global certificate for this value.** Differential evolution,
basin enumeration, positive Hessian, and high-precision agreement are serious evidence,
but none supplies the required lower bound over the full six-dimensional domain. A true
certificate would need interval branch-and-bound plus interval Newton isolation of every
remaining stationary box. Therefore the honest statement is

```text
inf F_7,3000 <= 0.003826231211304474248285482857707954213,
```

with strong numerical evidence for equality. I do not use this number as an admissible
`c`, and I found no concrete admissible triple exceeding the claimed ceiling.

## Interval status and reproducibility

All reported witness gaps are stored as decimal strings. I evaluated their cumulative
sums, `K`, `w`, `W`, caps, and final bounds with `mpmath.iv` at 100 decimal digits. The
printed upper and lower endpoints use explicit decimal ceiling and floor rounding. This
certifies the unsafe witness direction relative to the interval backend. It is not a
proof-assistant certificate or a global-minimum certificate.

The implementation has independent checks for:

- the two-sinc kernel against direct quadrature;
- analytic first and second derivatives against finite differences;
- the `O(n^2)` gradient against central differences;
- reversal invariance;
- direct evaluation of the definition.

All six automated tests pass. Main artifacts:

- `audit.py`: kernel, derivatives, objectives, multistart searches;
- `w_binary_challenge.py` and `w_balanced_challenge.py`: structured basin attacks;
- `refine_witnesses.py`: KKT refinement;
- `interval_verify.py`: directed point-witness checks;
- `periodic_certificate.py`: the all-`n` construction and tail bounds;
- `f7_landscape.py` and `high_precision_f7.py`: the `F_7,3000` search and refinement;
- [constants.json](constants.json), [intervals-requested.json](intervals-requested.json),
  [f7-high-precision.json](f7-high-precision.json), and
  [periodic-certificate.json](periodic-certificate.json): machine-readable outputs.

## Bottom line

The audit found a real formal defect: steps 2 and 3 are not universally valid. The
numerical claim itself survived every attack. After an explicit case split repairs the
algebra, the period-37 construction plus five small-`n` witnesses controls every `n` and
stays strictly below `0.6751676068`. The weakest unresolved numerical point is the word
"global" for the reported `F_7,3000` minimum. I found compelling evidence, not a formal
global certificate.
