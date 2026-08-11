# Level 2: projective gap consistency and the anti-duplication law

## Disposition

Level 2 of the hierarchy in `INTERACTION-CONTROL-REPORT.md` asks for state
retaining *one off-line pair marked against two consecutive on-line gaps*, an
exact object giving *projective consistency between one-gap marginals and
marked two-gap words*, and a kill control that *duplicates one off-line pair
independently in overlapping cells*. All three are delivered here, and they
repair the two defects `SIGNED-INCIDENCE-LAW.md` recorded against itself:

- level 1's per-cell envelope was **n-extensive** — n cells could each sit at
  the floor, so one off-line pair's budgeted negativity grew with the number
  of on-line zeros;
- level 1's exclusion used the **exactness** of the family's declarations, so
  an epsilon-perturbed family was untouched.

Both had one cause: level 1 used only the *diagonal* of LAW D. Used
off-diagonal, LAW D says every incidence value is one fixed analytic kernel
evaluated at an argument the configuration's gaps determine — so a declared
correlation *is* a declared gap, and a marked word cannot choose its own
outer value. The resulting caps are declaration-free, which is what makes
the exclusion robust.

As before: no proportion moves, nothing here is evidence about RH, and the
laws hold for every conjugate-closed multiset in the open strip with bounded
local density (the Davenport–Heilbronn zero included, checked below).

## Pinned inputs

Unchanged from the level-1 report: paper PDF SHA-256
`6792988e6cd0e17690621ce898abd5d534f98407741bc7cb14bbe7d07c77d72f`; the
§2.2 window; the critical Gabor grid; the transpose summand; normalisation
`aL^2`. Two further inputs are used, both already inside the paper's own
toolbox:

- **(2.17)**, the majorant `|Phi2(r)| <= psi(r) = min(L, 2/|r|, c_rho/(w r^2))`.
  For this hunt's septic ramp `c_rho = 4||rho'||_inf + 4||rho''||_1 = 105/4`
  exactly (`rho'(x) = 140 x^3 (1-x)^3`, so `||rho'||_inf = 35/16` at `x = 1/2`
  and `||rho''||_1 = 2 rho'(1/2) = 35/8`).
- **the unconditional local zero-density bound** `N(t+1) - N(t) <= A_0
  log(t+3)` (classical, Titchmarsh Theorem 9.2) — the same input the paper's
  own Proposition 4.2 uses for its tail. Write `nu` for the max number of
  distinct on-line zeros in a unit interval, so `nu <= A_0 log T`. `A_0` is
  left symbolic; this hunt does not pin its value.

## The two laws

**LAW G (projective gap consistency).** Put `omega(g) := Phi2(g)/Phi2(0)`. On
the full grid the normalised on-line correlation of two zeros separated by
`g` is exactly `omega(g)`, with

```text
omega(0) = 1,      |omega(g)| < 1  for g != 0,
```

the second because `phi^2 >= 0` is continuous with interval support. Hence:

- **a correlation is a gap.** Demanding correlation `>= c` caps the gap:
  measured at `L = 8`, `c = 0.99` buys `g <= 0.0719`, `c = 0.9` buys
  `g <= 0.2305`, `c = 0.5` buys `g <= 0.5557`.
- **a marked two-gap word is not free.** For three consecutive on-line zeros
  the outer correlation must be `omega(g1 + g2)` — not any independently
  chosen value. The natural independent guess `omega(g1) omega(g2)` is
  refuted with residual `0.13228305` at `(g1, g2) = (0.7, 1.3)`
  (`omega(2.0) = +0.0710` against the product `-0.0613`).

**LAW H (anti-duplication caps).** The kernel decays by (2.17) while local
density is capped by `nu`, so the total incidence mass of any single point
against a whole configuration is bounded **independently of that
configuration's size**:

```text
on-line:  sum_{j != i} omega(x_i - x_j)^2  <=  kappa(nu)
             = 2 nu [ 1 + sum_{k>=1} (psi(k)/aL)^2 ]
on/off :  sum_j |Bhat(x_j, z)|^2           <=  kappa_cross(nu, y)
             = 2 nu [ E(y)^2 + sum_{k>=1} (psi_y(k)/aL)^2 ],
```

where `E(y) = Phi2(iy)/Phi2(0)` is the depth inflation and
`psi_y(r) = min(aL E(y), (c_rho/w) cosh(yL/2)/r^2)` (near field by mass, tail
by two integrations by parts). Consequently the signed aggregate interaction
of one off-line pair with **all** on-line zeros obeys

```text
sum_j 2 Re( Bhat(x_j, z)^2 )  >=  -2 kappa_cross(nu, y),
```

an n-independent floor where level 1 had `-2 n sigma^2(y)`. One pair cannot
be spent twice. Measured at `L = 8`: `kappa(1) = 2.2750`, `kappa(3) = 6.8251`,
`kappa_cross(3, 0.3) = 31.0360`.

## The kill control, run

The cheat the hierarchy names: spend **one** off-line pair independently in
`n` overlapping cells, each at level 1's per-cell floor `-2 sigma^2(y)`.
Every cell is individually legal, so level 1 accepts the total; level 2's
aggregate floor does not move with `n`.

| n | declared total | level-2 floor | rejected | margin |
|---|---|---|---|---|
| 10 | −8.6229 | −62.0719 | no | −53.45 |
| 40 | −34.4915 | −62.0719 | no | −27.58 |
| 160 | −137.9660 | −62.0719 | **yes** | +75.89 |

**Stated rather than hidden: the improvement is asymptotic in `n`, not
universal.** The crossover here is `n > kappa_cross/sigma^2 = 72.0`; below it
level 2 adds nothing. This is the right place for it to bite, because the
family's defeat of the recovery coefficient requires `n -> infinity`.

## The robust exclusion

The family's on-line block has `R(P) = n(n-1)`: every pair of its `n` on-line
labels is *fully* correlated. LAW G says full correlation means zero gap, so
that cross mass is available only from a single point of multiplicity `n` —
which the paper charges to the index side at the flat cost 4, not to the rank
side as `n` simple zeros. Measured, with `n = 50`:

| spacing | max_i R_i | (family declares 49) |
|---|---|---|
| 0 | 49.00000 | attained exactly |
| 1e-3 | 48.95954 | |
| 1e-2 | 45.18010 | |
| 1e-1 | 7.85791 | already 6x short |

LAW H makes this declaration-free. Since `R(P) <= n kappa(nu)` for **any**
real configuration,

```text
n - 1  <=  kappa(nu)  =  2 nu [1 + S(L)]      hence   n = O(log T),
```

using `nu <= A_0 log T`. No perturbation of the family's declared numbers
evades this: it bounds the quantity, not the declaration. That is the
epsilon-robust exclusion level 1 could not give.

The bound is a function of `nu` and is honest about it — at `L = 8`,
`nu = 3` excludes every `m >= 2` (m = 2 needs 9 per label against a cap of
6.83; m = 10 needs 201, an excess of 29.5x), while `nu = 8` excludes `m = 10`
(11.0x) but not `m = 2`. The correct reading is not "the family is dead at
every size" but: **at each height `T` there is an explicit finite bound on
how large a family member can be**, where the defeat needed unbounded `m` at
fixed `T`. Members with `m = 1` (n = 4) are excluded by neither cap and need
not be: they give `theta <= 3/(n-1) = 1`, which is no defeat at all.

## The residue

The family forced `theta <= 3/(n-1)` and drove it to zero by taking `n`
large. Level 1 capped the realisable members through *depth*, leaving a floor
exponentially small in the bandwidth. Level 2 caps them through *density*:

```text
theta  >=  3 / kappa(nu)          (this family shape only)
```

| L | nu = A_0 L/lambda | level-1 floor (depth) | level-2 floor (density) | ratio |
|---|---|---|---|---|
| 8 | 8 | 6.729e-01 | 1.648e-01 | 0.2x |
| 16 | 16 | 4.340e-02 | 9.073e-02 | 2.1x |
| 24 | 24 | 2.062e-03 | 6.162e-02 | 29.9x |
| 32 | 32 | 8.543e-05 | 4.651e-02 | 544.5x |

Exponential in `L` becomes polynomial: `~ e^{-L/2}` becomes `~ 1/log T`. The
two floors are independent, so the larger one holds; level 1 remains the
better statement at small bandwidth, which the table shows rather than hides.

**This is a statement about what this adversary family can obstruct, not a
proof that any particular `theta` is admissible.** Establishing an actual
strengthened inequality is level 3's telescoping local-potential task and is
not attempted here.

## Controls ledger

| control | instrument | measured |
|---|---|---|
| float mirror vs mpmath closed form | `float_vs_mpmath_defect` | `4.5e-7` — bulk scans are the same function as the precision path |
| majorants really majorise | `majorant_control` | worst slack `+0.0117` (real), `+0.0315` (depth); never negative over 400 samples x 3 depths |
| caps never exceeded | `cap_scan` | worst excess `-5.41` (on-line), `-29.44` (cross) over 40 random configurations at measured `nu` |
| the scan has power (decoy) | `decoy_cap` | a cap planted 4x too small is violated in 11/12 configurations — the pass is not vacuous |
| collapse saturation (lesion) | `collapse_saturation` | `R_i -> n-1` exactly at zero spacing, `6x` short by spacing 0.1 |
| n-independence | `cross_aggregate` | aggregate mass flat across `n = 20, 80, 240` at fixed density |
| duplication cheat | `duplication_cheat` | accepted by level 1, rejected by level 2 past `n = 72`, margin growing linearly |
| rival (Davenport–Heilbronn depth) | `dh_rival_two_gap` | depth `0.30851718`, inflation `E(y) = 1.19539`, cap `31.856` — the rival obeys the laws, as a kernel lemma must |

## Reproduction

```bash
.venv/bin/python hunts/frontier_math/gap_consistency.py
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_gap_consistency.py
```

Roughly 50 s and 15 s respectively. Bulk scans run in float against the
closed forms, cross-checked against the mpmath path as the first control;
the family arithmetic is exact.

## What level 3 needs

The hierarchy's next row asks for marked `k`-gap words with overlap
constraints and *a local potential inequality whose boundary terms
telescope*, killed by periodic obstruction words and the direct-sum family.
LAW G supplies the missing ingredient it was waiting on: gap words are now
constrained objects rather than free declarations, and consecutive words
overlap in a determined way. The open question is whether a potential
`V(g)` exists with `2 Re(Bhat^2)` bounded below by a telescoping difference
along the ordered configuration — which would convert these per-point caps
into a genuine additive floor, the thing an actual strengthened rank–trace
inequality would need.
