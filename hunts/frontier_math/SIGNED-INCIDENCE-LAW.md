# The signed on/off incidence law: level 1 of the hierarchy, delivered

## Disposition

`INTERACTION-CONTROL-REPORT.md` closed with: *"No decimal search should run
before level 1 below has an unconditional zeta constraint that excludes the
obstruction family."* This report delivers that constraint. Three signed
incidence laws — a diagonal law, a subgrid envelope, and a depth floor with a
strip cap — hold unconditionally for the actual zeros of zeta read through
the pinned paper's own window/grid interface, and every member of the exact
obstruction family (both the scalar family and its moment-matched dilution)
violates at least one of them at every bandwidth and every placement, with
exact integer margins where the violation is sharpest.

Nothing here is evidence about RH, and no proportion moves. The laws hold for
any conjugate-closed multiset in the open strip — the Davenport–Heilbronn
off-line zero satisfies them too, as a structural lemma must (a lemma failing
on the rival would be a bug, and passing distinguishes nothing). What changes
is the *adversary's* freedom: the family that forced every universal recovery
coefficient to zero is not realisable as incidence data of anything living in
the strip.

## Pinned inputs

- Paper PDF SHA-256:
  `6792988e6cd0e17690621ce898abd5d534f98407741bc7cb14bbe7d07c77d72f`
  (re-downloaded this session; hash matches the one pinned by the two
  earlier audits).
- Local state at the start of this session: `c35dc04`.
- The paper's interface, as used here: window `phi` of its §2.2 (flat top,
  C³ ramps, `supp phi = [-L/2, L/2]`, `1 <= w <= L/8`), critical Gabor grid
  `tau_k` at spacing `h = 2pi/L`, evaluation vectors
  `u_rho = (phihat(gamma_rho - tau_k))_k`, summands `m_rho u u^T` (transpose,
  not conjugate transpose — the corrected reading that `CLEAN-KILL-REPORT.md`
  pinned), normalisation `aL^2` (its (4.4)).
- Family under exclusion: `interaction_obstruction.ScalarFamily(m)` (one
  off-line pair with evaluation scalars `im, -im` against `n = 2m^2 + 2`
  mutually-unit on-line labels) and `MomentMatchedFamily(m, k, ·)` (same bad
  block plus trace-repairing positive pairs and background dilution).

## The three laws

Write `Phi2` for the Fourier transform of `phi^2`, `aL = Phi2(0)`, and for a
point `z = t - iy` of the open strip (depth `y = beta - 1/2`, `|y| < 1/2`
unconditionally) let `Bhat(z, z') = (aL^2)^{-1} sum_k phihat(z-tau_k)
phihat(z'-tau_k)` denote normalised bilinear incidence.

**LAW D (diagonal law).** For all complex `z, z'`, the full-grid kernel is
alias-free:

```text
sum_{k in Z} phihat(z - tau_k) phihat(z' - tau_k) = L * Phi2(z - z').
```

The paper states its Lemma 2.2 for real arguments; the proof — Poisson
summation plus the support observation that the only surviving dual frequency
is 0, because `H = phi_z * phi_{z'}` is supported in `[-L, L]` and vanishes at
the endpoints — never uses reality, and the paper's own Appendix B records
numerical checks of the identity "at both real and complex arguments". The
consequence it never draws: taking `z' = z`,

```text
sum_{k in Z} phihat(z - tau_k)^2 = a L^2     for EVERY z in C.
```

The *bilinear* self-incidence of every zero equals `+m_rho` per unit
multiplicity in the paper's normalisation — at every depth, at every
position. (The quantity that explodes like `X^{|2beta-1|}` for deep pairs —
the paper's Remark 5.10 — is the *Hermitian* mass `sum |phihat|^2 =
L*Phi2(2iy)`; the bilinear square is rigid.) A pair `{rho, 1-conj(rho)}`
therefore contributes bilinear trace exactly `+2 m_rho`, like two on-line
zeros. The paper's §6 says explicitly that "nothing is assumed about the
traces of the individual pair blocks"; LAW D is that unretained datum, pinned.

**LAW E (signed subgrid envelope).** The imaginary mass is again alias-free:
`Im phihat(t - iy - r)` as a function of real `r` is band-limited to
`[-L/2, L/2]` with density `phi(u) sinh(yu)`, so

```text
sum_{k in Z} (Im phihat(t - iy - tau_k))^2
    = L * int phi^2(u) sinh^2(yu) du  =:  a L^2 sigma^2(y),
```

independent of `t`. Since every omitted term of LAW D's real part is
`(Re phihat)^2 >= 0`, for EVERY subgrid `S` (any truncation, any placement)
and every real ordinate `x`:

```text
Re sum_{k in S} phihat(z - tau_k)^2   in  [-aL^2 sigma^2(y), aL^2 (1 + sigma^2(y))]
|Im sum_{k in S} phihat(x - tau_k) phihat(z - tau_k)|  <=  aL^2 sigma(y)
```

(the second by Cauchy–Schwarz against the two alias-free masses). Hence every
normalised on/off cross cell obeys the rational-boundable envelope

```text
2 Re( Bhat(x, z)^2 )  >=  -2 sigma^2(y),
```

and every pair's truncated bilinear trace is `>= -2 m_rho sigma^2(y)`. This
is the "rational lower envelope for `2 Re(B(x,z)^2)` on every cell" that the
hierarchy's level 1 required, and it is signed in the load-bearing direction:
`sigma(0) = 0`, so **negative incidence mass requires depth**. On-line data
cannot manufacture any of it, at any truncation.

**LAW F (depth floor and strip cap).** By convexity of `sinh` through the
origin, `sigma^2(y) <= sinh^2(yL/2)`. All zeros of zeta satisfy
`0 < beta < 1` unconditionally (classical, de la Vallée Poussin), so
`y < 1/2` and

```text
sigma(y) < sinh(L/4)      for every zero at bandwidth L.
```

An off-line pair whose cross column reaches `|Im Bhat| = m` needs
`sigma(y) >= m` by LAW E, hence depth `y >= y_min(m) := inf{y : sigma^2(y) >=
m^2}` — and is impossible at ANY placement once `m >= sigma(1/2^-)`.

## What is from the paper and what is new

From the paper: the window family, the critical grid, the transpose summand,
the normalisation, Lemma 2.2 for real arguments, the parenthetical that pair
traces are unretained, and the numerical observation (its Appendix B) that
Lemma 2.2 holds at complex arguments. New here: the complex statement used
structurally; the bilinear/Hermitian split (rigid diagonal vs `X^{|2beta-1|}`
mass); the alias-free imaginary-mass identity; the subgrid two-sided
envelope; the depth floor and cap; and the assembly into an exclusion of the
pinned obstruction family. All of it is elementary — Poisson summation and
support arithmetic — which is the point: it was available to the paper's
interface all along and simply not retained.

## The exclusion, wall by wall

Every member of the family dies on the first wall it hits; the table lists
them in the order they bite. Margins are exact integers or measured values
from `incidence_law.py`.

| Wall | Statement | What it kills | Margin |
|---|---|---|---|
| W1 (cap) | `sigma(y) < sigma(1/2^-) <= sinh(L/4)` at every placement | every member with `m >= sigma(1/2^-)`: at `L = 8`, `sigma(1/2^-) = 1.315`, so **every `m >= 2`** dies at every placement; the theta -> 0 defeat needed `m -> infinity` | `m - 1.315` at `L = 8` |
| W2 (diagonal) | full grid: bilinear pair trace `= +2 m_rho` (LAW D) | the bad pair's declared `-2m^2` on the full grid, every `m >= 1` | exact integer `2m^2 + 2` (= 4 at `m = 1`, 202 at the report's pinned `m = 10`) |
| W3 (strictness) | on a proper subgrid, on-line self- and mutual incidences sit strictly below 1 (omitted-tail positivity) | the family's on-line declarations (`P = n` exactly, mutual incidence exactly 1), on every truncation — so the family cannot escape W2 by truncating | measured deficits `> 0` at every probe; e.g. `1.2e-3` for a zero one window-length inside a half grid |
| W4 (depth floor) | `sigma(y) >= m` forces `y >= y_min(m)` | constrains any near-family configuration: at `L = 8` even `m = 1` owes depth `y >= 0.4154` of an available `0.5` | `depth_floor(1) = 0.41537...` |

The moment-matched dilution reuses the identical bad block
(`MomentMatchedFamily(m, k, ·).bad == ScalarFamily(m)`, asserted in code), so
W1–W4 transfer unchanged; the dilution repaired the *aggregate* trace
identity, and none of these walls is aggregate.

Quantitative residue worth recording: the family's defeat of the recovery
coefficient was `theta <= 3/(2m^2+1)` for every abstract `m`, driving
`theta` to zero. With LAW E/F, members realisable at bandwidth `L` have
`m < sigma(1/2^-)`, so the defeat available from this family is capped at

```text
theta  >=  3 / (2 sigma^2(1/2^-) + 1)
```

— measured `0.6729` at `L = 8`, `2.68e-2` at `L = 16`, `7.55e-4` at `L = 24`.
Exponentially small in `L`, but nonzero, explicit, and now the adversary pays
*depth* for every unit of negativity, which is the currency the level-2 mass
accounting can charge (below).

## Mass constraints, recorded and hedged

The hierarchy's level 1 also asks for "an unconditional mass constraint" on
the depth cells. Two classical ones are recorded here for the level-2 LP;
they are literature-pinned statements, hedged, not instrumented in this
session, and none of the exclusion above uses them.

- **Littlewood's lemma** plus the unconditional second moment of
  `zeta(1/2+it)` gives `sum_{T < gamma <= 2T} m_rho (beta - 1/2)^+ <<
  T log log T`; in kernel-depth units `b = yL` at bandwidth `L = lambda l`
  this reads `sum m_rho b_rho <= (lambda/2)(log log T + O(1)) N(T, 2T)` —
  the average depth per zero is `O(log log T)` kernel units.
- **Zero-density** (Ingham's `N(sigma, T) << T^{3(1-sigma)/(2-sigma)}
  log^5 T` suffices; sharper is known): cells at fixed depth `y >= delta`
  carry `O(T^{1-c(delta)})` pairs — power-small mass exactly where LAW E
  permits the most negativity.

Together with LAW E these say: negative incidence mass requires depth, depth
is scarce in aggregate, and fixed depth is power-scarce. That is the shape
the level-2 "marked two-gap words with projective consistency" analysis needs.

## What is not achieved, stated so it cannot be misread

- **No proportion moves.** The pinned `0.6725007...` is untouched. The laws
  add retained state to the interface; converting that state into a positive
  `theta` for an actual strengthened rank–trace lemma is the open level-2+
  task, and `theta_recovery_floor` decays with `L`, so nothing here even
  hints at a constant.
- **The exclusion is of the exact pinned family.** Epsilon-perturbed
  families (on-line incidences `1 - delta`, pair diagonal `-2m^2 + delta`)
  are constrained by W1/W4 but not killed by W2/W3's exactness; a
  perturbation-robust exclusion is precisely the projective-consistency work
  of level 2, and pretending otherwise would repeat the mistake that
  `CLEAN-KILL-REPORT.md` exists to prevent.
  *(Delivered 2026-08-11: `LEVEL2-GAP-CONSISTENCY.md` supplies it by
  bounding the quantity rather than the declaration — `R(P) <= n kappa(nu)`
  for any real configuration — and also removes the n-extensivity of the
  per-cell floor below.)*
- **The laws do not distinguish zeta from anything.** They hold for every
  conjugate-closed multiset in the open strip (measured on the
  Davenport–Heilbronn off-line zero, defect `2.7e-14`). Gate #3 does not
  apply because no RH-explaining structure is claimed — but it was checked
  anyway, in the direction it must hold.

## Controls ledger

| control | instrument | measured |
|---|---|---|
| truncation ladder (LAW D, real + deep diagonal; LAW E) | `audit_identities` | defects descend `1.7e-13 -> 5.4e-19` (K = 150, 300, 600 at dps 25); tail rate consistent with `K^-3` |
| lesion (grid stretched by 65/64: aliasing returns) | `audit_identities` | defect `0.3038`, flat across the ladder — does not respond to refinement, the artifact-vs-real signature |
| decoy (diagonal planted wrong by `aL^2/64`) | `audit_identities` | refuted at exactly the planted offset |
| translation invariance | `audit_identities` | shifted grid, same defect floor |
| envelope floors on random subgrids | `envelope_scan` | worst margins `+3.3e-4` (floor), `+6.7e-3` (ceiling), `+1.8e-2` (cross) over 60 trials — no violation, and the floor is nearly attained, so the envelope is not slack |
| strictness on proper subgrids | `online_subgrid_strictness` | deficits strictly positive at every probe |
| exact family margins | `family_margins` | integer `2m^2 + 2`; `m_cap(L=8) = 1.315`; `depth_floor(1) = 0.4154` |
| rival (Davenport–Heilbronn off-line zero, pinned digits) | `dh_rival_check` | LAW D defect `2.7e-14` at true depth `0.30851718...`; `sigma^2 = 0.4615` |
| precision response | test ladder at dps 15/18/25 | identity defects track the truncation floor, not the working precision; the lesion's defect tracks neither |

## Reproduction

From the repository root:

```bash
.venv/bin/python hunts/frontier_math/incidence_law.py
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_incidence_law.py
```

The first command prints the full audit (~100 s); the second runs the
controls (~60 s). The family side of every exclusion check is integer or
rational arithmetic; the kernel side is closed-form (the ramp is polynomial,
so `phihat` and `Phi2` are finite combinations of sin/cos values) evaluated
in mpmath at stated precision with the ladders above.
