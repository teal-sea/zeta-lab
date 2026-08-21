# Adversary 1 (normalization and definition): findings

Scratch analysis, 2026-08-16. Written by an adversary tasked with breaking the
claim `0.0576 < Lambda_DH <= 0.4006343708899557`, not with defending it. All
numbers below were produced by code written from the definitions in
`zeta/epstein.py`, in
`/tmp/claude-0/-home-user-zeta-lab/ea2c50e5-c6c1-5be9-ac30-eda79b8fac85/scratchpad/`
(`a1_h0.py`, `mel2.py`, `mel3.py`, `a1_zeta_frame.py`, `dob2.py`). Nothing in
this directory was modified.

## Summary

The interval **survives** as a statement about the object the claim itself
defines. Every internal normalization check passed, several to 50 digits.

The interval **does not survive** as a statement about the object it is
*named* after. In the normalization used by every source the hunt cites for
it (de Bruijn 1950, Newman, Rodgers-Tao, Polymath 15, and Dobner 2020, whose
Theorem 1 the strictness of the lower bound leans on), the de Bruijn-Newman
constant of the Davenport-Heilbronn function is **four times** the number
here:

    hunt frame    :  0.0576 < Lambda_DH <= 0.4006343708899557
    Dobner frame  :  0.2304 < Lambda_DH <= 1.6025374835598228

## 1. H_0 = Xi_DH, and (c, a) = (1, 1) - confirmed, not the defect

Independent quadrature of `int_0^inf Phi_DH(u) cos(zu) du` against
`zeta.epstein.completed_dh(1/2 + iz)` at dps 40, nine points, real and
complex:

| z | relative defect |
|---|---|
| 0.3 | 1.09e-52 |
| 1.0 | 2.55e-52 |
| 5.0 | 4.74e-52 |
| 14.7 | 2.35e-51 |
| 2.0 + 0.4i | 0.0 |
| 0.7i | 0.0 |
| 8.5 - 1.25i | 0.0 |
| 30.0 | 4.82e-51 |
| 85.7 + 0.308517182457i | absolute 1e-59, both sides ~1e-32 |

Rival constants are excluded by orders of magnitude, at dps 30:

| rival | relative distance from the quadrature at z = 1 / z = 4 / z = 2+0.5i |
|---|---|
| (c, a) = (1, 1) | 3.9e-32 / 3.7e-32 / 1.1e-32 |
| (c, a) = (1/8, 1/2) | 0.865 / 0.416 / 0.837 |
| (c, a) = (1, 2) | 0.266 / 1.076 / 0.854 |

So the zeta-style `H_0 = (1/8) Xi(z/2)` reading is dead, as the hunt says.

## 2. The Mellin derivation - confirmed

With `psi(x) = sum_{n>=1} n a_n exp(-pi n^2 x / 5)`:

* **Theta transformation** `psi(1/x) = x^{3/2} psi(x)`, exact rational
  inputs, dps 50: relative defect 5.3e-57, 5.4e-57, 7.3e-57, 1.4e-56,
  6.1e-57 at x = 3/10, 7/10, 1, 19/10, 4. This is exactly the evenness of
  Phi_DH, which is de Bruijn's hermitian hypothesis.
* **No pole terms.** `F(s) = int_1^inf psi(x) [x^{(s+1)/2-1} + x^{(2-s)/2-1}] dx`
  with **no** `1/s` or `1/(s-1)` residue terms reproduces `completed_dh` to
  3.2e-32 (s=2), 2.5e-32 (s=1), 2.5e-32 (s=0), 1.6e-31 (s=1/2+5i),
  4.9e-32 (s=4/5+3i), 8.6e-31 (s=-3). The zeta analogue of this split needs
  `-1/s - 1/(1-s)`; DH needs nothing, because `psi` decays
  super-exponentially at both ends (measured: psi(0.02) = 8.03e-12,
  matching `x^{-3/2} exp(-pi/(5x))` to six digits).
* **The factor 4 and the e^{3u/2}** follow from `x = e^{2u}`, `dx/x = 2 du`,
  `x^{(s+1)/2} = e^{u(s+1)}`, `s = 1/2+iz`, plus evenness converting the
  full-line integral to twice the half-line one. Verified numerically in
  section 1.

## 3. The defect: the frame is not the de Bruijn-Newman frame

Dobner, arXiv:2005.05142v2, equations (1), (2), (5), (6), read from the PDF:

> (1)  xi((1+iz)/2) = int_{-inf}^{inf} Phi(u) e^{izu} du
> (2)  Phi(u) := 4 sum (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) e^{-pi n^2 e^{4u}}
> (5)  Phi_F(u) := (1/2pi) int_{-inf}^{inf} xi^F((1+ix)/2) e^{-ixu} dx
> (6)  xi_t^F((1+iz)/2) := int_{-inf}^{inf} e^{tu^2} Phi_F(u) e^{izu} du

and in his proof of Theorem 1, `H(z) := xi^F((1+iz)/2)`.

The argument is `(1+iz)/2 = 1/2 + i z/2`. The hunt's is `1/2 + i z`. So

    z_Dobner = 2 z_hunt,     and therefore     t_Dobner = 4 t_hunt,
    Lambda_F (Dobner) = 4 * Lambda_DH (hunt).

The quadratic scaling is the hunt's own rule (THEOREM13.md section 6:
"Strips scale by 1/a, times by a^2"), applied to a = 1/2.

**Cross-check on zeta, both frames, verified numerically** (dps 30, my own
Phi in each frame against `zeta.core.xi`):

| frame | H_0(z) | quadrature defect | Delta for zeta | Delta^2/2 | literature |
|---|---|---|---|---|---|
| Polymath / Rodgers-Tao / Dobner (x = e^{4u}) | (1/8) Xi(z/2) | 4.4e-17 (input-precision limited) | 1 | **1/2** | de Bruijn's classical 1/2 |
| this hunt (x = e^{2u}) | Xi(z) | 4.7e-32 | 1/2 | **1/8** | - |

So the `Delta^2/2` dictionary is **correct** and reproduces de Bruijn's 1/2
for zeta *in zeta's classical frame*. It is the hunt's own frame that is not
that frame. In the hunt's frame the classical facts read

    Lambda_zeta <= 1/8   (de Bruijn),      0 <= Lambda_zeta <= 0.055   (Newman, Polymath 15)

and `NOVELTY.md`'s "zeta record for calibration: 0 <= Lambda_zeta <= 0.22 ...
Lambda_zeta < 1/2" is quoted in the other frame without conversion.

### 3a. The false sentence

`THEOREM13.md` section 6:

> Dobner's deformation xi_t^F((1+iz)/2) = int e^{tu^2} Phi_F(u) e^{izu} du is
> the hunt's H_t up to the constant factor 2 (Phi even turns the full-line
> integral into 2 int_0^inf ... cos(zu) du), so the two share zeros and share
> Lambda exactly.

The factor 2 is right and the conclusion is wrong: the substitution also
carries `z -> z/2`. Working it out, Dobner's `Phi_F(u) = Phi_DH(2u)` and

    xi_t^F((1+iz)/2) = H_{t/4}(z/2).

They share zeros only after the z-rescaling, and they do **not** share
Lambda; they differ by exactly 4.

`Phi_F(u) = Phi_DH(2u)` is measured, not merely derived. Evaluating Dobner's
(5) directly for DH, `Phi_F(u) = (1/pi) int_0^R Xi_DH(x/2) cos(xu) dx` with
R = 55 at dps 15 (truncation floor about 1e-9):

| u | Dobner Phi_F(u) via (5) | hunt Phi_DH(u) | hunt Phi_DH(2u) | \|Phi_F - Phi_DH(2u)\| |
|---|---|---|---|---|
| 0 | 2.30541982461 | 2.30541982597 | 2.30541982597 | 1.4e-9 |
| 0.15 | 2.03294525009 | 2.23862824073 | 2.03294524905 | 1.0e-9 |

The u = 0.15 row separates the hypotheses: Dobner's Phi_F agrees with
Phi_DH(2u) to the truncation floor and misses Phi_DH(u) by 0.206, i.e. by
2e8 times the numerical noise.

This sentence contradicts the paragraph immediately above it in the same
section, which correctly notes that zeta's classical convention has a = 1/2
while DH's has a = 1, and that a rescaling moves t quadratically.

### 3b. The numbers

    sigma_0 (flint, outward)   = 1.3951361582351097210613588712 ... 9375
    Delta  = sigma_0 - 1/2     = 0.8951361582351097210613588712   (hunt frame, a = 1)
    Delta^2/2                  = 0.40063437088995569444695475     (matches the claim)
    Delta_Dobner = 2 Delta     = 1.7902723164702194421227177424
    Delta_Dobner^2/2           = 1.6025374835598227777878190108   = 4 x the claim
    lower endpoint 4 x 0.0576  = 0.2304

Cross-check that the whole hunt lineage sits in the a = 1 frame: pair 1 of
`hunts/flow_repair/NOTES.md` has y0 = 0.30851718245663738555, and
y0^2/2 = 0.04759142593549104 reproduces that table's "naive y0^2/2" column
0.0475914 exactly. In Dobner's frame the same quadruple sits at
y0_D = 0.61703436491327477 and its naive landing is 0.19036570374196417.

## 4. Attacks that did NOT break anything

* **Pole terms.** None needed; verified at six s including s = 1 and s = -3.
* **The factor 4 / the e^{3u/2}.** Correct.
* **Evenness / hermitian symmetry.** Correct to 5e-57.
* **Decay.** `psi` super-exponential at both ends; b = 3 > 2 stands.
* **Delta^2/2 vs Delta^2/8 vs 2 Delta^2.** The rule is right; it reproduces
  de Bruijn's classical 1/2 for zeta in zeta's classical frame.
* **S# membership of DH**, checked one by one against Dobner's verbatim
  (i)-(iii) (extracted from the PDF, section 2):
  - not identically zero: f(2) != 0 (|f(2)| >= 1 - 0.2666).
  - (i) `sum |a_n| n^{-sigma} <= zeta(sigma) < inf` for sigma > 1 since
    |a_n| <= max(1, kappa) = 1.
  - (ii) m = 0; f entire (coefficient sum over a period is 0), finite order
    (a finite linear combination of order-1 Dirichlet L-functions).
  - (iii) `gamma(s) = alpha s^m (s-1)^m Q^s Gamma(omega s + mu)` with m = 0,
    alpha = (5/pi)^{1/2} in C\{0}, Q = (5/pi)^{1/2} > 0, omega = 1/2 > 0,
    mu = 1/2 with Re mu = 1/2 >= 0; and xi^F(s) = xi^F(1-s), measured
    defect ~1e-50.
  - Dobner's derived consequence "a_n nonzero for more than one n": holds.
  So Theorems 1 and 2 do apply, the real-rooted set is a closed half-line,
  and the strict lower bound is licensed. **No defect here.** The half-line
  structure is invariant under `t -> 4t`, so it transfers to the hunt's
  frame; only the *value* of Lambda does not.

## 5. What I would change

1. State the frame in the headline, every time: "in the normalization
   H_0 = Xi_DH, i.e. s = 1/2 + iz", and publish both pairs of numbers.
2. Delete or repair the "share Lambda exactly" sentence in THEOREM13.md
   section 6.
3. Convert the zeta calibration figures in NOVELTY.md, or move the whole
   hunt into Dobner's frame.

Note what the conversion buys rather than costs: in the common frame the
lower bound reads `Lambda_DH > 0.2304`, which is **above** the current best
upper bound for zeta (0.22, Polymath 15). Stated in the hunt's frame, 0.0576
sits below 0.22 and the comparison reads backwards.
