# Results: a kernel-checked zero of zeta on the critical line between 14.13 and 14.14

**2026-10-11. Grade: kernel-checked**, in a hunt directory (`hunts/README.md`: a hunt
does not promote its own claim; landing this in the Lean arm is the owner's call).

    theorem HardyFirstZero.first_zero_on_line :
        ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50), riemannZeta (1 / 2 + t * I) = 0

Lean 4 `v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` (the revision
`lean/lake-manifest.json` pins), `riemannZeta` is Mathlib's own. Zero `sorry`, no
`native_decide`, no `axiom` declaration; `#print axioms` reports `propext`,
`Classical.choice`, `Quot.sound` for the theorem and for the eight named lemmas it is
assembled from (`lean/CheckAxioms.lean`). The four `ZetaLean` modules it imports are compiled from
this commit's own sources by `lean/build.sh` (`RUNS.md`). Outside review: none yet,
pending external verification. Nothing here bears on RH (`docs/08`): one zero on the line
is a fact about one zero.

## 1. What is kernel-checked, file by file

| file | what it proves |
|---|---|
| `Spine.lean` | `exists_zero_of_sign_data`: a zero in `(a, b)` from `hX` and `hG` below |
| `Phase.lean` | `gammaR_re_pos`: `hG` from Euler's limit; `gammaR_re_pos_first` at the endpoints; `first_zero_on_line_of_zeta_product` |
| `EulerMaclaurin.lean` | `corrected_trapezoid`; `zeta_em4`, the order-4 representation of `riemannZeta` on `Re s > 0, Im s > 0`; `zeta_em4_error`, its remainder bound |
| `BoxSupport.lean` | `contains_sumBoxes`, `main_eq`, `em30_bound`: the remainder at `N = 30` as a rational function of the height |
| `Boxes.lean` (generated) | the 60 term boxes `m^(-s)`, `1 ≤ m ≤ 30`, at both endpoints, each checked against `dirichletTermBox2` by `decide +kernel` |
| `FirstZero.lean` | `zeta_product_re_neg` (`hX` at the endpoints) and `first_zero_on_line` |

**The sign test** (`Spine.lean`). For real `a < b`:

    (hX : (riemannZeta (sOf a) * conj (riemannZeta (sOf b))).re < 0)
    (hG : 0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re)
      → ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + t * I) = 0

with `sOf t = 1/2 + t*I`. `hardyZ t = Lambda(sOf t) / d(t)` with `d(t) > 0` and
`Lambda = zeta * Gammaℝ`, so `Z(a) Z(b) d(a) d(b) = X G` with `X`, `G` the two products;
the left side is real, so multiplying by `conj X` and taking real parts gives
`Z(a) Z(b) d(a) d(b) Re X = ‖X‖² Re G > 0`, and the intermediate value theorem on
`continuous_hardyZReal` gives the zero. `hG` only asks that the phase of `Gammaℝ` turn by
less than a quarter turn between `a` and `b` (the true turn is `0.0040528` radians), so
no value of the Riemann-Siegel phase is ever computed.

**The phase lemma** (`Phase.lean`). With `z = 1/4 + ia/2`, `w = 1/4 - ib/2`,
`delta = (b - a)/2`, `K = ab/4`, `c_j = j + 1/4`: `Gammaℝ(sOf a) conj Gammaℝ(sOf b) =
pi^(-1/2 + i delta) Gamma(z) Gamma(w)` (`gammaR_prod`); the Euler-limit approximant
`V_n = pi^(-1/2 + i delta) GammaSeq z n GammaSeq w n` is a positive real times
`exp(x_n + i phi_n)` with `phi_n = delta log pi - delta log n + Σ_{j ≤ n} arctan(delta c_j /
(c_j² + K))`, because `(z + j)(w + j) = (c_j² + K) - i delta c_j` (`Vn_polar`);
`phi_n <= delta (log pi + 5)` (`phi_le`) and `phi_n >= delta (log pi - 1 - 2K) - 66 delta³`
for `n >= 1` (`le_phi`); so `Re V_n >= cos L ‖V_n‖` with `L < pi/2`, and
`GammaSeq_tendsto_Gamma` carries it to the limit (`gammaR_re_pos`). At the endpoints,
with `L = 11/20` and the crude bounds `0 <= log pi <= pi - 1`, the window is
`[-0.5045, 0.0357]` against a true limit of `-0.0040528`.

**The zeta representation** (`EulerMaclaurin.lean`). For `Re s > 0`, `Im s > 0`, `N >= 2`:

    ‖riemannZeta s - (Σ_{n<N} n^(-s) + N^(1-s)/(s-1) + N^(-s)/2 + s/12 · N^(-s-1))‖
      ≤ ‖s(s+1)(s+2)(s+3)‖ · ((N-1)^(-σ-3) / (σ+3)) / 720

(`zeta_em4_error`). The proof: on `[x, x+1]` with the kernel `k = (t-x)²(x+1-t)²/24`, one
fundamental-theorem step on `k g''' - k' g'' + k'' g' - k''' g` (its derivative is
`k g'''' - g` since `k'''' = 1`) gives the corrected trapezoid rule with remainder
`∫ k g''''`, `0 <= k`, `∫ k = 1/720` (`corrected_trapezoid`); for `g = t^(-s)` the block
`eBlock s x` is closed-form and bounded by `‖P4 s‖ x^(-σ-4)/720` (`norm_eBlock_le`); for
`Re s > 2` every series converges absolutely and the identity is a rearrangement of
shifted Dirichlet series (`zeta_em4_of_two_lt`); the tail is differentiable on the
quarter plane by `differentiableOn_tsum_of_summable_norm` on small balls, and the
identity theorem on that convex set carries the identity to the critical line
(`zeta_em4`), exactly the pattern of the lab's `dhBlockSum_eq_DH`; the tail is summed by
the integral test (`norm_tail_le`).

**The evaluation** (`BoxSupport.lean`, `Boxes.lean`, `FirstZero.lean`). The main term is
`Σ_{m<30} m^(-s) + 30^(-s) · c(s)` with `c(s) = 30/(s-1) + 1/2 + s/360` (`main_eq`), an
exact Gaussian rational at a rational point. Each `m^(-s)` is enclosed by the lab's
`dirichletTermBox2` (`lean/ZetaLean/IntervalCExp.lean`) at `nLog = 40`, `nExp = 24`,
`p = 96`, `kE = 8`; the generator `gen_boxes.py` writes each box as a literal from the
lab's bit-exact mirror, and the kernel checks every literal against the definition
(`dirichletTermBox2 ... = tA m := by decide +kernel`), so the mirror is not trusted. The
remainder at `N = 30` is bounded with `‖z‖ <= |Re z| + |Im z|` and
`29^(-7/2) <= 1/(29³ · 5)` (`em30_bound`), giving the inflation radii `1091/5000000` and
`547/2500000`. One interval product, decided by the kernel, shows the upper end of
`Re(zeta_a conj zeta_b)` over the inflated boxes is negative (`product_hi_neg`;
the generator's exact rational pre-check of the same quantity gives `-1.37863e-5`, against
the true value `-1.56806e-5` of `Re(zeta_a conj zeta_b)`).

## 2. The map: what represents zeta on `Re s = 1/2`

**Mathlib at the pinned revision.** Searched by name and by grep over
`Mathlib/NumberTheory/LSeries/`, `NumberTheory/Harmonic/`, `Analysis/SpecialFunctions/Gamma/`
and the whole tree for `EulerMaclaurin`, `Euler-Maclaurin`, `Stirling`, `logGamma`, `Binet`.

| declaration | where | hypotheses | use on `Re s = 1/2` |
|---|---|---|---|
| `riemannZeta_def_of_ne_zero` | `LSeries/RiemannZeta` | `s ≠ 0` | the definition, `zeta = Lambda / Gammaℝ`; `Lambda` is a Mellin transform of a theta kernel with no error bound attached |
| `completedRiemannZeta_eq`, `differentiable_completedZeta₀` | same | none | `Lambda = Lambda0 - 1/s - 1/(1-s)`, `Lambda0` entire; existence, not evaluation |
| `completedRiemannZeta_one_sub`, `riemannZeta_one_sub` | same | Gamma-pole guards | functional equation; used by `HardyZ.lean` for realness |
| `zeta_eq_tsum_one_div_nat_cpow`, `..._add_one_cpow`, `completedZeta_eq_tsum_of_one_lt_re` | same | `1 < re s` | Dirichlet series only right of 1; `EulerMaclaurin.lean` spends the first |
| `differentiableAt_riemannZeta`, `analyticOn_riemannZeta` | same | `s ≠ 1` | what the identity-theorem continuation needs |
| `riemannZeta_conj` | `Harmonic/ZetaAsymp` | none | conjugation |
| `ZetaAsymptotics.term`, `zeta_limit_aux1` | `Harmonic/ZetaAsymp` | real `s > 1` | an Euler-Maclaurin-like integral, real argument only |
| `hurwitzZeta_zero`, `expZeta_zero`, the `LSeriesHasSum` forms | `LSeries/HurwitzZeta*` | `1 < re s` for the series | same as zeta |
| `DirichletCharacter.LFunction_eq_LSeries` | `LSeries/DirichletContinuation` | `1 < re s` | same |
| `LSeries_eq_mul_integral` | `LSeries/SumCoeff` | partial sums `O(n^r)`, `r < re s`, summability | Abel summation; `r = 1` for zeta |
| `riemannZetaZeros`, `isDiscrete_riemannZetaZeros` | `LSeries/ZetaZeros` | none | discreteness of zeros |
| `Complex.digamma` and its recurrence, reflection, duplication | `Gamma/Digamma` | pole guards | no bound anywhere; its TODO is Gauss's integral |
| `Complex.GammaSeq_tendsto_Gamma`, `Gamma_conj`, `Gamma_ne_zero_of_re_pos` | `Gamma/Beta`, `Gamma/Basic` | none | Euler's limit, which `Phase.lean` spends |

No Euler-Maclaurin formula, no complex Stirling or Binet formula, no Dirichlet eta
lemma, and no explicit error bound for any representation valid on the line before
this hunt. Mathlib's `Stirling.lean` is for `n!`.

**The lab's own Lean** (`lean/ZetaLean/`), consumed or used as templates:
`HardyZ.lean` (`hardyZReal`, `hardyZReal_zero_iff`, `continuous_hardyZReal`, imported by
`Spine.lean`); `DHTailBound.lean` (`dhBlockSum_eq_DH`, the identity-theorem continuation
pattern, and `DH_tail_bound`, the integral-test pattern); `DHTailBound2.lean`
(`norm_trapezoid_sub_integral_le`, the order-2 template for `corrected_trapezoid`);
`Rigor.lean`, `IntervalExp.lean`, `IntervalCExp.lean` (`ComplexInterval`, `inflate`,
`dirichletTermBox2`, `contains_dirichletTermBox2`, imported by the box files);
`Ball*.lean`, `DHCertSupport.lean` (not needed at this height: rectangles suffice).

## 3. The route, and the ones not taken

| piece | route taken | routes not taken, and why |
|---|---|---|
| the phase | the sign test plus a quarter-turn bound from Euler's limit | Stirling or Binet for complex `Gamma`: absent from Mathlib, a project of its own; the integral for `Gamma'`: an absolute bound of order one against `|Gamma(1/4 + 7.065i)| = 2.33e-5`; digamma: no bound in Mathlib |
| zeta on the line | order-4 Euler-Maclaurin, 30 terms | order 2 (the lab's trapezoid): 471 terms for margin 1; Riemann-Siegel: one term but Gabcke's remainder, unformalized; Riemann's theta integral: `Lambda(1/2 + 14.13i) = -6.55e-8` against an integrand of absolute size `0.0115`; Dirichlet eta: the same continuation plus a division by `1 - 2^(1-s)`, no gain |
| the arithmetic | 60 literal term boxes, each checked by `decide +kernel`, then one interval product | one `decide +kernel` over the whole 29-term sum at both endpoints: stopped unfinished after 30 minutes (`RUNS.md`) |

## 4. Measured constants

All recomputed by `test_hardy_first_zero.py`; values from `sizing.py` and `gen_boxes.py`.

**Endpoints** (Arb at 128 bits and `mpmath.iv`, agreeing to every printed digit;
enclosure-carrying, so hardened; they are not used by the Lean proof, which computes its
own enclosures):

| | value |
|---|---|
| `Z(14.13)` | `-0.0037463383557063` |
| `Z(14.14)` | `+0.0041856189735666` |
| `Z'(gamma_1)` | `0.793160` |
| `theta(14.14) - theta(14.13)` | `0.0040528408849` |
| `Re(zeta(1/2+14.13i) conj zeta(1/2+14.14i))` | `-1.56806e-5` |

**Order-4 remainder bound against Arb** (defect is an upper bound on
`|zeta(s) - main term|` from the Arb ball; the bound is the sharp form with `‖P4 s‖`,
not the cruder rational form the Lean instantiation uses):

| `N` | bound at `14.13` | defect at `14.13` |
|---|---|---|
| 10 | `7.6146e-3` | `1.3228e-3` |
| 20 | `5.5701e-4` | `1.1315e-4` |
| 30 | `1.26796e-4` | `2.7207e-5` |

**Truncation that decides the sign** (margin = `-Re(M_a conj M_b)` over the slack
`|M_a| E_b + |M_b| E_a + E_a E_b`): order 4 needs `N = 15, 18, 21, 27` for margins
`1, 2, 4, 10`; at `N = 30` the slack is `1.0231e-6` against `Re(M_a conj M_b) =
-1.56742e-5`, margin `15.32`. Order 2 needs `N = 471` for margin 1 (margin `1.112` at
`N = 500`) and fails at `N = 30`.

**The boxes as the kernel sees them.** At `N = 30`, `nLog = 40`, `nExp = 24`, `p = 96`,
`kE = 8`, the main-term boxes are `3.7e-9` wide (widest term `2.1e-10`) with endpoints of
at most 97 bits. With the sharp remainder bound the upper end of the product is
`-1.45539e-5`; with the Lean instantiation's cruder radii `1091/5000000` and
`547/2500000` it is `-1.37863e-5`. At `nLog = 16` the boxes cannot decide the sign, and
with ten times the radii neither can the product: those are the two lesions.

**Decimals of `gamma_1` against terms** (order 4, `N` for margins 1, 2, 4, 10; each
interval is the decimal bracket of `gamma_1` and each brackets a sign change):

| decimals | interval | margin 1 | 2 | 4 | 10 |
|---|---|---|---|---|---|
| 2 | `(14.13, 14.14)` | 15 | 18 | 21 | 27 |
| 3 | `(14.134, 14.135)` | 30 | 36 | 42 | 55 |
| 4 | `(14.1347, 14.1348)` | 57 | 69 | 81 | 106 |
| 5 | `(14.13472, 14.13473)` | 102 | 121 | 145 | 187 |
| 6 | `(14.134725, 14.134726)` | 242 | 281 | 338 | 439 |

**Control.** On `(14.12, 14.13)`, which holds no zero, the same test at `N = 30` does
not pass: `Re(M_a conj M_b) > 0`.

## 5. What it cost, and what is left

Lean compile times on one core of the container, warm page cache: compile cycles of 4 to
20 s for every hand-written file, 2 min 48 s for `Boxes.lean` (120 kernel decisions), 10 s
for `FirstZero.lean`; the clean build of everything, the four `ZetaLean` dependencies
compiled from source included, took 4 min 14 s (`RUNS.md`). About 2,200 lines of Lean,
833 of them generated.

What is left is not mathematics:

1. **Review.** Nobody but the author has read the proofs. The statement is the thing
   to check: Mathlib's `riemannZeta`, the point `1/2 + t*I`, the open interval of reals.
2. **Landing.** Moving the files into `lean/ZetaLean/` (the kernel-checked arm) and into
   `lake build` is the owner's decision; the hunt does not promote itself.
3. **A second kernel.** The toolchain ships `leanchecker` and `nanoda`; the lab has used
   the latter before. Not run here.
4. **More digits.** The trade table prices them: four decimals need about 81 terms at
   margin 4, six need about 338. The Lean changes in the generator's `N` and points and in the
   `N`-specific `em30_bound`.

## 6. Prior art

Searched 2026-10-11, for any formally verified (Lean, Isabelle, Coq or Rocq, HOL)
localization of an explicit nontrivial zero of zeta:

- arXiv API, eight queries (zeta with Lean and zeros, Isabelle with zeta and zeros,
  "formally verified" with zeta, formalization with "critical line", "proof assistant"
  with "Riemann zeta", Euler-Maclaurin with formalization, Hardy "Z function" with Lean,
  kernel with zeta, Lean and zero);
- zbMATH Open API, ten queries (proof assistant, Isabelle, Lean, Coq, HOL, "formally
  verified", formalization, interval arithmetic, "formal proof", "verified computation",
  each with zeta or Riemann);
- web search, about a dozen queries, including Lean Zulip, Mathlib pull requests,
  PrimeNumberTheoremAnd, CoqInterval and Turing's method;
- the Isabelle Archive of Formal Proofs topic lists for number theory and analysis;
- the statement file of the `zeta23` Lean formalization; `references/papers.md`.

**Found, and none of it a formal localization of an explicit zero:**

- Alpöge and Furman, arXiv `2608.13637` (2026), with a Lean 4 formalization: more than two
  thirds of the zeros are simple and on the line, as an asymptotic proportion in dyadic
  windows. Their theorems imply zeros on the line at large heights; they name none.
- Eberl's Isabelle entries (AFP, 2017): `The Hurwitz and Riemann ζ Functions`, which
  continues zeta by Euler-Maclaurin, `The Euler-MacLaurin Formula`, `Stirling's formula`.
  The infrastructure for this computation exists in Isabelle; no entry localizes a zero.
- Loeffler and Stoll (2025), `Formalizing zeta and L-functions in Lean`: the Mathlib
  library this hunt sits on; non-vanishing on `Re s >= 1`, no zeros located.
- Platt and Trudgian (2021), RH verified to `3 · 10^12` with interval arithmetic: rigorous
  numerics, not a proof assistant.
- Hu, Xu, Sun, Jin and Xiong, arXiv `2606.15096` (2026): Rocq/CoqInterval checks of
  RH-adjacent inequalities, no zero.

**Not reachable from this session:** GitHub code search (refused for repositories outside
the session), the Lean Zulip search (needs a login), zbMATH's web interface (403; its API
was used). So the bounded statement is: **no formal localization of an explicit nontrivial
zero of zeta was found in the searched set.** That is not a novelty claim; it says nothing
about private or unindexed work, and the theorem here is original to this lab in the
provenance sense only.

## 7. Limitations, and the kill conditions

**Limitations.** One interval, `(14.13, 14.14)`, one zero; nothing about any other zero and
nothing about RH. The theorem is checked against the pinned Mathlib build in the main
clone's `lean/.lake` and this commit's `ZetaLean` sources; it is not yet in `lake build`,
nobody but its author has read it, and no second kernel has replayed it. The trade table,
the timings and the margins are measurements (floating point or exact rational arithmetic
on one machine), not theorems, and the theorem does not depend on them: the kernel decides
every inequality the proof uses. The Arb and `mpmath.iv` endpoint values are a cross-check
on the numbers, not an input to the proof.

**Kill conditions** (`MISSION.md`). None fired: the Arb enclosures sit inside the order-4
bound at every truncation tried, with a factor about 4.7 to spare; the kernel accepted the
box evaluation at the first parameter set the mirror passed; and the prior-art search
found no formal localization of an explicit zero.

## 8. The doors

The hunt measures a cost curve, terms per endpoint against decimals of `gamma_1` pinned,
not a mathematical ceiling; it is recorded in door form because the curve has an optimum
that later work will want to move. Candidate status: measured, at the two-decimal
interval, order 4, `N` from 15 to 30; the curve itself is not proved, only the one point
`N = 30` is used by the theorem.

**Active constraints at the optimum.** At `N = 30` the binding constraint is the remainder
bound, not the box width: the boxes are `3.7e-9` wide while the radii are about `2.2e-4`,
and the sharp bound is itself about 4.7 times the true defect. Ranked by what moving it
buys: the crude `‖z‖ <= |Re z| + |Im z|` and `29^(-1/2) <= 1/5` in `em30_bound` (worth a
factor of about 1.7 in the radius), then the `720` and the `N - 1` of the tail; the Taylor
orders of the boxes have more than two orders of magnitude to spare and do not bind.

**The frozen-constant inventory.** The order of the expansion (4): order 2 costs 471
terms; order 6 would, by the same arithmetic, cost fewer terms (not measured) and a longer
kernel proof, a genuine trade shape. The interval `(14.13, 14.14)`: a decimal more costs
about twice the terms (section 4), a genuine trade against the headline. `N = 30`: chosen
for a margin of 15 before the radii were made crude. `(nLog, nExp, p, kE) = (40, 24, 96, 8)`:
chosen, not optimized; lowering them shrinks literals and kernel time until the lesion at
`nLog = 16`. `L = 11/20` and `0 <= log pi <= pi - 1` in the phase lemma: free, the window
is a factor three inside `pi/2`. The constant `66` and the dropped `j = 0` term in
`le_phi`: free at this `delta`.

**The information class.** Every door above stays inside the data the current family
reads: values of `n^(-s)` at two rational points and elementary bounds. The one door that
reads more is the Riemann-Siegel route, which replaces 30 terms by one at the price of the
Gabcke remainder, a different and much longer piece of analysis.
