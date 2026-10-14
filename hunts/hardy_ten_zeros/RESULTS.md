# Results: at least ten kernel-checked zeros of zeta on the critical line below height 50

**2026-10-14. Grade: kernel-checked**, in a hunt directory (`hunts/README.md`: a hunt
does not promote its own claim; landing this in the Lean arm is the owner's call).

    theorem HardyTenZeros.ten_zeros_on_line_below_fifty :
        ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
          ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ts k * I) = 0

and the ten interval theorems it is assembled from, each of the form
`∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + t * I) = 0`:

| theorem | interval `(a, b)` | ordinate inside (mpmath, measured) |
|---|---|---|
| `HardyFirstZero.first_zero_on_line` (hunt #132) | `(1413/100, 707/50)` | `14.134725` |
| `HardyTenZeros.zero_in_2102` | `(2102/100, 2103/100)` | `21.022040` |
| `HardyTenZeros.zero_in_2501` | `(2501/100, 2502/100)` | `25.010858` |
| `HardyTenZeros.zero_in_3042` | `(3042/100, 3043/100)` | `30.424876` |
| `HardyTenZeros.zero_in_3293` | `(3293/100, 3294/100)` | `32.935062` |
| `HardyTenZeros.zero_in_3758` | `(3758/100, 3759/100)` | `37.586178` |
| `HardyTenZeros.zero_in_4091` | `(4091/100, 4092/100)` | `40.918719` |
| `HardyTenZeros.zero_in_4332` | `(4332/100, 4333/100)` | `43.327073` |
| `HardyTenZeros.zero_in_4800` | `(4800/100, 4801/100)` | `48.005151` |
| `HardyTenZeros.zero_in_4977` | `(4977/100, 4978/100)` | `49.773832` |

Each interval is the two-decimal interval holding the stated ordinate, as hunt #132 used
for the first. Lean 4 `v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`
(the revision `lean/lake-manifest.json` pins), `riemannZeta` is Mathlib's own. Zero
`sorry`, no `native_decide`, no `axiom` declaration; `#print axioms` reports `propext`,
`Classical.choice`, `Quot.sound` for the theorem, the ten interval theorems and the
nine named lemmas they rest on (`lean/CheckAxioms.lean`, twenty reports, audited
fail-closed by `lean/check_axioms.py`). `lean/build.sh` compiles every imported module
from this commit's sources: four `ZetaLean` modules, the six `HardyFirstZero` modules of
hunt #132 (unchanged) and this hunt's thirteen files (`RUNS.md`).

**What this does not say.** It says there are at least ten zeros on the critical line
with `0 < t < 50`. It does not say that these are the ten lowest zeros, that an interval
holds exactly one zero, or that there are no other zeros below 50: that needs a zero
count (Turing's method, for example), which is not attempted. The ordinates in the third
column are mpmath's, a measurement; the theorems name only the intervals. Outside
mathematical review and replay by an independent kernel are pending. Nothing here bears
on RH (`docs/08`): ten zeros on the line say nothing about the others.

**Automatic verification.** `.github/workflows/hardy-ten-zeros.yml` runs for relevant pull
requests and pushes to `main`, and on manual dispatch. It checks the exact PR head, runs
this hunt's numerical controls and generator check, fetches the pinned Mathlib cache,
rebuilds everything above serially into fresh scratch storage, and requires exactly the
twenty standard-axiom reports; missing, duplicate and nonstandard reports fail, and a
cancelled or skipped proof job fails its verdict job. A workflow definition is not a
replay: the Actions result at the commit being reviewed is the receipt.

Reproduce on a suitable build host, with elan installed:

```bash
(cd lean && lake exe cache get)
set -o pipefail
LAKE_DIR="$PWD/lean/.lake" bash hunts/hardy_ten_zeros/lean/build.sh 2>&1 | tee hardy-ten-zeros-build.log
.venv/bin/python hunts/hardy_ten_zeros/lean/check_axioms.py hardy-ten-zeros-build.log
```

## 1. What is kernel-checked, file by file

| file | what it proves |
|---|---|
| `PhaseShort.lean` | `le_phi_tail`: a lower end for hunt #132's partial phases that does not grow with the height; `gammaR_re_pos_tail`, the phase lemma with it; `gammaR_re_pos_short`, the phase condition for every bracket `0 ≤ a ≤ b ≤ 50`, `b - a ≤ 1/100`; `window_132_fails_at_4977`, the obstruction to hunt #132's window, stated |
| `TenSupport.lean` | `emN_bound`: the order-4 remainder at any truncation `N`, with an exact squared norm; `cBox_contains`, `zeta_mem_mainBox`: the main term as a box and the inflated box containing `ζ(1/2 + it)`; `contains_cpow_mul_coarsen`, `contains_one_cpow`: composite term boxes from their factors; `zero_of_tables`: one interval from two tables and one product |
| `Box2102.lean` ... `Box4977.lean` (generated) | per bracket: the term boxes at both ends (exp towers for primes, checked against `dirichletTermBox2`, coarsened products for composites), each by `decide +kernel`; the interval product; `zero_in_<tag>` |
| `TenZeros.lean` | `ten_zeros_on_line_below_fifty` |

**The sharpened phase window** (`PhaseShort.lean`). Hunt #132's lemma bounds the partial
phases of `π^(iδ) GammaSeq(z, n) GammaSeq(w, n)`,

    φ_n = δ log π - δ log n + Σ_{j ≤ n} arctan(δ c_j / (c_j² + K)),  δ = (b-a)/2,  K = ab/4,  c_j = j + 1/4,

below by `δ (log π - 1 - 2K) - 66 δ³`. At a two-decimal bracket (`δ = 1/200`) that leaves
the quarter turn once `K > 157.2`, above `t ≈ 25.1`; at `(49.77, 49.78)` it is `-6.19`, and
`window_132_fails_at_4977` proves it is below `-π/2` there. The loss is in the first terms,
where `c_j² < K` and `c/(c² + K) ≥ 1/c - K/c³` is useless. The arctangents are nonnegative,
so dropping the first `m` gives, for `1 ≤ m ≤ n`,

    φ_n ≥ δ (log π - 1 - log m - K/(m² - 1/16)) - δ³/(m² - 1/16)

from `Σ_{j=m}^{n} 1/c_j ≥ H_{n+1} - H_m ≥ log n - 1 - log m` (Mathlib's harmonic bounds)
and the telescoping `1/c_j² ≤ 1/(j - 1/4) - 1/(j + 3/4)`, which gives
`Σ_{j ≥ m} 1/c_j³ ≤ 1/(m² - 1/16)`. `gammaR_re_pos_tail` takes this lower end and the old
upper end `δ (log π + 5)` and repeats hunt #132's limit argument from `n ≥ m`.
`gammaR_re_pos_short` instantiates it once with `m = 8`, `L = 1/5`, and only
`0 ≤ log π ≤ π - 1`, `log 8 ≤ 7`, `K ≤ 625`, `δ ≤ 1/200`: the window is inside
`[-0.0889, 0.04]` for every bracket below 50, against true phase increments between
`0.0041` and `0.0104` (table in section 4).

**The remainder at any truncation** (`TenSupport.lean`). Hunt #132's `zeta_em4_error`
(order 4, for `Re s > 0`, `Im s > 0`, `N ≥ 2`) is used as it stands. Its instantiation
`em30_bound` fixed `N = 30` and used `‖z‖ ≤ |Re z| + |Im z|`; `emN_bound` takes any `N` and
uses `‖s(s+1)(s+2)(s+3)‖² = Π_{j<4} ((j + 1/2)² + t²)` on the line, exact and rational at a
rational height: for any rationals `r > 0`, `R ≥ 0` with `r² ≤ N - 1` and `Π ≤ R²`,

    ‖ζ(1/2 + it) - M_N(t)‖ ≤ R / ((N-1)³ · r · (7/2) · 720).

The generator picks `r` and `R` within `1e-6` and `1e-3` of `√(N-1)` and `√Π`, so the radius
the kernel uses is the sharp order-4 bound to within `1e-5` relative
(`test_lean_radii_are_what_the_side_conditions_need`).

**The evaluation** (`TenSupport.lean`, the `Box*.lean` files). The main term is
`Σ_{m<N} m^(-s) + N^(-s) · c_N(s)` with `c_N(s) = N/(s-1) + 1/2 + s/(12N)` (hunt #132's
`main_eq`), `c_N` an exact Gaussian rational. Term boxes: `1` exactly for `m = 1`; for a
prime `m`, the lab's `dirichletTermBox2` at `(nLog, nExp, p, kE) = (36, 16, 80, 8)` written
as a literal from the bit-exact mirror and checked by `decide +kernel` together with its
`normBound ≤ 2^8` side condition; for a composite `m = f g` (`f` its smallest prime factor),
the 80-bit coarsened product of the boxes of `f` and `g`, again checked literal by literal,
with containment from `n^(-s)` being multiplicative over the naturals
(`contains_cpow_mul_coarsen`, restated from the lab's
`ZetaLean.ComplexInterval.contains_cpow_mul_coarsen` in `lean/ZetaLean/DHCertSupport.lean`
so this hunt does not import that module's dependency chain). So only the 219 prime terms
need an exp tower; the 447 composite terms are one product each. One interval product per
bracket, decided by the kernel, shows the upper end of `Re(ζ_a conj ζ_b)` over the inflated
boxes is negative, and `zero_of_tables` closes the bracket through hunt #132's sign test
`exists_zero_of_sign_data` and `gammaR_re_pos_short`.

## 2. The three obstacles, sized before the Lean was built

The owner's brief named three. Each was measured first (`sizing.py`, `RUNS.md`).

1. **The phase lemma.** Hunt #132's window fails at two-decimal brackets from the fourth
   ordinate on (section 1, table in section 4). Keeping it would have meant narrower
   brackets: at `t ≈ 50` it needs `b - a < 0.00254`. The width-0.002 bracket
   `(49.7728, 49.7748)` around the last ordinate passes it (lower end `-1.239`), but its
   ends have `|Z| = 0.00146` and `0.00137` and need 80 and 83 terms (45 towers), against
   55 and 50 terms (31 towers) at `(49.77, 49.78)`, and the headline would lose its
   uniform two-decimal form. Sharpening the lemma cost about 280 lines of Lean and removed
   the constraint entirely.
2. **Narrower brackets need tighter enclosures.** Not needed once the window was
   sharpened: every bracket is two-decimal, width `1/100`. What binds instead is the
   endpoint nearest its zero: `25.01` is `0.00086` from the ordinate (`|Z| = 0.00118`) and
   `40.92` is `0.00128` from it (`|Z| = 0.00191`).
3. **Terms per endpoint.** Truncations are chosen per endpoint (`sizing.choose_truncations`),
   minimizing `N_a + N_b` subject to the rectangle sign test passing with the Lean radii
   multiplied by 1.5; the generator then re-runs the test in exact rational arithmetic at
   both radii and refuses to write a file that fails either. Over brackets 2 to 10:

| route (same margin 1.5) | term boxes | exp towers | projected kernel minutes |
|---|---|---|---|
| order 4, Lean radii (taken) | 684 | 219 | 11.2 |
| order 4, sharp bound | 684 | 219 | 11.2 |
| order 6, sharp bound | 334 | 131 | 6.7 |
| order 8, sharp bound | 246 | 103 | 5.3 |

   Projected at the measured 52 s per 17 towers of the first generated file (`RUNS.md`).
   **Order 4 was taken.** It reuses hunt #132's kernel-checked representation unchanged;
   orders 6 or 8 would save 4.5 to 6 minutes per build at this height but need a new
   Euler-Maclaurin development (a degree-6 or degree-8 kernel, its corrected trapezoid,
   a new block bound, continuation and tail), several hundred lines of new analytic
   proof surface to save minutes. The brief's rough estimate of `N` above 100 per endpoint
   at `t ≈ 50` was pessimistic: the truncations there are 55 and 50, because the radius
   is the sharp bound and the endpoints of a two-decimal bracket keep `|Z|` near `0.005` to
   `0.009`; the prime-only towers then cut the exp towers from 684 to 219.

**Box parameters.** Measured on one prime box at `t = 49.77` (`RUNS.md`, `term-cost`):
2.2 to 2.9 s of kernel time at hunt #132's `(40, 24, 96, 8)`, 1.2 to 1.3 s at
`(36, 16, 80, 8)`, with worst term widths `9.3e-10` and `1.5e-8` against radii near `1e-3`.
The second was taken. `nExp` sets the cost (literal sizes grow with the Taylor order of the
exponential); `nLog` sets the width.

## 3. The route, and the ones not taken

| piece | route taken | routes not taken, and why |
|---|---|---|
| the phase | hunt #132's sign test and Euler-limit window, with the first `m = 8` factors dropped | narrower brackets under the old window: `b - a < 0.00254` at `t ≈ 50`, 163 terms against 105 at the last ordinate (section 2); Stirling, Binet or digamma: absent from Mathlib (hunt #132, section 2) |
| zeta on the line | hunt #132's order-4 Euler-Maclaurin, any `N`, per-endpoint truncation | order 6 or 8: about half the towers, a new analytic development (section 2); Riemann-Siegel: Gabcke's remainder, unformalized |
| the arithmetic | exp towers for primes, coarsened products for composites, literal per term, one product per bracket | towers for every term: 684 instead of 219; one `decide` over a whole sum: more than 30 minutes for 29 terms in hunt #132 |
| the assembly | one generated file per bracket, each a checkpoint, then `Fin 10` | one file for all brackets: no checkpoint, about 8,600 lines |

## 4. Measured constants

All recomputed by `test_hardy_ten_zeros.py` from `sizing.py` and `gen_boxes.py`.

**Endpoints and the phase** (`Z` by Arb at 128 bits and `mpmath.iv`, agreeing; enclosures,
so hardened; the Lean proof does not use them):

| bracket | `Z(a)` | `Z(b)` | true increment `θ(b) - θ(a)` | hunt #132 lower end | tail lower end, `m = 8` |
|---|---|---|---|---|---|
| `(14.13, 14.14)` | `-0.0037463` | `+0.0041856` | `0.004053` | `-0.4988` | `-0.0136` |
| `(21.02, 21.03)` | `+0.0023190` | `-0.0090458` | `0.006039` | `-1.1044` | `-0.0183` |
| `(25.01, 25.02)` | `-0.0011762` | `+0.0125556` | `0.006908` | `-1.5637` | `-0.0219` |
| `(30.42, 30.43)` | `+0.0063652` | `-0.0066734` | `0.007887` | `-2.3135` | `-0.0278` |
| `(32.93, 32.94)` | `-0.0069863` | `+0.0068345` | `0.008283` | `-2.7111` | `-0.0309` |
| `(37.58, 37.59)` | `+0.0119714` | `-0.0073982` | `0.008943` | `-3.5309` | `-0.0373` |
| `(40.91, 40.92)` | `-0.0130095` | `+0.0019092` | `0.009368` | `-4.1844` | `-0.0424` |
| `(43.32, 43.33)` | `+0.0129417` | `-0.0053708` | `0.009654` | `-4.6919` | `-0.0464` |
| `(48.00, 48.01)` | `-0.0080954` | `+0.0075870` | `0.010167` | `-5.7605` | `-0.0547` |
| `(49.77, 49.78)` | `+0.0054312` | `-0.0087688` | `0.010348` | `-6.1932` | `-0.0581` |

The window lower ends use the true `log π`; `-π/2 = -1.5708`. The upper end is
`δ (log π + 5) = 0.0307` throughout.

**Truncations, radii and the decision** (radius: the Lean radius; Arb ratio: radius over
the defect `|ζ - M_N|` Arb encloses, the kill condition's quantity; upper end: the exact
upper end of the interval product, and with the radii times 1.5):

| bracket | `N_a`, `N_b` | radius at `a`, `b` | Arb ratio at `a`, `b` | upper end | at radii x 1.5 | file, s |
|---|---|---|---|---|---|---|
| `(21.02, 21.03)` | 27, 20 | `8.85e-4`, `2.66e-3` | 6.85, 7.10 | `-7.20e-6` | `-1.90e-7` | 52 |
| `(25.01, 25.02)` | 39, 23 | `4.67e-4`, `3.17e-3` | 7.83, 8.20 | `-5.15e-6` | `-3.38e-7` | 69 |
| `(30.42, 30.43)` | 31, 30 | `2.32e-3`, `2.62e-3` | 9.59, 9.62 | `-1.074e-5` | `-5.43e-7` | 65 |
| `(32.93, 32.94)` | 33, 32 | `2.54e-3`, `2.84e-3` | 10.29, 10.31 | `-1.009e-5` | `-2.54e-7` | 67 |
| `(37.58, 37.59)` | 35, 37 | `3.48e-3`, `2.85e-3` | 11.61, 11.58 | `-3.122e-5` | `-1.13e-6` | 78 |
| `(40.91, 40.92)` | 38, 59 | `3.63e-3`, `7.54e-4` | 12.53, 12.32 | `-8.60e-6` | `-2.38e-7` | 91 |
| `(43.32, 43.33)` | 37, 46 | `5.02e-3`, `2.30e-3` | 13.22, 13.13 | `-1.506e-5` | `-7.86e-7` | 83 |
| `(48.00, 48.01)` | 45, 47 | `3.75e-3`, `3.21e-3` | 14.48, 14.46 | `-9.60e-6` | `-1.32e-7` | 91 |
| `(49.77, 49.78)` | 55, 50 | `2.11e-3`, `2.97e-3` | 14.91, 14.94 | `-1.314e-5` | `-8.51e-7` | 97 |

The order-4 bound sits 6.85 to 14.94 times above the true defect, the ratio growing with
the height (hunt #132 measured 4.7 at `14.13`). With the radii doubled, every bracket fails
(`test_lesion_twice_the_radii_cannot_decide`).

## 5. What it cost

Lean on one 4-core container, warm page cache, one process at a time (`RUNS.md`): the nine
bracket files 52 to 97 s each, 692 s (11.5 minutes) in all, against the 11.2 projected
before they were spent; `PhaseShort.lean` 7 s, `TenSupport.lean` 10 s, `TenZeros.lean` 22 s,
`CheckAxioms.lean` 8 s. The clean rebuild of everything by `lean/build.sh` into a fresh
directory, the four `ZetaLean` and six `HardyFirstZero` dependencies compiled from source
included, took 1029 s (17 minutes): 240 s for the dependencies, 738 s for the nine
bracket files, 28 s for the assembly (`RUNS.md`, `clean-build`). About 9,210 lines of
Lean in this hunt, 8,574 of them generated; the largest file is 1,285 lines.

**Planted faults** (`RUNS.md`, `planted-faults`; the test-side ones are permanent tests):

- in the kernel, on a scratch copy importing `Box2102`: one digit of the `m = 13` literal
  changed, the box of `7` claimed as the product of the boxes of `2` and `3`, a radius half
  the remainder bound, and both radii doubled in the product are each refused, and the
  kernel proves the negations of the first, second and fourth by `decide +kernel`; the
  unchanged `m = 13` check is accepted beside them;
- in Python, the remainder constant `720` changed to `700` in the radii turns 8 of 45 tests
  red and makes `gen_boxes.py --check` exit 1; restored, 45 of 45 pass and the generator
  reproduces all nine files;
- standing tests: a wrong sign on the Bernoulli term and a missing `N^(-s)/2` break the
  bound against Arb at `49.77`; an interval with no zero (`(49.70, 49.71)`, `Z > 0` at both
  ends) admits no truncation up to 80; `nLog = 16` boxes cannot decide `(49.77, 49.78)`;
  doubling the radii fails all nine; a wrong composite factorization misses the true term;
  hunt #132's window leaves the quarter turn at the last bracket; the axiom audit refuses
  eleven malformed logs.

## 6. Prior art

Searched 2026-10-14, for any formal (Lean, Isabelle, Coq or Rocq, HOL) localization of
explicit nontrivial zeros of zeta, extending hunt #132's search of 2026-10-11 (its
`RESULTS.md`, section 6):

- arXiv API, six queries: zeta with Lean and zeros; "formally verified" with "critical
  line"; "proof assistant" with "Riemann zeta"; "Hardy Z" with formalization; zeros with
  zeta and Isabelle; "Turing's method" with formal;
- zbMATH Open API, eight queries: zeta Lean zeros; formal proof zeta critical line;
  Isabelle zeta zeros; Coq Riemann zeta zeros; formally verified zeros zeta; proof
  assistant Riemann zeta; interval arithmetic zeros zeta formal; Turing method formal
  verification (three needed a retry after an empty response);
- web search, four queries, including the Isabelle Archive of Formal Proofs and Mathlib's
  `riemannZeta`.

**Found, and none of it a formal localization of an explicit zero:** arXiv `2608.13637`
(two thirds of the zeros simple and on the line, with a Lean 4 formalization; a proportion,
no zero named, as hunt #132 recorded), arXiv `2609.33043` and `2610.08965` (further
proportion results for distinct and simple zeros), arXiv `2610.03728` (a Riemann-Siegel
remainder decomposition with one corollary checked in Lean; no zero located), Loeffler and
Stoll's Mathlib zeta library, and the computational verifications of RH (Turing's method,
Brent 1979, Platt and Trudgian), which are interval computations outside a proof assistant.
The only formal localization found is hunt #132's single zero, which this hunt extends.
So the bounded statement is: **no formal localization of several explicit nontrivial
zeros of zeta was found in the searched set.** That is not a novelty claim; GitHub code
search and the Lean Zulip were not reachable, and nothing is said about unindexed work.
The theorem is original to this lab in the provenance sense only.

## 7. Limitations, and the kill conditions

**Limitations.** At least ten zeros below 50, each in a stated interval; no zero count, no
claim that the intervals hold one zero each, and nothing about the zeros between them or
above 50. The theorem is checked against the pinned Mathlib build in the main clone's
`lean/.lake` and this commit's sources, in this container; it is outside the root
`lake build`, and the dedicated workflow above covers it. Outside mathematical review and
second-kernel replay are pending. The truncation choices, the order comparison, the
projections and the timings are measurements, not theorems, and the theorem does not
depend on them: the kernel decides every inequality the proof uses.

**Kill conditions** (`MISSION.md`). None fired: the Arb defect sits inside every radius
with a factor 6.85 to 14.94 to spare; the kernel cost was 11.5 minutes for the nine new
brackets against a budget of a few hours; the sharpened window stays inside
`[-0.0889, 0.04]` at every bracket against `π/2`; the search found no formal localization
of several explicit zeros.

## 8. The doors

The hunt measures a cost curve (kernel time against the height and the localization),
not a mathematical ceiling; it is recorded in door form because that curve has an optimum
later work will move. Candidate status: measured, at two-decimal brackets below 50,
order 4; the curve is not proved, only the nine chosen truncation pairs are used.

**Active constraints at the optimum.** The phase window does not bind (`0.089` against
`L = 1/5` and `π/2`), nor do the box widths (at most `3e-8` per term against radii near
`1e-3`). What binds is the remainder radius at the endpoint nearest its zero: `N_b = 59`
at `40.92` (`|Z| = 0.0019`) is the largest truncation in the hunt, above both ends at
`49.77`, and `N_a = 39` at `25.01` (`|Z| = 0.0012`) is the largest below `t = 37`, where
the others are 20 to 33. Ranked by what moving it buys: the overshoot of the
order-4 bound (6.85 to 14.94 times the true defect, growing with the height), then the
alignment of two-decimal endpoints, then the order of the expansion.

**The frozen-constant inventory.** The order (4): order 6 would need 131 towers instead
of 219, order 8 103, a genuine trade of minutes per build against a new analytic
development; by the form of the two bounds the truncation at fixed `|Z|` grows like
`t^(8/7)` at order 4 and `t^(12/11)` at order 6 (a derivation from the bounds' shape, not
measured above 50), so the trade moves toward order 6 with the height. The two-decimal
alignment: centred brackets of the same width would keep both endpoints away from the
zero, a genuine trade against the headline form. The margin 1.5 on the radii: 684 terms
against 615 at margin 1, 11 percent. `(nLog, nExp, p, kE) = (36, 16, 80, 8)`: chosen by one
measurement, not optimized; `kE = 8` covers every prime up to 157 at `t = 49.78`
(`normBound` 254.2 against 256), and 163 would need `kE = 9`. `m = 8`, `L = 1/5`, the caps `b - a ≤ 1/100` and `b ≤ 50` in
`gammaR_re_pos_short`: free, the window has a factor of about 2 to `L` and 17 to `π/2`.

**The information class.** Every door above stays inside the data the current family
reads: values of `n^(-s)` at rational points and elementary bounds. The doors that read
more are the Riemann-Siegel route (one main term at this height, the price is Gabcke's
remainder) and a zero count by Turing's method, which needs values of `Z` on a grid and a
bound on `S(t)`, and is what turning "at least ten" into a statement about all zeros below
50 would take.
