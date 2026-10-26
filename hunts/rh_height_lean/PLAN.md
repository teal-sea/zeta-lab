# PLAN: hunt #137 (`rh_height_lean`), the statement and the proof skeleton

**Written 2026-10-21 by the statement-and-skeleton role of the campaign workflow.** A plan,
not a result (`hunts/README.md`). Grades as in `MISSION.md`: *measured*, *hardened*,
*kernel-checked*. The Lean files named in section 1 are kernel-checked as files, at the root
package's pins; the target theorem is **not** proved, and the theorems that are proved are
reductions whose hypotheses are the four open pieces of section 4. Every numerical value in
this plan, other than the rational constants of the Lean statements, is measured (mpmath at
20 to 30 digits, floating point, one route) unless it says otherwise, and none is pinned by a
test yet. The rational constants in the Lean statements were chosen from these measurements;
a measurement proves none of them. The two routines of `zeta/rigor.py` named in the mission
are cited by role: the zero-count routine (line 763) and the RH-to-height routine
(line 1110).

**Integration note (2026-10-21, end of the wave).** The four pieces of section 4 closed and the
target is proved: `RHHeight.rh_height_fifty : RHHeight50` in `lean/RHHeight/Main.lean`.
`RESULTS.md` has its state, its checks, and where the built `horizontal_legs` departs from
section 4.2 (its own partitions, corner truncations `N = 4` and `28`). This plan is left as
written, with one correction to section 7: a top height of `99.85` cannot give
`RHHeight100`, because `RHUpToHeight 99.85` says nothing about zeros with
`99.85 < Im rho <= 100`; `RESULTS.md` section 7 puts the top at 100.

## 0. The design in one paragraph

Count with the vendored `zeta23` folded argument principle between the heights `T1 = 3` and
`T2 = 52`. At those two heights `Re zeta > 0` on the whole horizontal leg `[1/2, 2] + iT`
(measured minima `0.533` and `1.041`), and it is always positive on the vertical leg
`sigma = 2`, so `log zeta` is a primitive of `zeta'/zeta` along the entire half contour and the
zeta half collapses, *exactly*, to `arg zeta(1/2 + 52i) - arg zeta(1/2 + 3i)`. The count becomes

    Ncount 3 52 = int_3^52 mu + (arg zeta(1/2 + 52i) - arg zeta(1/2 + 3i)) / pi,

with measured terms `10.042613 + (-0.280901 + 0.147028)/pi = 10.000000`. The Gamma half is
enclosed with the vendored `digamma_stirling`, keeping the exact `log |w|` and `1/(2w)` terms,
which is what makes the low bottom height affordable. Below the contour, `0 < Im rho <= 3` is
excluded analytically by hunt #132's Euler-Maclaurin representation at `N = 1`, with no
interval arithmetic. An enclosure of the count inside `(9, 11)` gives `Ncount 3 52 = 10`;
hunt #133's ten distinct zeros on the line, all in `(3, 50)`, then exhaust the window, so
every zero with `0 < Im rho <= 52` is on the line and simple. The Lean reduction from the
four named pieces to the target is already proved (`RHHeight/Skeleton.lean`), with hunt #133's
theorem plugged in (`RHHeight/Assembly.lean`): what remains is exactly the four pieces.

## 1. Files and the build

| file | what it is | status |
|---|---|---|
| `lean/RHHeight/Statement.lean` | the target `RHHeight50`, `RHHeight100`, `RHUpToHeight T`, the window set, the companion `ZeroCountUpTo`; four small proved facts | compiles, imports Mathlib only |
| `lean/RHHeight/Skeleton.lean` | the four missing pieces as `Prop`s; the proved reduction to the target from them and hunt #133's statement | compiles, zero `sorry` |
| `lean/RHHeight/Assembly.lean` | hunt #133's theorem plugged in: `rhHeight50_of_four`, the target conditional on the four pieces alone | compiles, zero `sorry` (see below) |
| `lean/RHHeight.lean` | root module (`Statement`, `Skeleton`) | compiles |
| `lean/CheckAxioms.lean`, `lean/CheckAssembly.lean` | pin the statements by `rfl` or by type, print axioms | every report is `propext, Classical.choice, Quot.sound` |
| `lean/check_axioms.py` | fail-closed audit of a build log, as in hunts #132 and #133 | accepts the real log; refuses a planted log |
| `lean/build.sh` | the build: raw `lean`, never lake | skeleton stage ran end to end, 2026-10-21 |
| `lean/lakefile.toml`, `lean/lean-toolchain` | pins for tooling (Lean `v4.35.0-rc2`, Mathlib `065356127b1d` through the vendored zeta23) | `lakefile.toml` is not exercised |

Three entry points: the skeleton (seven vendored zeta23 modules from source, then this
package's `Statement`, `Skeleton` and root module, then `CheckAxioms.lean`); the same plus
the assembly point (`--assembly`: the four `ZetaLean` interval and Hardy-Z modules, hunt
#132's six modules and hunt #133's twelve, all from source, then `RHHeight.Assembly` and
`CheckAssembly.lean`); and one file against an existing output directory:

```bash
export PATH="$HOME/.elan/bin:$PATH"
LAKE_DIR="$PWD/lean/.lake" bash hunts/rh_height_lean/lean/build.sh OUT_DIR 2>&1 | tee build.log
.venv/bin/python hunts/rh_height_lean/lean/check_axioms.py build.log
LAKE_DIR="$PWD/lean/.lake" bash hunts/rh_height_lean/lean/build.sh --assembly OUT_DIR
LAKE_DIR="$PWD/lean/.lake" bash hunts/rh_height_lean/lean/build.sh --file RHHeight/Statement.lean OUT_DIR
```

The last line is the one-file command; `RHHeight/Statement.lean` needs nothing in `OUT_DIR`,
`RHHeight/Skeleton.lean` needs the skeleton stage's output, and `RHHeight/Assembly.lean` the
`--assembly` stage's.
It is, spelled out,
`cd hunts/rh_height_lean/lean && LEAN_PATH=OUT_DIR:<each lean/.lake/packages/*/.lake/build/lib/lean> lean --root=. -DautoImplicit=false -DrelaxedAutoImplicit=false RHHeight/Statement.lean -o OUT_DIR/RHHeight/Statement.olean`.

What ran, on the campaign box on 2026-10-21, under a load average between 100 and 230: the
skeleton stage of `build.sh`, end to end into a fresh directory, in about 6 minutes (17 to
25 s for `Statement.lean`, mostly import time; 30 to 50 s for `Skeleton.lean`), and
`check_axioms.py` accepted its log. The `--assembly` stage was **not** run end to end: its
modules were compiled into scratch with the same `lean` invocations by a parallel runner
(hunt #132's and #133's eighteen modules in 38 minutes wall, six at a time, against the root
package's prebuilt `ZetaLean` oleans rather than from source), and then `Assembly.lean` and
`CheckAssembly.lean` compiled against them, with the three standard axioms. Serially under
that load the stage would take about two hours (the sum of the measured per-module times); on
an idle 4-core container hunt #133 measured 17 minutes for the same modules.

## 2. The target

```lean
def RHUpToHeight (T : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ T →
    ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1

def RHHeight50 : Prop := RHUpToHeight 50
def RHHeight100 : Prop := RHUpToHeight 100
```

(namespace `RHHeight`). `riemannZeta` is Mathlib's. Simplicity is `analyticOrderAt riemannZeta
rho = 1`, the multiplicity `zeta23` counts: `Zeta23.zeroMult rho` is by definition
`(analyticOrderAt riemannZeta rho).toNat`, and `toNat_analyticOrderAt_eq_one_iff` (proved)
shows `zeroMult rho = 1` is the same condition. `CheckAxioms.lean` pins `RHHeight50` to the
unfolded text by `rfl`, `zeroMult` to its definition by `rfl`, and the window
`stripZerosUpTo T` to `Zeta23.zerosIn 0 T`. Also stated: `ZeroCountUpTo T n :=
(stripZerosUpTo T).ncard = n`; the planned proof gives `ZeroCountUpTo 50 10` on the way.

## 3. Inventory, with signatures copied from source

Copied from the sources at this commit, then checked: the zeta23 closure (40 modules), hunt
#132's six modules and hunt #133's support modules were compiled into scratch with raw
`lean`, and a scratch file restating the main signatures below as `example`s, with `#check`
for the rest, elaborated against them without error (2026-10-21; the file is not landed).

### 3.1 The zeta23 counting machinery (`lean/vendor/zeta23/Zeta23/`)

`Statement.lean` (namespace `Zeta23`):

```lean
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ
```

Multiplicity convention: `Ncount` counts with multiplicity `zeroMult`, over the half-open
ordinate window `T₁ < Im ρ ≤ T₂` (positive ordinates, not `|Im ρ|`). `toNat` sends `⊤` to `0`,
so `1 ≤ zeroMult ρ` is a real fact (`ZetaSeam.one_le_mult`); a `finsum` over an infinite set is
`0`, so finiteness of the window (`zerosIn_finite`) is needed before reading `Ncount` as a sum.

`Statement/SeamClosed.lean`, `Statement/Seam.lean`, `Defs.lean`:

```lean
theorem zetaSeam : ZetaSeam
theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite
-- ZetaSeam fields
one_le_mult : ∀ ρ, IsNontrivialZero ρ → 1 ≤ zeroMult ρ
reflect_zero : ∀ ρ, IsNontrivialZero ρ → IsNontrivialZero (reflect ρ)
mult_reflect : ∀ ρ, IsNontrivialZero ρ → zeroMult (reflect ρ) = zeroMult ρ
finite_window : ∀ T₁ T₂ : ℝ, ({ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite
def reflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ
```

`RvM/Defs.lean`, `RvM/NcountWindow.lean`, `RvM/CountByIntegral.lean`, `RvM/Fold.lean`,
`RvM/MainTerm.lean` (namespace `Zeta23.RvM` unless shown):

```lean
def GoodHeight (T : ℝ) : Prop := ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.im ≠ T

def halfContour (F : ℂ → ℂ) (T₁ T₂ : ℝ) : ℂ :=
  (∫ σ in (1/2:ℝ)..2, F (σ + T₁ * I)) + (∫ t in T₁..T₂, F (2 + t * I)) * I
    - ∫ σ in (1/2:ℝ)..2, F (σ + T₂ * I)

lemma halfContour_add (F G : ℂ → ℂ) (T₁ T₂ : ℝ)
    (hb : IntervalIntegrable (fun σ : ℝ => F (σ + T₁ * I)) MeasureTheory.volume (1/2) 2)
    (hb' : IntervalIntegrable (fun σ : ℝ => G (σ + T₁ * I)) MeasureTheory.volume (1/2) 2)
    (hr : IntervalIntegrable (fun t : ℝ => F (2 + t * I)) MeasureTheory.volume T₁ T₂)
    (hr' : IntervalIntegrable (fun t : ℝ => G (2 + t * I)) MeasureTheory.volume T₁ T₂)
    (ht : IntervalIntegrable (fun σ : ℝ => F (σ + T₂ * I)) MeasureTheory.volume (1/2) 2)
    (ht' : IntervalIntegrable (fun σ : ℝ => G (σ + T₂ * I)) MeasureTheory.volume (1/2) 2) :
    halfContour (fun s => F s + G s) T₁ T₂ = halfContour F T₁ T₂ + halfContour G T₁ T₂

theorem N_eq_halfContour_completedZeta {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ) = (1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im

theorem halfContour_completedZeta_split {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    halfContour (logDeriv completedRiemannZeta) T₁ T₂ =
      halfContour (logDeriv riemannZeta) T₁ T₂ + halfContour (logDeriv Complex.Gammaℝ) T₁ T₂

-- the unfolded rectangle, valid down to 0 < T₁ (the fold needs 1 ≤ T₁)
theorem rectangleIntegral'_logDeriv_completedZeta_eq_Ncount {T₁ T₂ : ℝ} (hT₁ : 0 < T₁)
    (hT : T₁ ≤ T₂) (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂) :
    RectangleIntegral' (logDeriv completedRiemannZeta) (-1 + T₁ * I) (2 + T₂ * I)
      = (Ncount T₁ T₂ : ℂ)

theorem exists_goodHeight (a : ℝ) : ∃ T ∈ Set.Icc a (a + 1), GoodHeight T
theorem Ncount_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :            -- namespace Zeta23
    Ncount a c = Ncount a b + Ncount b c
theorem Ncount_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Ncount a b ≤ Ncount c d
```

### 3.2 The Gamma side (`RvM/GammaSide.lean`, `Defs.lean`, `GammaFacts/`)

```lean
def mu (τ : ℝ) : ℝ :=                                                  -- namespace Zeta23
  (1 / (2 * Real.pi)) * (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re
    - Real.log Real.pi / (2 * Real.pi)

theorem gamma_side {T₁ T₂ : ℝ} (_h0 : 0 < T₁) (_h0' : 0 < T₂) :
    (1 / Real.pi) * (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im = ∫ t in T₁..T₂, mu t
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + (1/2 : ℂ) * Complex.digamma (s / 2)
theorem re_logDeriv_Gammaℝ_half (t : ℝ) :
    (logDeriv Complex.Gammaℝ (1/2 + t * I)).re = Real.pi * mu t
theorem mu_smooth : ContDiff ℝ ∞ mu                                     -- namespace Zeta23
theorem mu_continuous (hΓ : Zeta23.GammaFacts) : Continuous mu
theorem gammaFacts : GammaFacts                                        -- namespace Zeta23

-- namespace Zeta23.StirlingVert, `variable {w : ℂ}`
theorem digamma_stirling (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 3 / w.im ^ 2
theorem re_digamma_stirling {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)|
      ≤ 4 / t ^ 2
theorem re_digamma_stirling' {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)| ≤ 5 / t ^ 2
theorem mu_stirling : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2
```

`mu_stirling` hides its constant behind `∃`; its proof uses `re_digamma_stirling'` and
`C = 20/(2 pi)`. The plan uses `digamma_stirling` directly (section 4.1), whose constant is
explicit and smaller in effect: `6/(pi t^2)` in `mu` against `20/(2 pi t^2)`.

### 3.3 The zeta side helpers (`RvM/Backlund.lean`, `RvM/ZetaGrowth.lean`)

```lean
lemma re_riemannZeta_two_pos (t : ℝ) : 0 < (riemannZeta (2 + t * I)).re
lemma hasDerivAt_log_riemannZeta_two (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.log (riemannZeta (2 + t * I)))
      (logDeriv riemannZeta (2 + t * I) * I) t
lemma continuous_logDeriv_riemannZeta_two :
    Continuous (fun t : ℝ => logDeriv riemannZeta (2 + t * I) * I)
theorem vertical_two : ∀ T₁ T₂ : ℝ,
    |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi
lemma hasDerivAt_riemannZeta_horizontal (hT : T ≠ 0) (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => riemannZeta (σ + T * I)) (deriv riemannZeta (σ + T * I)) σ
lemma intervalIntegrable_logDeriv_horizontal (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : u ∈ Set.Icc (1/2 : ℝ) 2) (hv : v ∈ Set.Icc (1/2 : ℝ) 2) :
    IntervalIntegrable (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) volume u v
lemma im_integral_le_two_pi (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : 1/2 ≤ u) (huv : u < v) (hv : v ≤ 2)
    (hno : ∀ σ ∈ Set.Ioo u v, (riemannZeta (σ + T * I)).re ≠ 0) :
    |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im| ≤ 2 * Real.pi
theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re
```

`im_integral_le_two_pi`'s proof is the template for the horizontal primitive: on a segment
where `ε ζ` stays in the slit plane, `Complex.log (ε ζ(σ + iT))` is a primitive of `ζ'/ζ`. The
Backlund bound `backlund_horizontal_at` exists but is far too coarse here (constant near 310).

### 3.4 What hunts #132 and #133 proved

The theorems (all kernel-checked there, standard axioms, `hunts/hardy_*/RESULTS.md`):

```lean
theorem HardyFirstZero.first_zero_on_line :
    ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50), riemannZeta (1 / 2 + t * I) = 0
theorem HardyTenZeros.zero_in_2102 :          -- likewise 2501 3042 3293 3758 4091 4332 4800 4977
    ∃ t ∈ Set.Ioo (2102 / 100 : ℝ) (2103 / 100), riemannZeta (1 / 2 + t * I) = 0
theorem HardyTenZeros.ten_zeros_on_line_below_fifty :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ts k * I) = 0
```

They prove at least ten zeros on the line below 50 and no upper count. The reusable lemmas:

```lean
-- HardyFirstZero.EulerMaclaurin
def QP : Set ℂ := {z | 0 < z.re ∧ 0 < z.im}
noncomputable def P4 (s : ℂ) : ℂ := s * (s + 1) * (s + 2) * (s + 3)
noncomputable def eBlock (s : ℂ) (x : ℝ) : ℂ := ...
noncomputable def emRHS (N : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
    + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
    - ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)
theorem zeta_em4 {s : ℂ} (hs : s ∈ QP) {N : ℕ} (hN : 1 ≤ N) : riemannZeta s = emRHS N s
theorem norm_eBlock_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖eBlock s x‖ ≤ ‖P4 s‖ * x ^ (-s.re - 4) / 720
theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 2 ≤ N) :
    ‖∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720
theorem zeta_em4_error {s : ℂ} (hs : s ∈ QP) {N : ℕ} (hN : 2 ≤ N) :
    ‖riemannZeta s - (∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1))‖
      ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720
-- HardyFirstZero.BoxSupport (general s)
theorem main_eq (s : ℂ) {N : ℕ} (hN : N ≠ 0) :
    ∑ i ∈ range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
      = ∑ i ∈ range N, (i : ℂ) ^ (-s)
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2 + s / (12 * N))
-- HardyFirstZero.Spine, HardyTenZeros.PhaseShort
theorem exists_zero_of_sign_data {a b : ℝ} (hab : a < b)
    (hX : (riemannZeta (sOf a) * conj (riemannZeta (sOf b))).re < 0)
    (hG : 0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + t * I) = 0
theorem gammaR_re_pos_short {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hw : b - a ≤ 1 / 100)
    (hb : b ≤ 50) : 0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re
-- HardyTenZeros.TenSupport (on the critical line only: s = sOf t = 1/2 + t I)
theorem emN_bound {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 2 ≤ N) {r R : ℝ} (hr : 0 < r)
    (hr2 : r ^ 2 ≤ (N : ℝ) - 1) (hR0 : 0 ≤ R) (hR : q4 t ≤ R ^ 2) :
    ‖riemannZeta (sOf t) - (∑ i ∈ range N, (i : ℂ) ^ (-sOf t) + (N : ℂ) ^ (1 - sOf t)
        / (sOf t - 1) + (N : ℂ) ^ (-sOf t) / 2 + sOf t / 12 * (N : ℂ) ^ (-sOf t - 1))‖
      ≤ R / (((N : ℝ) - 1) ^ 3 * r * (7 / 2) * 720)
theorem zeta_mem_mainBox {t : ℚ} (ht : 0 < t) {N : ℕ} (hN : 2 ≤ N) {T : ℕ → ComplexInterval}
    (hT : ∀ m < N + 1, (T m).contains ((m : ℂ) ^ (-sOf (t : ℝ))))
    {r R e : ℚ} (hr : 0 < r) (hr2 : r ^ 2 ≤ N - 1) (hR0 : 0 ≤ R) (hR : q4Q t ≤ R ^ 2)
    (he : R / (((N : ℚ) - 1) ^ 3 * r * (7 / 2) * 720) ≤ e) :
    ((mainBox T N t).inflate e).contains (riemannZeta (sOf (t : ℝ)))
theorem contains_cpow_mul_coarsen (p : ℕ) {a b : ℕ} {A B : ComplexInterval} {s : ℂ}
    (hA : A.contains ((a : ℂ) ^ (-s))) (hB : B.contains ((b : ℂ) ^ (-s))) :
    ((A.mul B).coarsen p).contains (((a * b : ℕ) : ℂ) ^ (-s))
```

### 3.5 The interval layers (`lean/ZetaLean/`, namespace `ZetaLean`)

`Rigor.lean`: `structure Interval where lo : ℚ; hi : ℚ; le : lo ≤ hi`,
`def Interval.contains (x : Interval) (r : ℝ) : Prop := (x.lo : ℝ) ≤ r ∧ r ≤ (x.hi : ℝ)`,
exact `add`, `neg`, `sub`, `mul` with `contains_*` lemmas, and the same for
`structure ComplexInterval where re : Interval; im : Interval` with
`contains (x) (z : ℂ) := x.re.contains z.re ∧ x.im.contains z.im`. No division, no `arg`.

`IntervalExp.lean`:
`theorem contains_expI (n : ℕ) (hn : 0 < n) : ∀ (k : ℕ) (x : Interval) (t : ℝ), x.contains t →
-(2 ^ k : ℚ) ≤ x.lo → x.hi ≤ (2 ^ k : ℚ) → (expI n k x).contains (Real.exp t)`;
`theorem contains_log1 {n : ℕ} {x : Interval} {t : ℝ} (hx : x.contains t) (hlo : 0 < x.lo)
(hhi : x.hi < 2) : (log1 n x).contains (Real.log t)`;
`theorem contains_logQ {n k : ℕ} {q : ℚ} (h0 : 0 < q / 2 ^ k) (h2 : q / 2 ^ k < 2) :
(logQ n k q).contains (Real.log q)`.

`IntervalCExp.lean`:
`theorem contains_expC (n : ℕ) (hn : 0 < n) : ∀ (k : ℕ) (x : ComplexInterval) (z : ℂ),
x.contains z → normBound x ≤ 2 ^ k → (expC n k x).contains (Complex.exp z)`;
`def dirichletTermBox2 (nLog nExp p kL kE : ℕ) (m : ℕ) (S : ComplexInterval) : ComplexInterval`
with
`theorem contains_dirichletTermBox2 {nLog nExp p kL kE : ℕ} (hnL : 0 < nLog) (hnE : 0 < nExp)
{m : ℕ} (hm : 0 < m) {S : ComplexInterval} {s : ℂ} (hS : S.contains s)
(h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
(hb : normBound (S.neg.mul { re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 })
≤ 2 ^ kE) : (dirichletTermBox2 nLog nExp p kL kE m S).contains ((m : ℂ) ^ (-s))`
(any `s`, not only the line);
`theorem norm_le_normBound {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
‖z‖ ≤ (normBound x : ℝ)`;
`theorem normLower_le_norm {B : ComplexInterval} {v : ℂ} (hB : B.contains v) :
((normLower B : ℚ) : ℝ) ≤ ‖v‖`;
`theorem contains_inflate {x : ComplexInterval} {z w : ℂ} {r : ℚ} (hx : x.contains z)
(hw : ‖w - z‖ ≤ (r : ℝ)) : (x.inflate r).contains w`;
`theorem contains_coarsen (p : ℕ) {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
(x.coarsen p).contains z`.

`HardyZ.lean`: `hardyZ`, `hardyZReal`, `hardyZ_zero_iff`, `continuous_hardyZReal` (the
sign-change route of hunts #132 and #133; not needed again here).

### 3.6 Mathlib facts the pieces lean on

`Real.pi_gt_three`, `Real.pi_gt_d2`, `Real.pi_gt_d6`, `Real.pi_lt_d6`
(`Mathlib.Analysis.Real.Pi.Bounds`); `Real.arctan_le_self`, `Real.self_le_arctan`
(`.../Trigonometric/Bounds.lean`); `Complex.arg_of_re_nonneg`, `Complex.abs_arg_le_pi_div_two_iff`,
`Complex.arg_nonneg_iff`, `Complex.arg_neg_iff`, `Complex.tan_arg`, `Complex.log_im`,
`Complex.hasDerivAt_log`; `ENat.toNat_eq_iff`; `riemannZeta_ne_zero_of_one_le_re`.

## 4. The four pieces

Each is a `Prop` in `RHHeight/Skeleton.lean`; the signature to prove is that `Prop` as a
theorem. The reduction `rhHeight50_of_pieces` consumes exactly these.

### 4.1 `gamma_increment` (`RHHeight.GammaIncrement`)

```lean
theorem gamma_increment :
    (92 / 10 : ℝ) ≤ ∫ t in (3 : ℝ)..52, Zeta23.mu t ∧ ∫ t in (3 : ℝ)..52, Zeta23.mu t ≤ 109 / 10
```

The integral is `(theta(52) - theta(3))/pi = 10.042613` (measured; `theta(3) = -2.994565`,
`theta(52) = 28.555235`; mpmath quadrature of `mu` agrees with `siegeltheta`, which checks the
normalization of `gamma_side`). Route:

1. Pointwise, for `t >= 1` with `w = 1/4 + i t/2` (so `w.re = 1/4`, `|w.im| = t/2 >= 1/2`):
   `|mu t - m t| <= 6/(pi t^2)`, where
   `m t = (1/(2 pi)) ((1/2) log((1 + 4t^2)/16) - 2/(1 + 4t^2) - log pi)`.
   From `digamma_stirling`, `Complex.abs_re_le_norm`, `Re log w = log |w|`,
   `|w|^2 = (1 + 4t^2)/16` and `Re (1/(2w)) = 2/(1 + 4t^2)`. Keeping `log |w|` and `1/(2w)`
   exactly is the point: it leaves `3/(Im w)^2 = 12/t^2`, against `20/t^2` for
   `re_digamma_stirling'`, which `mu_stirling` uses.
2. An antiderivative: `F t = (1/(2 pi)) ((t/2) log((1+4t^2)/16) - t - (1/2) arctan(2t) - t log pi)`,
   `HasDerivAt F (m t) t`; FTC gives `int_3^52 m = F 52 - F 3 = 10.026188`, and
   `int_3^52 6/(pi t^2) = (6/pi)(1/3 - 1/52) = 0.599892`.
3. `intervalIntegral.integral_mono_on` twice, with `mu` continuous: `Zeta23.mu_smooth.continuous`
   (`Zeta23/GammaFacts.lean`, a light module), not `mu_continuous gammaFacts`, whose import
   `GammaFacts.Complete` pulls in `GammaFacts.IntMu` (26 minutes of compile time under load).
4. Rational bounds for `log(10817/16)`, `log(37/16)`, `log pi` (`ZetaLean.Interval.logQ`, or
   Mathlib's series bounds; `log pi` through `Real.pi_gt_d6`, `Real.pi_lt_d6` and
   monotonicity). The arctan term needs no numerics: `0 <= arctan 104 - arctan 6 <= pi/2`
   costs at most `1/8`.

The route gives `[9.4263, 10.6261]` before the elementary bounds, inside `[9.2, 10.9]` with
`0.23` and `0.27` to spare. The upper constant leaves the integer step only `0.036` below 11
(`10.9 + (1/5)/pi = 10.9637`, as the sibling plan notes); that step is already proved, so its
margin costs nothing, and the slack is left in the piece that still has to be proved. Depends on: zeta23 `Defs`, `GammaFacts`, `GammaFacts.StirlingVert`,
Mathlib calculus. Risk: low to
moderate; standard FTC and integral comparison, about 250 lines. The one trap is the complex
form of `mu`'s argument, `1 / 4 + Complex.I * τ / 2`.

### 4.2 `horizontal_legs` (`RHHeight.HorizontalLegs`)

```lean
theorem horizontal_legs :
    (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 3 * I)).re) ∧
    (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 52 * I)).re) ∧
    -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 3 * I)).arg ∧ (riemannZeta (1 / 2 + 3 * I)).arg ≤ 0 ∧
    -(1 / 3 : ℝ) ≤ (riemannZeta (1 / 2 + 52 * I)).arg ∧ (riemannZeta (1 / 2 + 52 * I)).arg ≤ 0
```

Measured on a 1500-point grid per leg: on `[1/2, 2] + 3i`, `Re zeta >= 0.532737` (at
`sigma = 1/2`), `|zeta| >= 0.538547`,
`arg zeta` in `[-0.1699, -0.1416]`; on `[1/2, 2] + 52i`, `Re zeta >= 1.040881` (at `sigma = 2`),
`|zeta| >= 1.048977`, `arg zeta` in `[-0.2809, 0.1244]`. At the left ends
`zeta(1/2 + 3i) = 0.532737 - 0.078897 i` (`arg = -0.147028`, `|Im|/Re = 0.1481`) and
`zeta(1/2 + 52i) = 1.739361 - 0.501857 i` (`arg = -0.280901`, `|Im|/Re = 0.2885`).

Route:

1. **Points off the line.** A sigma-general version of hunt #133's `zeta_mem_mainBox`: at a
   rational `s = sigma + i t` in `QP`, `zeta s` lies in the box of
   `sum_{n<N} n^(-s) + N^(-s) c_N(s)` (`main_eq`; term boxes by `dirichletTermBox2` for primes
   and `contains_cpow_mul_coarsen` for composites; `c_N(s) = N/(s-1) + 1/2 + s/(12N)` an exact
   Gaussian rational) inflated by a rational `R >= ‖P4 s‖ (N-1)^(-sigma-3) / (720 (sigma+3))`
   (`zeta_em4_error`). New Lean: the general `c_N` box and a rational bound for
   `(N-1)^(-sigma-3)` (for example `(N-1)^(-3) r^(-k)` with `r^2 <= N-1` and `k = floor(2 sigma)`).
2. **Segments.** For `sigma` in `[a, b]`, a uniform bound
   `‖M_N(sigma + iT) - M_N(a + iT)‖ <= (sigma - a) L`, termwise from
   `‖n^(-s) - n^(-s_a)‖ = n^(-a) (1 - n^(-(sigma - a))) <= (sigma - a) n^(-a) log n` and an
   elementary bound for the `N^(-s) c_N(s)` term, plus the remainder bound taken at its worst
   on the segment. Then `Re zeta >= Re M_N(a + iT) - (b - a) L - R_max > 0`.
3. **The partition.** This role's float sizing found 3 segments on the bottom leg (`N = 2`) and
   8 on the top leg (`N` from 9 to 13). The sibling numeric role then redid it in Arb
   (`NUMERIC_PLAN.md`, section 3) and found that those partitions close on the bare bounds and
   with the factor 3/2 on the remainder radius, but not with 3/2 on the variation term as
   well; it generated partitions that do, and they are the ones to build: bottom leg
   `[1/2, 7/8], [7/8, 5/4], [5/4, 2]`, all `N = 2`; top leg breakpoints
   `1/2, 19/32, 11/16, 7/8, 17/16, 5/4, 13/8, 2` with `N = 12, 11, 12, 11, 9, 9, 8`. Its Arb
   lower bounds for `Re zeta` are `0.486` on the bottom leg and `1.039` on the top leg.
4. **The two arguments**, from on-line boxes at `t = 3` and `t = 52` (hunt #133's
   `zeta_mem_mainBox` applies as it stands, `t` rational) and a small lemma: for `Re z > 0`,
   `|arg z| <= |Im z| / Re z` (`Complex.tan_arg`, `Real.arctan_tan`, `Real.arctan_le_self`), and
   `Im z <= 0` gives `arg z <= 0`. These two boxes need tighter radii than positivity does.
   With hunt #133's radius, and the box centred at the main term `M_N` as the Lean box is:
   `N = 3` at `t = 3` (radius `0.0064`, lower end `-0.1617` against `-1/5`) and `N = 24` at
   `t = 52` (radius `0.0499`, lower end `-0.3264` against `-1/3`). `N = 23` fails there
   (`-0.3353`); this role first sized it around zeta's value instead of `M_23`, and the sibling
   role caught it.

Counting prime exp towers (the composites are one product each, as in hunt #133): the sibling
plan counts 41 for the legs and projects 125 s of kernel time at hunt #133's measured rate.

Depends on: hunts #132 and #133's support modules, `ZetaLean.IntervalCExp`. Risk: moderate,
mostly volume (the off-line generalization of `TenSupport.lean`, the segment lemma, one
generated box file per leg), about 500 lines plus generated files. The margins are
wide: the smallest `Re zeta` on a leg is `0.53` (Arb lower bound over the leg `0.486`), against
remainder radii near `0.1`.

### 4.3 `exact_argument` (`RHHeight.ExactArgument`)

```lean
theorem exact_argument (T₁ T₂ : ℝ) (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hleg₁ : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₁ * I)).re)
    (hleg₂ : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₂ * I)).re) :
    (Zeta23.Ncount T₁ T₂ : ℝ) = (∫ t in T₁..T₂, Zeta23.mu t) +
      ((riemannZeta (1 / 2 + T₂ * I)).arg - (riemannZeta (1 / 2 + T₁ * I)).arg) / Real.pi
```

This is where the enclosures of the argument change become an exact count: the identity is
exact, and `count_eq_ten_of` (proved) turns it, with the enclosures of 4.1 and 4.2, into
`Ncount 3 52 = 10` (the enclosure is `(9.09, 11)`). Route:

1. `GoodHeight T₁` and `GoodHeight T₂` from positivity: a zero at height `T` with real part in
   `[1/2, 1)` contradicts `hleg`; one with real part in `(0, 1/2)` reflects, by
   `zetaSeam.reflect_zero`, to `reflect ρ = 1 - conj ρ` at the same height with real part in
   `(1/2, 1)`.
2. On each horizontal leg `ζ(σ + iT)` lies in the slit plane, so `Complex.log` of it is a
   primitive of `ζ'/ζ(σ + iT)` (the pattern of `im_integral_le_two_pi` with `ε = 1`); on the
   vertical leg use `hasDerivAt_log_riemannZeta_two`. FTC on the three legs telescopes the zeta
   half of `halfContour` to `log ζ(1/2 + iT₂) - log ζ(1/2 + iT₁)`; take `Complex.log_im`.
3. `N_eq_halfContour_completedZeta`, `halfContour_completedZeta_split`, `gamma_side`.

Depends on: zeta23 `RvM.MainTerm` and its closure (38 modules; with `GammaFacts.Complete`,
40, built from source into scratch on the campaign box in 35 minutes wall, six at a time,
under load, for the signature check of section 3). Risk: low; pure plumbing
over vendored lemmas, no numerics, about 150 to 200 lines. The cast shape `(σ : ℂ) + T * I`
must match `halfContour`'s integrands.

### 4.4 `low_height` (`RHHeight.LowHeight`)

```lean
theorem low_height :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 3 → False
```

Route: `ρ ∈ QP`. `zeta_em4` at `N = 1` gives `ζ(s) = 1/(s-1) + 1/2 + s/12 - Σ' eBlock s (k+1)`
(the `0^(-s)` term vanishes since `-s ≠ 0`), and `1/(s-1) + 1/2 + s/12 = (s+2)(s+3)/(12(s-1))`.
Split the tail at `k = 0`: `norm_eBlock_le` at `x = 1` and `norm_tail_le` at `N = 2` give
`‖tail‖ <= ‖P4 s‖ (1 + 1/(σ+3)) / 720`. A zero would force
`60 (σ+3) <= ‖s‖ ‖s+1‖ ‖s-1‖ (σ+4)`, which fails on `(0,1) × (0,3]`: squared,
`(σ²+t²)((1-σ)²+t²) <= 1/16 + t² + t⁴ <= 90.07`, `(σ+1)² + t² <= 13`, `(σ+4)²/(σ+3)² <= 16/9`,
and `90.07 * 13 * 16/9 = 2082 < 3600`. Measured on a grid of `(0,1) × (0,3]`: the true
remainder is at most `0.21` of the bound, and bound over main term at most `0.713`.

Depends on: `HardyFirstZero.EulerMaclaurin` only. Risk: low, about 150 lines. It does not
extend far: the ratio of bound to main term reaches `0.99` at `Im rho = 3.4` and `1.07` at
`3.5` (measured), which is why the bottom height is 3.

## 5. Why these heights

**The bottom height `T1 = 3`.** The fold needs `1 <= T1`; below `T1` the zeros must be excluded
some other way. At `T1 = 3` that exclusion is the analytic `low_height`; at `T1 = 10` it would
need a two-dimensional covering of `(0,1) × (0,10]` or a second count. The price is the
Stirling error, `(6/pi)(1/T1 - 1/T2)`, which grows as `T1` falls:

| `T1` | Stirling error `(6/pi)(1/T1 - 1/52)` | `low_height` by the `N = 1` bound |
|---|---|---|
| 2 | 0.918 | yes |
| 3 | 0.600 | yes (ratio 0.713) |
| 10 | 0.154 | no (fails above about 3.4) |

At `T1 = 3` the count's enclosure is `(9.09, 11)` with the constants of section 4, so the
error is affordable. With `mu_stirling`'s constant `20/(2 pi)` instead, the error at `T1 = 3`
would be `0.999` and the count would not close; that, not anything about zeta, is the reason
to use `digamma_stirling` directly.

**The top height `T2 = 52`.** Any `T2` in `[50, 52.970)` gives the same ten zeros (mpmath:
`gamma_10 = 49.773832`, `gamma_11 = 52.970321`). At `T2 = 50`, `zeta(1/2 + 50i) =
-0.0817 + 0.3308 i` is in the second quadrant, `|zeta|` drops to `0.331` on the leg, and
`arg zeta` turns by `-1.652` along it, so the leg needs several directions, and a cruder
sizing (a disk about each left-end value, the same remainder and derivative bounds) asks for
25 to 34 sub-segments with `N` up to 26 there, against 7 to 9 with `N` up to 17 at
`T2 = 52`. At `T2 = 52` the leg stays in the right half-plane, one direction suffices, and
the corner values at `sigma = 2` cancel.

**Cross-checks of the count** (measured, not the proof): mpmath `nzeros(3) = 0`,
`nzeros(50) = 10`, `nzeros(52) = 10`. The folded count evaluated in mpmath, with the
continuous argument along each leg, is `10.000000` at `(3, 50)` and at `(3, 52)`; at `(3, 52)`
the principal-argument form of 4.3 gives the same value.

## 6. The skeleton, proved now

`RHHeight/Skeleton.lean`, all kernel-checked with standard axioms (`CheckAxioms.lean`):

```lean
def TenZerosOnLine : Prop :=      -- the type of HardyTenZeros.ten_zeros_on_line_below_fifty
  ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
    ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ts k * I) = 0

theorem count_eq_ten_of (hΓ : GammaIncrement) (hH : HorizontalLegs) (hE : ExactArgument) :
    Ncount 3 52 = 10
theorem mem_and_simple_of_Ncount_le {T₁ T₂ : ℝ} {n : ℕ} (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zerosIn T₁ T₂) (hcard : S.card = n) (hN : Ncount T₁ T₂ ≤ n) :
    ∀ ρ ∈ zerosIn T₁ T₂, ρ ∈ S ∧ zeroMult ρ = 1
theorem on_line_and_simple_of_count {T₁ T₂ : ℝ} {n : ℕ} (ts : Fin n → ℝ)
    (hinj : Function.Injective ts)
    (hts : ∀ k, T₁ < ts k ∧ ts k ≤ T₂ ∧ riemannZeta (1 / 2 + ts k * I) = 0)
    (hN : Ncount T₁ T₂ ≤ n) :
    ∀ ρ ∈ zerosIn T₁ T₂, ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1
theorem rhUpToHeight52_of_pieces (hΓ : GammaIncrement) (hH : HorizontalLegs)
    (hE : ExactArgument) (hL : LowHeight) (h10 : TenZerosOnLine) : RHUpToHeight 52
theorem rhHeight50_of_pieces (hΓ : GammaIncrement) (hH : HorizontalLegs)
    (hE : ExactArgument) (hL : LowHeight) (h10 : TenZerosOnLine) : RHHeight50
theorem zeroCount50_of_pieces (hΓ : GammaIncrement) (hH : HorizontalLegs)
    (hE : ExactArgument) (hL : LowHeight) (h10 : TenZerosOnLine) : ZeroCountUpTo 50 10
```

`low_height` also places hunt #133's ten ordinates above 3, so they lie in the window
`(3, 52]`. `RHHeight/Assembly.lean` plugs hunt #133 in, so the target is conditional on the
four pieces alone (compiled against hunt #133's modules, standard axioms, `CheckAssembly.lean`):

```lean
theorem tenZerosOnLine : TenZerosOnLine := HardyTenZeros.ten_zeros_on_line_below_fifty
theorem rhHeight50_of_four (hΓ : GammaIncrement) (hH : HorizontalLegs) (hE : ExactArgument)
    (hL : LowHeight) : RHHeight50
theorem zeroCount50_of_four (hΓ : GammaIncrement) (hH : HorizontalLegs) (hE : ExactArgument)
    (hL : LowHeight) : ZeroCountUpTo 50 10
```

Once the four pieces are theorems the target is one line, in a module that imports
`RHHeight.Assembly` and the pieces' modules:

```lean
theorem rh_height_fifty : RHHeight.RHHeight50 :=
  RHHeight.rhHeight50_of_four gamma_increment horizontal_legs exact_argument low_height
```

## 7. The second target, `T = 100`

Measured: `gamma_29 = 98.831194`, `gamma_30 = 101.317851`, `nzeros(100) = 29`. At
`T2 = 99.85` the top leg keeps `Re zeta >= 1.193`, and the identity of 4.3 evaluates to
`29.000000` at `(3, 99.85)`; the Stirling error is `0.617`. So the same plan gives the count
there: `ExactArgument` and `LowHeight` unchanged, and a `GammaIncrement` and a
`HorizontalLegs` at the new top height. What is missing is the input, nineteen more located zeros on the
line in `(50, 99.85)` (a hunt #133 style extension; its phase lemma `gammaR_re_pos_short` is
stated for `b <= 50` and would need its constants revisited), and a top-leg box file at
`t = 99.85` with larger `N`. The sibling plan (`NUMERIC_PLAN.md`, section 3) has the Arb
partition at 99.85 (8 segments, `N` from 12 to 23), `arg zeta(1/2 + 99.85i) = 0.1999` (positive,
so the `T = 100` analogue of `HorizontalLegs` needs an interval such as `[0, 1/3]` there), its
box at `N = 55`, and the count with margin `0.3535`.

## 8. Reconciliation with the sibling numeric plan

`hunts/rh_height_lean/NUMERIC_PLAN.md` and `numeric_plan.py` (another role of this workflow;
read here, not edited) first planned an independent contour from `T1 = 10` to `T2 = 50`, with a
chain of quarter-turn directions on the legs and the Gamma side budgeted at `20/(2 pi)`, the
constant inside `mu_stirling`'s proof. After this plan and the skeleton appeared, it adopted
`(3, 52)` as its plan of record, hardened it in Arb (its section 3: the count from the stated
rational bounds is `[9.0939, 10.9637]`; the route's own enclosure `[9.3718, 10.5947]`), and
kept `(10, 50)` as a cross-check and as the fallback should `low_height` at 3 fail. Its three
corrections to this plan are taken: the box at `1/2 + 52i` needs `N = 24` (section 4.2), the
partitions to build are its Arb partitions (section 4.2), and the integer step's top margin is
`0.036` (section 4.1). It also replays the zero-count routine of `zeta/rigor.py` (line 763)
and the RH-to-height routine (line 1110) with Arb, and supplies the independent counts.

## 9. Kill conditions and open questions

None of `MISSION.md`'s kill conditions has fired, as far as this role checked: the statement
uses Mathlib's `riemannZeta`; the skeleton and the assembly point need only the standard three
axioms; the planned count agrees with mpmath's `nzeros` at 50 (and 52) and, at
`(3, 99.85)`, with `nzeros(100) = 29`; no piece has yet had its bounded attempt. This role ran
no new search for prior formal work. Open:

* whether the four pieces close as planned; the riskiest by volume is `horizontal_legs`;
* the fallback contour `(10, 50)` of the sibling plan, if `low_height` at 3 fails, would need a
  different exclusion below 10 (section 5);
* the second kernel check named in the mission (NanoDa or Comparator) for the final theorem;
* a test pinning the measured numbers of sections 4, 5 and 7 (recorded here, not tested);
* the `T = 100` input of section 7.
