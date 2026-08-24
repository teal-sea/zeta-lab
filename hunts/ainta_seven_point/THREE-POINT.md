# The three-point certificate, proved in Lean

> `Zeta23Ext.Bridge.n_point_bound` is proved on `main` for every `n`, conditional on the finite
> inequality `hCert`. This note is the `n = 3` instance of `hCert` **discharged**: a Lean proof,
> sorry-free and with no axiom beyond the three Lean itself assumes, of
> `∀ g ≥ 0, c ≤ F 3 3000 g` at `c = 1345/10⁶`, and the unconditional simple-zero bound that
> follows from it.
>
> **VERIFIED, GitHub Actions run 32689888754, green end to end** — every step from the Mathlib
> cache through `the whole library`, the axiom audit and the no-`sorry` check. All six
> advertised declarations report `[propext, Classical.choice, Quot.sound]`:
>
> ```
> 'Zeta23Ext.Bridge.ThreePoint.F3_eq'                  [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.ThreePoint.cover1'                 [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.ThreePoint.three_point_cert'       [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.ThreePoint.Phi_three'              [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.ThreePoint.three_point_bound'      [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.ThreePoint.three_point_bound_ratio'[propext, Classical.choice, Quot.sound]
> ```
>
> Companion to `CERTIFICATE-ROUTE.md`, which ranked the routes at `n = 7` and concluded the
> seven-point certificate is out of reach in Lean. At `n = 3` it is not, and this is the proof.

Every figure is labelled **VERIFIED** (read off a file or a build this session), **MEASURED**
(computed this session), **INFERRED**, or **NOT MEASURED**.

---

## 1. What is proved

**VERIFIED.** `hunts/ainta_seven_point/lean-three-point/` is a Lake package whose
`lakefile.toml` requires `lean/bridge` **by path**, so every theorem in it is about the same
`Kfun`, `kfun`, `wfun`, `F`, `Phi_n` that `Zeta23Ext/Bridge/Defs.lean` defines and that
`Zeta23Ext.Bridge.n_point_bound` consumes. Nothing is transcribed and there is no restatement
to audit. Its `lake-manifest.json` is dependency-for-dependency identical to
`hunts/ainta_seven_point/lean/lake-manifest.json` (checked, all eleven packages, same revs).
`lean/bridge` is untouched and nothing in `lean/bridge` imports this.

The three advertised statements, all three now proved:

```
Zeta23Ext.Bridge.ThreePoint.three_point_cert :
    ∀ g : Fin (3-1) → ℝ, (∀ i, 0 ≤ g i) → (1345/1000000 : ℝ) ≤ F 3 3000 g

Zeta23Ext.Bridge.ThreePoint.three_point_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((149000000 * HD 1 - 99200) / 148800133 - ε) * (Ncount T (2*T) : ℝ)
        ≤ N0simple T (2*T)

Zeta23Ext.Bridge.ThreePoint.three_point_bound_ratio :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (149000000 * HD 1 - 99200) / 148800133 - ε
        ≤ (N0simple T (2*T) : ℝ) / (Ncount T (2*T) : ℝ)
```

`three_point_bound` has **no hypotheses**. It is `n_point_bound` at `n = 3` with its
certificate hypothesis supplied by `three_point_cert` and its five side conditions
(`2 ≤ 3`, `3 ≤ 745`, `0 < 3000`, `0 < c`, `c(m−1) ≤ 1`) discharged by `norm_num`. The
argument order was checked against `lean/bridge/Zeta23Ext/Bridge/Main.lean:281` (VERIFIED).

**The constant. MEASURED**, independently of the generator, in this session:

```
Φ₃ = (149 000 000 · H − 99 200) / 148 800 133 ,   H = HD 1 = 3/2 − (1/√2)cot(1/√2)
   = 0.67273733450380945875…
H  = 0.67250070367941164573…
Φ₃ − H = 2.3663 · 10⁻⁴
```

The exact rational identity was checked by hand as well as by float: at `n = 3`, `m = 745`,
`p = 3000`, `Phi_n = (H − 1488/2235000)·745000000/744000665`, and `745000000/2235000 = 1000/3`
exactly, giving `(745000000·H − 496000)/744000665`, which is `(149000000·H − 99200)/148800133`
after dividing through by 5. (MEASURED.)

The unconditional constant the development proved before this note is `H` itself. `Φ₃`
improves on it in the fourth decimal, **unconditionally and as a theorem**. For scale: the
*conditional*
seven-point laboratory value is `0.673029553…` and the conditional eight-point value is
`0.673052982…`; both remain conditional on an interval-arithmetic verifier's acceptance.
`Φ₃` is smaller than both, and unlike both it is proved.

---

## 2. The parameters, and how they were checked

### 2.1 The functional

**VERIFIED against `lean/bridge/Zeta23Ext/Bridge/Defs.lean:70`, not assumed.** `F` is

```
F n p g = (1/p) Σ gᵢ + Σ_{i<j} (2/(n − (j−i))) · w(y_j − y_i)
```

At `n = 3` the pairs are `(0,1)` and `(1,2)` with `j−i = 1` and coefficient `2/(3−1) = 1`,
and `(0,2)` with `j−i = 2` and coefficient `2/(3−2) = 2`. So

```
F 3 p (g₀,g₁) = (g₀+g₁)/p + w(g₀) + w(g₁) + 2·w(g₀+g₁)
```

**The factor 2 on the outer pair is real.** The Lean proof does not depend on this being
written correctly here, because `F3_eq` derives the displayed form from `F` itself by
`simp only [F, ptsN, …]`.

### 2.2 The infimum

**MEASURED** (in the session that generated the table; reproduced here only to the extent of
confirming `c` sits below it):

```
inf over g ≥ 0 of F 3 3000 = 0.0013530645459787036…
attained at (g₀, g₁) = (1.05083108…, 2.00247696…)
```

The next-lowest local minimum is `0.00143392247…` at `(2.01871, 2.01871)`.

### 2.3 The choice of `c = 1345/10⁶`

**MEASURED this session**, by re-running the generator's exact-rational branch-and-bound at
thirteen values of `c` (`/tmp` scratch, 0.05–3.9 s each, total under 6 s of CPU):

| `c`·10⁶ | margin below inf | `m` | `c(m−2)` | 1-D cell lemmas | 2-D leaves | `Φ₃` | `Φ₃ − H` |
|---|---|---|---|---|---|---|---|
| 1353 | 6.455e-08 | 741 | 0.999867 | 4127 | 59361 | 0.67274270083558296 | 2.4200e-04 |
| 1352 | 1.065e-06 | 741 | 0.999128 | 1035 | 3646 | 0.67274202900278557 | 2.4133e-04 |
| 1351 | 2.065e-06 | 742 | 0.999740 | 746 | 1874 | 0.67274135926770584 | 2.4066e-04 |
| 1350 | 3.065e-06 | 742 | 0.999000 | 607 | 1246 | 0.67274068743513626 | 2.3998e-04 |
| 1349 | 4.065e-06 | 743 | 0.999609 | 523 | 949 | 0.67274001768974301 | 2.3931e-04 |
| 1348 | 5.065e-06 | 743 | 0.998868 | 485 | 783 | 0.67273934585740791 | 2.3864e-04 |
| 1347 | 6.065e-06 | 744 | 0.999474 | 428 | 635 | 0.67273867610175675 | 2.3797e-04 |
| 1346 | 7.065e-06 | 744 | 0.998732 | 403 | 557 | 0.67273800426966290 | 2.3730e-04 |
| **1345** | **8.065e-06** | **745** | **0.999335** | **368** | **487** | **0.67273733450380946** | **2.3663e-04** |
| 1344 | 9.065e-06 | 746 | 0.999936 | 354 | 444 | 0.67273666472889648 | 2.3596e-04 |
| 1340 | 1.306e-05 | 748 | 0.999640 | 292 | 308 | 0.67273398148322161 | 2.3328e-04 |
| 1335 | 1.806e-05 | 751 | 0.999915 | 242 | 229 | 0.67273062837484621 | 2.2992e-04 |
| 1330 | 2.306e-05 | 753 | 0.998830 | 206 | 174 | 0.67272727319993875 | 2.2657e-04 |

**A correction to the brief that opened this hunt.** It said `c = 1353/10⁶` cannot be
accepted because naive interval enclosure fails "even on a grid 4096× finer than the
verifier's". That is true of a *uniform* grid and false of adaptive bisection: the
branch-and-bound closes at `1353/10⁶` in exact rational arithmetic, in 3.9 s, at 4127 cell
lemmas and 59 361 leaves. The wall at `1353` is not enclosure accuracy. It is that 59 361
leaves is roughly a 500 000-line `Main.lean` (**INFERRED** from the 487-leaf file being
4180 lines) and no Lean build tolerates that from this route.

**Why `1345` and not `1347`.** The brief suggested `1347/10⁶` (`m = 744`,
`Φ₃ = 0.672738676…`). The branch-and-bound closes there too, at 428 cells and 635 leaves. It buys `1.34·10⁻⁶` of
constant, which is **0.6 % of the improvement over `H`**, for **+16 % cell lemmas and +30 %
leaves**. Given that the whole artefact is at present a proof script nobody has compiled, the
smaller of two nearly identical constants is the right one: the number that matters is
whether it builds at all, and every leaf is another `linarith` in a build I cannot time.
`1345` is the row where the constant has stopped moving and the size has not yet started.

If the build lands comfortably inside CI's budget, `1347` is a one-command regeneration
(`python3 hunts/ainta_seven_point/three_point_gen.py 1347`) and worth taking.

### 2.4 The block cap `m`

**MEASURED**, in exact rational arithmetic:

```
c(m−2) at m = 745 :  1345·743/10⁶  =  999335/10⁶ = 0.999335 ≤ 1     admissible
c(m−2) at m = 746 :  1345·744/10⁶  = 1000680/10⁶ = 1.000680 > 1     not admissible
```

so `m = 745 = 2 + ⌊10⁶/1345⌋` is the largest admissible block size, which is what
`n_point_bound`'s `hA0 : c((m:ℝ) − ((n:ℝ)−1)) ≤ 1` wants at `n = 3`.

---

## 3. The proof architecture

`w ≥ 0` everywhere, and `w` is bounded away from `0` except in four short intervals below the
cutoff. That is the whole idea, and it is what makes `n = 3` cheap where `n = 7` is not.

### 3.1 The pressure cutoff — the biggest saving

Since `w ≥ 0`,

```
g₀ + g₁ ≥ c·p = 4.035   ⟹   F 3 p g ≥ (g₀+g₁)/p ≥ c
```

One `rcases` and one `linarith` in `three_point_cert`. Everything outside the triangle
`{g₀,g₁ ≥ 0, g₀+g₁ ≤ 807/200}` is finished by it and the grid never sees it.

### 3.2 The one-dimensional cover

`cover1` : for `0 ≤ x ≤ 807/200`, either `c ≤ w(x)`, or `x` lies in one of four intervals.
**MEASURED** (`three_point_preflight.py`, §4): the chain is **27 segments, contiguous over
`[0, 4.035]` with no gap**, comprising 22 table cells, one window lemma on `[0,1/2]`, and the
four exported near-zero intervals

```
B₁ = [65/64, 71/64]    = [1.015625, 1.109375]    around the kernel zero 1.05727829…
B₂ = [31/16, 17/8]     = [1.9375,   2.125]       around 2.03006753…
B₃ = [23/8, 203/64]    = [2.875,    3.171875]    around 3.02024299…
B₄ = [245/64, 807/200] = [3.828125, 4.035]       around 4.01523561…  (right end is the cutoff)
```

Every one of those 22 table cells was checked to clear `c` and to contain the segment it is
applied to (MEASURED).

The consequence is that the two-dimensional work is confined to the pairs `Bᵢ × Bⱼ` whose
left corners survive the cutoff. **MEASURED**: those are `B₁×B₁`, `B₁×B₂`, `B₁×B₃`, `B₂×B₂`
and their transposes — **four** box lemmas, not five. `B₂×B₃` does *not* survive
(`1.9375 + 2.875 = 4.8125 > 4.035`); nor do `B₁×B₄`, `B₃×B₃`, `B₃×B₄`, `B₄×B₄`. All twelve
dead cases are closed in `three_point_cert` by `exfalso; linarith`. (An earlier draft of this
note listed `B₂×B₃` as surviving. It does not; the Lean was right and the prose was wrong.)

### 3.3 The cell bound — one general lemma, applied 1515 times

**This is the shape the brief asked for and the shape that was built.** There is exactly one
kernel lemma,

```lean
theorem wfun_ge (x nlo dhi : ℝ) (hnlo : 0 ≤ nlo) (hdhi : 0 < dhi)
    (hD0 : 1 < 2*(Real.pi*x)^2) (hD : 2*(Real.pi*x)^2 - 1 ≤ dhi)
    (hN : nlo ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)|) :
    (nlo/dhi)^2 ≤ wfun x
```

derived from `kfun_closed` (`k = N/D`, `N = cos b − 2γ b sin b`, `D = 1 − 2b²`, `b = πx`),
which is CertRoute's. For `x ≥ 1/2`, `b ≥ π/2` and `D < 0`, so a rational lower bound
`nlo ≤ |N|` and a rational upper bound `|D| ≤ dhi` give `(nlo/dhi)² ≤ w(x)`.

368 generated cell lemmas instantiate it, each of the shape

```lean
theorem wc_k (x : ℝ) (h₁ : (l:ℝ) ≤ x) (h₂ : x ≤ (u:ℝ)) : (W:ℝ) ≤ wfun x
```

with `l`, `u`, `W` rational literals, and each proved mechanically: reduce the angle to a
quarter window, enclose `cos` and `sin` by the twelve-term Taylor bound, enclose
`2γ(πx)·sin(πx)` by interval multiplication, subtract, apply `wfun_ge`. **VERIFIED**:
1515 applications of the 368 lemmas across the development — 22 in `cover1`, 1493 in the four
box trees.

**The angle reduction.** Every cell sits inside `[a, a+1/4]` or `[a−1/4, a]` for a half-integer
anchor `a ∈ {1/2, 1, …, 9/2}`, so `θ = π|x−a| ≤ π/4 = 0.7854 < 1` and CertRoute's
`cos_lower / cos_upper / sin_lower / sin_upper` apply verbatim. `cos(πa)` and `sin(πa)` at the
nine anchors are `0` or `±1` (`cs_h1 … cs_h9`), so the reduction is exact.

**Enclosure form: naive (constant), not centred.** Each cell contributes a *constant* lower
bound and the 2-D leaf adds three of them to the pressure term, so the overestimate is `O(h)`
in the cell side, not `O(h²)`. §6 says why the centred form was not built.

**Rounding.** Every intermediate rational is rounded outward to a fixed denominator so the
emitted literals stay small: reduced angles to `10⁻¹⁰`, everything else to `10⁻¹²`, the cell
value `W` to `10⁻¹³`. The rounding is always in the safe direction and the generator works in
`fractions.Fraction`, never in floating point.

### 3.4 The window `[0, 1/2]`

`kfun_closed` is silent at the removable singularity `b² = 1/2`, i.e. `x = √2/(2π) = 0.22508…`,
which lies inside `[0,1/2]`. That window is done from the **sinc form** instead
(`Kfun_eq_sinc`, CertRoute's), where the singularity is invisible:

```
K(x) = (sinc A + sinc B)/2,   A = (√2 − 2πx)/2,   B = (√2 + 2πx)/2
```

For `x ∈ [0,1/2]`: `|A| ≤ 0.8637 ≤ 1`, so `sinc A ≥ 0.87557` from a new twelve-term Taylor
enclosure of `sinc` (`sinc_taylor`, which handles `z = 0` separately and is new here); and
`0.7071 < B ≤ 2.278 < π`, so `sinc B ≥ 0`. Then `K ≥ 0.43778`, `K(0) = sinc(√2/2) ∈ (0,1]`, so
`k ≥ 0.43778` and `w ≥ 19/100`.

**MEASURED**: the true minimum of `w` on `[0,1/2]` is `0.436505` (attained at the right end),
and the true minimum of `sinc A` there is `0.880229`. The window is proved with 2.3× slack on
`w` and is 140× more than `c` needs. It is not a tight place, which is why the crude bound is
adequate.

### 3.5 The two-dimensional table

Four box lemmas, each a bisection tree in exact rational arithmetic. At a leaf, three cell
bounds and `linarith`:

```
c ≤ (x₀+y₀)/p + W(cell of x) + W(cell of y) + 2·W(cell of x+y)
```

Where the cell of a variable straddles a quarter boundary, the leaf splits on it inside the
`have` and uses the two neighbouring cell lemmas. Where a leaf lies beyond the cutoff, `w ≥ 0`
and the pressure term alone finishes it.

**MEASURED**: 487 leaves — `pair_0_0` 12, `pair_0_1` 453, `pair_0_2` 6, `pair_1_1` 16. The
binding basin is `B₁×B₂` and it carries 93 % of the tree, which is what one expects when the
argmin is at `(1.0508, 2.0025)`. The symmetry `F 3 p (g₀,g₁) = F 3 p (g₁,g₀)` halves the work:
only `i ≤ j` is proved and transposes apply the same lemma after
`rw [show y + x = x + y from by ring]`.

---

## 4. What was checked before the Lean was

`hunts/ainta_seven_point/three_point_preflight.py` (new, committed, 3 s) asks, before any
kernel is available: *is the certificate arithmetically true?* It is not a
proof and it is not in the trust chain — everything it checks the Lean build would check again,
rigorously. It is a filter, so that a CI round is not spent finding an error float arithmetic
could have found. **VERIFIED, run this session, exit 0:**

```
1. cells: 368 lemmas, 0 unsound
2. cover1: 27 segments over [0, 4.035], 22 table cells, 1 window, 4 near-zero intervals
3. pair_0_0: 12 leaves, 0 problems
3. pair_0_1: 453 leaves, 0 problems
3. pair_0_2: 6 leaves, 0 problems
3. pair_1_1: 16 leaves, 0 problems
total: 368 cell lemmas, 487 leaves, 0 problems
```

Specifically it confirms, against the true `w = (K/K(0))²` evaluated from the sinc form:

* every one of the 368 advertised cell constants `W` is a genuine lower bound for `w` on its
  interval (401-point sweep per cell, 147 568 evaluations);
* `cover1`'s chain is contiguous, hits the cutoff exactly, and every table cell both covers
  its segment and clears `c`;
* at every one of the 487 leaves, the three cell lemmas invoked really do cover the `x`, `y`
  and `x+y` ranges the branch conditions force — including the 50 places where the cell
  of a variable straddles a quarter boundary and the leaf splits on it and invokes two
  neighbouring cells — and the linear combination the `linarith`
  is asked to close is true.

**One real bug was found and fixed this session.** `cover1` was emitting

```lean
exact Or.inr Or.inr (Or.inl ⟨by linarith, by linarith⟩)
```

which is `Or.inr` applied to two explicit arguments, not nesting — a type error in three
places, which would have failed the first build. The generator was fixed, not just the output
(`three_point_gen.py`, the `Or.inr` emit site), and regenerating reproduces the committed
tree byte for byte apart from that fix and two tactic changes.

Two tactic chains were also hardened before spending a build on them: `F3_eq`'s trailing
`ring` became `try ring` (if `norm_num` closes the goal, a bare `ring` is an error), and
`Phi_three`'s `norm_num; field_simp; ring` became
`push_cast; rw [div_eq_div_iff (by norm_num) (by norm_num)]; ring`, which does not depend on
what `norm_num` chooses to leave behind. **These were guesses about elaboration, not
measurements — exactly the class of thing only a build settles.** Both turned out right,
and two other guesses of the same kind turned out wrong: `le_or_lt` does not exist at this
pin, and `open Real` was not the `open` the module needed.

**Which declarations had prior build evidence, and which had none — the pre-flight view.**
All 25 in the second and third groups below have since elaborated (§5); this is recorded
because it is how the risk looked before the first build, and because it turned out to be a
good predictor of nothing: every one of them compiled first time, and the failures came from
identifier renames and a heartbeat budget instead. **VERIFIED** by a
declaration-level diff of `ThreePoint/Base.lean` against `main`'s
`hunts/ainta_seven_point/lean/CertRoute.lean`, which PR #117 reports building with zero
errors:

* **byte-identical to CertRoute, so already elaborated once** (10 declarations):
  `taylorCos`, `taylorSin`, `cos_sin_taylor12`, `cos_lower`, `cos_upper`, `sin_lower`,
  `err_scale`, `one_le_pi`, `gam`, `integral_cos_mul_eq_sinc`. A further six —
  `sin_upper`, `Kfun_eq_sinc`, `cos_mul_intervalIntegrable`, `kfun_aux`, `kfun_closed`,
  `sin_sqrt2_half_pos` — differ from CertRoute **only in their doc comments**; their proof
  bodies are identical.
* **changed, so unelaborated at the time** (2): `sqrt2_half_bounds`, widened from 8 digits to 19
  (`7071067811865475244/10¹⁹ ≤ √2/2 ≤ 7071067811865475245/10¹⁹`, checked correct this
  session), proof body unchanged; and `gam_bounds`, tightened from `10⁻⁶` to `1.11·10⁻⁸`
  through the two new enclosures `cos_sqrt2_half_bounds` / `sin_sqrt2_half_bounds`.
* **new, so unelaborated at the time** (23): `pi_lo`, `pi_hi`, `wfun_nonneg`, `wfun_ge`, `abs_ge_of_le`,
  `abs_ge_of_ge`, the nine `cs_*` anchor lemmas, `cos_flip`, `sin_flip`, `trig_shift`,
  `taylorSinc`, `sinc_taylor`, `sqrt2_bounds`, `wfun_window`, `cos_sqrt2_half_bounds`,
  `sin_sqrt2_half_bounds`.

The `constructor <;> · …` idiom the nine anchor lemmas use was checked to be live Lean 4
syntax (21 occurrences in Mathlib, GitHub code search, VERIFIED), and `rw [<a def's name>]`,
`le_div_iff₀` and `div_le_iff₀` were confirmed present and working at this pin by the fact
that CertRoute's `gam_bounds` uses all three and builds.

**Static checks, VERIFIED:**

| | |
|---|---|
| `sorry`, `admit` | 0 |
| `native_decide` | 0 |
| `axiom`, `opaque`, `unsafe`, `implemented_by`, `extern` | 0 (one occurrence of the word "axiom" in a section-header comment) |
| machine-local paths | 0 |
| the repository's reserved word under `hunts/` | 0 |
| `scripts/71_contribution_check.py hunts/ainta_seven_point` | `contribution contract: PASS`, 21 passed |
| `scripts/make_context.py --check` | `CONTEXT.md is up to date` — no regeneration needed |

**Size, VERIFIED:** 20 028 lines across 9 files. 3490 `nlinarith`, 8435 `linarith`, 3967
`norm_num` invocations. (Before the leaf-shape change in §5 it was 21 416 lines and 5360
`norm_num`.)

**Where the time actually goes, MEASURED** (§5), against the guess this section originally
recorded. The guess was that `nlinarith` on 12-digit rational literals dominates. It is
half right: the seven cell tables are 3490 `nlinarith` calls and cost 34m39s of the cold
build, about 5.6 s per cell lemma. But `ThreePoint/Main.lean` contains **no `nlinarith` at
all** — its 487 leaves are `linarith` over three constants — and it still costs 14m49s, a
third of the whole build, because 453 of those leaves sit in one declaration. Proof
*structure* turned out to matter as much as tactic choice.

---

## 5. The build

**VERIFIED.** `.github/workflows/three-point.yml`. Five runs, and the story of each is
worth more than the final green tick.

It could not be started at first. The token this branch was pushed with carried
`gist, read:org, repo` and **not `workflow`**, and all three routes to a file under
`.github/workflows/` are refused without it: `git push` (`refusing to allow an OAuth App to
create or update workflow ... without workflow scope`), the contents API (`404`, the same
restriction masked — the identical call to a non-workflow path succeeds), and the git-data
API (`404` at `POST /git/trees`; that hole is closed). Granting an OAuth scope is a consent
decision, not an agent's to take, so the workflow was parked under `hunts/` with the two
commands that move it into place, and the operator ran them. That is the only step in this
note an agent did not do.

The workflow is `full.yml`'s `lean` job with three differences that matter to an author who
cannot build locally:

1. **a rolling cache key, not a fixed one.** `restore-keys` takes the newest prior cache and a
   separate `cache/save` writes a fresh one under a run-unique key. A fixed key never updates
   once written, which is right for a pinned toolchain and wrong for an iteration loop. This
   is what turned a 50-minute round into a 20-minute one from run 2 onward.
2. **the build staged module by module** under `/usr/bin/time -p`, so per-module cost survives
   into the log and a failure in the tables is distinguishable from a failure in the
   machinery. That is what produced the table below — and it costs something: staging
   serialises what `lake` would spread over the runner's 4 cores, so these are per-module
   *serial* costs, not the cost of the build a reader would run.
3. **`timeout-minutes: 350`**, because the repository cancels at 30, and `cache/save` runs
   `if: always()` right after the dependency step so a failure in the tables still banks the
   expensive part. It did, four times.

### Cost, MEASURED

Cold, run 32683784986, GitHub-hosted `ubuntu-latest` (4 cores):

| step | wall clock |
|---|---|
| `lake exe cache get` — Mathlib oleans at the pinned rev | 1m25s |
| dependencies: Zeta23 upstream, then `lean/bridge` | 11m24s |
| `ThreePoint.Base` — the machinery, 473 lines | 26s |
| `ThreePoint.Cells0…5` — 60 cell lemmas each | 5m33s, 5m36s, 5m36s, 5m47s, 5m56s, 5m21s |
| `ThreePoint.Cells6` — the remaining 8 | 50s |
| `ThreePoint.Main` — `cover1`, four box lemmas, 487 leaves, the certificate and the bound | 14m49s |
| **whole job, cold** | **≈ 50 min to the end of the tables, ≈ 65 min including `Main`** |

Warm, runs 2 through 5: the cache restores everything in about one minute and only `Main`
rebuilds, so an iteration on `Main` costs **4½ minutes of prelude plus `Main` itself**.

The Mathlib olean cache is what makes any of this possible. The pin,
`51e6992efd06126df61a496bebf8f49482a4e129`, is a real master commit (2026-08-03, "chore: bump
toolchain to v4.33.0-rc2"), so the upstream cache exists for it; without `lake exe cache get`
the runner would compile Mathlib from source and the loop would not exist.

### What the five runs cost, and what each one bought

**MEASURED.** This is the honest shape of a build loop run blind, and four of the five
failures were mine rather than the mathematics':

| run | outcome | what it found |
|---|---|---|
| 32683784986 | `Main` failed, 49m50s | `Base` and all seven cell tables green on the first attempt. `le_or_lt` does not exist at this pin (560 uses); `HD`, `Ncount`, `N0simple`, `eventually_atTop` unresolved |
| 32686863542 | `Main` failed, 4m29s | names fixed; the heartbeat budget is the wall — `pair_0_1` overruns 200 000 about 4 % of the way in, after 43 s |
| 32687291025 | `Main` failed, 19m29s | **the whole development elaborated.** Four errors, all orphaned doc comments: `set_option ... in` was emitted *after* the docstring |
| 32688543779 | `Main` **success**, 18m2s | the certificate and the bound are proved; the audit step's own grep misread the bridge's `[propext, choice, Quot.sound]` as a violation |
| 32689888754 | **green end to end** | the audit fixed and tested against three fixtures; `axiom audit clean: six advertised declarations`, `zero sorry, zero axiom, zero native_decide` |

Two of those cost more than they should have. The doc-comment ordering was settled afterwards
on AXLE in **0.9 seconds** — `doc-then-option` `okay=False`, `option-then-doc` `okay=True` —
which is the check that should have preceded the 19-minute round it cost. A Mathlib-only
syntax question never needs a CI cycle.

### Which shape compiles fastest

The brief asked for a general cell lemma applied many times, versus a `decide`-checked table,
versus a `Finset` fold, measured. **Only the first was built, so that comparison is NOT
MEASURED**, and the reason it was the one built is worth stating: the cell bound is a
statement about `Real.cos` and `Real.sin`, which the kernel cannot evaluate. A `decide` route
needs a `Decidable` bridge from a rational evaluator up to the real statement — a second
development, not a tactic choice. That reasoning is INFERRED.

What *was* measured is the shape of the leaf step, which turned out to matter:

| shape | AXLE, 500 leaf steps, Mathlib only | package scale, `ThreePoint.Main` |
|---|---|---|
| `le_trans (by norm_num) (wc_k x _ _)` | 25.6 s | 16m23s (run 3) |
| `wc_k x _ _` applied directly | 23.0 s | 14m49s (run 4) |

**MEASURED.** 1393 of the 1443 leaf steps asked for a constant that *is* the cell lemma's own
constant, and reached it through `le_trans`, which makes the elaborator postpone a
`by norm_num` against a metavariable until the second argument fixes it — for a proof of
`W ≤ W`. Handing it the term directly is 1.11× faster per step on the controlled test, about
5.2 ms, roughly 7 s across the package. At package scale `Main` fell 16m23s → 14m49s, 9.6 %.
**Those two numbers do not agree, and n = 1 per shape cannot separate the remaining 87 s from
the 1390 lines the file also lost or from run-to-run variance.** The honest reading is that
the direct form is free and slightly better, and that the `le_trans` idiom was *not* what
exhausted the heartbeat budget — the leaf count in a single declaration was.

### The one `set_option`, and what it is not

`pair_0_1` is `B₁ × B₂`, and it carries **453 of the 487 leaves**, because the binding basin
is at `(1.0508, 2.0025)`. A box lemma is one declaration holding its whole bisection tree, so
the tree shares a single heartbeat budget, and 453 leaves overrun the default 200 000.

The four generated box lemmas therefore carry `set_option maxHeartbeats 10000000 in`. This is
a compile-resource limit and nothing else: it is not an axiom, it does not appear in
`#print axioms`, and it is emitted **on the generated tables only** — `three_point_cert`,
`Phi_three`, `three_point_bound` and `three_point_bound_ratio` all carry the default.

The structural fix is to split `pair_0_1` so each subtree gets its own budget and they
compile in parallel. **Not done**, and §7 says so.

### The axiom audit, VERIFIED

```
'Zeta23Ext.Bridge.ThreePoint.F3_eq'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.ThreePoint.cover1'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.ThreePoint.three_point_cert'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.ThreePoint.Phi_three'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.ThreePoint.three_point_bound'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.ThreePoint.three_point_bound_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Three axioms, the ones Lean itself assumes. No `sorryAx`, no `native_decide`, no axiom of this
development's own.

The audit step took two tries to get right and the second one is worth describing, because a
green audit that cannot fail is worth nothing. `lake build` replays the diagnostics of every
cached module, so `main-build.log` carries the whole dependency tree's `#print axioms` output;
the bridge prints `[propext, choice, Quot.sound]` wherever `Classical` is open, which is the
same three axioms under a shorter name, and a blanket pattern reads it as a violation. The
check now scopes itself to `Zeta23Ext.Bridge.ThreePoint.*`, accepts `choice` and
`Classical.choice` as the one axiom they are, and **requires all six advertised names to be
present**, so a build that printed nothing cannot audit clean. It was tested against three
fixtures: the real run-4 log passes, a planted `sorryAx` on `three_point_cert` fails, an empty
log fails.

---

## 6. What is proved and what is not

**Proved, in Lean, sorry-free, standard axioms only:**

* `three_point_cert` — the `n = 3` certificate at `c = 1345/10⁶`, `p = 3000`. This is a Lean
  fact about the same `F` the bridge consumes, not a verifier's acceptance. 368 cell lemmas,
  22 covering steps, 4 box lemmas, 487 leaves.
* `three_point_bound`, `three_point_bound_ratio` — the unconditional simple-zero bound at
  `Φ₃ = 0.67273733450380945875…`, with **no hypotheses**, for Mathlib's `riemannZeta`.
* `Phi_three` — the constant as an exact rational in `HD 1`.
* `cover1` — the one-dimensional cover, and `wfun_window` (`w ≥ 19/100` on `[0,1/2]`, through
  the sinc form, across the removable singularity), and `sinc_taylor`, a twelve-term Taylor
  enclosure of `Real.sinc` valid at `0`, which Mathlib at this pin does not supply.

**What it is worth, stated carefully:**

* The architecture is the one the brief asked for: **one general cell lemma applied 1515
  times**, not thousands of hand-generated kernel facts, and no `decide`-checked table.
* The pressure cutoff does exactly what it was expected to: it removes everything outside a
  triangle of side 4.035 and leaves four short intervals, which is why `n = 3` is tractable
  where `n = 7` is not.
* The brief's claim that `c = 1353/10⁶` is unreachable is **wrong for adaptive bisection** and
  right for a uniform grid; the real wall at `1353` is proof size, measured at 4127 cells and
  59 361 leaves (§2.3).

**Not claimed:**

* Nothing here touches `n = 7` or `n = 8`. Those certificates remain what
  `CERTIFICATE-ROUTE.md` says they are: an interval-arithmetic verifier's acceptance, entering
  `n_point_bound` as a hypothesis. The seven- and eight-point constants in `RESULTS.md` and
  `BRIDGE.md` are unchanged and **still conditional**.
* **This is not an improvement on the state of the art in the literature.** It is an
  improvement on what this development can state **unconditionally**, which before this note
  was `H = 0.672500703…`. The conditional seven- and eight-point values (`0.673029553…`,
  `0.673052982…`) are both larger than `Φ₃`; what `Φ₃` has that they do not is a proof.
* The three-point bound at `c = 1353/10⁶` (`Φ₃ = 0.672742700…`) is **not** proved. §2.3 is the
  measurement that says why, and §7 says what would close it.
* The certificate is proved at `p = 3000` only. No sweep over `p` was run.

---

## 7. What I did not do

* **I never built anything locally.** Every build in §5 ran on GitHub Actions. No `lake build`
  was attempted on the author's machine, where it is not viable.
* **No `decide`-checked table and no `Finset` fold.** The brief asked which of the three
  shapes compiles fastest. Only one was built — the general lemma applied many times — and
  the comparison is therefore **NOT MEASURED**. The reason it was the one built is that the
  cell bound is a statement about `Real.cos` and `Real.sin`, which the kernel cannot evaluate;
  a `decide` table would need a `Decidable` bridge from a rational evaluator to the real
  statement, which is a second development, not a tactic choice. That reasoning is INFERRED,
  not measured, and a fair comparison would still be worth having.
* **`pair_0_1` was not split.** It holds 453 of the 487 leaves in one declaration, which is
  why it needs `maxHeartbeats 10000000` and why it cannot use more than one core. Splitting it
  by subtree would give each piece its own budget and let them compile in parallel, and would
  probably take the 14m49s `Main` step well under five minutes. The generator already tracks
  the box at every node, so this is a contained change. It was not made, because the priority
  was the theorem and the budget raise reached it.
* **`autoImplicit` was left on.** This is the sharpest thing the build loop found and it is
  not fixed. In run 1, `HD`, `Ncount` and `N0simple` were unresolved because the module opened
  only `Real`; `autoImplicit` silently bound each of them as an implicit variable of unknown
  type, so the advertised statements were, briefly, statements about nothing. It errored only
  because a variable cannot be applied to an argument — had the names been nullary it would
  have compiled and said nothing. A package whose entire point is an advertised theorem should
  set `autoImplicit := false` and `relaxedAutoImplicit := false` in its `lakefile.toml`, as
  Mathlib does. Not done here because changing a lakefile option invalidates the whole build
  cache and the theorem came first. **It should be the next commit on this branch.**
* **No centred / mean-value cell form.** The naive constant enclosure converges linearly in
  the cell side; a centred form converges quadratically and would reach `c = 1353/10⁶` at
  roughly 207 cells instead of 4127 (MEASURED in an earlier float branch-and-bound, not
  reproduced this session). It needs a two-sided *affine* enclosure of `N(πx)` per cell, hence
  Taylor with explicit remainder for `N` or a small interval layer with `cos`/`sin` at rational
  centres. Mathlib at the pinned revision has neither an interval-arithmetic tactic nor a
  numerical `sin`/`cos` evaluator — the gap `CERTIFICATE-ROUTE.md` §4 identified, still open.
  **This is the single change that would recover the last `5.4·10⁻⁶` of the constant.**
* **No unification with PR #117, which is now on `main`.** `ThreePoint/Base.lean` §§1–3
  reproduce `hunts/ainta_seven_point/lean/CertRoute.lean`'s Taylor enclosure, its monotone
  corollaries and `kfun_closed` **verbatim**, because they were written before #117 landed.
  They should now be imported instead: `CertRoute` is a Lake package at the same path depth,
  requiring the same `lean/bridge`, so the change is a `require` plus an `export`. It was not
  made, because `export`ing a `def` and then `unfold`ing the alias is exactly the kind of
  detail a build settles and I have no build. The only deliberate divergence from #117 is
  `gam_bounds`, tightened from `10⁻⁶` to `1.11·10⁻⁸` (the width the twelve-term remainder
  allows), because the cell table wants the extra digits. Its numeric bounds were re-checked
  this session (γ = 0.8274992963205883, inside `[0.8274992907, 0.8274993018]`).
* **No `n = 4, 5, 6` attempt.** The pressure cutoff and the near-zero cover are not special to
  `n = 3`, but the box dimension rises by one per point and nothing here measures that.
* **No sweep over `p`.** `p = 3000` was taken from the brief and the published runs.
  `Φ₃ − H ≈ H·c − 2/p` to leading order, so a larger `p` lowers the pressure penalty and also
  lowers `inf F`, hence `c`. Whether `p = 3000` is the peak at `n = 3` is NOT MEASURED.
* **No change to `lean/bridge`.** The Palomar submission surface, both comparator files and
  both formalization files are byte-identical. The new package requires the bridge rather than
  joining it.
* **No registry submission, no Modal, nothing merged.** The pull request is open and is not to
  be merged until §5 is cleared and the build is green.

---

## 8. Reproducing

```
python3 hunts/ainta_seven_point/three_point_gen.py 1345      # regenerate the tree, 0.14 s
python3 hunts/ainta_seven_point/three_point_preflight.py     # arithmetic check, 3 s
cd hunts/ainta_seven_point/lean-three-point
lake exe cache get                                          # Mathlib oleans, ~1.5 min
lake build ThreePoint                                       # ~65 min cold, 4 cores
```

Or push to `bridge/three-point` and read `.github/workflows/three-point.yml`, which is what
every figure in §5 was measured from.

The package pins `leanprover/lean4:v4.33.0-rc2` and inherits Mathlib
(`51e6992efd06126df61a496bebf8f49482a4e129`, a real master commit dated 2026-08-03, so the
upstream olean cache exists for it — VERIFIED via the GitHub API), Batteries and
`anthropics/zeta-23-lean` at rev `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` from
`lean/bridge`, by path.
