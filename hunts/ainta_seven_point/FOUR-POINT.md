# The four-point certificate, proved in Lean

> `THREE-POINT.md` discharged `n_point_bound`'s certificate hypothesis at `n = 3` and got the
> laboratory's first unconditional improvement on `H`: `Φ₃ = 0.67273733450380945875…`, `+2.3663·10⁻⁴`.
> This note pushes the same ladder one rung: `n = 4`, three gaps, a tetrahedron instead of a
> triangle, and
>
> ```
> Φ₄ = (906250·HD 1 − 1085)/904171 = 0.67284701976668870316…
> Φ₄ − H = 3.4632·10⁻⁴,   which is 1.464× the three-point gain
> ```
>
> proved unconditionally, sorry-free, with no axiom beyond the three Lean itself assumes.
>
> **VERIFIED, GitHub Actions run 32738666418, green end to end on the first build** — every step
> from the Mathlib cache through the whole library, the axiom audit and the no-`sorry` check.
> All six advertised declarations report `[propext, Classical.choice, Quot.sound]`:
>
> ```
> 'Zeta23Ext.Bridge.FourPoint.F4_eq'                  [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.FourPoint.cover1'                 [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.FourPoint.four_point_cert'        [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.FourPoint.Phi_four'               [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.FourPoint.four_point_bound'       [propext, Classical.choice, Quot.sound]
> 'Zeta23Ext.Bridge.FourPoint.four_point_bound_ratio' [propext, Classical.choice, Quot.sound]
> ```
>
> One run, 3h18m30s, no iteration. The three-point result took five.

Every figure is labelled **VERIFIED** (read off a file or a build), **MEASURED** (computed this
session), **INFERRED**, or **NOT MEASURED**.

---

## 1. What is proved

**VERIFIED.** `hunts/ainta_seven_point/lean-four-point/` is a Lake package whose `lakefile.toml`
requires `lean/bridge` **by path**, so every theorem in it is about the same `Kfun`, `kfun`,
`wfun`, `F`, `Phi_n` that `Zeta23Ext/Bridge/Defs.lean` defines and that
`Zeta23Ext.Bridge.n_point_bound` consumes. Its `lake-manifest.json` and `lean-toolchain` are
byte-identical copies of `lean-three-point`'s. `lean/bridge` is untouched, nothing in
`lean/bridge` imports this, and nothing here imports `lean-three-point`: the two packages are
independent instances of the same construction at `n = 3` and `n = 4`.

```
Zeta23Ext.Bridge.FourPoint.four_point_cert :
    ∀ g : Fin (4-1) → ℝ, (∀ i, 0 ≤ g i) → (2310/1000000 : ℝ) ≤ F 4 2500 g

Zeta23Ext.Bridge.FourPoint.four_point_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((906250 * HD 1 - 1085) / 904171 - ε) * (Ncount T (2*T) : ℝ)
        ≤ N0simple T (2*T)

Zeta23Ext.Bridge.FourPoint.four_point_bound_ratio :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (906250 * HD 1 - 1085) / 904171 - ε
        ≤ (N0simple T (2*T) : ℝ) / (Ncount T (2*T) : ℝ)
```

`four_point_bound` has **no hypotheses**. It is `n_point_bound` at `n = 4` with its certificate
hypothesis supplied by `four_point_cert` and its five side conditions (`2 ≤ 4`, `4 ≤ 435`,
`0 < 2500`, `0 < c`, `c(m−3) ≤ 1`) discharged by `norm_num`.

**The constants, MEASURED:**

```
H  = HD 1 = 3/2 − (1/√2)cot(1/√2) = 0.67250070367941164573…
Φ₃ = (149000000·H −  99200)/148800133 = 0.67273733450380945875…   (THREE-POINT.md, proved)
Φ₄ = (   906250·H −   1085)/   904171 = 0.67284701976668870316…   (this note)

Φ₃ − H = 2.3663·10⁻⁴
Φ₄ − H = 3.4632·10⁻⁴          =  1.464 × the three-point gain
Φ₄ − Φ₃ = 1.0968·10⁻⁴
```

The exact rational was derived twice and the two agree. By hand:
`Phi_n n c m p = (H − q(m−1)/(pm)) / (1 − c(m−q)/m)` with `q = n−1 = 3`, `c = N/D = 231/100000`,
`m = 435`, `p = 2500` is `(D·p·m·H − D·q(m−1)) / (p(Dm − N(m−q)))`
`= (108750000000·H − 130200000)/108500520000`, and dividing through by `120000` gives
`(906250·H − 1085)/904171`. Independently, `Phi_four`'s tactic chain
(`unfold; push_cast; rw [div_eq_div_iff …]; ring`) was run on a Mathlib-only mock of `Phi_n` on
AXLE and closed, which is Lean agreeing that the identity holds. (MEASURED, both.)

---

## 2. Choosing the route, with the arithmetic that chose it

Two routes were on the table and both were measured before anything was generated.

### 2.1 Route (b): better `(c, p)` at `n = 3`

**MEASURED.** `p = 3000` was inherited from the brief and the published seven-point runs, and it
is **not** the `n = 3` optimum. To leading order `Φ_n ≈ H + H·c(p) − q/p`, and by the envelope
theorem `dc/dp = −Σg*/p²`, so the optimum sits where `H·Σg* = q`. At `n = 3` that is
`Σg* = 2/H = 2.974`; the argmin of `F 3 3000` has `Σg* = 3.053`, i.e. **past** the optimum, so
`p` should come **down**. Sweeping `p` and taking the true infimum at each (two basins tracked
separately, Nelder–Mead from grid seeds). In both tables of this section `c = ⌊inf·10⁶⌋/10⁶`,
i.e. the largest admissible `c` at **zero margin**, so the `Φ` columns are an upper envelope: an
actual proof has to sit below them, and §2.1's second table and §2.2's second table are what it
costs to come down from the envelope by a usable margin.

| `p` | `inf F 3 p` | argmin | `c·p` | `m` | `Φ₃` | `Φ₃ − H` |
|---|---|---|---|---|---|---|
| 960 | 0.0034665545 | (1.038, 1.038) | 3.32 | 290 | 0.6727401909 | 2.3949e-04 |
| 1000 | 0.0033800341 | (1.038, 1.038) | 3.38 | 297 | 0.6727660742 | 2.6537e-04 |
| 1005 | 0.0033697033 | (1.038, 1.038) | 3.39 | 298 | 0.6727686778 | 2.6797e-04 |
| **1010** | **0.0033580070** | **(1.051, 2.002)** | **3.39** | **299** | **0.6727711826** | **2.7048e-04** |
| 1020 | 0.0033283797 | (1.051, 2.002) | 3.39 | 302 | 0.6727705648 | 2.6986e-04 |
| 1500 | 0.0023707397 | (1.051, 2.002) | 3.56 | 423 | 0.6727574188 | 2.5672e-04 |
| 3000 | 0.0013530645 | (1.051, 2.002) | 4.06 | 741 | 0.6727499009 | 2.4200e-04 |
| 8000 | 0.0005927312 | (2.019, 2.019) | 4.74 | 1691 | 0.6726485886 | 1.4788e-04 |

The peak is a **kink at `p ≈ 1007`**, where the binding basin switches from the symmetric
`(1.038, 1.038)` to the asymmetric `(1.051, 2.002)` — exactly where `H·Σg*` crosses `q`.
Its value is `Φ₃ − H = 2.705·10⁻⁴`, against `2.420·10⁻⁴` at `p = 3000`.

But the peak is at zero margin, and margin is what the branch and bound spends. Running
`three_point_gen.py`'s own exact-rational branch and bound at `p = 1010` (MEASURED, each row
under 31 s of CPU):

| `c`·10⁶ | margin below inf | `m` | cell lemmas | leaves | `Φ₃` | `Φ₃ − H` |
|---|---|---|---|---|---|---|
| 3358 | 6.97e-09 | 299 | 101784 | 596726 | 0.6727711826 | 2.7048e-04 |
| 3355 | 3.01e-06 | 300 | 2346 | 5369 | 0.6727691994 | 2.6850e-04 |
| 3350 | 8.01e-06 | 300 | 1195 | 2384 | 0.6727658468 | 2.6514e-04 |
| 3340 | 1.80e-05 | 301 | 662 | 1122 | 0.6727591697 | 2.5847e-04 |
| 3330 | 2.80e-05 | 302 | 507 | 729 | 0.6727524922 | 2.5179e-04 |
| 3320 | 3.80e-05 | 303 | 398 | 530 | 0.6727458144 | 2.4511e-04 |

So route (b) exists and is real: at a size the three-point build is already known to survive
(398 cells, 530 leaves, against the committed 368 and 487) it buys `+8.5·10⁻⁷`, and at roughly
six times that size it buys `+3.2·10⁻⁶`. **It is a fourth-decimal correction to a
fourth-decimal result.**

### 2.2 Route (a): `n = 4`

**MEASURED.** `F 4 p (g₀,g₁,g₂) = (g₀+g₁+g₂)/p + (2/3)(w g₀ + w g₁ + w g₂) + w(g₀+g₁) + w(g₁+g₂)
+ 2 w(g₀+g₁+g₂)`. Sweeping `p` with the true infimum at each:

| `p` | `inf F 4 p` | argmin | `c·p` | `m` | `Φ₄ − H` |
|---|---|---|---|---|---|
| 1500 | 0.0034288831 | (1.047, 1.981, 1.047) | 5.14 | 294 | 2.8959e-04 |
| 2000 | 0.0027498396 | (1.047, 1.981, 1.047) | 5.50 | 366 | 3.3857e-04 |
| 2500 | 0.0023423879 | (1.047, 1.981, 1.047) | 5.86 | 429 | 3.6763e-04 |
| **3000** | **0.0020513764** | **(1.052, 2.964, 1.052)** | **6.15** | **490** | **3.7366e-04** |
| 4000 | 0.0016291359 | (1.052, 2.964, 1.052) | 6.52 | 616 | 3.4194e-04 |
| 8000 | 0.0008987030 | (2.015, 2.011, 2.015) | 7.18 | 1116 | 2.2782e-04 |

The unconstrained peak is `3.74·10⁻⁴` near `p = 3000` — **larger than the whole route-(b) peak**
before any size is spent. Under a size budget the best `p` moves down to `2400–2600`, because
`c·p` is the pressure cutoff and the cost of the table is driven by it. The size/constant
frontier at `p = 2500` (exact-rational branch and bound, MEASURED, generator-accurate counts):

| `c`·10⁶ | `m` | `c(m−3)` | cell lemmas | leaves | `Φ₄` | `Φ₄ − H` |
|---|---|---|---|---|---|---|
| 2300 | 437 | 0.998200 | 842 | 2364 | 0.6728403587 | 3.3966e-04 |
| **2310** | **435** | **0.997920** | **983** | **3315** | **0.6728470198** | **3.4632e-04** |
| 2315 | 435 | 0.998784 | 1075 | 4082 | 0.6728503501 | 3.4965e-04 |
| 2320 | 434 | 0.998196 | 1148 | 5288 | 0.6728536988 | 3.5300e-04 |
| 2325 | 434 | 0.999062 | 1330 | 7313 | 0.6728570289 | 3.5633e-04 |
| 2330 | 433 | 0.997690 | 1516 | 11863 | 0.6728603588 | 3.5966e-04 |

### 2.3 The comparison, and the arithmetic

**MEASURED.** The three-point build's own numbers were the yardstick at decision time: 368 cell
lemmas cost 34m39s of *staged, serial* CI and 487 leaves in one declaration cost 14m49s, i.e.
**5.65 s per cell lemma** and **1.83 s per leaf** on a GitHub-hosted `ubuntu-latest`. The
projection made before generating anything, dividing by four cores and adding the measured 13 min
of prelude:

| | best in a comparable budget | `Φ − H` | gain over the proved `Φ₃` | cells | leaves | projected |
|---|---|---|---|---|---|---|
| **route (b)**, `n = 3` | `p = 1010`, `c = 3355/10⁶` | 2.6850e-04 | **+3.19e-05** | 2346 | 5369 | ≈ 111 min |
| **route (a)**, `n = 4` | `p = 2500`, `c = 2310/10⁶` | 3.4632e-04 | **+1.097e-04** | 983 | 3315 | ≈ 63 min |

```
route (b):  3.19e-05 / 1.85 h  =  1.72e-05 of constant per CI-hour
route (a):  1.097e-04 / 1.06 h =  1.035e-04 of constant per CI-hour
                                  ──────────
                                  6.0× better
```

**Route (a) was chosen, and the routes are not combinable**: route (b) *is* the
`p`-optimisation, and route (a) already carries it out at `n = 4` (that is why `p = 2500`
appears rather than the inherited `3000`).

**The absolute times in that table are wrong by about 3×, and the ranking is not.** §5 measures
that `lake` did not spread the modules over four cores, so dividing by four was a mistake — but
it was the same mistake on both rows. Redoing the arithmetic at the measured rates (6.51 s per
cell lemma for the `n = 4` table, 1.34 s per leaf, and the three-point's own 5.65 s per cell for
the `n = 3` row, whose cells stop at `x ≈ 3.4` and are cheaper):

```
route (a):  MEASURED, the run took 3h18m30s
            1.097e-04 / 3.31 h  =  3.32e-05 of constant per CI-hour
route (b):  2346·5.65 + 5369·1.34 + 15 min prelude  =  21 349 s  =  5.93 h
            3.19e-05  / 5.93 h  =  5.38e-06 of constant per CI-hour
                                   ──────────
                                   6.2× better  (projected 6.0×)
```

and with one thing the projection could not see: **route (b)'s best-in-budget point would not have
built at all.** 21 349 s is 356 minutes, against the workflow's `timeout-minutes: 350`. The route
that was rejected on efficiency turns out also to have been the route that did not fit.

### 2.4 Why not `n = 5`

**MEASURED, and this is the reason the ladder stops here for now.** `n = 5` has a higher
unconstrained peak (`Φ₅ − H ≈ 4.2–4.5·10⁻⁴`), but the adjacent-pair coefficient falls to
`2/(5−1) = 1/2`, so the one-dimensional cover must be run at level `2c` (§3.1), the near-zero
intervals widen accordingly, and the bisection is four-dimensional. At a size comparable to the
chosen four-point tree:

| | cells | leaves | `Φ − H` |
|---|---|---|---|
| `n = 4`, `p = 2500`, `c = 2310/10⁶` | **983** | **3315** | **3.4632e-04** |
| `n = 5`, `p = 3000`, `c = 2500/10⁶` | 1937 | 4532 | 3.3540e-04 |
| `n = 5`, `p = 2500`, `c = 2900/10⁶` | 3152 | 4575 | 3.3339e-04 |
| `n = 5`, `p = 2500`, `c = 2950/10⁶` | 4363 | 8163 | 3.6642e-04 |

`n = 5` is **dominated on both axes** at the four-point operating point: it needs about twice the
cells and 1.4× the leaves to reach a *smaller* constant. To beat `n = 4` it needs roughly 4.4×
the cells and 2.5× the leaves for `+2.0·10⁻⁶`. That is the wall, and it is a different wall from
the three-point one: at `n = 3` the binding constraint was proof size at fixed geometry; at
`n = 5` it is the cover level, which is a consequence of the functional and not of the enclosure.

---

## 3. The proof architecture, and the one thing that is genuinely new

The skeleton is `THREE-POINT.md` §3 unchanged: `w ≥ 0` everywhere and `w` is bounded away from
`0` except in short intervals around the low zeros of the kernel, so a pressure cutoff removes
the tail and a small table covers the rest. `four_point_gen.py` **imports** the cell machinery
from `three_point_gen.py` rather than copying it, so the two tables are literally the same table
generator; what differs is forced by the functional.

### 3.1 The cover level — the correction that matters

**This is the only mathematically new point in the note, and getting it wrong would have
produced a tree that looks right and proves nothing.**

At `n = 3` the pair `(i, i+1)` carries `2/(n − 1) = 1`, so a gap `x` with `c ≤ w(x)` closes the
whole certificate on its own: the cover can be run at level `c`. At `n = 4` that coefficient is
`2/3`, and `c ≤ w(x)` only buys `(2/3)c`. The cover must therefore be run at

```
level = c·(n−1)/2 = 3c/2 = 3465/10⁶      (so that (2/3)·level = c exactly)
```

and its near-zero intervals are correspondingly wider — `1.22×` wider in half-width, since `w`
is quadratic at a simple zero of `k`. A first sizing pass of this hunt used level `c` and
reported leaf counts about 30 % too optimistic; the numbers in §2 are the corrected ones.
`four_point_preflight.py` §2 checks the level explicitly against the cover's advertised statement,
so the mistake cannot recur silently.

**MEASURED.** At `c = 2310/10⁶`, `p = 2500`, cutoff `S = c·p = 231/40 = 5.775`, the cover at
level `3465/10⁶` is **31 contiguous segments over `[0, 5.775]`** — 26 table cells, the
`[0, 1/2]` sinc window, and **four** exported near-zero intervals:

```
B₁ = [63/64,  73/64]  = [0.984375, 1.140625]   around the kernel zero 1.05727829…
B₂ = [121/64, 141/64] = [1.890625, 2.203125]   around 2.03006753…
B₃ = [179/64, 105/32] = [2.796875, 3.28125]    around 3.02024299…
B₄ = [237/64, 231/40] = [3.703125, 5.775]      the tail
```

`B₄` is not a zero basin, and it is 2.07 wide against the others' 0.16 to 0.48. Beyond
`x ≈ 4.47` the *local maxima* of `w` themselves fall below `3c/2` — `w`'s envelope decays like
`γ²/(π²x²) = 0.06938/x²`, and `√(0.06938/0.003465) = 4.475` (MEASURED) — so the cover cannot clear
anything past there, and the basin around the zero `4.01523561…` merges with that whole stretch
into one interval running to the cutoff.

It costs almost nothing, and the pressure cutoff is why. Only **three** of the 64 dispatch cases
contain `B₄` at all — `(1,1,4)`, `(1,4,1)`, `(4,1,1)` in one-based numbering — because
`B₄`'s left end plus the two smallest others is `0.984375 + 0.984375 + 3.703125 = 5.671875`,
leaving `0.103125` of room below the cutoff `5.775`. They collapse to two box lemmas carrying
**4 leaves each out of 3315** (MEASURED). Every other appearance of `B₄` is dead.

### 3.2 The tetrahedron

**MEASURED.** The surviving boxes are the triples `(Bᵢ, Bⱼ, Bₖ)` whose left corners sum below the
cutoff. Of the `4³ = 64` cases, **44 are dead by pressure** and 20 survive; the functional is
symmetric under `(g₀,g₁,g₂) ↦ (g₂,g₁,g₀)` (and only under that — it is *not* fully symmetric, the
way `F 3` is), so the 20 collapse to **13 box lemmas**, and the 7 transposed cases apply the same
lemma to `(z, y, x)` after three `rw [show … from by ring]` steps.

The leaf distribution is as lopsided as at `n = 3` and for the same reason — the binding basin is
at `(1.052, 2.964, 1.052)` at `p = 3000`, and near `(1.05, 1.98, 1.05)` here:

```
box_0_1_0  2515 leaves      box_0_0_1    92      box_0_1_2   4
box_0_1_1   253             box_0_0_0    57      box_0_2_1   4
box_0_2_0   188             box_0_0_2    37      box_0_3_0   4
box_1_0_1   147             box_1_1_1     6      box_1_0_2   4
box_0_0_3     4
```

### 3.3 Chunking — the structural fix `THREE-POINT.md` §7 left undone

**THREE-POINT.md** recorded that `pair_0_1` held 453 of 487 leaves in one declaration, needed
`maxHeartbeats 10000000`, could not use more than one core, and that splitting it "would probably
take the 14m49s `Main` step well under five minutes." It was not done there. It is done here,
because at `n = 4` it is not optional: `box_0_1_0` holds 2515 leaves.

The generator cuts every box tree into **chunk lemmas of at most 110 leaves**, bin-packs the
resulting **76 chunks across 16 modules** by leaf count (loads 206–208 leaves per module, MEASURED),
and emits a small **router lemma per box** whose branches all end in `exact ch_k x y z (by linarith)…`.
Each chunk gets its own heartbeat budget and `lake` compiles the 16 modules in parallel.

**MEASURED twice, and it is the figure that set the size budget.** Before the build: a real
110-leaf chunk (`ch_17`, 398 lines, 82 distinct cell lemmas referenced), with the cell lemmas
replaced by axioms of exactly the same statements so that only the leaf structure is timed,
elaborates on AXLE in **76.7 s — 0.70 s per leaf**. After the build: the whole `FourPoint.Chunks`
step is **1h13m48s for 3315 leaves — 1.34 s per leaf on the CI runner** (§5), against the 1.83 s
per leaf the three-point `Main` averaged over 487 leaves of which 453 sat in one declaration. So
a chunked leaf costs **27 % less** than a leaf inside a huge declaration *while carrying twice the
work* — six `have`s and a `linarith` over thirteen hypotheses, against three and six — and the
`FourPoint.Main` step that holds the certificate itself costs 20 seconds against the three-point
`Main`'s 14m49s.

### 3.4 The leaf

Six `w`-facts instead of three, and the six `wfun_nonneg` facts are hoisted once to the top of
each chunk lemma rather than repeated: a term whose interval bound would be `0` is then simply
omitted from the leaf, which is why the tree needs **983** cell lemmas rather than the 1153 the
branch and bound touches (**MEASURED**; 170 of the intervals it visits carry a zero bound).

```
c ≤ (x₀+y₀+z₀)/p + (2/3)(W(x) + W(y) + W(z)) + W(x+y) + W(y+z) + 2·W(x+y+z)
```

**A measured negative.** A cell lemma costs several times what a leaf costs, so it looked worth
trying to push work the other way: refuse to let a single `have` span more than `K` quarter
windows (taking its bound to `0` instead, which the hoisted `wfun_nonneg` covers) and let the
bisection compensate. It buys nothing, because almost nothing straddles. **MEASURED** at
`c = 2310/10⁶`, `p = 2500`:

| `K` | cell lemmas | leaves |
|---|---|---|
| no cap | 983 | 3315 |
| 3 | 983 | 3315 |
| 2 | 979 | 3316 |

### 3.5 The extra anchors

**VERIFIED.** The three-point table's cells never left `[0.5, 4.3]`, so nine half-integer anchors
sufficed. The four-point cells reach `6.2434`, so `FourPoint/Base.lean` adds `cs_5`, `cs_h11` and
`cs_6` in the shape of the existing nine. All three were checked on AXLE before the first build
(`okay=True`, 0.6 s).

---

## 4. What was checked before the Lean was

`hunts/ainta_seven_point/four_point_preflight.py` (new, committed) reads the **generated Lean**,
not the generator's in-memory tree, so it also catches emission bugs the generator cannot see.
**VERIFIED, exit 0:**

```
1. cells: 983 lemmas, 0 unsound
2. cover1: 31 segments over [0, 5.775], 26 table cells, 1 window, 4 near-zero intervals
           at level 0.003465
3. chunks: 76 lemmas, 3315 leaves, 0 problems
4. routers: 13 boxes, 76 regions, 0 problems
5. dispatch: 64 cases (44 dead by pressure), 0 problems
total: 983 cell lemmas, 3315 leaves, 76 chunks, 13 boxes, 0 problems
```

It checks, against the true `w = (K/K(0))²` evaluated from the sinc form:

* every one of the 983 cell constants is a genuine lower bound for `w` on its interval
  (401-point sweep per cell, 394 183 evaluations);
* the cover's chain is contiguous, hits the cutoff exactly, every table segment lies inside the
  cell it invokes, and every table cell clears **`3c/2`**, not `c`;
* at every one of the 3315 leaves, the cell lemmas invoked really do cover the `x`, `y`, `z`,
  `x+y`, `y+z` and `x+y+z` ranges the branch conditions force — including the leaves that split a
  straddling cell — and the linear combination the `linarith` is asked to close is true;
* every one of the 76 router regions lands in a chunk lemma whose hypotheses cover it;
* every one of the 64 dispatch cases names a box lemma whose bounds are the right three near-zero
  intervals in the right order, or declares the case dead — in which case the pressure cutoff
  really does kill it.

**A green check that cannot fail is worth nothing** (THREE-POINT.md §5), so it was fault-injected
four ways and caught all four (**VERIFIED**):

| planted fault | caught as |
|---|---|
| a leaf's claimed `W` inflated 10× | `ch_24: leaf claims 0.00135743827 > weakest of ['wc_27'] = 0.000135743827` |
| a cell lemma's constant inflated 100× | `unsound cell wc_120: claims 3.200827e-02, true min on [1.983…,1.988…] is 3.208341e-04` |
| a dispatch case pointed at the wrong box | `dispatch (0,1,0) direct calls box_0_0_0, expected box_0_1_0` |
| a live dispatch case declared dead | `dispatch (0,0,1) declared dead but its corner 3.859375 is below the cutoff 5.775` |

### The Lean questions, settled without a CI round

**MEASURED.** THREE-POINT.md §5 recorded that a doc-comment ordering question cost a 19-minute CI
round and was afterwards settled on AXLE in 0.9 s. Every idiom this tree introduces was therefore
put to AXLE **first**, on Mathlib-only fragments with `wfun`, `HD`, `F`, `ptsN` and `Phi_n`
replaced by the bridge's own definitions over opaque stand-ins:

| question | verdict | wall |
|---|---|---|
| `cs_5`, `cs_h11`, `cs_6` in the shape of the existing anchors | `okay=True` | 0.6 s |
| `F4_eq`: does `simp only [F, ptsN, sum3, Fin.sum_univ_four, Fin.isValue]; norm_num; try ring` close the six-term expansion? | `okay=True` | 1.0 s |
| `Phi_four`: does `unfold; push_cast; rw [div_eq_div_iff …]; ring` give `(906250·H − 1085)/904171`? | `okay=True` | (same run) |
| the transpose step: three `rw [show … from by ring] at h` then `linarith` | `okay=True` | (same run) |
| does `exact` bridge `((2500:ℕ):ℝ)` in the goal and `(2500:ℝ)` in the box lemma? | `okay=True` | (same run) |
| a real 110-leaf chunk with axiom cell lemmas | `okay=True`, **76.7 s** | §3.3 |

A control run of the same file, before `box_demo` was reduced to a statement, returned
`okay=False` — so the `True`s are not vacuous.

**Static checks, VERIFIED:**

| | |
|---|---|
| `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `unsafe` in the package | 0 (outside comments) |
| machine-local paths | 0 |
| the repository's reserved word under `hunts/` | 0 |
| `scripts/71_contribution_check.py hunts/ainta_seven_point` | `contribution contract: PASS`, 21 passed |
| `scripts/make_context.py --check` | `CONTEXT.md is up to date` |

**Size, VERIFIED:** 76 026 lines across 39 files.

---

## 5. The build

**VERIFIED.** `.github/workflows/four-point.yml`, GitHub Actions run **32738666418**, job
`97467548455`, GitHub-hosted `ubuntu-latest` (`ubuntu-24.04`, runner 2.336.0). **Green end to end
on the first attempt**, 14:26:05Z → 17:44:35Z.

### Cost, MEASURED

| step | wall clock |
|---|---|
| restore elan and lake | 0s — **cache miss**, see below |
| install elan, toolchain | 12s |
| `lake exe cache get` — Mathlib oleans at the pinned rev | 1m36s |
| dependencies: Zeta23 upstream, then `lean/bridge` | 11m00s |
| save cache after dependencies | 1m10s |
| `FourPoint.Base` — the machinery, 3 anchors added | 26s |
| `FourPoint.Cells` — **983 cell lemmas, 17 modules** | **1h46m43s** |
| `FourPoint.Cover` — 31 segments | 27s |
| `FourPoint.Chunks` — **3315 leaves, 76 lemmas, 16 modules** | **1h13m48s** |
| `FourPoint.Boxes` — 13 routers | 1m36s |
| `FourPoint.Main` — `F4_eq`, the 64-case certificate, `Phi_four`, both bounds | 20s |
| the whole library | 8s |
| axiom audit, forbidden-token scan | 0s |
| save cache | 1m01s |
| **whole job, cold** | **3h18m30s** |

The two rates that matter, and both are now measurements rather than projections:

```
cell lemmas :  6403 s / 983  =  6.51 s per lemma
leaves      :  4428 s / 3315 =  1.34 s per leaf
```

### Three things the build settled that the projection got wrong

**1. `lake` did not use the four cores, and the workflow change that assumed it would bought
nothing.** `three-point.yml` staged every module in a separate step, which *serialises* what
`lake` would otherwise spread over the runner; this workflow deliberately built all 17 cell
modules in one `lake build` so that it could parallelise. The measured per-lemma rate is
**6.51 s against the three-point's 5.65 s** — i.e. the same rate, on cells that are *more*
expensive (this table runs out to `x = 6.24` against the three-point's `4.3`, so the `2(πx)²`
literals are twice the size and `nlinarith` is slower on them). Whatever the reason — the
independent `Cells{k}` modules import only `FourPoint.Base` and nothing forces an order — the
elapsed time is what a serial build would cost. **Every projection in §2.3 divided by four cores
and was therefore about 3× optimistic in absolute terms.** The *ranking* it produced was
unaffected, because both routes were divided by the same wrong number.

**2. Chunking is worth what `THREE-POINT.md` §7 guessed it was worth.** That note recorded that
`pair_0_1` held 453 of 487 leaves in one declaration, needed `maxHeartbeats 10000000`, could not
use more than one core, and that splitting it "would probably take the 14m49s `Main` step well
under five minutes". Measured here, on leaves carrying **twice** the work (six `have`s and a
`linarith` over thirteen hypotheses, against three and six):

| | leaves | s / leaf |
|---|---|---|
| three-point `Main`, one 453-leaf declaration among 487 | 487 | 1.83 |
| four-point `Chunks`, 76 declarations of ≤ 110 leaves | 3315 | **1.34** |

and `FourPoint.Main` — which holds `F4_eq`, the whole 64-case certificate, `Phi_four` and both
bounds — costs **20 seconds**, against the three-point `Main`'s 14m49s. The cost was never in the
certificate; it was in the leaf count inside single declarations.

**3. A GitHub Actions cache cannot be read across branches.** The workflow lists
`three-point-${{ runner.os }}-` as a last-resort `restore-keys` entry, on the reasoning that the
two packages pin the same toolchain and the same `lake-manifest.json`, so a three-point cache
carries a `lean/bridge/.lake` this job could use. It restored **nothing in 0s**: Actions caches
are scoped to the branch that wrote them plus the default branch, and the three-point caches were
written on `bridge/three-point`. The entry is harmless and was left in place — it will start
working the day either branch lands on `main` — but the 11-minute dependency build is unavoidable
for the first run on any new branch. **INFERRED** from the 0s restore and the documented scoping
rule; not tested directly.

### The axiom audit, VERIFIED

```
'Zeta23Ext.Bridge.FourPoint.F4_eq'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.FourPoint.cover1'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.FourPoint.four_point_cert'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.FourPoint.Phi_four'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.FourPoint.four_point_bound'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23Ext.Bridge.FourPoint.four_point_bound_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Three axioms, the ones Lean itself assumes. No `sorryAx`, no `native_decide`, no axiom of this
development's own. The audit is `three-point.yml`'s, scoped to `Zeta23Ext.Bridge.FourPoint.*`,
accepting `choice` and `Classical.choice` as the one axiom they are, and **requiring all six
advertised names to be present** so that a build which printed nothing cannot audit clean.

### `set_option maxHeartbeats`, and where it is not

`20000000` on the 76 chunk lemmas, the 13 routers and the private `cert_core`. It is a
compile-resource limit and nothing else: not an axiom, absent from `#print axioms`. The four
**advertised** statements — `four_point_cert`, `Phi_four`, `four_point_bound`,
`four_point_bound_ratio` — and `F4_eq` and `cover1` all carry the **default** budget, which is why
`four_point_cert` is a three-line wrapper (`intro`, `rw [F4_eq]`, `exact cert_core …`) over a
private lemma that carries the case analysis. `THREE-POINT.md` put the raise on its certificate;
this does not.

### One run, not five

The three-point build took five runs and four of the failures were the author's rather than the
mathematics'. This one took one. The difference is not luck: `four_point_preflight.py` checked the
arithmetic of the generated Lean before it was pushed, and every Lean idiom the tree introduces was
put to AXLE on a Mathlib-only fragment first (§4). **The 19-minute CI round that
`THREE-POINT.md` §5 spent on a doc-comment ordering was the whole argument for doing it that way,
and it held.**

---

## 6. How much further it goes, and where the wall is

The brief asked for the constant pushed as far as is actually buildable. With the two rates of §5
measured, that is now a calculation rather than a guess. Regenerating at a larger `c` is one
command; the dependency build is cached after run 1, so a further run costs `6.51·cells +
1.34·leaves` plus about two minutes of prelude.

**MEASURED** (cell and leaf counts from the generator; times projected at the measured rates):

| `c`·10⁶ | cells | leaves | projected job | `Φ₄ − H` | gain over `c = 2310` | gain per CI-hour |
|---|---|---|---|---|---|---|
| **2310** | **983** | **3315** | **3h18m (actual)** | **3.4632e-04** | — | — |
| 2315 | 1075 | 4082 | 3h30m | 3.4965e-04 | +3.33e-06 | 9.5e-07 |
| 2320 | 1148 | 5288 | 4h05m | 3.5300e-04 | +6.68e-06 | 1.6e-06 |
| 2325 | 1330 | 7313 | 5h10m | 3.5633e-04 | +1.00e-05 | 1.9e-06 |
| 2330 | 1516 | 11863 | **7h11m** | 3.5966e-04 | +1.33e-05 | — |

**The hard wall is the workflow's own `timeout-minutes: 350`.** `c = 2325/10⁶` fits, at 310
projected minutes against a 350-minute cap — forty minutes of margin on a two-rate linear model,
which is not much. `c = 2330/10⁶` needs 431 minutes and **does not fit**. Beyond that the branch
and bound itself starts to run away: at `c = 2358/10⁶` (the largest admissible value at
`p = 2500`, `inf F 4 2500 = 0.00234239`) the leaf count is in the hundreds of thousands, the same
shape `THREE-POINT.md` §2.3 measured at `c = 1353/10⁶`.

**The soft wall bites first, and it is the same criterion that chose the route.** Route (a) was
taken over route (b) because it returned more proved constant per CI-hour. Measured, it returned
`+1.097e-04 / 3.31 h = 3.32e-05` per CI-hour. The next rung up returns `1.6e-06` per CI-hour —
**twenty times worse than the run that was just made, and three times worse than route (b)**, the
route that was rejected as not worth the CI. Spending four more hours to move `Φ₄` by 1.9 % would
be a worse use of the build loop than the thing already judged not worth doing.

So the answer to "how much further" is: **about 4 % of the current gain is available inside the
workflow's timeout, at between twenty and thirty-five times the cost per unit, and nothing beyond
that without a different enclosure.** The deliverable stays at `c = 2310/10⁶`, and the table above
is the measurement that says why, not a preference.

### Retuning `(c, p)` again does not help either

**MEASURED** (§2.2). `p = 2500` is already the size-constrained optimum for `n = 4`; the
unconstrained peak is near `p = 3000`, and moving there raises the cutoff `S = c·p` from `5.775`
to `6.15`, which adds a fifth and sixth near-zero interval and roughly doubles the cell table for
`+2.7e-06`. The `p` sweep was run before generation for exactly this reason.

### What would actually move it

Unchanged from `THREE-POINT.md` §7, and now with a number attached. The naive constant enclosure
converges linearly in the cell side; a centred/mean-value form converges quadratically. At `n = 3`
that was measured to be the difference between 4127 and roughly 207 cells. If it bought the same
factor here, `c = 2358/10⁶` — the *analytic* ceiling at `p = 2500`, `Φ₄ − H = 3.6864e-04` — would
come inside the timeout, and `n = 5` would stop being dominated. It needs a two-sided **affine**
enclosure of `N(πx)` per cell, hence Taylor with explicit remainder for `N`, or a small interval
layer with `cos`/`sin` at rational centres. Mathlib at the pinned revision has neither an
interval-arithmetic tactic nor a numerical `sin`/`cos` evaluator — the gap
`CERTIFICATE-ROUTE.md` §4 identified, still open, and now the binding constraint on this ladder
rather than a footnote to it.

---

## 7. What is proved and what is not

**Proved, in Lean, sorry-free, standard axioms only:**

* `four_point_cert` — the `n = 4` certificate at `c = 2310/10⁶`, `p = 2500`. A Lean fact about the
  same `F` the bridge consumes, not a verifier's acceptance. 983 cell lemmas applied 18 595 times,
  31 covering steps, 76 chunk lemmas over 3315 leaves, 13 box routers, 64 dispatch cases.
* `four_point_bound`, `four_point_bound_ratio` — the unconditional simple-zero bound at
  `Φ₄ = 0.67284701976668870316…`, with **no hypotheses**, for Mathlib's `riemannZeta`.
* `Phi_four` — the constant as an exact rational in `HD 1`.
* `cover1` — the one-dimensional cover at level `3c/2` over `[0, 5.775]`.

**What it is worth, stated carefully:**

* This is the best **unconditional** constant this development can state. It replaces `Φ₃` in that
  role and improves it by `1.0968e-04`.
* **It is not an improvement on the state of the art in the literature.** The conditional
  seven- and eight-point values (`0.673029553…`, `0.673052982…`) are both larger than `Φ₄`; what
  `Φ₄` has that they do not is a proof. `Φ₄` closes **21 %** of the gap between the proved `Φ₃`
  and the conditional seven-point value, where `Φ₃` closed 45 % of the gap between `H` and it.
* The `n = 3` result is untouched. `lean-three-point` still builds and still proves `Φ₃`; the two
  packages share no code beyond the generator's cell machinery, which is imported rather than
  copied.

**Not claimed:**

* Nothing here touches `n = 7` or `n = 8`. Those certificates remain an interval-arithmetic
  verifier's acceptance entering `n_point_bound` as a hypothesis, and the seven- and eight-point
  constants in `RESULTS.md` and `BRIDGE.md` are unchanged and **still conditional**.
* The certificate is proved at `p = 2500` only, and at `c = 2310/10⁶` only. §6 measures what the
  neighbouring values cost; none of them is proved.
* `n = 5` is **not** shown to be impossible — §2.4 shows it is dominated *at this operating point
  and with this enclosure*, which is a different statement.

---

## 8. What I did not do

* **No local build.** Every build ran on GitHub Actions; `lake build` is not viable on this
  machine.
* **No centred / mean-value cell form.** Unchanged from THREE-POINT.md §7: the naive constant
  enclosure converges linearly in the cell side, a centred form would converge quadratically, and
  it needs a two-sided *affine* enclosure of `N(πx)` per cell that Mathlib at this pin does not
  supply. It is still the single change that would move this result most, and it would move
  `n = 5` further than `n = 4`.
* **No `n = 6, 7`.** §2.4 measures the `n = 5` wall; `n ≥ 6` is worse for the same reason — the
  cover level is `c(n−1)/2`, so it rises with `n` and the near-zero intervals widen with it — and
  was not measured.
* **No second run at a larger `c`.** §6 is a projection from two measured rates, not a build. It
  says `c = 2325/10⁶` fits inside the workflow's timeout with forty minutes of margin and
  `c = 2330/10⁶` does not, and that the next rung returns twenty times less constant per CI-hour
  than the run that was made. **The projection is a linear model in two parameters fitted to one
  run; the 350-minute boundary between `2325` and `2330` is where it deserves least trust.**
  It was not spent, because doing so would have been a worse use of the build loop than route (b),
  which was rejected on exactly that ground.
* **No `decide`-checked table and no `Finset` fold.** Unchanged from THREE-POINT.md §7 and for the
  same reason: the cell bound is a statement about `Real.cos` and `Real.sin`, which the kernel
  cannot evaluate, so a `decide` route needs a `Decidable` bridge from a rational evaluator up to
  the real statement — a second development, not a tactic choice. INFERRED, not measured.
* **The four-core assumption was never checked before it was used.** §5 measures that the build
  ran at serial rates and the workflow's un-staging bought nothing; nothing here diagnoses *why*,
  and `lake --version`, `-j`, and the runner's effective core count were not examined. A
  `/usr/bin/time -v` on the cells step would have printed the CPU-percent figure that settles it,
  and the step used `-p`.
* **No unification with the three-point package or with PR #117.** `FourPoint/Base.lean` is
  `ThreePoint/Base.lean` with the namespace changed and three anchor lemmas added. Three copies of
  the same enclosure machinery now exist (`lean/CertRoute.lean`, `lean-three-point`,
  `lean-four-point`) and they should become one; that is a refactor with a build cost and no new
  mathematics, and it was not the priority.
* **No change to `lean/bridge`.** The Palomar submission surface is byte-identical.
* **Nothing merged, nothing submitted.** The pull request is open and is not to be merged.

---

## 9. Reproducing

```
python3 hunts/ainta_seven_point/four_point_gen.py 2310 2500   # regenerate the tree
python3 hunts/ainta_seven_point/four_point_preflight.py       # arithmetic check
cd hunts/ainta_seven_point/lean-four-point
lake exe cache get
lake build FourPoint
```

Or push to `bridge/four-point` and read `.github/workflows/four-point.yml`, which is what every
figure in §5 was measured from (run 32738666418).

`four_point_gen.py` takes `c` and `p` on the command line, so the rows of §6 are one command each:
`python3 four_point_gen.py 2320 2500`, and so on. The generator is deterministic — regenerating at
`2310 2500` reproduces the committed tree byte for byte.

The package pins `leanprover/lean4:v4.33.0-rc2` and inherits Mathlib
(`51e6992efd06126df61a496bebf8f49482a4e129`), Batteries and `anthropics/zeta-23-lean` at rev
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510` from `lean/bridge`, by path.
