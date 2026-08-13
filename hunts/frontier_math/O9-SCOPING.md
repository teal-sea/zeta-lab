# O9 scoping — what the nine-window table costs as an interval object

**Date:** 2026-08-13. **Code:** `o9_scoping.py`, `test_o9_scoping.py` (17 pins).
**Reads:** `RETENTION-PROBLEM.md` §4 (the obligations) and §7 (the arithmetic).
**Writes nothing into the Lean package** — this is a cost estimate for a build
that has not started, produced before starting it rather than after.

Run:

```bash
.venv/bin/python hunts/frontier_math/o9_scoping.py
.venv/bin/python -m pytest -q hunts/frontier_math/test_o9_scoping.py
```

## 0. Why this file exists

`RETENTION-PROBLEM.md` §4 names O9 — the damage cap table on
`[28/5, 60] x [0, 1/2]` — as **"the only real work"** left in the `k = 1`
retention chain, the other four open obligations being small. `PROOF-LEDGER.md`
prices the same item as "the real remaining cost: a two-variable
interval-arithmetic statement, the analogue of the `BandCert` leaf tables
already in this package". Neither says how large that table is, and the number
turns out to decide the shape of the build.

## 1. The headline

**O9 as written cannot be held by interval arithmetic at all, and the reason is
not size.** The recorded caps `c_k` are defined in §4 as the *supremum* of
`Dam(y,s)/y^2` over each window box, rounded up. Recomputing them finds the
supremum attained, to four figures, at an interior point of every window, always
at `y = 1/2`:

| k | window | `c_k` | recomputed sup | ratio | argmax |
|---|---|---|---|---|---|
| 0 | `[6.0653, 7.0514]` | 1.758572e-02 | 1.758569e-02 | 1.0000 | `s=6.5167, y=0.500` |
| 1 | `[12.2342, 13.1999]` | 3.900230e-03 | 3.900218e-03 | 1.0000 | `s=12.6988, y=0.500` |
| 2 | `[18.4704, 19.4332]` | 1.693130e-03 | 1.693117e-03 | 1.0000 | `s=18.9400, y=0.500` |
| 3 | `[24.7289, 25.6909]` | 9.444500e-04 | 9.444420e-04 | 1.0000 | `s=25.2003, y=0.500` |
| 4 | `[30.9971, 31.9586]` | 6.021000e-04 | 6.020920e-04 | 1.0000 | `s=31.4704, y=0.500` |
| 5 | `[37.2701, 38.2315]` | 4.172400e-04 | 4.172320e-04 | 1.0000 | `s=37.7444, y=0.500` |
| 6 | `[43.5460, 44.5072]` | 3.061500e-04 | 3.061449e-04 | 1.0000 | `s=44.0213, y=0.500` |
| 7 | `[49.8237, 50.7849]` | 2.342000e-04 | 2.341968e-04 | 1.0000 | `s=50.3000, y=0.500` |
| 8 | `[56.1026, 57.0637]` | 1.849400e-04 | 1.849385e-04 | 1.0000 | `s=56.5789, y=0.500` |

An inequality that is an equality somewhere has no margin, and an enclosure of
positive width can never close it: bisection refines forever around the
maximiser. Measured, at inflation `1.00x` the first window alone burns 14 398
leaves and still hits a depth-30 wall (`test_the_bare_caps_do_not_terminate`).

The same tangency appears a second time, at the window *edges*: `I_k` is by
construction the set where `Qim^2 - Qre^2 > 0`, so on the complement the
companion claim "no damage outside the windows" is an equality at every
endpoint. Bare, the complement also fails to close (404 leaves, depth wall).

Both are presentational, and both have room to be fixed.

## 2. The two knobs, and how much each one has

**Knob A — inflate the caps.** O9 feeds §7 only as an upper bound, so replacing
`c_k` by `lambda * c_k` weakens the statement in the safe direction. The cost is
paid in the final arithmetic, where the caps enter through the integer trade
`P(c,q)`. Reproducing §7 exactly from the table:

| row | recomputed | §7 |
|---|---|---|
| nine windows, both sides | 7.5279200e-02 | 7.5279200e-02 |
| far intervals | 3.6305144e-03 | 3.6305145e-03 |
| tail beyond `s = 400` | 5.4146344e-04 | 5.4146340e-04 |
| **total deficit** | **7.9451178e-02** | 7.9451178e-02 |
| **budget** | **1.2986000e-01** | 1.2986000e-01 |
| **surplus** | **5.0408822e-02** | 5.0408822e-02 |

Bisecting on `lambda`, the **largest inflation §7 still absorbs is `1.3945x`**.
That is the whole of the 1.6345x margin the chain already reports, spent on the
windows alone.

**Knob B — widen the windows.** The recorded `I_k` are the damage support, and
they sit in a `[28/5, 60]` interval at a 15.3 % duty cycle: width `~0.96` at
spacing `>6.16`. There is room to grow each window by a margin on both sides,
and because the added strips carry no damage, **the caps do not move** — grid
suprema over the widened boxes stay under `c_k` at every `k`
(`test_widening_a_window_does_not_raise_its_cap`). Widening costs nothing on the
window side and buys a strict margin on the complement side.

## 3. The measured cost

Windows widened by `0.02`, adaptive bisection on the longer side, Arb balls at
160 bits:

| inflation | §7 surplus | window leaves | max depth | status |
|---|---|---|---|---|
| 1.00x | 5.041e-02 | 14 398+ | 30 | does not close |
| 1.05x | 4.430e-02 | 307 | 10 | closes |
| 1.10x | 3.820e-02 | 151 | 8 | closes |
| 1.15x | 3.210e-02 | 89 | 8 | closes |
| **1.20x** | **2.599e-02** | **63** | **6** | **closes** |
| 1.25x | 1.989e-02 | 47 | 6 | closes |
| 1.30x | 1.379e-02 | 36 | 6 | closes |
| 1.35x | 7.000e-03 | 29 | 5 | closes |

The complement, over the ten gaps between the widened windows:

| widening | leaves | max depth | status |
|---|---|---|---|
| 0.00 | 404+ | 30 | does not close |
| 0.01 | 241 | 14 | closes |
| **0.02** | **201** | **12** | **closes** |
| 0.05 | 159 | 10 | closes |
| 0.10 | 120 | 8 | closes |

**Recommended operating point: inflation `1.20x`, widening `0.02`.**
That is **63 + 201 = 264 leaves, maximum depth 12**, and it leaves the §7
arithmetic a surplus of `2.599e-02` against a budget of `1.2986e-01` — a 1.16x
margin still in hand against the `1.3945x` wall. The whole sweep runs in under a
second.

For scale: `BandCert/Data.lean`, which already compiles in this package, records
**3005 integers in 70 KB**. O9 at the recommended point is roughly a third of
that. **Size was never the obstacle.**

## 4. What the build actually needs

1. **`Qre_closed` / `Qim_closed` are already kernel-checked**
   (`EForm3/ClosedForm.lean`), so the enclosure never has to carry a quadrature.
   O9 is interval arithmetic on an explicit elementary expression — the same
   position `BandCert` was in.
2. **One new leaf is needed: the removable branch `Qim(y,s)/y`.** Writing the
   check as `Qim^2 - Qre^2 <= c y^2` directly forces every box touching `y = 0`
   to establish `Qim^2 <= Qre^2`, which is false at the zeros of `Qre(0, .)`;
   that alone accounted for most of the cost in the first run of this probe.
   Rewriting it as `y^2 (R^2 - c) <= Qre^2` with `R = Qim/y` removes the
   degeneracy. `R` needs `sinh(a/2)/a`, and `Leaves.lean` already carries the
   same device for `sin(u/2)/u` (its `sfnL` series), so this is a copy of an
   existing pattern rather than new machinery.
3. **Argument reduction to `s/2 <= 30`.** `Leaves.lean` L3 already has it, with a
   `2^-64` enclosure of pi.
4. **The recorded table changes shape**: nine rows of
   `(s_lo, s_hi, cap)` become nine *widened* rows with caps inflated `1.20x`,
   plus a leaf list per window and per gap. Both numbers are small enough that
   `decide` — which is what `Check.lean` uses, not `native_decide` — stays
   plausible; that should be the first thing measured once the checker exists,
   since kernel reduction, not leaf count, is the real risk at this size.

## 5. Scope, and what this is not

This is a probe. It measures a cost and reports a shape; it lands nothing in
`zeta23ext` and moves no obligation from open to closed. O9 remains open, the
`k = 1` chain remains at hardened grade, and `k >= 2` — the 1.99x budget
shortfall of `PROOF-LEDGER.md`, which is on the budget side and is not touched by
anything here — remains the actual open mathematics. Nothing in this file is
evidence about RH.

The grid suprema in §1 are grid maxima, so they are lower bounds on the true
suprema: they can show a cap is attained, which is what they are used for, and
they cannot show a cap is safe. The enclosure sweep in §3 is what carries the
inequality, and it carries it for the *inflated* caps only.
