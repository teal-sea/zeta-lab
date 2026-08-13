# Two roads to a theorem, priced

State as of 2026-08-13. The single-pair (`k = 1`) retention inequality is
closed at **hardened** grade with no separation hypothesis (ledger, four
instruments plus a coordinator reproduction). Two roads lead onward and
they buy different things. This page prices both from measurements, not
estimates, and says which numbers are still unmeasured.

---

## ROAD A — kernel-check the `k = 1` theorem

**What you get.** A sorry-free Lean statement anyone can check without
trusting us: retention for every `n`, every shift, every depth in
`[0, 1/2]`, **no separation hypothesis**. The tree today carries only
`d >= 4` or `n <= 3`. This is the lab's top certainty rung and the closest
thing on the board to the Phase II objective.

**What it costs.** Twelve obligations. Seven are already kernel-checked in
`BandCert` (see `arm_identification.py`): the fixed-point interval layer,
the complex interval layer `CIv`, `sin`/`cos` with argument reduction,
`sinh`/`cosh`, `sqrt2`, `A`/`A^2`, and — the one that matters —
`phiC_mem`, which encloses `Phi2` at a **complex** point. Since
`ghat(z) = Phi2(-i z)` (residual exactly 0.0), the damage
`D(y,s) = -Re[Phi2(s - iy)^2]` is three composition steps on machinery
that already compiles.

Four of the five new obligations are small: the `linarith` reduction from
`retention_gap` + `energy_F`, the wiring lemma, the integer square
completion, and two one-variable bounds on `phiR`. The fifth is the table.

### The fork inside Road A, measured

|  | A1 — 2-D table over `[28/5,60] x [0,1/2]` | A2 — monotonicity + 1-D table at `y = 1/2` |
|---|---|---|
| extra lemma needed | none | `D(y,s)/y^2 <= 4 D(1/2,s)` |
| that lemma's status | — | **0 violations** over 400 `s`-points x 6 depths (Arb, 128-bit) |
| does the reduction close? | — | **yes, with room**: budget coefficient `Shq(y)/2 / y^2` is *increasing* in `y`, so its floor is `0.13087` at `y -> 0`; the requirement is `4 x 1.372e-02 = 5.487e-02`. Margin **2.39x** |
| measured cell count | degenerates (see below) | **45 cells, 0 undecided** with a single global cap |
| for scale | — | `BandCert`'s existing tables use 62–248 cells |

**A1 degenerates for an instrument reason, not a mathematical one.** With
a *constant* cap the top slab `y in [0.375, 0.5]` fails to discharge
(266159 cells, 266067 undecided) because the cap must scale like `y^2`
and a constant one cannot be met by a slab whose enclosure spans the
peak. A correct 2-D table needs `y`-dependent caps — which is the same
content as A2's monotonicity lemma, obtained the expensive way. **A2 is
the road.**

### What is NOT yet measured, and it is the one real unknown

The 45-cell figure is for a **single global cap** (`D <= D_1`
everywhere). LEMMA C needs **per-window caps**. Two attempts to size that
table both failed, for identified reasons, and the failures are the
finding:

1. Asking the table to prove `D <= 0` on cells straddling a window edge is
   **unprovable by enclosure** — `D` is exactly `0` there. 6.36M cells,
   99.995% undecided.
2. Enlarging the windows to fixed brackets fixes that in principle, but at
   half-width `0.6` the enclosure of `D` over the whole bracket is
   `2.73e-02` against a true peak of `4.40e-03` — a **6x** dependency
   blow-up — and the resulting cap sum `3.54e-02` already exceeds the
   budget `3.375e-02`. The bracket caps must be computed by subdivision
   *inside* each bracket, not by one wide evaluation.

So the honest number is: **45 cells for the coarse form; the per-window
form is unsized, and sizing it is the first task on Road A.** It is
ordinary interval-arithmetic engineering with a known technique
(`BandCert` already does exactly this for its bands), not research.

**Risk profile.** Low. Every step is known to be true; the only question
is cell count. Failure mode is cost, not refutation.

---

## ROAD B — prove the multi-pair (`k >= 2`) statement

**What you get.** Blocker 2 proper — the quantifier the source paper's
programme actually needs, and the one question here that is **ours**
rather than an improvement to someone else's paper. The source paper does
not ask what happens with `k` blocks.

**What it costs.** Unknown, which is the honest headline. What exists:

- The **exact identity** (`kpair_identity.py`, residual `4.21e-17`):
  `slack_k` = gain − damage + repulsion − inter-pair, where the repulsion
  term carries no pair index.
- A **mechanism**, measured: the adversary has two routes and both pay.
  Spread the centres and `damage/gain` falls from `1.0420` at `k = 1,2` to
  `0.2483` at `k = 12`, because only two positions carry the top window
  peak and the rest decay like `1/s^2`. Stack the centres and the
  inter-pair term turns positive at `1.7556` per ordered pair.
- A **search** with measured power: worst relative margin `+0.343` at
  `k = 4` over `n <= 24` and mixed depths, with a planted-fault ladder
  whose firing threshold (`1.5`) matches the margin's prediction
  (`1.522`).

**What is missing** is the step from "both routes pay" to an inequality.
That requires a quantitative version of *"only two positions carry the top
peak"* — i.e. a lower bound on how fast a pair's collectable damage falls
as its centre moves away from the on-line mass. Nobody has written that
lemma and I do not know that it is easy.

**Risk profile.** Genuine research risk. It could fall out of the squeeze
in a day, or the squeeze could turn out to be true but not provable by any
argument that discards cross-window relief — which is exactly how the
per-pair route died. **There is no evidence the statement is false**: no
violation in ~70k configurations across four independent searches.

---

## Comparison

| | Road A (`k = 1` in Lean) | Road B (`k >= 2` proof) |
|---|---|---|
| what it produces | an externally checkable theorem | a new mathematical statement |
| certainty on arrival | kernel-checked | hardened, then paper |
| risk of failure | ~none; cost only | real |
| cost known? | **yes, modulo one sizing task** | **no** |
| reuses existing work | heavily (7/12 obligations) | the identity only |
| blocked by the other? | no | no |
| community value | high — anyone can check it | high — but only if it lands |
| ours or theirs? | improves their result | **our question** |

**They are independent and can run at once.** Road A is engineering with
a known technique and a bounded downside; Road B is the research bet. The
sequencing argument is that Road A converts existing hardened work into
the repo's strongest currency and cannot fail, so it should not wait on a
research question; and Road B's first task (the falling-damage lemma) is
one person-scale piece of mathematics that does not need the Lean arm.

**Recommended:** run both. Road A first task — size the per-window table
by subdividing inside each bracket. Road B first task — state and attempt
the falling-damage lemma. Neither depends on the other, and Road A's
first task is the one that can be handed off.

---

*No proportion is claimed to have moved, and nothing on either road is
evidence about RH.*
