# O9: work order for the next session

**Status:** ready to build. Scoping is done (`O9-SCOPING.md`, `o9_scoping.py`,
17 pins in `test_o9_scoping.py`). Nothing below is research; every number it
needs already exists.

**Goal:** move obligation O9 of `RETENTION-PROBLEM.md` §4 from open to
kernel-checked, so the `k = 1` retention inequality stops being the last
hardened-grade step in its chain.

**Not in scope:** the `k >= 2` budget shortfall (1.99x, `PROOF-LEDGER.md`). That
is open mathematics and is untouched by this work order.

---

## 0. The one thing to know before starting

The O9 statement in `RETENTION-PROBLEM.md` §4 **cannot be built as written**.
Its caps `c_k` are the attained suprema of `Dam(y,s)/y^2`, so the inequality is
an equality at an interior point of every window and no enclosure of positive
width closes it. Same at the window edges for the companion "no damage outside
the windows" claim, which is an equality there by construction.

Build the **restated** version below instead. It is weaker, it is what §5 step 4
actually consumes, and §7 has the room to pay for it.

---

## 1. The statement to build

Let `WIDEN = 1/200` and `INFL = 6/5`. For each `k < 9` take the recorded window
`[lo_k, hi_k]` and cap `c_k` from §4, and set

    J_k = [lo_k - WIDEN, hi_k + WIDEN],    d_k = INFL * c_k

> **O9'** For every `y in [0, 1/2]` and every `s` with `28/5 <= s <= 60`:
> either `s` lies in exactly one `J_k` and then `Dam y s <= d_k * y^2`,
> or `s` lies in no `J_k` and then `Dam y s = 0`.

Negative `s` is the mirror image (`Dam` is even in `s`: `Qre` is even and `Qim`
odd in the second argument), so build it for `s > 0` only.

The `J_k` are pairwise disjoint: widths at most `0.9961` at left-endpoint
spacing `> 6.16`. `J_0` starts at `6.0603 > 28/5`; `J_8` ends at
`57.0687 < 60`.

**`WIDEN` is capped at `0.00695`, and the cap is load-bearing.** §5 step 3
groups the offsets inside one window and charges every pair `Kpair >= 39/50`,
which O3 supplies only on `|u| <= 1`. A widened window wider than `1` holds two
of its own points further apart than that: `Kpair(1.01) = 0.77943` is already
under `39/50`. Widest recorded window is `0.9861`, so `WIDEN <= 0.00695`.
`o9_scoping.py` asserts this rather than trusting it; do not raise `WIDEN`
without also re-deriving O3 at the larger radius and re-running §7 with the
smaller `q`.

**Why the inflation is affordable.** O9 enters §7 only as an upper bound.
Re-running the §7 arithmetic with caps scaled by `INFL` gives deficit
`1.0387e-01` against budget `1.2986e-01`, surplus `2.599e-02`. The wall is at
`1.3945x`; `6/5` sits comfortably inside it. `o9_scoping.py` §[2] recomputes all
of this, and `test_o9_scoping.py` pins it.

**Why the widening is free.** The added strips carry no damage, so the caps do
not move, checked at every `k` in `o9_scoping.py` §[3] and pinned by
`test_widening_a_window_does_not_raise_its_cap`.

---

## 2. Shape of the build: copy `BandCert`

`Zeta23Ext/BandCert/` is the same object one level up in difficulty and it
already compiles. Mirror it as `Zeta23Ext/EForm3/DamageTable/`:

| BandCert file | what the O9 analogue does |
|---|---|
| `Iv.lean` | **reuse as-is.** Fixed-point intervals at scale `2^64`, with soundness lemmas. Do not rewrite it. |
| `Leaves.lean` | **reuse, plus one addition**, see §3. |
| `Phi.lean` | interval evaluators for `Qre`, `Qim/y` from the closed forms |
| `Check.lean` | `Bool`-valued leaf checker + the lemma that `true` implies the real inequality |
| `Data.lean` | the recorded leaf list |
| `Verify.lean` | `decide` that the recorded data passes the checker |
| `Main.lean` | O9' as a `theorem`, from checker + data |

**Use `decide`, not `native_decide`.** `BandCert/Check.lean` does, and the house
rule is that nothing counts on a compiler-trusted step. At this size that should
hold, but **measure kernel reduction time early**, it is the only real risk in
this build, and it is not the leaf count.

---

## 3. The evaluators, and the one new leaf

`Qre_closed` and `Qim_closed` are already kernel-checked in
`EForm3/ClosedForm.lean`, so **no quadrature enclosure is needed**. With
`kp = s + sqrt2`, `km = s - sqrt2`:

    Qre(y,s) = C(y,kp) + C(y,km)
        C(a,k) = [a sinh(a/2) cos(k/2) + k cosh(a/2) sin(k/2)] / (a^2 + k^2)

**Do not evaluate `Dam y s <= d_k y^2` directly.** Every leaf touching `y = 0`
would then be asked to establish `Qim^2 <= Qre^2`, which is **false** at the
zeros of `Qre(0, .)`, and the subdivision runs forever there. This cost 225k
leaves and a non-terminating sweep on the first pass of the scoping probe.

Evaluate instead through `R = Qim/y`, which is analytic across `y = 0`:

    Dam <= d y^2   <=>   y^2 (R^2 - d) <= Qre^2

    R(y,s) = Sdiv(y,kp) + Sdiv(y,km)
        Sdiv(a,k) = [cosh(a/2) sin(k/2) - k (sinhc(a/2)/2) cos(k/2)] / (a^2 + k^2)

A leaf passes if `sup R^2 <= d` (then `Qre` is irrelevant), else if
`y_hi^2 * sup(R^2 - d) <= inf Qre^2`.

**The one new leaf is `sinhc x = sinh x / x`.** Needed only on `|x| <= 1/4`
(since `y <= 1/2`), where the series `sum x^(2n)/(2n+1)!` truncated at 14 terms
has tail below `2^-160`. `Leaves.lean` already carries the identical device for
`sin(u/2)/u`: its `sfnL` list and the `L6` branch. **Copy that pattern.** No
new machinery.

Argument reduction: `s/2` runs to `30`, and `Leaves.lean` L3 already has
reduction with a `2^-64` enclosure of pi.

---

## 4. The leaf table, and how to generate it

`o9_scoping.py` already computes the subdivision. Have it emit the table rather
than re-deriving one: bisect the longer side, accept a leaf when the test in §3
passes, at `INFL = 6/5` and `WIDEN = 1/200`.

Measured size at that operating point:

| part | leaves | max depth |
|---|---|---|
| nine windows | 110 | 7 |
| ten complement gaps | 279 | 16 |
| **total** | **389** | **16** |

Per window: `[35, 20, 11, 8, 8, 7, 7, 7, 7]`. The whole sweep runs in under a
second. For scale, `BandCert/Data.lean` records **3005 integers in 70 KB**; this
is about an eighth of that.

If `decide` turns out slow, buy margin on the inflation knob, not the widening
one: `INFL = 5/4` gives 77 window leaves, `13/10` gives 46, `27/20` gives 42.
All still inside the `1.3945x` wall, but re-run `total_deficit` in
`o9_scoping.py` for whatever you pick and keep the surplus positive. Raising
`WIDEN` past `0.00695` is not available at all (§1).

---

## 5. The other four obligations, while you are in there

O9 was the reason this chain sat at hardened grade, but three of the remaining
four are small and the ledger already calls them "hours, not research":

- **O3** `|u| <= 1 -> 39/50 <= Kpair u` (true value `0.78066657`)
- **O4** `|u| <= 6 -> 1/125 <= Kpair u` (true value `0.00834800`)
- **O10** the integer trade (Lemma 5.1): `m -> 4cm - qm(m-1)` is concave with
  real maximum `1/2 + 2c/q`, so the integer maximum is a neighbour of it
- **O11** the §7 rational arithmetic, `norm_num` on the table, once the caps
  carry `INFL`

O3/O4 are one-variable and `EForm3/Estimates.lean` already carries the pattern
(`fk`). `RETENTION-PROBLEM.md` §4 gives the closed form that makes them
elementary, plus the monotonicity (`Qre 0 .` decreasing on `[0, 2pi]`) that
turns each into a single endpoint evaluation.

**O11 changes**: §7's table was computed at `INFL = 1`. Rebuild it at `6/5`,
`total_deficit(Fraction(6,5))` in `o9_scoping.py` gives every row.

---

## 6. Done means

1. `cd lean && PATH="$HOME/.elan/bin:$PATH" lake build`, zero `sorry`s, and the
   same for the `zeta23ext` package build.
2. No `native_decide`, no `axiom`, no weakened statement.
3. `.venv/bin/python -m pytest -q hunts/frontier_math/test_o9_scoping.py` green.
4. `RETENTION-PROBLEM.md` §4 updated: O9 marked built, with `INFL` and `WIDEN`
   recorded in the table so the caps in the file match the caps in the Lean.
5. `PROOF-LEDGER.md` row updated, and state plainly that the `k = 1` chain
   moved to kernel grade **and that `k >= 2` did not**. Ledger defect #19 was
   exactly this confusion; do not repeat it.
6. A row in `ACTIVE-CLAIMS.md` while the work is running, per that file's
   protocol.

## 7. If it is submitted to a prover

Split it. The table and checker are generated artifacts and belong to a coding
session; a prover is the wrong instrument for 264 rows of data. What is
lemma-shaped, and worth a submission in the `lean/ARISTOTLE-RUNS.md` format:

- the `sinhc` leaf and its soundness bound on `|x| <= 1/4`
- `Qim y s = y * R y s`, the removable-branch identity
- the bridge lemma: checker returns `true` implies O9' holds on that box

The standing rule from that ledger applies unchanged: whatever comes back is
input, and it counts only after the static refusal scan and a zero-`sorry`
`lake build` on this repository's pin. A returned artifact's own claims about
its status are not the gate.
