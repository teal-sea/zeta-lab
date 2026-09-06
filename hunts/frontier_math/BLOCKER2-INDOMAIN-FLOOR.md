# The in-domain floor for the finite-m margin, and two artifacts on the way to it

**2026-08-13/14.** Measurements only. Nothing here is kernel-checked, nothing
here is evidence about RH, and nothing here closes blocker 2.

Recorded because these numbers were produced in a session and existed nowhere
else. `PROOF-LEDGER.md` logs the general shape five times, a quantity carried
across contexts without being re-derived where it is used, and a measurement
that lives only in a transcript is the same failure with the transcript as the
context.

## 1. The domain, which is where the first artifact came from

The retention claim is about off-line zero pairs at depth `y = |β − ½|`, and
zeros lie in the critical strip, so **`y < ½` always**. It is a geometric
constraint, not a modelling convenience; `PREPRINT.md` states it and
`depth_uniform.py`'s eighteen cells tile `(0, ½]` exactly.

An evolutionary search run against `paper_joint` reported a configuration with
margin per pair `−0.786`, spacing `2.086` mean gaps, depth **`0.979`**, a
24-site occupancy, and read it as a counterexample. It reproduces here
(`−0.782`; the difference is step and `G`). It is not a counterexample: `y =
0.979` is outside the domain, and at `y > ½` the `cosh(y·w)` pair term runs away
and the instrument is being read outside its calibration.

The same spacing and occupancy, at every valid depth, closes:

| `y` | 0.05 | 0.1 | 0.2 | 0.3 | 0.4 | 0.49 | 0.499 |
|---|---|---|---|---|---|---|---|
| margin/pair | +0.016 | +0.021 | +0.038 | +0.057 | +0.083 | +0.099 | +0.100 |

The search's guard admitted `0.01 < y < 0.99`. Clamped to `0 < y < 0.5`, the
"massive region of catastrophic resonances" disappears, it is massive, and it
is entirely outside the strip.

## 2. The second artifact: refinement has artifacts of its own

Screening at the evaluator's own resolution (`step 0.005`, `G = 60`) produces
violations that are not there. `sparse-24` (every third of 24 sites), `s =
2.0000`, `y = 0.0237` reads `−0.004396` at that setting and closes under any
refinement:

| step | G | margin/pair |
|---|---|---|
| **0.005** | 60 | **−0.004396** |
| 0.0025 | 60 | +0.000298 |
| 0.001 | 120 | +0.000328 |
| 0.0005 | 200 | +0.000339 |

That much argues for a two-stage evaluator: screen coarse, re-score any positive
hit at finer resolution. **Two stages are not enough.** A second candidate,
`every-5`, `s = 4.0`, `y = 0.011`: went `+0.000075` coarse and `−0.002288` at
`step 0.0025 / G = 120`, i.e. it *appeared* only at the refinement stage, and
died on the full ladder:

| step | G | `every-5` (candidate) | `every-4` (control) |
|---|---|---|---|
| 0.005 | 60 | +0.000075 | +0.000075 |
| 0.0025 | 120 | **−0.002288** | +0.000069 |
| 0.00125 | 120 | +0.000069 | +0.000069 |
| 0.000625 | 400 | +0.000073 | +0.000073 |
| 0.0003125 | 400 | +0.000073 | +0.000073 |

The control is a structurally adjacent configuration that closes throughout,
which is what identifies the candidate's `−0.002288` as an isolated artifact of
one setting rather than a feature. **A ladder is required, not a refinement.**

## 3. The floor

The tightest converged in-domain margin found is

> **`+0.000073`** at `every-5` / `every-4`, `s = 4.0000` mean gaps, `y = 0.011`,
> stable from `step 0.000625` down.

Two things about it. It is roughly **4.6× tighter** than the `+0.00034` that an
evolutionary run and an independent hand scan agreed on earlier, and it sits at
a **different resonance**, `s ≈ 4`, not the `s ≈ 2` both had converged on, and
at a shallower depth. Whether the floor keeps falling with `s` is unmeasured and
is the obvious next probe: a pattern in `s` would be a candidate lemma, and a
floor that does not converge would be a different finding entirely.

## 4. What this is not

No in-domain violation survives refinement, and that is not evidence that none
exists. A failed adversarial search bounds the searcher. `docs/25`'s scoring
rule is the relevant one: *"nobody has attacked it yet" scores as a penalty, not
as survival.*

Blocker 2's multi-pair statement remains open, and `7df6ed8` (defect #19)
records that the `k = 1` closure is not it.
