# R-8539DC: the third autocorrelation constant, and the functional it belongs to

Run `9698c990-e812-4890-94d8-f30a65b820af`, 2026-08-23. Issue
[teal-sea/zeta-lab#123](https://github.com/teal-sea/zeta-lab/issues/123).
Reproduce with `python3 hunts/r_8539dc/probe.py` (standard library only).

**Verdict in one line: the reporter was right about the artifacts he read, the
authors fixed it in December 2025, and the improvement survives, but the two
problems are still labelled in opposite senses by the paper and the colab, and
the public problem page has not been updated.**

## 1. The two functionals, and why the published `abs()` is a no-op

Write `f` for a step function on `[-1/4, 1/4]` with `n` equal steps of width
`h = 1/(2n)` and heights `a_0 … a_{n-1}`. Then `f*f` is supported on
`[-1/2, 1/2]`, is piecewise linear with knots at multiples of `h`, and takes
the value `h·b_k` at the k-th knot, where `b = a ⋆ a`. A piecewise-linear
function attains its extrema at knots, so with `∫f = h·Σa`:

| | functional | discrete form |
| --- | --- | --- |
| **A** | `max_t (f*f)(t) / (∫f)²` | `2n · max_k b_k / (Σa)²` |
| **B** | `max_t \|f*f(t)\| / (∫f)²` | `2n · max_k \|b_k\| / (Σa)²` |

The published verification cell computes `abs(2n·max(conv)/sum²)`. That outer
`abs` is a no-op, and not by accident: `∫_{-1/2}^{1/2} f*f = (∫f)² > 0` forces
`max_t f*f(t) > 0` for every admissible `f`. So the code computes **A**,
cleanly and unambiguously, while the inequality printed above it defined **B**.
Those are two different problems, exactly as Tao said.

Since `A ≤ B` always, a bound under B is also a bound under A, never the
reverse. That asymmetry is what makes the mix-up load-bearing rather than
cosmetic.

## 2. Both functionals on both published sequences, exact

Heights are published as ten-place decimals, so they are exact rationals with
denominator `10^10`; the whole computation below is integer arithmetic, no
float anywhere in the chain. Thirty digits shown, truncated.

| construction | published as | **A** = `max f*f/(∫f)²` | **B** = `max\|f*f\|/(∫f)²` |
| --- | --- | --- | --- |
| `height_sequence_3`, n=400 | `C_3 ≤ 1.4557` | **1.455642795374540494110788362985** | 4.334046524387984273610361795864 |
| `height_sequence_4`, n=150 | `C_3' ≤ 1.4688` | **1.468762069741021809514483638412** | **1.468762069741021809514483638412** |

Read this table as follows.

- The n=400 construction reproduces `1.4557` **only** under A. Under B it gives
  `4.3340…`, which is not an improvement on anything, it is three times the
  trivial `π/2` bound. The convolution's extreme knot is negative
  (`min_k b_k = −4.3340…` at knot 215, against `max_k b_k = +1.4556…` at knot
  176): the construction buys its A-score by pushing the autoconvolution deeply
  negative somewhere else, which is precisely the freedom that B forbids. This
  confirms the reporter's observation on the artifacts as published in November
  2025.
- The n=150 construction gives the same number under both functionals, its
  `max|b|` *is* its `max b`. So it is a legitimate bound for both problems, and
  it is the one that has to be compared with Matolcsi–Vinuesa's `1.4993`. It
  also reproduces `1.4688` exactly, which is the check that keeps this hunt's
  discretisation honest: had the knot argument or the `2n` factor been wrong,
  this number would not have landed.

## 3. Which convention each prior bound belongs to

Answered by the corrected paper itself, not inferred here:

| prior bound | functional | source | note |
| --- | --- | --- | --- |
| `1.4993` | **B** (`max\|f*f\|`) | Matolcsi–Vinuesa 2010, JMAA 372(2) 439–447 | improved by AlphaEvolve to `1.4688` |
| `1.45810` | **A** (`max f*f`) | Vinuesa, generalized (thesis 2009, p. 75, per the colab) | improved by AlphaEvolve to `1.4557` |
| `1.5098` | **A** restricted to `f ≥ 0` | Matolcsi–Vinuesa 2010 | that is the separate problem `C_1` |

arXiv v1 cited `1.45810` to `matolcsi-vinuesa`; the correction moved that
citation to `vinuesageneralized`. So the misattribution the problem page
confesses to ("some results for one problem incorrectly attributed to another")
is visible in the v1→v2 diff as a changed `\cite` key, not just as a changed
formula.

## 4. Was it corrected? Yes, twice, in December 2025

| artifact | state | date |
| --- | --- | --- |
| arXiv:2511.02864 **v1** | one problem, `max\|f*f\| ≥ C(∫f)²`, prior `1.45810` cited to Matolcsi–Vinuesa, AlphaEvolve `1.4557` | 2025-11-03 |
| arXiv:2511.02864 **v2** | **corrected**: problem split into (a) `max\|f*f\| ≥ C_3(∫f)²` and (b) `\|max f*f\| ≥ C_3'(∫f)²`; priors `1.4993` and `1.45810`; AlphaEvolve `1.4688` and `1.4557` | 2025-12-15 |
| arXiv:2511.02864 **v3** | same third-autocorrelation text as v2 (v3 changes other sections) | 2025-12-22 |
| colab `mathematical_results.ipynb` | **corrected** in commit `39d0c63`, "Fixed typo in third autocorrelation inequality. Now the colab contains both versions of the problem, with the corresponding AlphaEvolve constructions" | 2025-12-19 |
| `problems/4.html` (public problem page) | **not corrected**: still one statement, `max\|f*f\|`, no bounds, no sibling page; comment still says the update is coming "soon" | repo last pushed 2026-07-11 |
| issue #1 | still open | as of 2026-08-23 |

The brief's premise that "no corrected table has appeared" is therefore wrong,
and the reason it looked true is worth naming: the correction landed in the
*paper* and in a *different repository's* notebook, while the issue that
reported it and the problem page that hosts it were both left as they were. A
reader who follows the report to its own thread still sees an unfixed problem.

`height_sequence_3` was **not** changed by the correction, the fix moved the
absolute-value bar in the statement to match the code, kept the number, and
added a second construction for the other problem. That is the honest repair,
not a quiet restatement: the n=400 object always was a witness for A.

## 5. Verdict

1. **Which number is stated against which functional.** `1.4557` and its
   predecessor `1.4581` are bounds on **A** = `max f*f / (∫f)²`, the
   sign-unrestricted version of the first autocorrelation problem. `1.4993`
   and `1.4688` are bounds on **B** = `max|f*f| / (∫f)²`, the
   Matolcsi–Vinuesa problem. As published in November 2025, `1.4557` sat under
   a statement that defined B; that is the defect the reporter found, and it
   was real.
2. **Does the claimed improvement survive the definition the paper writes
   down?** Under the *corrected* statements, yes, and with no number moving:
   `1.4557 < 1.4581` under A, `1.4688 < 1.4993` under B, both verified here in
   exact arithmetic. Under the *original* v1 statement, no: the n=400 witness
   scores `4.3340…` on that functional. Nothing was withdrawn; a statement was
   repaired and a second experiment was reported.
3. **What remains broken.** The primed and unprimed labels are swapped between
   the two corrected artifacts. arXiv v2/v3 calls `max|f*f|` the constant
   `C_3` (1.4993 → 1.4688) and `|max f*f|` the constant `C_3'` (1.4581 →
   1.4557). The colab calls `|max f*f|` `C_3` (1.4581 → 1.4557) and `max|f*f|`
   `C_3'` (1.4993 → 1.4688). Anyone citing "AlphaEvolve's `C_3`" without
   saying which artifact they read has a fifty-fifty chance of naming the other
   problem. The public problem page, which is what the paper's per-problem URL
   points at, has neither correction.

This hunt makes no new bound and takes no position on what should be said to
whom upstream. Both quantities above are *measured* on the certainty ladder,
in the strong sense that every arithmetic step is exact rational arithmetic on
the published decimals; what is not exact is the published sequences
themselves, which are ten-place truncations of whatever the search actually
found. A truncated witness is still a witness, the bound is whatever the
written-down step function gives, and that is what was computed.

## Loose threads

- **The n=400 witness is a very lopsided object under B.** Its autoconvolution
  reaches `−4.334` while its positive peak is `+1.456`, a ratio of about 2.98.
  Whether an A-optimal construction *must* be lopsided under B, or whether this
  one merely is, would say something about how far apart the two constants can
  be. First step: sweep A-optimising step functions at small `n` (say n ≤ 24,
  where exhaustive local optimisation is cheap) and record `max|b| / max b` for
  each optimum. If that ratio grows with `n`, the two problems separate
  structurally rather than numerically.
- **`1.4581` is sourced to page 75 of a 2009 thesis, and this hunt did not open
  it.** The convention attribution in §3 is taken from the corrected paper's
  own citation change, which is a strong but secondary source. First step:
  fetch `https://www.icmat.es/Thesis/CVinuesa.pdf`, read p. 75, and confirm the
  construction there is scored under `max f*f` and not `max|f*f|`. This matters
  because it is the one link in the corrected chain that was repaired by moving
  a citation rather than by rerunning a computation.
- **The sibling problem has no public problem page.** `problems/4.html` says a
  sibling will be added; nine months on there is none, so the repository's
  problem list is missing an entry that the paper references. First step: check
  whether `problems/*.html` numbering has a free slot or whether adding one
  renumbers the set, which would tell you whether the omission is editorial
  inertia or a structural cost.
- **The lab has no instrument for "recompute a published constant from a
  published witness under a stated functional".** This hunt hand-rolled 60
  lines of exact rational convolution to do it. Reported as a Core candidate in
  `HANDBACK.json`, not built here.
