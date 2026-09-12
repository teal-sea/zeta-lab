# NOTES: what the probe measured

Run of 2026-08-07, `probe.py`, backends `['mpmath.iv', 'python-flint']`,
raw numbers in `results.json`. Probe language throughout: *measured*,
*observed*, *decided* (= an enclosure returned `lo > 0` or `hi < 0`).

## 1. The near-miss is real, decided on both backends

At the exact rationals 7005.02, 7005.0819, 7005.15 the sign of Z was
decided at 64 bits as **−, +, −** by both backends independently. With
continuity of Z that brackets ≥ 2 critical-line zeros inside an interval
of width 0.13, the pair, and the bump's clearance is decided positive:
both backends agree

    Z(7005.0819) = 0.003967335016595021…   (midpoints agree to all 16 digits)

The dense window scan (81 samples on [7004.9, 7005.3], step 0.005) found
exactly **2 sign changes, zero undecided samples, on both backends**. The
window contains no other zeros (γ₆₇₀₈ = 7004.04, γ₆₇₁₁ = 7006.74), so the
lower bound 2 meets the strip count from the float regime.

Backend cost asymmetry, measured: the same 81-point scan took **0.028 s
(python-flint)** vs **28.7 s (mpmath.iv)**, the ~1000× gap `AGENTS.md`
warns about, observed directly.

## 2. Lesion: the default grid policy is blind to the pair 1 time in 5

The default scan step at this height, mean_spacing/20 ≈ **0.0448, is wider
than the whole Lehmer gap (0.0377)**. Sweeping the window phase through
five offsets spanning one step: **4 phases reported 2 changes, 1 phase
(shift 0.027) reported 0**, every sample decided, and the count is an
honest lower bound both times, but at that phase the instrument simply
cannot see the closest pair below 10⁴. A sign-change scan misses, never
invents; here is the miss, measured. Anyone running a default-step scan
across t ≈ 7005 should know the pair is invisible at some phases.

## 3. Precision response: the standing rule, passed

Enclosure width at the bump vs prec_bits (python-flint / mpmath.iv):

| bits | flint width | iv width |
|-----:|------------:|---------:|
| 32   | 1.7e-2 (straddles 0) | 6.3e-3 (decides!) |
| 64   | 4.1e-13     | 1.5e-12  |
| 128  | 2.2e-32     | 7.9e-32  |
| 256  | 6.7e-71     | 2.3e-70  |

Width shrinks like ~2^−prec while the midpoint stays pinned, a real
quantity responding to precision, per the ROADMAP standing rule. Two
details worth keeping:

- At 32 bits **flint straddles zero but mpmath.iv decides**, the iv
  enclosure happens to be tighter at very low precision. The backends
  disagree about *decidability*, never about the value; that is the
  designed failure mode (return 0, escalate), observed at its boundary.
- Sliding the probe point toward γ₆₇₀₉: at distance 10⁻³ … 10⁻⁹ both
  backends decide at 64 bits. At 10⁻¹², where |Z| ≈ 5×10⁻¹³, flint still
  decides at 64 bits (width 4.0×10⁻¹³, a margin of ~20%), iv needs 128.
  The decision cost grows exactly when it must and not before.

## 4. Rival (gate #1): the counterexample kills the magnitude heuristic

The prediction going in was that Davenport–Heilbronn's off-line zero at
0.8085 + 85.6993i would show a "failed Lehmer bump": Z_dh sneaking close
to zero and not quite crossing. **Measured: the closest approach on
[85.2, 86.2] is −0.3566 at t = 85.707.** Not close at all, two strip
zeros hide behind an extremum that misses zero by two orders of magnitude
more than ζ's bump *clears* it (+0.004).

So the hunt's most useful observation is negative, and it is the rival
that provides it: **"|Z| gets suspiciously small" is not the signature of
zeros near or off the line, crossing is binary and magnitude is a
distraction.** A claim of the form "near-misses of Z flag danger" would
pass ζ at 7005 and fail to flag DH at 85.7, which is precisely the kind
of claim gate #1 exists to kill. The instruments that survive this
contrast are the ones the repo already trusts: sign counting on the line
against strip counting (argument principle), never |Z| thresholds.

## Standing-checklist accounting

- **Rival**: run, and it produced the headline (§4).
- **Decoy/surrogate**: not applicable, no arithmetic-vs-null claim is
  being made; the probe measures instrument behaviour at named points.
- **Lesion**: run (§2); the planted challenge is the pair itself and the
  default grid fails it at 1 of 5 phases.
- **Precision response**: run (§3), passed.

## Disposition

Instrument (`probe.py`, `scan_signs`) retained; no claim promoted; no
ledger entry (nothing here is a conjecture, it is a portrait of the
closest call, drawn with error bars). Nothing in this note is evidence
for RH (Littlewood, `docs/08`). Candidate for the spine, if anyone wants
it: the default-step blind spot (§2) is an honest sharp edge of the
packaged grid scanner worth a line in its docstring, that change belongs
to `zeta/`, not to this hunt.
