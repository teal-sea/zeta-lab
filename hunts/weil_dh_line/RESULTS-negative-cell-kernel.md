# Kernel-checked negative direction for the DH band form

Date 2026-10-29. Work for `DESIGN-kernel-negative-cell.md`. No claim about the
continuum form is made or changed here; this is about one finite band matrix.

## Step 0: where the negative eigenvalue starts

Ball LDL^T inertia (Arb, 256 bits, all pivots decided) on the DH form, even and odd
sectors, at the cell's endpoints:

| c | N ≤ 56 | N = 64 | N = 80 | N = 96 |
|---|---|---|---|---|
| 3062/100 (30.62) | positive | positive | positive | positive |
| 3082/100 (30.82) | positive | **one negative pivot** (even) | one negative (even) | one negative (even) |

The odd sector is positive throughout. So the smallest matrix that shows the effect is
the even sector at N = 64, c = 1541/50 (30.82), 65 modes, with exactly one negative
pivot. Script: `sweep_small_N.py`; runtime under two seconds for the whole grid.

## The cell's own direction is delocalised

At (c, N) = (1541/50, 64) the bottom eigenvalue is about −4.8e-32 (mpmath at 120 dps;
the float64 value, −3.4e-15, is noise at this conditioning). The rational Rayleigh
quotient of the rounded eigenvector is −4.8e-32 against an entry perturbation bound of
5.5e-73, so the certificate passes, but it needs all 65 components: truncating to 48
components flips the quotient positive. The Lean check for this configuration is
therefore a 2145-term integer quadratic form; it is priced, not built.
Script: `cert_negative_cell.py`.

## What was kernel-checked

A 2×2 principal minor of the same family turns negative between c = 50 and c = 55.
At c = 55 (N = 64, even sector) the entries at modes (54, 55) are

    a = M 54 54,  b = M 54 55,  d = M 55 55,

exact rational midpoints of Arb enclosures with entry radius below 1e-72
(`cert_2x2_c55.json`). With `w = (d, -b)` the quadratic form is
`d * (a*d - b*b) = -23.436...`, and `d > 0`, so the block is indefinite.

`Cert2x2.lean` proves `d * (a * d - b * b) < 0` over ℚ by `norm_num`, in 13 seconds,
`#print axioms` reports the standard three. Grade: **kernel-checked** for the rational
block; the passage from the true Arb matrix to these three rationals is the enclosure,
which is cited and not formalized. The statement is about c = 55, not about the cell at
30.82.

## Honest scope

- Kernel-checked: the 2×2 rational block at c = 55 has a negative direction.
- Hardened, not kernel-checked: the cell at c = 30.82 with one negative pivot; its
  direction exists numerically with a wide margin but needs the full 65-mode
  certificate.
- Not touched: the nesting argument, the continuum form, N = 256.

## The cell itself, now kernel-checked

The 65-mode certificate at (1541/50, 64) is built and checked. Shape of the proof:

- entries: exact rational midpoints scaled by `L = 2^269` to integers;
- vector: bottom eigenvector at 120 dps, rounded at 40 decimal places;
- proof: `Cert65Rows.lean`, 65 row theorems `row_i : sum_j B_ij u_j = (literal)`, each
  by `norm_num` on 65 terms, plus one final theorem summing the row values;
- result: the signed sum is `-4.59e129`, compile time **12 m 22 s**, exit 0.

Two cheaper-looking encodings failed first and are recorded: the single 2145-term
`norm_num` hit the heartbeat limit at 200k and then timed out at 15 minutes with a
raised limit; a 65-row statement whose goal repeated all 4225 terms blew the heartbeat
budget during elaboration. Splitting into 65 small theorems is what made the kernel
check practical.

A rounded variant (entries to multiples of 2^-112) also passes numerically: rounding
perturbation 6.3e-33 against a margin of 4.8e-32, a factor 7.7. Its compile was not
completed; it is the fallback if the exact file ever needs to be smaller.

## Next

None required for this claim. Axiom print is running; scale-up to N = 256 or to the
other window endpoints would repeat the same pipeline.