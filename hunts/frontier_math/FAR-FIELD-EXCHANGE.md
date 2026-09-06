# The far-field exchange: what the δ = 2π route actually is

Record of a measurement-and-proof exchange with the theorem-proving
service during submission 9 (`eform3`), 2026-08-13. It is written down
because the mathematical content is not in any artifact yet, the job
is still running, and because the shape of the argument changed twice
during it, in both directions.

## 1. The brief's prescribed route is false, and this is why

The submission asked for `|Qim(y,s)| ≤ C₂·y/s²` by two integrations by
parts, and built a 1/s⁴ counting argument on it. **No constant C₂ makes
that true.**

`Qim` is the imaginary part of the Fourier–Laplace transform of a window
with a jump at `±1/2`; the jump forces decay of order `y/|s|` and no
better. Squaring gives damage of order `y²/s²`, not `y²/s⁴`, so the
counting the brief proposed is unreachable at any constants.

Established three independent ways:
- **numerically here**: `|Qim|·s` stays in 0.13–0.30 across s = 20…1600
  while `|Qim|·s²` grows 5 → 220;
- **by the boundary term**: the integrand's value at the support edge is
  `cos(√2/2)·sinh(y/2) = 0.153 ≠ 0`;
- **by the prover, twice independently**: jump-formula asymptotics, and
  directly from the closed forms for `Qre` and `Qim`.

The asymptote is `(1 + cos√2)/2 · sinh(y/2)/y = 0.2920` at y = 1/2. The
coordinator's error was importing a 1/s² rate from a companion result
about `c₂ = g⋆g`, which is continuous because an autocorrelation
vanishes at the edge of its support. Ledgered as defect #15.

## 2. What the route to δ = 2π actually is

Two ingredients, and the second is the one that matters:

1. **Sharp far-field constants.** An exact closed form for `Qim` giving
   a decreasing majorant with honest constants.
2. **Near-field cancellation.** Inside `|s| ≤ R₀`, `Qre(y,s)² > Qim(y,s)²`,
   so those offsets contribute **no damage at all**, rather than
   contributing the uniform cap, which is what the previous run did.

**That distinction is the whole difference between δ = 26 and δ = 2π.**
It is not a constant-chasing improvement on the brief's route; the
brief's route does not exist.

## 3. The measured facts the argument is designed against

At y = 1/2 unless stated, from closed forms validated against quadrature
to 12 digits:

| quantity | value |
|---|---|
| max true damage `max(0, Qim² − Qre²)` | 0.00439642 at s = 6.51700 (= 0.0175857 y²) |
| true no-damage radius (`Qre² ≥ Qim²` for all `\|s\| ≤ R`) | **R = 6.0653187731** (= 0.9653·2π) |
| damage support | nonzero on 15.3% of the range: windows of width ≈ 0.962 just above each 2πk |
| first six peaks | 4.396e−3, 9.751e−4, 4.233e−4, 2.361e−4, 1.505e−4, 1.043e−4 |
| **sum of ALL peaks (3183 windows to s = 20000)** | **6.8591e−03**; the tail beyond six is 8.4% of the total |
| both sides vs budget `Shq/2 = 3.3754e−02` | **40.6% of budget → margin 2.46×** |
| sharp envelope `sup_{s≥s₀} \|Qim\|·s/y` | 0.9463 / 0.9336 / 0.9077 / 0.8040 at s₀ = 5.7 / 6.0 / 2π / 12, essentially y-independent |

**The 2.46× is the true adversarial value, not an upper estimate.**
Damage windows recur at spacing 2π and are narrower than the spacing, so
a 2π-separated configuration can place a point in *every* window. There
is no configurational saving available; the worst case is exactly the
sum of peaks, and it is attained.

This corrected the prover's own working figure of 2.7×, which had summed
only the six visible windows and treated the k⁻² tail as negligible.

## 4. The prover's lemmas, checked here

| claim | verdict |
|---|---|
| `Qre(y,s) ≥ Qre(0,s) − 0.0107` for 0 ≤ y ≤ 1/2 | **holds**, true max drop 0.00649642 at (y,s) = (0.500, 7.8380), 60.7% of the allowance, and the worst point lies *beyond* R₀ |
| its derivation `(y²/2)cosh(y/2)·(1/12)` | reproduces exactly: 0.01074389; with the sharp `L2 = 0.0712006` it would be 0.00917965 (14% held in reserve) |
| `Qre(0,·)` monotone decreasing on [0, 2π] | **holds**, max increase −3.56e−12; endpoints `Qre(0,0) = 0.918725 = A`, `Qre(0,2π) = 0.049027` |
| far-field majorant `Φ(5.7) = 0.03753` | `\|Qim\| ≤ 0.193727 y` against true 0.155601 y → **1.2450× pointwise, 1.5501× squared**, as the prover stated |

A coordinator caution that the monotonicity had a direction error was
**withdrawn**: the lemma is stated in additive slack form, which absorbs
the y-dependence explicitly rather than assuming a monotonicity that
does not hold (`Qre` is *not* increasing in y: 0.135442 < 0.139436 at
s = 5.7).

## 5. Normalisation note, so it is not re-litigated

Two `Shq` in play, and they are the same statement:

    Shq_prover(y) = ĝ(2y)² − A²,   Shq_here(y) = ∫ g·sinh²(yu) du,
    Shq_prover = 2(ĝ(2y) + A) · Shq_here        [factor 3.746969 at y = 1/2]

checked to 1.7e−17. A coordinator claim that a floor of `0.23 y²` was
false was **withdrawn**, it is false in one normalisation and true in
the other. `Shq_here/y² → L2 = 0.0712006`; `Shq_prover/y² → 4A·L2 =
0.261655`. Since the final inequality consumes the quotient
`(damage sum)/(Shq/2)`, the normalisation cancels.

Corrected constants now in use: `A = 0.9187253699`, `ĝ(1) = 0.9547589817`,
`Shq_prover(1/2) = 0.06750841 = 0.270034 y²`.

## 6. Where the recoverable slack is

Margin ≈ 1.19 at the prover's current constants after all three losses
multiply. The Φ-tail is near-sharp beyond s ≈ 12, so essentially all
recoverable slack sits on the **first window**. Cheapest order if the
margin thins in Lean:

1. two-piece envelope (flat cap on the first window, then `C·y/s` with
   C ≈ 0.80 beyond s = 12);
2. swap `1/12 → L2 = 0.0712006` in the slack lemma (14%, one constant);
3. `R₀: 5.7 → 5.87` (available at the current cap; the truth is 6.0653).

None disturbs the structure of the argument.
