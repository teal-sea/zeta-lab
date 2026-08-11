# RESULTS — frontier math after the 10 August 2026 paper

**Status: CLEAN KILL. The unconditional candidates `0.6725124`, `0.672529`,
and `0.6725318` are withdrawn. Gate 0 failed: the zero-side summand uses
transpose, not conjugate transpose, so the asserted on/off cross-block sign is
false. The measure-level collapse and quantified walls below are unaffected.**

Everything reproduces from the repo root:

    .venv/bin/python hunts/frontier_math/configuration_lp.py
    .venv/bin/python hunts/frontier_math/cg_transplant.py
    .venv/bin/python -c "import sys; sys.path.insert(0,'hunts/frontier_math'); \
        import blockpos; blockpos.__name__; exec(open('hunts/frontier_math/blockpos.py').read())"

Sources: the paper (URL in `../wide_search/HANDOFF.md`; section/line cites
follow its pdftotext rendering), Cheer–Goldston PAMS 118 (1993) 365–372,
Chirre–Gonçalves–de Laat Adv. Math. 361 (2020) (arXiv:1810.08843),
Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh (arXiv:2306.04799).

## 0. Closure: the candidate is withdrawn

The exact failure, pinned dependencies, smallest Gaussian-integer obstruction,
formal obstruction, and reproduction commands are in
`CLEAN-KILL-REPORT.md`. The first false statement was
`tr(P1 Q') >= 0`. The old `blockpos.py` constructed `u u*`; upstream uses
`u u^T`. For the one-dimensional vectors `1`, `i`, and `-i`, the correct
interaction is `-2`. A five-on-line-point witness makes the proposed additive
inequality demand `9 >= 13`.

## 1. THREAD 1 answered: the measure-level LP collapses

`wide_search` left one open route to the interval (0.6725007, 0.68185): a
joint formulation keeping cross-window information. Formulated here
(`configuration_lp.py`): minimise the density of simple on-line points over
(multiplicity types p_m, off-line pair density q, off-diagonal pair measure
ρ ≥ 0) subject to the bandwidth-one data R̂₂(α) = δ(α)+|α| on [−1,1].

- **The type structure reduces out exactly**: eliminating (p_m, q) against
  the density constraint gives
  `p₁ = 2 − D + Σ_{m≥3}(m²−2m)p_m` (the m ≥ 3 and off-line types enter with
  nonnegative coefficients `m²−2m` and 0). So the
  LP value is the dual of the Montgomery–Taylor extremal problem, and
  integrality devices beyond (m−1)(m−2) buy nothing at the measure level.
- **Measured**: the (X, J, ε) ladder descends 0.6794 → 0.6776 → 0.6765
  (ε = 0.4/X at the truncation floor ~1/(π²X)), consistent with convergence
  to the paper's 0.6725007 from above and with nothing in between. Two
  independent corroborations: the paper scopes Theorem D's optimality to
  "the values of F on [−1,1] only" (§1.2), and Cheer–Goldston's closing
  remark records 1993 numerics that the pure-frequency problem attains the
  MT constant.
- **Consequence**: the ceiling gap (0.6725007, 0.68185) is *not* about the
  pair measure at all — it measures what configuration realizability
  (ordered real sequences) adds beyond measure positivity. CG's 1993
  improvement (§3 below) is the constructive half of that statement.

## 2. The λ > 1 sieve wall, quantified

The paper's §4 machinery is support-agnostic; only the prime-side second
moment caps λ at 1 (its §7.5(a)). The tempting unconditional route — bound
the off-diagonal prime sums by the Selberg-sieve upper bound
Σ_{n≤N} Λ(n)Λ(n+h) ≤ C·𝔖(h)·N with classical C — **fails structurally**:
for X = T^λ, λ > 1, the off-diagonal and expected-value terms are each of
scale x/T · N = T^{λ−1}·N and cancel to O(N) only under Hardy–Littlewood
with error; a sieve constant C multiplies the x-scale term, so the loss is
(C−1)·T^{λ−1}·N/log T, unbounded relative to N for any fixed C > 1. Only
C = 1 + o(1) — HL itself — closes it. This makes Remark 1.1's wall
("0.70 needs support ≈ 1.04") mechanism-explicit: no constant-factor upper
bound on prime pair correlations, however sharp, opens the band.

## 3. WITHDRAWN: the Cheer–Goldston transplant

**Withdrawn claim shape:** the paper's Theorem D constant for simple zeros on
the critical line was claimed to improve unconditionally,

    N₀ˢ(T,2T) ≥ (0.6725124 + o(1)) N(T,2T)    [paper: 0.6725007…]

by transplanting Cheer–Goldston's 1993 gap-rigidity floor into the paper's
Frobenius counting. The floor: consecutive gaps of on-line zeros cannot all
sit at zeros λ_k of the MT kernel, because abutting near-λ₁ gaps force
next-to-consecutive gaps near 2λ₁, and λ₂ = 2.03007 ≠ 2λ₁ = 2.11455.

**The failed step.** The old instrument replaced the upstream transpose
summand `u u^T` by the Hermitian summand `u u*`. That changed correct on/off
blocks `2 Re(B(γ,z)^2)`, which can be negative, into
`2|B(γ,z)|^2`. The following advertised chain therefore breaks at its middle
line:

    ‖Â‖²_F = tr P₁² + 2 tr(P₁Q′) + tr Q′²
    tr P₁²  = s₁ + cross₁₁            (exact: simple on-line, B(γ,γ)→1)
    tr(P₁Q′) ≥ 0                       (blockwise nonnegativity)
    tr Q′²  ≥ 4 tr Q′ − 4(s₂+p)        (per-eigenvalue (x−2)² ≥ 0; n₊(Q′) ≤
                                        s₂+p is the paper's Prop 4.1)

The middle line is false. Hence the upstream inequality does not gain
`+cross11`, and the computed ordered-gap floors below do not imply a zeta-zero
bound.

**Computed** (`cg_transplant.py`):

| quantity | value | control |
|---|---|---|
| CG floor at their edges, ν = 0.83625 | 0.00012638 | CG printed 0.00012636 |
| CG conditional constant | 0.6727535 | CG printed 0.6727534 |
| transplant floor c_u at ν_on = 0.6725007 | 5.8384e-6 | stable across 16× g-table refinement |
| edges attaining it | (0.92252, 1.03787, 1.35395, 1.99782) | |
| withdrawn arithmetic value | 0.6725124 | no zeta implication after Gate 0 failure |
| lesion: λ₂ → 2λ₁ | floor = 0.00000000 | the mechanism dies exactly where it must |

The floor is 22× smaller than CG's because the unconditional census is
thinner (ν_on = 0.6725 vs 0.83625: the adversary has fewer gaps to place,
mean gap 1.49 vs 1.20, so the length constraint pinches less — but
all-gaps-beyond-d is still infeasible: 1.99782 × 0.6725 = 1.336 > 1).

Taper, truncation, census, bootstrap, and exact-LP work cannot repair the
failed algebraic implication. They are closed as moot for this candidate.

## 4. The CGdL transplant reduces to one named obstruction

Chirre–Gonçalves–de Laat's RH-conditional 0.6792 uses two zero-side facts:
(i) F(α) ≥ 0 for all α, (ii) the g ≥ 0 diagonal-isolation drop. For (i),
**no RH is needed**: BGSTB 2023 (arXiv:2306.04799, Theorem 1) show the
weighted form factor is nonnegative unconditionally — the conjugate-closure
of the zero multiset makes it an integral of |Σ_ρ x^ρ/(1−(ρ−(½+it))²)|²;
the Cauchy weight's strip (poles at ±2i) covers every pair of strip zeros
(total imaginary displacement < 1 < 2). We re-derived this before finding
it; it is *known*, and recorded here so the next session does not re-derive
it either. What does **not** transfer is (ii): for the paper's machinery
the analogue would be running its inertia counting against a kernel with
ĝ ≤ 0 outside [−1,1] — which is not the Gram matrix of any window family
(autocorrelations are ≥ 0), so its §4 does not apply as written. That is
the single obstruction. The prize if it falls, measured by the LP with the
out-of-band constraint added (`configuration_lp.py`, BGSTB positivity as
data): the class value at (X=80, J=320) is 0.6863 and still descending
with X — consistent with landing near CGdL's 0.6792 for ζ unconditionally.

## 5. WITHDRAWN AS A ZETA INPUT: the gap-distribution LP

`gap_lp.py` replaces CG's five hand-tuned buckets with the full projection
of the configuration LP onto gap statistics: a fine-binned distribution of
consecutive distinct on-line gap lengths, chain levels 2 and 3 (pairs j
apart in the ordering are disjoint classes, so per-class floors add with no
double counting), a conservative total-internal-length constraint with
boundary slack, and the census bootstrap iterated to its fixed point (it
converges in two rounds).

**A control earned its keep here, twice.** The first implementation
assigned bins to partition cells by bin midpoint; a bin straddling a cell
edge was credited wholesale to one cell, so the chain count n_I could
exceed reality and the floor came out invalidly high — including a
conditional value of 0.6728294 that would have "beaten" Cheer–Goldston.
The bin-width ladder caught it (the floor *fell* under refinement; a real
quantity rises toward a tight relaxation). After snapping cell edges onto
the bin grid the ladder is monotone as it must be
(0.69 → 1.02 → 1.44 → 1.47 ×1e-5 for h = 0.02 … 0.0025), and the inflated
claim is withdrawn. Recorded because the defect is the instructive part:
a chain-count credit is a claim about *which cell a gap is in*, and any
discretisation that answers optimistically manufactures floor.

**Historical discovery numbers** (fixed snapped edges and monotone in the
reported refinement ladder; sampled kernel minima are not exact continuum
lower objects):

| census ν | floor (h = 0.005) | withdrawn arithmetic value |
|---|---|---|
| 0.6725007 (unconditional bootstrap start) | 1.4371e-5 | 0.6725294 |
| same, edges re-checked at h = 0.0025 | 1.5554e-5 | 0.6725318 |
| 0.83625 (CG's conditional census) | ~1.0–1.4e-4, edge-sensitive | does **not** beat CG's 0.6727534 at current search depth |

These values are ordered-real-configuration optimization outputs only. They
do not yield an unconditional zeta bound. The former unconditional candidate
**0.672529 is withdrawn**. The grid-locked edge optimisation had
completed for the unconditional census: at edges (1.035, 1.085, 1.900) the
floor is monotone under fixed-cell refinement — 1.4371e-5 (h = 0.005),
1.4710e-5 (0.0025), 1.4988e-5 (0.00125) — so the trend value is
the arithmetic trend was 0.6725307, but no bound survives. The matching
conditional search was interrupted mid-run (HANDOFF has the resume note). The
conditional lane's verdict is honest: the generalised LP has not so far
beaten the 1993 constant once the discretisation is done correctly — CG's
hand-tuned edges were good, and the inflation that briefly suggested
otherwise was an artifact. The floor's extreme sensitivity to the cell
edge nearest λ₂ (a shift of 0.005 moves the level-2 kernel minimum by a
factor ~1.4) is itself a finding: the binding structure is the distance
from 2·(cell edge) to λ₂, which is where a sharper argument or a better
kernel should focus.

## 6. Lanes deliberately left

- **Conditional CG improvement**: our coarse edge grid reaches 0.6727450,
  *below* CG's hand-tuned 0.6727534 — their 1993 optimisation stands; a
  joint kernel-and-buckets optimisation (not just edges) is the open lane
  for "the best result attainable from Montgomery's theorem", which CG pose
  explicitly and which remains open.
- **λ_k arithmetic structure**: the whole floor exists because
  {λ_k} is not an arithmetic progression; nobody has characterised the
  best kernel *for the floor* rather than for the main term.

## Controls ledger

| control | instrument | measured |
|---|---|---|
| calibration (CG 1993 reproduction) | `cg_transplant.py` | floor and constant to their printed digits |
| lesion (λ₂ → 2λ₁) | `cg_transplant.py` | floor exactly 0 |
| precision ladder | `cg_transplant.py` | c_u stable to 5 digits across 16× refinement |
| exact obstruction | `clean_kill.py` | `tr(P1 Q') = -2`; proposed inequality `9 >= 13` |
| corrected zero-side check | `blockpos.py` | negative on/off blocks now occur |
| GUE anchor | `configuration_lp.py` | τ = −sinc² satisfies the data rows at the truncation floor |
| LP ladder direction checks | `configuration_lp.py` | value ↑ as ε ↓, ↓ as X ↑, both as predicted |
