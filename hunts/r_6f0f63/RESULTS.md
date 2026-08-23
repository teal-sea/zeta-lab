# R-6F0F63 — the ceiling of the Delsarte LP for kissing numbers

Everything below is **float grade** (rung 1, "measured"). No interval arithmetic
is used anywhere in `probe.py`, so no statement here climbs past *measured*
except where it reproduces a value that is a theorem elsewhere. Nothing here is
evidence for or against RH (`docs/08`).

Reproduce with `.venv/bin/python hunts/r_6f0f63/probe.py` (7 s, numpy + scipy
HiGHS only). Raw output: `results.json`.

Labels: **VERIFIED** = checked here against an independent oracle;
**MEASURED** = computed here, no external check; **INFERRED** = read off the
measurements, not directly computed.

---

## 0. The planted-fault ladder, which fires first

A verifier that cannot fail is not a verifier. Five items, all as expected
(`results.json → planted_faults`):

| # | planted | expected | observed | VERDICT |
|---|---|---|---|---|
| 1 | none (control): n=8 certificate rebuilt from contacts | P2, P3 hold; value 240 | sup = -1.1e-16, min f_k = 0.075, value = 240.0000000000086 | VERIFIED |
| 2 | none (control): n=24 certificate rebuilt from contacts | P2, P3 hold; value 196560 | sup = -4.0e-17, min f_k = 2.41e-4, value = 196560.0000032882 | VERIFIED |
| 3 | f_0 scaled by 1.01 (breaks P3) | sup ≈ 0.01·f_0 > 0 | sup = 9.375e-5 = 0.01·f_0 exactly | VERIFIED |
| 4 | f_4 negated (breaks P2 only) | P2 check fires, P3 scan stays a scan | min f_k < 0; sup = 0.089 | VERIFIED |
| 5 | node set starved to 14 points at degree 12 | LP reports below 240 and P3 fails | grid value 235.86, sup = 0.052 | VERIFIED |

Fault 4 exists because the interval scan is not the whole verifier: a
certificate can be inadmissible with `f(t) ≤ 0` everywhere, and only the
coefficient sign test sees it.

## 1. Reproduction, field for field

The two exactly tight cases were rebuilt **from their contact structure**, not
from printed coefficients: the optimal polynomial vanishes to order 2 at each
inner product realised by the configuration and to order 1 at the two endpoints
of `[-1, 1/2]`.

- E8 contacts `{-1, -1/2, 0, 1/2}` →
  `f(t) = (t+1)(t+1/2)² t² (t-1/2)`, degree 6.
  Gegenbauer coefficients, normalised to `f_0 = 1`:
  **`[1, 8, 25, 52, 66.5, 60, 27.5]`**, all non-negative, sum **240** exactly.
  VERIFIED (sum matches τ₈ = 240 to 4e-14 relative).
- Leech contacts `{-1, -1/2, -1/4, 0, 1/4, 1/2}` →
  `f(t) = (t+1)(t+1/2)²(t+1/4)² t² (t-1/4)²(t-1/2)`, degree 10, all
  coefficients non-negative, sum **196560** exactly. VERIFIED (1.7e-11
  relative).

That both come out with non-negative Gegenbauer coefficients *without being
asked to* is the reproduction: the structure, not the arithmetic, is what is
being checked.

## 2. The soundness read: the acceptance step is not sound as usually run

This is the load-bearing finding.

The standard way to compute this bound replaces the semi-infinite condition
(P3) `f ≤ 0 on [-1, 1/2]` with `f ≤ 0` on a finite node set. That is a
**relaxation**: it enlarges the feasible set, so the LP optimum on a node set
can sit *below* the true LP value, and a number below the true LP value is not
a bound at all.

Measured, dimension 24, degree 10 (`node_sweep_n24_d10`). `τ₂₄ = 196560`:

| nodes m | LP optimum on the grid | sup f on [-1,1/2] | repaired value | below τ₂₄? |
|---|---|---|---|---|
| 20 | 170028.40 | 1.6e+0 | — (repair fails, f_0 < sup) | yes |
| 40 | 184954.45 | 2.7e-1 | 252531.4 | yes |
| 100 | 194640.18 | 6.1e-2 | 207288.0 | yes |
| 300 | 196456.02 | 5.7e-3 | 197578.7 | yes |
| 600 | 196505.76 | 1.5e-3 | 196804.5 | yes |
| 1200 | 196553.78 | 3.8e-4 | 196628.5 | yes |
| 2400 | 196558.00 | 9.4e-5 | 196576.5 | yes |
| 5000 | 196559.26 | 2.2e-5 | 196563.5 | yes |
| 10000 | 196559.91 | 5.4e-6 | 196561.0 | yes |
| 20000 | 196559.97 | 1.3e-6 | 196560.2 | yes |

**MEASURED: at every node count tested, up to 20000 nodes in dimension 24 and
40000 in dimension 8, the node-discretised LP optimum is strictly below the true
kissing number.** At m = 600, a node count nobody would call coarse, the LP
reports 196505.76 for a quantity that is exactly 196560. Published as a bound
that number is false by 54, and it is false in the direction that looks like an
improvement. The same happens in dimension 8: m = 600 reports 239.9930 for a
quantity that is exactly 240.

**INFERRED: the discretisation error is one-sided and decays like m⁻².** The sup
of f over the interval falls by a factor of ≈ 4 for every doubling of m
(1.5e-3 → 3.8e-4 → 9.4e-5 → 2.2e-5 at m = 600, 1200, 2400, 5000). One-sided,
because the LP always exploits the gaps between nodes.

**The constant that encodes the target rather than the mathematics is the node
set.** Move the target and acceptance moves with it: the interval `[-1, 1/2]`
comes from the 60° angle, and the node placement on it is a free choice made by
whoever ran the optimisation. Nothing in the LP output records it.

**The repair.** A failed verification is not fatal, it is a worse number. If
`M = sup f > 0`, then `f - M` satisfies (P3) exactly, leaves every `f_k` for
k ≥ 1 untouched, and gives the valid value `(f(1) - M)/(f_0 - M)` whenever
`f_0 > M`. Every "repaired value" above is that number, and it converges to
196560 **from above** as m grows, which is what a sound acceptance step must do.
The true LP value is therefore bracketed: grid optimum ≤ truth ≤ repaired value.

## 3. The ceiling of the parameterisation

Held fixed: the method (Delsarte LP, Gegenbauer basis, `f_0 = 1`). Swept: the
degree d, 1…30, at m = 600 Chebyshev-clustered nodes. Reported: the smallest
degree within 1e-6 relative of the best value the sweep reached, and the
bracket at that degree.

| n | ceiling degree | LP optimum (lower) | repaired (upper) | sup at that degree |
|---|---|---|---|---|
| 3 | 27 | 13.1582 | 13.1582 | 9.3e-07 |
| 4 | 9 | 25.5584 | 25.5588 | 1.7e-05 |
| 5 | 10 | 46.3374 | 46.3383 | 2.1e-05 |
| 6 | 10 | 82.6305 | 82.6326 | 2.5e-05 |
| 7 | 10 | 140.1612 | 140.1636 | 1.7e-05 |
| 8 | 6 | 239.9930 | 240.0040 | 4.6e-05 |
| 9 | 11 | 380.0958 | 380.1072 | 3.0e-05 |
| 10 | 11 | 595.8260 | 595.8770 | 8.6e-05 |
| 11 | 11 | 915.3846 | 915.4822 | 1.1e-04 |
| 12 | 11 | 1416.0512 | 1416.2200 | 1.2e-04 |
| 13 | 12 | 2233.5500 | 2233.7665 | 9.7e-05 |
| 14 | 12 | 3492.1028 | 3492.3648 | 7.5e-05 |
| 15 | 12 | 5430.8261 | 5431.5382 | 1.3e-04 |
| 16 | 13 | 8313.5976 | 8315.2068 | 1.9e-04 |
| 17 | 13 | 12218.1464 | 12225.0230 | 5.6e-04 |
| 18 | 13 | 17876.3693 | 17885.7964 | 5.3e-04 |
| 19 | 13 | 25899.3418 | 25916.6059 | 6.7e-04 |
| 20 | 13 | 37970.8824 | 38001.8998 | 8.2e-04 |
| 21 | 13 | 56843.6858 | 56877.8357 | 6.0e-04 |
| 22 | 14 | 86532.5352 | 86561.9092 | 3.4e-04 |
| 23 | 14 | 128091.2138 | 128138.8828 | 3.7e-04 |
| 24 | 10 | 196505.7627 | 196804.5402 | 1.5e-03 |

All MEASURED. Dimensions 8 and 24 are additionally VERIFIED: the bracket
contains 240 and 196560, the values the LP attains exactly, and the ceiling
degrees the sweep finds, **6 and 10**, are exactly the degrees of the two
certificates rebuilt in §1 — the sweep discovers the published parameterisation
rather than being handed it.

**The headline of §3: degree is not the binding parameter.** For every dimension
from 3 to 24 the LP value stops moving by degree 14 at the latest, and adding
degree up to 30 buys nothing measurable. The parameterisation's ceiling in d is
reached early and cheaply. What binds is the *node count*, §2 — and the node
count is the free parameter the literature does not report, because it is an
implementation detail of an optimisation whose output is a single number.

So the answer to "what could this parameterisation achieve that the published
run did not" is, for this method, **nothing in d**. That is a negative ceiling
result and it is the useful kind: it says the headroom in the Delsarte LP is not
in the polynomial degree, so anyone looking for headroom must change the method
(more constraints, i.e. the SDP/Bachoc-Vallentin side), not tune this one.

## 4. What this procedure cannot decide here

Stated plainly, per item 4 of issue #110:

1. **The SDP half was not touched.** Cohn-Elkies sphere packing in R^n and the
   three-point Bachoc-Vallentin SDP for kissing numbers are the other half of
   the family the issue names, and neither was attempted at this budget. Nothing
   here bounds their ceiling.
2. **No claim of novelty, and no new bound.** The values in §3 are the
   literature's; the point of computing them was the bracket and the ceiling
   degree, not the number.
3. **Float grade throughout.** The sup in §2 comes from Chebyshev interpolation
   and companion-matrix roots in double precision, not from ball arithmetic. A
   rung-2 version of this hunt would recompute the sup with `zeta/rigor.py`'s
   enclosures and rationalise the coefficients; that would turn the repaired
   value into a genuinely enclosure-carrying bound, and it was not done.
4. **The published node counts are unknown to this run.** §2 shows that a
   discretised LP under-reports; it does **not** show that any published table
   under-reports, because this run did not read what node sets those runs used
   or whether they verified (P3) globally afterwards. The soundness finding is
   about the procedure as usually implemented, not an accusation against a
   specific table.
5. **Dimension 3 at degree 27** is the one row where the sweep's saturation
   degree is high, and this run did not establish whether that is real structure
   or the 1e-6 saturation tolerance chasing float noise.

---

## Loose threads

- **The m⁻² law, and the node placement that would beat it.** The one-sided
  discretisation error decays like m⁻² with Chebyshev-clustered nodes. Placing
  nodes adaptively at the near-active constraints (the contact values) should do
  far better, and the contact values are known a priori for the lattice cases.
  *Why it matters:* the whole soundness problem in §2 is the cost of m; a node
  rule that reaches sup < 1e-9 at m = 100 makes the repair penalty negligible
  and the bracket tight. *First step:* re-run `node_sweep(24, 10, ...)` with
  nodes concentrated near `{-1/2, -1/4, 0, 1/4}` and compare the sup at equal m.

- **The repair is a general instrument and this hunt built it by hand.** Any
  semi-infinite LP solved on nodes admits the same `f → f - sup f` repair, which
  converts an invalid optimisation output into a valid weaker bound with the sup
  as the explicit price. *Why it matters:* it turns "the grid was too coarse"
  from a fatal objection into a quantity. *First step:* see `core_candidates` in
  `HANDBACK.json`.

- **The n=3 degree-27 row.** Either real, or the saturation tolerance chasing
  noise. *Why it matters:* it is the only counterexample to "degree saturates by
  14", which is §3's headline. *First step:* re-run n=3 at m = 20000 with
  tolerance 1e-9 and see whether the saturation degree drops.

- **The three-point SDP ceiling is the natural next instance, not this one.**
  §3 says the two-point LP has no headroom in its degree, which is exactly the
  argument for measuring the ceiling of the method that does. *Why it matters:*
  it is where the issue's premise ("headroom hides in hand-chosen parameters")
  would actually be tested. *First step:* reproduce the Bachoc-Vallentin
  dimension-4 bound (24) and sweep its two degree parameters.
