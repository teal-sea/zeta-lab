# blockpos-0.672529: WITHDRAWN / FALSIFIED

**Status:** WITHDRAWN / FALSIFIED UNDER CURRENT FORMULATION
**Date withdrawn:** 2026-08-15

---

## Claim

The constructive block-positivity residue transplants to the pinned upstream zero side, giving an unconditional lower bound of 0.672529 on the proportion of simple zeros of ζ(s) on the critical line.

---

## Failure Route 1: White-Box Kill

The earlier direct analysis identified the load-bearing structural failure.

**The mechanism:** The construction assumed that off-line pair blocks interact non-negatively with the on-line part. This fails because the pinned upstream zero side uses the un-conjugated transpose `u u^T`, not `u u*`. For an off-line root γ = α + iβ, the vector u = φ̂(γ − τ) is complex (u = x + iy). The pairing of such a root with its conjugate yields:

```
u u^T + ū ū^T = 2(xx^T − yy^T)
```

This is a hyperbolic block. A matrix of this form has a negative eigenvalue (unless y = 0, which holds only for on-line roots). The off-line block therefore interacts negatively with the on-line part.

**Exact witness:** u_x = 1, u_z = i, u_conj(z) = −i gives tr(P₁Q′) = −2. With five unit on-line labels the final inequality reads 9 ≥ 13, a contradiction.

**Artifacts:**
- Report: `hunts/frontier_math/CLEAN-KILL-REPORT.md`
- Script: `hunts/frontier_math/clean_kill.py`
- Lean obstruction: `lean/ZetaLean/FrontierMathObstruction.lean`
- Regression test: `tests/test_frontier_math_clean_kill.py`

---

## Failure Route 2: Blind Attack (Independent Confirmation)

A separately executed blind attack was run against `blockpos-0.672529` without prior knowledge of the white-box failure route.

**Branch:** `research/blind-attack-blockpos`
**Research commit:** `b5788357bdd52e137fdf273c5fcd4815dafea535`
**Canonical PR:** `#39`
**Canonical merge:** `78656b0230f92de5636c1d2aa604de3ccffa42de`

**The question posed:** What modification of the world would preserve the appearance of this result while making its interpretation false?

**Finding:** If an implementation evaluates `u u*` instead of `u u^T`, it constructs a Gram matrix that is positive semi-definite by definition. This perfectly preserves the appearance of block positivity, but makes the interpretation false. The actual `u u^T` construction for an off-line root yields a hyperbolic block. A dedicated scan found the cross-block interaction to be approximately **−0.000435**, strictly negative.

**Artifacts:**
- Report: `hunts/frontier_math/BLIND-ATTACK-REPORT.md`
- Script: `hunts/frontier_math/blind_attack.py`
- Ledger entry: `harness/departments/review_ledger.py` (AttackOutcome, role="blind", claim_withdrawn=True)
- Test: `tests/test_review.py`
- Integration commit: `78656b0230f92de5636c1d2aa604de3ccffa42de` (PR #39)

The blind attack independently reached the same structural diagnosis as the white-box kill. Both failure routes are preserved separately. They are not collapsed into one event.

---

## What This Does Not Establish

- This does not establish a new zero-density or zero-proportion theorem.
- The number 0.672529 is not a surviving result.
- The siblings 0.6725124 and 0.6725318 are also withdrawn.

---

## Residual Speculative Thread

The possibility that some contour or integration reformulation could replace `u u^T` with a legitimate `u u*`-type structure is recorded as:

**Status: PARKED / SPECULATIVE**

It does not keep `blockpos` open. It should not receive immediate research priority.

---

## Research Record Note

A candidate improvement was developed far enough to expose a specific structural claim, attacked independently under a blind protocol, falsified, and withdrawn with the failure evidence preserved. The adversarial record is retained in full in the graveyard and review ledgers.

---

## Relation to Pub 1

This result postdates the Pub 1 scientific snapshot (`24fce230968e8d78f6d50ccba39f6ee72da926ee`). It does not modify Pub 1's claims, evidence snapshot, or frozen SHA.

---

## Next Frontier Item

`R-FB9C81 / urms2-0.51`: no recorded blind attack yet; review is not yet standing.
