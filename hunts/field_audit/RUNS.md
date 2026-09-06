# Runs: `field_audit`

One night, one host (13-inch laptop, no cloud, no Lean build). Every external
repository was read or replayed read-only; nothing was posted, opened,
commented, forked or starred anywhere.

```runmanifest
id: field_audit-2026-08-24-night1
hunt: field_audit
started: 2026-08-24T05:55-05:00
finished: 2026-08-24T06:45-05:00
ran:
  - gh api /search/repositories and /repos/{owner}/{repo} sweeps over the August 2026 wave, plus all 28 forks of anthropics/zeta-23-lean, read-only
  - arXiv API query cat:math.NT AND all:"simple zeros", August 2026
  - git clone of trmdy/zeta-simple-zeros-673137 into a scratch directory, read-only
  - pip install --only-binary=:all: python-flint==0.9.0 into a scratch virtualenv, then pip install -e . of the competitor package
  - zeta-673200-verify fast
  - python -m unittest discover -s tests
  - zeta-673200-verify main --workers 6
  - exact-rational recomputation of the seven- and nine-point span capacities from their published weight tables
  - 300-bit Arb recomputation of their seven-point, refined and nine-point assembly constants
  - .venv/bin/python hunts/field_audit/assembly_compare.py
  - python3 hunts/field_audit/rank.py
  - full read of src/zeta_ext/{verify_general,kernel,parallel,cli,design,nine_point,h0_cert}.py against lean/bridge/Zeta23Ext/Bridge/Defs.lean
outcome: this laboratory ranks tenth of fifteen public claims and its best figure was beaten on 2026-08-11, a week before its own hunt opened; Hunt #82's barrier is untouched because every public claim sits below its ceiling, and the leading constructions are outside the family it names anyway, having changed both the window and the block profile; the competitor's 2,168,370-box run replayed here to an identical node count with no defect found in the verifier, but its second-derivative table digest is host-dependent and that table is the one the tangent pruner rides on
artifacts:
  - hunts/field_audit/RESULTS.md
  - hunts/field_audit/assembly_compare.py
  - hunts/field_audit/rank.py
```

## What each command established

**The sweep.** Eleven repositories carrying claims for this quantity that this
laboratory had not seen, eight of them created 2026-08-11 or 2026-08-12. Also:
no arXiv preprint for any of them, and the `riemannzeta.fun` leaderboard still
recording `0.672500703679`. Table in `RESULTS.md` §2.

**The replay.** `zeta-673200-verify fast` completes in 0.6 s and its 23-test
suite in 0.5 s. Both pass. The window bounds, `H(v) = 0.67245704141454428878`,
and all three published assembly constants reproduce to every digit they print.
Span capacities are exactly `2` on all six seven-point spans and all eight
nine-point spans, in exact rational arithmetic. `RESULTS.md` §4.

**The long run.** `zeta-673200-verify main --workers 6`: their exhaustive
interval subdivision for `F >= 891/200000`. **It reproduces**, 482.6 s wall
against 441.7 s on their host at ten workers, with `verified=True` and an
identical `nodes=2168370`, `splits=1084023`, `maximum_depth=50` and all three
prune counters. The `w` table digest matches theirs byte for byte; **the `w''`
table digest does not**, and that is the table the tangent pruner rides on, the
one component whose corruption could produce a false acceptance rather than a
false failure. Not one branch of the search changed regardless. Both directions
of that finding are written out in `RESULTS.md` §7.

**What was not run, and why it matters.** The nine-point run behind their
headline `0.6733127422722459` visits 116,272,426 nodes by their own record and is
out of reach on this host. Their headline is therefore assembly-verified here and
floor-reported. Nothing in any other repository in `RESULTS.md` §2 was run at
all, including the leading claim.

**The comparison.** `assembly_compare.py` reproduces both of this laboratory's
own published constants from an independent reimplementation of `Phi_n`
(`0.6730295534796927114` against `0.6730295534796928`, and
`0.6730529829896288869` against `0.6730529829896288`), which is what licenses
using the same script to price the refined assembly against our own floors.
Both of our optima sit exactly at the cap `m = (n-1) + floor(1/c)`.

**The read.** No defect found in the competitor verifier. The specific pattern
this laboratory found in Ainta's, a constant wired to the target, is absent:
their rationals are thresholds compared against computed enclosures, and the
assembly then uses the rational, which is the conservative side. Details, and
the two non-code reservations, in `RESULTS.md` §6.
