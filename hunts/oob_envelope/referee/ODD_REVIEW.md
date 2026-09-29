# Independent odd-sector review

Current verdict: INCONCLUSIVE while the main computation is running.
Independent L=1.19 endpoint: not yet established.
Zhu validation: PASS, real odd bound >7.99e-15 at L=4/5, T=150, H=0.
Execution ledger: ODD_RUNS.md; final counts await all owned app outcomes.
Analytic argument: ordinary derivation; no kernel check or human peer review.

## Independence and analytic audit

Formulas and exact shifts were frozen at commit 3ce6ab9 before reading any
odd-worker implementation or result artifact. The endpoint stated in the
brief was known. Source uses the prior referee's CC rule, spherical series,
envelope witness and Arb machinery. No numerical-lane code is imported.
The arithmetic library is shared with the worker, so this is independent
implementation and quadrature, not independent arithmetic-library evidence.

[ODD_FORMULAS.md](ODD_FORMULAS.md) derives the odd transform with order 2i+1,
the negative rank-one pole, the first omitted order 1001, the negative pole
tail deficit, all head/tail norms, exact support cancellation at 2L, and
the complex/parity split. No gap was found in the corrected analytic
implication. Applying it to all complex functions requires both numerical
parity bounds. The existing even referee premise is recorded in REVIEW.md;
the new odd numerical premise is still pending in this checkpoint.

The original K1 ceiling 2.27e-17 concerns the even/global window infimum.
It cannot cap an odd-sector lower bound. The appropriate normalization
check here is the odd calculation in
[Zhu v2, section 6.2](https://arxiv.org/html/2608.24827v2).

## Completed Zhu validation

Thirty independently assembled ten-panel blocks cover [0,150] exactly once,
with 200 odd modes, 768-bit Arb, and CC degree 192. The reducer checks
all source and output hashes and the complete panel inventory. Its exact
dyadic factor has an Arb residual norm below 7.726e-111; total entry error
is below 5.256e-64. The tail deficit is below 1.857e-314 and coupling below
3.480e-156. These outward-safe bounds are read from the saved balls.

The fixed shift 8e-15 closes, giving the safe full-sector endpoint 7.99e-15.
An exact dyadic Rayleigh vector gives an enclosed reduced-form value
9.1183384545008638e-15 to the displayed precision, consistent with Zhu's
reported 9.1183e-15. This upper witness concerns R, not the full Q form.
The lower target is intentionally more conservative than Zhu's 8.2065e-15.

Eight deciding artifacts, including the full head and dyadic factor in
lossless gzip form, were downloaded and checked against their durable
manifest. Both decompressed hashes also match. See
outputs_odd/3ce6ab9/zhu/download_verification.json.

## Remaining deciding steps at this checkpoint

Complete the main assembly, factor/residual and tail reduction at the frozen
3e-44 shift; execute the pole-sign fault and artificial negative-operator
control; freeze results; compare worker output; verify terminal apps and
the final SHA-256 manifest. No main endpoint is asserted at this checkpoint.
