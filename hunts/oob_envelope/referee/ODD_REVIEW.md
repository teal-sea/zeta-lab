# Independent odd-sector review

Verdict: PASS, independent odd route and both required controls.
Independent L=1.19 endpoint: Q(f)>=2.99e-44 ||f||^2 for real odd f.
Zhu validation: PASS, real odd bound >7.99e-15 at L=4/5, T=150, H=0.
Executions: 132 completed, zero failed, zero inconclusive; 2.3481 core-hours.
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
the odd premise now also closes. Their minimum gives the full-complex bound
5.7179e-48 at this fixed window, with the same ordinary analytic dependency.
No uniform RH statement or novelty claim is made.
Both T=150 and T=500 meet the source digamma lemma's T>=15/4 hypothesis.

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

## Main endpoint and error budget

The independently derived matrix uses 500 odd modes, 1000 half-unit panels,
CC degree 192, and 1280-bit Arb. The negative pole remains in the head and
its omitted tail is charged in eps_D. All 100 block hashes and their source
hashes match, and every panel occurs exactly once.

| quantity | independent outward-safe bound |
|---|---|
| fixed exact shift | 3e-44 |
| quadrature error per entry | <1.699e-64 |
| head factor residual norm r | <1.511e-110 |
| arithmetic plus quadrature operator error e | <8.491e-62 |
| tail deficit eps_D | <1.316e-185 |
| coupling norm eps_B | <4.615e-91 |
| full odd lower endpoint | >2.99e-44 |

The computed lower ball is approximately 2.9999999999999999915e-44;
its exact outward dyadic pair is in main/result.json and positivity.json.
The pair [m,e] represents the exact rational m times 2^e.
The deciding inequality is min(3e-44-r-e,beta-eps_D)-eps_B. An exact dyadic
Rayleigh vector for R gives [3.463166547529606864e-44 +/- 2.77e-63].
That witness bounds the reduced form from above, not Q.

## Controls and post-freeze comparison

Both controls passed, separately from positivity:

1. Flip -2 pp^T to +2 pp^T in the actual head. The first-mode pole changes
   from approximately -0.60272047 to +0.60272047 and fails the independently
   integrated pole identity. On a saved exact dyadic direction aligned with
   p, the Rayleigh value changes from 0.08526141 to 1.29098130. On the same
   near-null vector used above, the increase is approximately 0.06816983.
   Thus the fault genuinely changes the form's numerical result. A positive
   pole adds a positive operator, so positivity alone should not reject it;
   the mathematical pole identity does. No minimum eigenvalue of the damaged
   matrix is asserted from these individual Rayleigh values.
2. The artificial operator R-1e-42 I has a Rayleigh enclosure
   [-9.6536833452470393136e-43 +/- 2.77e-63]. The same factor routine refuses
   it at shift zero and returns no positive bound. This is an enclosed
   negative-operator control, not a negative result about zeta or a rival
   L-function.

All deciding independent artifacts were frozen in commit `cefd6363`
before comparison. The only worker artifacts
then read at 08ff0491 were odd_main_result.json, odd_zhu_result.json and
odd_derivation.md. No worker Python implementation was read, even afterward.
The worker's displayed values 3.46316654753e-44 and 9.11833845450e-15 agree
with the independent Rayleigh values at their displayed precision.
Its 3.42853488205e-44 endpoint is above this review's intentionally
conservative endpoint. The tighter worker endpoint itself was not reproduced
by our fixed shift. The analytic conventions and complex split agree;
quadrature and tail norms were independently implemented and bounded.

## Evidence, execution counts, and limitations

Deciding files are under outputs_odd/3ce6ab9/{main,zhu}/: exact head matrices
and dyadic factors in lossless gzip, complete error budgets, exact endpoint
pairs, Rayleigh vectors, controls, quadrature checks and assembly manifests.
All 17 deciding downloads and both pairs of decompressed payload hashes
match their durable manifests. Frozen sources and exact inputs are local.
Intermediate panel matrices remain on volume oob-envelope-referee under
odd/3ce6ab9/, addressed by the locally saved unit manifests and hashes.
The final local head and factor are sufficient for the finite residual check.
SHA256SUMS covers the local evidence; no manifest hashes itself.

There were 130 successful assembly inputs and two successful reducers:
132 successes, zero failed inputs, zero inconclusive inputs, no retries and
no quota block. They evaluated 1300 panels and 250900 CC nodes, counting
repeated panel endpoints. Three factor proposals gave two positive witnesses
and the one expected negative-control refusal. Both controls passed.
Recorded input work is 8452.92747759819 core-seconds, under 2.3481 core-hours.
All five apps are stopped with zero tasks. Charging each complete app
lifetime at its maximum core count gives 9680 core-seconds, under 2.689 hours,
including an allowance for initialization and final checkpoint time.

The numerical step carries enclosures; the reduction remains ordinary
mathematics, pending external verification. Arithmetic-library independence
is absent. There was no heavy local computation, push, PR or publication.
The scoped hygiene checks passed. The contribution structure check still
fails on three pre-existing hunt-level omissions outside the writable scope;
the exact findings and baseline evidence are saved under outputs_odd/.
