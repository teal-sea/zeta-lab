# Research checkpoint: CHHL error, central obstruction, and factorial certificates

**Snapshot date: 2026-09-06. Purpose: preserve and document the existing record, not begin another mathematical pass.**

## 1. Read this first

This checkpoint separates four questions that became conflated during the conversation: what was computed, what has a written argument, what received a separate written-proof review, and what controls the original research target. Saving a draft does not promote it. A successful finite checker does not establish an infinite or asymptotic claim.

The completed total-error bound in the laboratory remains the reproduced classical level `E(N) <<_A N^3/(log N)^A` for each fixed A>0. No subsequent component draft or factorial experiment in this snapshot improves that completed bound. The current factorial constructions give fixed leading constants above one; no rate in the number of refinements has been proved that supplies an RH-scale bound.

There are substantive items to retain: independently reviewed Wronskian results, an independently reviewed factorial-certificate pilot, reproducible objective comparisons, exact finite arithmetic checks, several unreviewed component proof drafts, and explicit limitations of attempted methods. The limitations belong beside the positive outcomes, not in discarded conversation history.

This is a research-artifact checkpoint, **not a verbatim export of the whole chat, a mirror of all repository history, or a backup of unseen desktop worktrees**. The inventory names exactly what is included. No additional unpublished RH proof is being held back.

## 2. Where the record is saved

At the start of this preservation pass, `teal-sea/zeta-lab/main` was observed at `cdbb5b47293421516e31c63e062c7b8e7c8cfa76`. The parent hunt is `hunts/prime_pair_error/`, with the conversation-era notes under `frontier/2026-09-06/`.

The original frontier handoff is already on main at `frontier/2026-09-06/archive/zeta_frontier_handoff_2026-09-06.zip`. Its 629,964-byte original has SHA-256 `61f4901f8659d13cd2c795b560475b1313db666650da78dabeccd7e03c1807de`. Its locally calculated Git blob identity, `36dc7cbe82fe673cdbe2cf91def4d8079ac12a66`, matches the blob in the observed main tree. All nine members named by its internal inventory were checked for size and hash. Its seven nested experiment ZIPs match the separately available original ZIPs byte for byte.

The factorial pilot is already on main under `frontier/2026-09-06/factorial_certificate_pilot/`, including its original 10,876-byte ZIP, review, and integrity test. The original SHA-256 is `215f0ab2de4957e5d98d42106f2a525286b9fa9e89fa5f4db167ceb82ed7ad0c`; its locally calculated Git blob `3aa47dc9e4afa9cf8574cfb1c91da65cccde9612` matches main's archive entry.

The full-cost and direct-certificate comparisons are pushed in **open, unmerged PR #196**, at head `46fdb433752a1b26abba516fc24d6db21543b2b8`. This preservation pass also created `snapshot/2026-09-06-factorial-comparisons` at that exact commit. The extra ref preserves the current comparison state without merging or editing the research PR. The PR's body describes the first experiment; `factorial_direct_bn/DIRECT_BN.md` on its head contains the second experiment. Do not conclude that the second is missing from reading the older PR description alone.

The three newer original packages are now saved in persistent Library under **`/Zeta Lab/Research snapshots/2026-09-06/`**:

| Original package | Bytes | SHA-256 |
|---|---:|---|
| `certificate_structural_step.zip` | 21,040 | `4c230a967b3932dba18c6ee176611804a180bbae606e64cf73879f67dadc7d90` |
| `certificate_refinement_rule.zip` | 26,100 | `962dbe79c58b4ceb59300d9c0d2687e63693e3b58fe5b320fa0420f13ae42f9c` |
| `certificate_route_test.zip` | 41,790 | `992ca6730314390f0754db1fc7e96d361aa8e16691c5c6e83765e95dc32dec5a` |

All three were read back from their new Library file references into separate container paths and compared byte for byte with their originals. This is not reliance on an upload success message. **Their original binary ZIPs have not been committed to GitHub by this pass.** The Library copies and the cumulative checkpoint are durable copies outside transient conversation attachments; their repository binary import remains separately identifiable work. Do not repeat the earlier claim that an archive is on main merely because a README mentions it.

The cumulative backup, `zeta_research_checkpoint_2026-09-06.zip`, contains all 12 available original research ZIPs, 16 loose original companion files, byte-identical extractions of the three latest packages, the inventory, this checkpoint, and a verifier. The two overlaps are intentional: the first handoff contains seven earlier ZIPs, and the route test carries its previous refinement inputs/results. None of those duplicates has been deleted or silently rewritten.

## 3. Mathematical objectives, kept separate

The original CHHL quantity is

`E(N) = 2 sum_{k=1}^N [psi_2(N,k) - S(k)(N-k)]^2`,

with `psi_2(N,k) = sum_{n=1}^{N-k} Lambda(n)Lambda(n+k)`. It includes proper prime powers and all nonzero separations; the diagonal is excluded. Odd separations are not identically zero. The initial unweighted/prime-only experiments are not this exact quantity.

CHHL Theorem 2 supplies a known implication from an unconditional eventual bound `E(N) <<_epsilon N^(2+epsilon)` **for every epsilon>0** to RH. Knowing this sufficient condition is not a method that proves it. The lab's Wronskian lower bound cannot be reversed to supply the missing upper bound.

The central route subsequently isolated `R(N)=psi(N)-N`. An unconditional square-root-with-arbitrarily-small-power remainder estimate is RH-strength; the suitable one-sided upper bound is already sufficient by the oscillation criterion described in `DIRECT_ATTACK.md`. Calling that bound the next target is not itself a new reduction or a demonstrated proof mechanism. A direct proof of it would settle RH, but would not automatically prove the stronger entire CHHL mean-square conjecture.

The factorial route seeks explicit ceilings `psi(N) <= B_N`. Its unresolved requirement is a family whose **whole** excess above N, not just a leading coefficient or a finite table, is at RH scale. The Nyman--Beurling possibility discussed at the end is a different known RH criterion and has not been executed in this record.

## 4. Chronology and disposition of each strand

### 4.1 Reverse-engineering primes: experimental precursor

Source: `prime_reverse_engineering_bundle.zip`, also nested in the original frontier handoff. Preserve its README, code, notebook, recorded metrics, holdout predictions, and trillion-scale stress data. It recovered the known Hardy--Littlewood prime-pair correction in a guided search. Exact-next-gap prediction was weaker. Its numerical prediction performance is not an analytic error bound or an independently discovered prime law. The multiplication/hole viewpoint and overlap counting were recognitions of established arithmetic, not novelty claims.

### 4.2 Möbius boundary cancellation: separate branch

Sources: `prime_mobius_review_bundle.zip` and the original pasted Möbius brief. The grouping `m,2m,3m,6m` supplies exact cancellation bookkeeping. Restricted prime-for-prime/sign-preserving matching runs into partner shortages; a valid algebraic rearrangement does not bound the surviving total. Preserve the numerical obstruction and proposed parity-changing replacements as a separate investigation. It is not part of the proof of the CHHL upper bound, and no near-square-root leftover estimate was obtained.

### 4.3 CHHL replication and residue corrections

Canonical source: `hunts/prime_pair_error/{RESULTS.md,probe.py,residue.py,results.json,results_residue.json}`; related preservation lineage PRs #181 and #186. The reported first pass replicated all eleven Table 1 rows using the paper's truncation convention and extended the calculation to 10^7. The endpoint-remainder heuristic was compared with Korevaar--te Riele. The subsequent mod-1/3/30 decomposition separates exact identities from one heuristic use of the singular series; fixed-coefficient corrections were evaluated at new cutoffs.

Source archive `prime_pair_q3_followup.zip` is retained as a precursor even though its attachment was not supplied to the original desktop agent. The desktop agent's independent derivation is the canonical lab pass; do not erase either provenance. The fact that a correction explains a modest share of squared error does not mean the rest is random noise.

### 4.4 Wronskian/Theorems A and B: completed internal written review

Canonical source: `RESULTS.md` Part 3, `REFEREE.md`, `wronskian.py`, and `results_wronskian.json`; author PR #188 and referee PR #189. The retained A statement bounds W by `N^(Theta+Theta_chi) log^4 N` using the repaired endpoint and uniformity arguments. Its useful RH-specialized consequence assumes RH for both functions. B supplies an unconditional Omega lower bound on E tied to zeros of the primitive character modulo 3. The review is a written-proof review, not a Lean check or external human endorsement.

Preserve the specific corrections: `(N-1)/2` endpoint convention; the double-zero kernel and finite truncation handling; distinction between the negative H constant and positive auxiliary limit; no four-digit finite agreement for the whole auxiliary term; no established RH converse for T; no established O(N) optimality; no assumed noncoincidence of ordinates. PR #189 was repaired and merged after its deleted-base problem. Do not reopen that finished audit merely because a new branch needs review.

### 4.5 Total-E upper-bound attempt

Canonical source: `UPPER_BOUND.md`, PR #191. The centered Fourier identity includes the diagonal subtraction and the two-sided factor. Singular-series tail, geometric leakage, and a high-denominator mixed moment fit near-quadratic component budgets. Minor-arc and residual fourth-moment bounds remain too expensive, and the low-denominator q=1 term contains the prime-counting remainder.

The completed total bound is `N^3/log^A N` for every fixed A, not a new exponent improvement. A component estimate at `N^(13/5)` is not the total-E bound. The report names the exact unresolved moments and retains the entire sharp-cutoff budget.

### 4.6 Zero-energy feasibility, sharp transfer, and multiscale drafts

Sources: the four frontier notes and checkers already on main, plus original ZIPs `zero_energy_feasibility.zip`, `prime_pair_sharp_transfer.zip`, `prime_pair_multiscale.zip`, and `central_arithmetic_attack.zip`. These remain unreviewed analytical drafts unless a later named review says otherwise.

The feasibility note derives a finite zero-energy kernel for an exponentially damped band and records why a global fourth-moment de-smoothing estimate loses control near zero. `SHARP_TRANSFER.md` replaces that failed estimate with local fourth-moment control plus a distant-frequency second-moment budget, deriving a sharp square-root-frequency-band bound of `N^(5/2+epsilon)`.

`MULTISCALE.md` claims, on its explicitly stated band and parameter range, `N^(3+epsilon)/T` for `4 <= T <= N^tau_*`, with `tau_*=4/(13-4sqrt(3))`. It counts other rational models and retains the uncovered regions. Its outermost-band exponent is not the exponent of the whole band union. No improved total-E bound follows.

The localization inequalities show that leaving the intensity expression unsplit, or making the central region narrower, does not eliminate the endpoint prime-counting requirement. This corrects the earlier conversational suggestion that the obstruction was only an artifact of splitting positive moments.

### 4.7 Direct arithmetic attack and counterfeit control

Source: `DIRECT_ATTACK.md` and `central_arithmetic_attack.zip`. Exact divisor identities yield `sum_{m<=N} psi(N/m)=log(N!)`. The compensated dilation transform on `x^s` has leading multiplier zeta(s), and therefore suppresses zero-shaped modes instead of yielding a contraction estimate. This defeats the proposed automatic-feedback estimate, not the full arithmetic identities or every possible factorization argument.

The deliberately counterfeit weight sequence preserves coarse positivity, density, second-moment scale, and fixed small-prime avoidance while carrying an oversized oscillation. It violates the exact divisor identities. It is a diagnostic for arguments using only those coarse properties, not an alternative prime system satisfying all the arithmetic, and not a counterexample to RH.

### 4.8 Factorial-certificate pilot and independent review

Canonical source: `factorial_certificate_pilot/`, PR #195. A balanced floor seed `g(t)=sum a_j floor(t/j)` with period L, nonnegativity, and initial coverage is lifted as `W(t)=sum_{k>=0}g(t/M^k)`. Exact divisor algebra gives a factorial ceiling B_N. The pilot tracks coefficient mass and rescaling errors, rather than only decimal constants.

All 87 reported seeds reproduced under the independent review; the seed-to-global-certificate argument and error budget survived. The period-30 seed and rescaling recover Chebyshev's construction. The best reported period-2310 seed has leading C approximately 1.06985445. This is an improvement to a starting template, not to modern prime-counting theory. Every fixed seed in this class has C>1.

### 4.9 Objective comparisons: preserved in PR #196

Sources on pinned head `46fdb433...`: `factorial_full_cost/COST_COMPARISON.md` and `factorial_direct_bn/DIRECT_BN.md`, their scripts/results and tests. Both used the original sizes and 348 cases, with exact feasibility checks after numerical proposals.

Full-cost optimization improved its conservative U_N in 30 rows but worsened the actual factorial B_N in every such row. The allowed error term was too loose to act as a reliable objective there. Direct B_N minimization then improved 14 rows by at most about 2.76, all at small tested cutoffs, and never changed the winning seed per (L,N). No persistent improving pattern or LP optimality proof was obtained. 'None found at 10^12' is not an exact optimality theorem: solver resolution remains a limitation.

These are finite negative/mixed results worth keeping. They do not invalidate the certificate inequality. The two unsuccessful objective adjustments motivated changing the permitted arithmetic rather than a fourth scoring function.

### 4.10 Structural extension: omitted-prime obstruction

Source: `certificate_structural_step.zip/STRUCTURAL_STEP.md`, full source and recorded data included in this snapshot. The omitted-prime lemma forces W(p)>=2 when p is absent from the permitted denominator factors. It yields a positive lower bound on C-1 in a fixed denominator family. Enlarging L from 2310 to 30030 at M=15 makes W(13) fall from 2 to 1 in the recorded candidate.

Its leading C falls from approximately 1.06985445 to 1.05580512 while finite coefficient mass rises from 15 to 39. Complete period checks and rational logarithm intervals support the seed feasibility and constant comparison. Finite actual B_N values and conservative U_N values remain distinct. This is a single checked enlargement with a written elementary argument, not a uniform family theorem or an independently reviewed new result.

### 4.11 Reusable positive-repair rule

Source: `certificate_refinement_rule.zip/REFINEMENT.md`. The carry function is

`b_n(t)=floor(t/n)-floor(t/(n+1))-floor(t/[n(n+1)])`,

which is nonnegative, vanishes before n, and equals one at n. The fixed signed correction is `h_p(t)=sum_{d|210}mu(d)b_p(t/d)`. Seed-level deficiencies below R=100000 are repaired left to right; a fixed lifted certificate shields the whole tail. M=15, mask 210, and the targets 17,19,23,29,31 are held fixed after the recorded exploratory choice.

The five stages lower C from 1.05580512 to 1.0500311981418249, with finite coefficient mass 4676/3, 1182 finite patches, and tail multiplier 15. The complete sufficient bound is

`psi(N) <= B_N <= C*N + (4676/3) S1(N) + 225 S2(N)`.

For K=floor(log_15 N), `S1=(K+1)(1+log N)-log(15)K(K+1)/2`. If N<R, S2=0; otherwise `S2=sum_{m=0}^{floor(log_15(N/R))}(m+1)[1+log(N/R)-m log15]`.

The full cost is retained, including the infinite tail. The reported five improvements do not prove convergence of C to one, bounded complexity under indefinitely many refinements, or the illustrative half-gap/double-mass tradeoff. Finite source checks are preserved rather than relabeled as a new independent referee pass.

### 4.12 Fixed-recipe ceiling and combined-weight repair

Source: `certificate_route_test.zip/ROUTE_ASSESSMENT.md` and `aggregate_results.json`. Two deductions and one finite comparison are recorded.

First, continuing the old menu once per new prime greater than 31, at fixed mask/M and with nonnegative repair charges, has a bounded remaining gross saving below 33/1519. The original five-stage constant therefore stays above 31239/30380 (greater than 1.028). An independent prefix view finds permanent early excess at 18,19,20,21,24,25,32. Later corrections beginning at 37 cannot remove it. This is a ceiling for that restricted continuation, not for all factorial certificates. The combined-weight variant has an analogous fixed-menu floor greater than 1.026.

Second, seed nonnegativity everywhere is stronger than necessary. It suffices to have W_g>=1 below R and g>=0 above R. Repeated use of `W_g(t)=g(t)+W_g(t/M)` proves global coverage. Repairing W_g instead of every negative seed value permits signed intermediate contributions without weakening the final certificate.

Applying this variant to the same five corrections gives C approximately **1.0486636637932206**, finite mass **2641/3**, **537** patches, and the same tail allowance **225 S2**. The record has 705 negative seed cells but valid lifted prefix coverage. Its final sufficient bound is

`psi(N) <= B_new(N) <= C_new*N + (2641/3) S1(N) + 225 S2(N)`.

These are the latest reported coefficient values. They improve this experimental family, not the completed total-E estimate or known prime-counting bounds. No scalable contraction theorem or separate proof review has been completed for this newer rule.

## 5. Corrections and limits that must survive the handoff

- Known ideas remain known: multiplication holes, sieving, divisor inversion, Chebyshev's factorial construction, and Nyman--Beurling are not new discoveries here.
- Recovering a known heuristic is not discovering an unknown law; fitted coefficients and frozen predictions are separate measurements.
- Lower bounds, upper bounds, and upper bounds for different quantities must not be interchanged. W is not E; a band is not the circle; a damped sum is not a sharp cutoff.
- An unproved transfer, asymptotic remainder, or convergence rate must not be concealed in a named lemma or a finite test result.
- Preservation, independent written review, formal verification, novelty, and progress on the original target are separate labels.
- Every new fixed coefficient above one still leaves a linear leading excess. Reducing a decimal or counting additional bands is not automatically a scalable advance.
- The baseline one-way prime-correction menu is restricted by a proved-in-the-draft ceiling. This is the stopping point of that recipe, not a theorem that creative alternatives fail.
- The failed base64 upload was real. Original bytes are now preserved by named stores and measured hashes; references to unuploaded files are not preservation.

## 6. Open questions, recorded without launching new work

The certificate continuation discussed was coordinated signed corrections that can revisit early excess, with a rule controlling net savings, coefficient growth, and tail protection. No such general repeated-cost theorem is supplied by this checkpoint. Repeating the same next-prime menu would not address the recorded ceiling.

Nyman--Beurling approximation was discussed as an alternative using balanced floor sums and weighted L2 approximation without pointwise majorization. It is a known criterion, not an experiment already performed here. No coefficient sequence, convergence result, or controlled infinite-tail estimate for that alternative has been produced in this record. It must not silently replace the CHHL objective.

The Möbius branch remains separate with its partner-shortage question. The original prime-prediction data remain a precursor, not the next theorem claim. The unresolved central arithmetic bound remains the RH-strength requirement itself. No new agent jobs, larger searches, or formalization runs are started by this preservation pass.

## 7. Reproduction, integrity, and scope boundaries

Each original ZIP retains its own script names, requirements, data, and internal manifests. The cumulative inventory additionally lists every direct ZIP member with size and SHA-256. The verifier checks the cumulative file inventory and ZIP-member lists; missing files, extra/missing members, byte changes, and empty archives fail rather than skip. New runs should write new outputs, not overwrite the archived measured results.

The latest packages' replay entry points are: `probe.py` then `check_and_compare.py` for the structural step; `refine.py --output <new-file>` for positive repair; and `aggregate_repair.py` for the combined-weight comparison, run in a scratch extraction because its default output name belongs to its original record. These notes are instructions, not a claim that these mathematical experiments were rerun during archival work.

This preservation pass checks bytes, manifests, parser integrity and source indexing. It does not independently re-prove the analytic drafts, prove numerical LP optimality, run Lean, or assert full repository CI is green. Existing reviews and recorded tests keep their original dates and scope.

Historical source notes saying 'not pushed' or recording an older PR state are preserved verbatim as historical artifacts. This checkpoint records current storage separately; it does not alter the past ZIPs to make their prose current. A future repository binary import must compare against these same hashes and verify the actual stored bytes before marking the import complete.

**Resumption point:** read this checkpoint, the pinned comparison reports, and the latest route assessment before selecting a new experiment. The current work is paused for preservation, with both favorable results and failed methods retained.
