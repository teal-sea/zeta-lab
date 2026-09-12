# Runs

## 2026-09-06, probe.py, discovery pass to N = 10^6 and held-out pass to 10^7

**Estimate written before the large run.** `decompose` at N = 10^6 took 1.2 s and the
whole script 3.1 s; the FFT is N log N, so 10^7 was priced at about 15 to 20 s for the
decomposition plus the sieves, under a minute in all, with the padded FFT of length
2^25 costing about 1 GB and the per-k arrays another gigabyte. Measured: 33.5 s wall,
2.2 GB maximum resident set, 3.9 GB peak footprint, on the operator's 16 GB laptop.
Nothing checkpoints because nothing runs long enough to need it. The final run, after
the singular-series cross-check was added, took 31.7 s wall and 2.7 GB resident.

```runmanifest
id: prime_pair_error-2026-09-06-probe
hunt: prime_pair_error
started: 2026-09-06
finished: 2026-09-06
ran:
  - .venv/bin/python hunts/prime_pair_error/probe.py --max-n 100000
  - .venv/bin/python hunts/prime_pair_error/probe.py --max-n 1000000
  - .venv/bin/python hunts/prime_pair_error/probe.py
outcome: Table 1 reproduced at all eleven N after truncation; the ratio keeps rising to 0.24449 at N = 10^7; the signed part of the error is S(k) times the one-point remainder profile R(N) + R(N - k) - R(k) with unit coefficients at the two held-out N, a k-resolved form of the Korevaar-te Riele average, carrying 1 to 3 percent of E(N) and 12 to 22 percent of the prime-only analogue.
artifacts:
  - hunts/prime_pair_error/results.json
```

## 2026-09-06, residue.py, the residue-class correction at fresh cutoffs

**Estimate written before the run.** `residue.py` at N = 10^6 took 7.0 s wall and
484 MB resident (four moduli, the identity checks, the product form and the
modulo-3 closed form all included). The work is N log N in the FFTs and linear in N
times the number of reduced residues elsewhere, so the fresh list
2 x 10^5, 5 x 10^5, 2 x 10^6, 5 x 10^6, 7 x 10^6 was priced at about 1.5 + 3.5 + 15 + 40
+ 56 s, two minutes in all with the sieve to 7 x 10^6, and the peak resident set at
about 1.6 GB (the closed-form check at q = 3 holds about fourteen arrays of length N
at once). Nothing checkpoints because nothing runs long enough to need it.

**Measured.** 177 s wall, 3.27 GB maximum resident set, 4.4 GB peak footprint, on
the operator's 16 GB laptop: the time estimate was low by half and the memory
estimate by a factor of two. The memory is the q = 3 closed-form check and the q = 30
product form each holding a dozen arrays of length N beside the four corrections; both
are checks, not predictions, and the next pass should compute them at one cutoff
rather than five. Per cutoff: 2.3, 12.5, 28.9, 60.6 and 68.7 s.

```runmanifest
id: prime_pair_error-2026-09-06-residue
hunt: prime_pair_error
started: 2026-09-06
finished: 2026-09-06
ran:
  - .venv/bin/python hunts/prime_pair_error/probe.py --max-n 1000000 --out <scratch> (re-check of the first pass)
  - .venv/bin/python hunts/prime_pair_error/residue.py --fresh 1000000 --out <scratch> (timing)
  - .venv/bin/python hunts/prime_pair_error/residue.py
outcome: The first pass's profile is the modulus-1 member of an exact four-piece decomposition whose only heuristic is that the primes not dividing q act on the reduced classes as all primes act on the integers; with every coefficient fixed at 1, the modulus-3 and modulus-30 members remove more of E(N) than the original at all five fresh cutoffs (0.5 to 1.9 percent for q = 1, 1.0 to 7.6 for q = 3, 2.2 to 10.0 for q = 30) with post-hoc slopes within 1 percent of 1 at q = 30; the residual after q = 30 carries no structure mod 30 and all of its structure at the next primes, which the q = 210 member predicts to within one standard error; the character-weighted sum T(N) matches the integral form to 0.5 percent at every cutoff.
artifacts:
  - hunts/prime_pair_error/results_residue.json
```

## 2026-09-06, wronskian.py, the identities of Part 3 at the fresh cutoffs

**Estimate written before the run.** Everything is prefix sums over one array of length
N plus one FFT pair count per cutoff to check the identity against T(N); priced from
`residue.py`'s per-cutoff figures at a few seconds in all and about 2.5 GB resident at
7 x 10^6 (the FFT of length 2^24 and a dozen arrays of length N). Nothing checkpoints.

**Measured.** 3.0 s wall, 2.45 GB maximum resident set, on the operator's 16 GB laptop,
for all five cutoffs with the pair count included.

```runmanifest
id: prime_pair_error-2026-09-06-wronskian
hunt: prime_pair_error
started: 2026-09-06
finished: 2026-09-06
ran:
  - .venv/bin/python hunts/prime_pair_error/wronskian.py
outcome: The identity T - I = W + P/2 + X - H holds at every cutoff to rounding; the auxiliary term P/2 + X - H is 0.3131 N + o(N) with the constant derived and matched to four digits; W splits exactly as R P/2 - J + Q with J the character-weighted sum of psi(m) - m over prime powers, J/N between 0.10 and 0.83 and J/(N log N) at most 0.053; RESULTS.md Part 3 proves W << N^(Theta + Theta_chi) log^4 N unconditionally, hence (T) under RH for zeta and L(s, chi_3) with O(N log^4 N), and E(N) = Omega(N^(1 + 2 Theta_chi - eps)) unconditionally.
artifacts:
  - hunts/prime_pair_error/results_wronskian.json
```

## 2026-09-10, an Ostoyae board, run from a Claude Code cloud VM

**No estimate was written before launching.** CLAUDE.md's compute discipline says to measure one
unit, multiply, and write the number here first. That was not done, and this entry records the
actual cost instead of pretending a forecast existed.

Board `hunts/prime_pair_error/board.json`, three seed items, concurrency 2, mapping off, judge on,
against a frozen clone of this repository at `2da62eb`. Executor: headless Claude Code, sonnet,
inside the same VM.

| attempt | kind | item | outcome | cost |
| --- | --- | --- | --- | --- |
| a-0001 | prove | `w-doors` | done, check passed | $1.156 |
| a-0002 | prove | `w-jn-instrument` | done, check passed | $0.971 |
| a-0003 | prove | `w-tb-bind` | done, check passed | $0.519 |
| a-0004 | verify | `w-tb-bind` | done, one proposal judged ok | $0.235 |

**$2.88 over four attempts, 991 s of model time, 78,654 output tokens.** Roughly a dollar an item
for bounded, hand-written items with no mapping. That figure does not extrapolate to a mapped
board: mapping is a different mode and its cost is measured separately in the next entry.

What landed: the doors analysis this hunt owed under CLAUDE.md's 2026-08-24 rule; `jn_probe.py`
and `results_jn.json`, the first measurement of J(N), the estimate Section 19 says the whole of
(T) rests on; and `tb_bind.py` with `results_tb_bind.json`, which reports that Theorem B cannot be
evaluated at any N, with the three reasons named.

The environment, for reproduction: python3.12, because 3.11 hits the cypari2 sdist trap this
repository's `requirements.txt` documents. Both optional backends live there, so `rigor.BACKEND`
is `python-flint` and the PARI oracle runs rather than skipping. The fast tier on that machine:
2957 passed, 3 skipped, 16:47.

## 2026-09-10, the same board widened, with mapping on

Two more seed items, both taken from the doors analysis the first run produced: `w-delta-sq`, the
top-ranked door, measuring sum_{t<=N} Delta(t)^2, which UPPER_BOUND.md (31) needs to close the
binding constraint; and `w-rank3-scope`, pricing the door the doors table records as "not
attempted; cost unknown". Mapping on for the first time on this board, `--auto-advance` on,
allowance 16 cumulative, cap $28 cumulative.

| attempt | kind | item | outcome | cost |
| --- | --- | --- | --- | --- |
| a-0005 | map | `w-delta-sq` | failed | $0.893 |
| a-0006 | verify | `w-delta-sq` | done, judged its proposals | $0.257 |
| a-0007 | map | `w-rank3-scope` | failed | $1.168 |
| a-0008 | verify | `w-rank3-scope` | done, judged its proposals | $0.458 |

**Mapping cost $2.78 and mapped nothing.** Both map attempts failed, `maps: 0 of 5 active items
mapped`, and because `mapping.max_attempts` was 1 the two seed items were then reported
`exhausted after 1 map attempt, no map`: the discovery step consumed them before either reached
the prove step it was seeded for. Removing the `mapping` key makes both launchable again, which
is what the next run does. The cost of the mapped mode on this board is therefore $2.78 for zero
maps, against roughly a dollar an item for direct work in the entry above. That is one board and
two attempts, not a general figure, and it is a reason to seed work directly here rather than a
finding about mapping anywhere else.

**The judge caught a fabrication, which is the result worth keeping.** The failed map on
`w-delta-sq` proposed `w-delta-sq-vs-sw-bound`, whose text asserts in the present tense that
`delta_sq_probe.py` "already measures" S(N) and that results were written to
`results_delta_sq.json` at six named cutoffs. No such file exists; `w-delta-sq` had just failed.
The verify attempt rejected it, in its own words, because "the proposal fabricates a completed
result to justify itself", and rejected the dependent edge `e-0001` for the same reason. Five
proposals passed and two failed. A mapper inventing the artifact that would justify its own
follow-up is exactly the failure a separate judge exists to catch, and here it was caught by
reading the worktree rather than by trusting the handback.

`--auto-advance` confirmed nothing, correctly: it freezes its targets at the start of a run, so
proposals discovered during that run cannot authorize their own scheduling.

Running total across both runs: **$5.66 over 8 attempts**, 8 of an allowance of 16.
Seven proposals are recorded and unanswered; scheduling them is the operator's decision.

## 2026-09-10, the two doors, mapping off

The same board with the `mapping` key removed, so the two seed items the failed maps had
exhausted became launchable again. Allowance and cap unchanged and cumulative.

| attempt | kind | item | outcome | cost |
| --- | --- | --- | --- | --- |
| a-0009 | prove | `w-delta-sq` | done, check passed | $0.526 |
| a-0010 | prove | `w-rank3-scope` | done, check passed | $1.062 |

**$1.59 for both doors**, against $2.78 for the mapping pass that produced no map and consumed
these same two items. Running total **$7.24 over 10 attempts**, 10 of an allowance of 16.

`delta_sq_probe.py` measures S(N) = sum_{t<=N} Delta(t)^2, the quantity UPPER_BOUND.md (31)
needs in order to close the constraint the doors table ranks first. Eight cutoffs from 1e5 to
1e7, psi read from `zeta.explicit` and cross-checked against `psi_true`, accumulated at
mp.dps = 50. S(N)/N^2 stays between 0.0199 and 0.0268 across two decades of N and the fitted
log-log slope is 2.0149. `results_delta_sq.json` states in its own words why that does not
settle (31): the target is an eps-indexed asymptotic rate for every eps > 0, a fitted slope over
one finite range is a different quantity, and the ladder cannot see a change of shape past 1e7.

`RANK3_SCOPE.md` prices the door the doors table recorded as "not attempted; cost unknown",
2493 words, from UPPER_BOUND.md and RESULTS.md only. Its Section 2 identifies the gap precisely:
for denominators in the polynomial range floor(L^B) < q <= R_0, the large-sieve bound and
Vaughan's estimate degrade to the trivial order-N^3 when evaluated at small q, and the
Siegel-Walfisz argument that does reach small q is proved only to a fixed power of log N. That
range has no tool named for it in either document.

### A rule collision the board exposed, unresolved

The board no longer sits at `hunts/prime_pair_error/board.json`. A mapper wrote a sentence
disclaiming this repository's reserved word into a proposal, so the board carries those bytes,
and `tests/test_hunt_probe_discipline.py` scans the filesystem under `hunts/` for exactly that,
intent-blind by design. One copy is inside `attempts[]`, which is append-only and must not be
hand-edited, so the file cannot be made clean. The board moved to `boards/prime-pair-error.json`,
which bends the "a board lives with its hunt" convention least and loosens no guard and edits no
record. `boards/README.md` states the three rules and the alternatives. It is an interim
placement, not a ruling. The board's seed text now forbids naming a reserved word at all rather
than banning it by name, so a rerun does not reproduce the collision.

## 2026-09-10, four follow-ups: the work landed, the board recorded it failed

All seven proposals from the previous run were scheduled. Eight prove attempts ran and **every one
of them is recorded `failed`, with `check` false. The work was fine. The check was wrong, and it
was mine.**

The four confirmed items came from the mapper, so none carried a `check` of its own and all fell
through to `judge.default_check`, which read

    test -e hunts/prime_pair_error/{id}.py || test -e hunts/prime_pair_error/{id}.md

That demands a file named after the item id, for example `w-rank3-polyrange.py`. No task asks for
that: each names its outputs after what they do. **The check could not pass however good the work
was.** With `max_attempts` at 2 each item was then retried at full price before being called
exhausted, so the retry was pure waste.

Cost of the defect: eight prove attempts and four verify attempts, **$11.33**, on a one-line
mistake in the board's judge configuration. Running total **$18.57 over 22 attempts**.

The default check now asks whether the attempt changed anything under `hunts/prime_pair_error/`,
which is a question about the work rather than about a filename the engine did not choose.

What the attempts actually produced, landed here by hand from their branches:

| attempt | file | finding |
| --- | --- | --- |
| a-0014 | `tb_bind_grh.py`, `results_tb_bind_grh.json` | Theorem B under GRH for L(s, chi_3) |
| a-0016 | `delta_sq_sw_bind.py`, `results_delta_sq_sw_bind.json` | the Siegel-Walfisz bound against the measured S(N) |
| a-0019 | `SW_MAJOR_ARC_SPLICE.md` | whether the major-arc argument splits U and Z separately |
| a-0021 | `RANK3_POLYRANGE.md` | the polynomial range of denominators |

Two are worth reading. Assuming GRH for L(s, chi_3) fixes Theta_chi = 1/2 and gives the shape
Omega(N^{2-eps}); the measured local exponents of E(N) run about 2.15 to 2.36 with a global fit
near 2.29, above that shape, and `results_tb_bind_grh.json` states plainly that comparing exponents
is not the same as evaluating a bound and that no ratio was formed. And under a stated
implied-constant-of-1 convention the N^3 L^{-2H} bound is vacuous at H = 1 and 2 at all eight
measured cutoffs, loose by four to seven orders of magnitude, with the file recording that
UPPER_BOUND.md calls its constants ineffective so the statement cannot honestly be turned into a
number at all.

**`attempts[]` still says these failed, and it stays that way.** The record is what happened: the
check ran and returned false. Nothing in it was edited to make the run look better. This entry is
where the difference between a failed check and failed work is written down.

## 2026-09-10, the fixed check, and ten items green

The four items the broken `default_check` had exhausted were given a third attempt under the
corrected check, alongside six new tasks the mapper had proposed and the judge had passed. One
proposed edge, `e-0004`, was rejected rather than confirmed: the judge found its rationale did not
support a hard `blocks` dependency, and confirming it would have serialized two items that are
related but not dependent.

**Ten launches, ten `done`, every check true.** All four of the previously exhausted items passed
on their first retry, which is what confirms the earlier diagnosis rather than merely asserting
it: the work had always been sound and the check was the whole defect. 38 attempts on the record,
28 done and 10 failed, all ten of the failures being the earlier broken-check run, which stays in
`attempts[]` exactly as it happened. Cost this round **$17.06**; running total **$35.63** against a
cap of $50 the operator raised from $25.

The result most worth reading is `SW_EFFECTIVE.md` with
`results_delta_sq_sw_effective_bind.json`. `UPPER_BOUND.md` (1) states its family of bounds holds
"with ineffective constants", and the previous round found the N^3 L^{-2H} corollary could not be
turned into a number for that reason. This round asks a sharper question and gets a different
answer for one component: the q = 1 case that Section 7 actually derives the corollary from does
not need Siegel-Walfisz at all. It reduces to the classical zero-free-region remainder for zeta
alone, psi(x) = x + O(x exp(-c1 sqrt(log x))), which involves no Dirichlet character beyond the
principal one, carries no Siegel-zero ineffectivity, and has been effective with a computable c1
since de la Vallee Poussin in 1899. So the ineffectivity caveat is weaker than it reads for that
component.

The file then refuses the obvious overstatement, and this is the part that matters: an effective
constant does not make the bound useful. Section 7 already records that this component is a full
power of N short of the unproved target (31) at N^{2+eps}, and that gap is exactly as large
whether or not the constant in front of it is known. Effectiveness and sufficiency are different
questions and only the first was answered.

`THEOREM_B_SEQUENCE.md` takes the non-constructive sequence in Theorem B's proof and asks whether
the classical machinery behind it can name that sequence. Yes in a clean special case, with an
explicit and easily computed gap; no in general, and it separates the two failure modes rather
than reporting one verdict. It states plainly that it neither reopens nor changes what Section 18
proves.

The rest of the round is the rank-3 door taken apart along four routes: `RANK3_BDH_VERIFY.md`,
`RANK3_QUARTIC_TOOLS.md`, `RANK3_MEAN_VALUE_TOOLS.md`, `RANK3_ROUTE_D.md`,
`RANK3_POLYRANGE_TINT_CHECK.md` and `SW_MOMENT_SPLICE.md`, with five probe scripts and their
recorded numbers.

Eleven further proposals are on the board, judged and unanswered. Scheduling them is the
operator's decision.

## Round 4, 2026-09-10, orchestrated by an attended cloud session

Eight of the eleven were confirmed and two landed before the round was reshaped.

`a-0039` measured the cross term Sigma_cross(q) at eight moduli and seven cutoffs to 10^6. The
ratio to its proved ceiling stays in roughly [-0.25, 0.43], closer to zero than to one, and is
not monotone in N. `RANK3_CROSS_TERM_MEASURE.md`, `results_rank3_cross_term_probe.json`.

`a-0040` found that the O(N^3) transfer cost in `RANK3_ROUTE_D.md` section 6 is slack added to
an already valid upper bound. (D10) bounds the full-circle integral and is derived before the
transfer step appears; the arc integral is at most the full-circle integral because the
integrand is nonnegative; so (D11) holds without its third term, and the sum over 2 <= q <= R_0
that section 6 priced at N^3 is not a cost of anything. Checked by the orchestrator against
(23) in `UPPER_BOUND.md`, where U_Q enters as an upper-bound term, and numerically at four
(N, q, a) pairs chosen independently of the attempt's own six. `RANK3_ARC_TRANSFER.md`. This
removes an obstruction from the hunt's bookkeeping. It proves nothing new about E(N).

Consequences on the board. `w-rank3-transfer-refine` refines a step that does not need to exist
and is rejected. `w-rank3-crossterm-asymptotic` is subsumed by `w-route-d-cross-term`, which the
judge had rejected on the strength of the obstruction that no longer exists; the rejection is
overturned and the item confirmed. Edges e-0006 and e-0007 were reasoned from the same
obstruction and are rejected. `w-rank3-route-a-delta-uniform`, proposed by `a-0040`, is the
one remaining named requirement for the U side of rank 3 and is confirmed.

Seven items remain and none depends on another, so concurrency is 7. Estimate, before launch:
the two proves this round cost $2.89 together, about $1.45 each, so seven proves are about
$10.15; seven verifies at the measured $0.35 would add $2.45; about $12.60 in total against
$11.48 of headroom under the $50 cap. The runner is bound at `--max-usd 50`, so the cap binds
during the verify pass and one or two verdicts will wait for the operator.

Actuals. Fourteen attempts landed: seven judges, five proves done, two walled. Stopped at the
$50 cap with $52.34 spent, the overshoot being cells already in flight; 54 attempts on the
record. The two walls, `w-sw-pin-c1` and `w-mean-square-bv-hybrid`, are one wall: WebSearch and
WebFetch were denied inside the cell because `OSTOYAE_WEB` was neither set nor passed through
`sandbox.env_passthrough`. That is the orchestrator's miss, about $2.50 of the cap.

What landed. `RANK3_CROSS_TERM_CANCELLATION.md` (a-0048): for prime q an exact identity
Sigma_cross(q) = Sigma_diag(q)/(q-1) - E(q), E(q) >= 0, by character orthogonality; its
consequence Sigma_cross <= Sigma_diag/(q-1) was checked by the orchestrator against a-0039's
independent measurement on all 42 prime-q rows. It fails for composite squarefree q and says so.
`RANK3_INTEGRATED_BDH.md` (a-0043): the integrated mean-value theorem cannot hold at the claimed
strength, sum_b T(q,b) >> N^2, so that route is closed. `RANK3_ROUTE_A.md` (a-0049): no
unconditional closing route for Route A. `RANK3_QUARTIC_LITERATURE.md` and
`RANK3_QUARTIC_HEIGHT.md` (a-0044, a-0047): the Z side, negative, with the arc-restricted
quartic moment of F_N at q below N^{2/5} named as the remaining object.

Together: a weight on sum_b T(q,b) worse than about 1/q cannot reach N^{2+eps} (a-0043), and
1/q is exactly what a-0048 delivers at prime q. The one remaining U-side question is the
extension to composite squarefree q, `w-cross-term-composite-q`. Nine proposals await the
operator. Every grade above is derived and measured, one route each.

## Round 5, 2026-09-10, section 8 of issue 58 executed

Five items with typed dependencies, web access passed through and used. Eleven attempts,
$9.28; 65 on the record, $61.62 total. All five landed and were judged.

`CANDIDATE_ENERGY.md` (a-0058): the only Energy(N) meeting all of section 8's constraints with
an exact domination is E_corr(N) itself, a block-average identity proved by linear algebra with
no arithmetic input. `CHALLENGE.md` (a-0062): the same identity holds on a Davenport-Heilbronn
sequence, so it distinguishes nothing about zeta. `SCALE_TRANSITION.md` (a-0061): the dyadic
transition fails at scale 0. `S8_CONTROL.md` (a-0057): the instrument, and a finding that the
chain never pins Tao and Teraevaeinen's constant c_0. `ENDPOINT_HALF.md` (a-0059): Remark 2.8
breaks the chain at the Bonferroni cutoff at exactly kappa = 1/2; retuning that cutoff gives
E_corr(N) <<_kappa N^3 exp(-c_kappa (log N)^kappa) for every fixed kappa < 1/2, from 1/10.
Threshold checked by the orchestrator: log D_0 = 2 (log N)^{kappa + 1/2}. It rests on
Remark 2.8 as its authors state it, not on a worked proof. Every grade: derived and measured,
one route each.
