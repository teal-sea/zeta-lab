# `hunts/`: exploratory studies

A **hunt** is an exploratory study: a scoped directory where an agent or a
person pursues one specific idea, with the understanding that most such
ideas fail.

`hunts/` is the one place in this repository where a claim can be written
down before any control has been run against it. So the classification is
explicit:

> **A hunt is exploratory. Nothing in `hunts/` is a result, not a result,
> and not evidence.**

Per `harness/README.md`, the admission rule for a *department* is
**no department without a battery**, work whose claims nothing in this tree can
falsify is not a department; it is exploratory, and exploratory work belongs
where nobody will mistake it for a result. That place is here.

A hunt can never become a department by growing, for the reason `ROADMAP.md`
records for `dossier/`: a hunt's negative controls are the *zeta*
department's, and a department whose battery belongs to another department
is not a department. A hunt borrows the zeta battery. That is the correct
relationship, not a deficiency, but the battery does have to actually be
invoked.

## What a hunt may and may not do

| May | May not |
|---|---|
| build its own instruments under `hunts/<name>/` | modify `zeta/`, `ontology/` or `harness/` without explicit permission |
| record raw measurements in its own `results*.json` | write a verdict into `README.md`, `ROADMAP.md` or `HANDOFF.md` as an established finding |
| use the word *measured*, *observed*, *consistent with* | use *certified*, which `zeta/rigor.py` owns |
| propose a candidate for the funnel or the battery | promote its own claim |

A hunt that wants its claim to count takes it through the battery
(`docs/doors/refute.md`) or the funnel (`docs/doors/discover.md`). Those are
the two routes that can say "yes", and neither of them is the hunt itself.

**Methods travel even when claims do not.** An identity, lemma, control or
technique a hunt produces goes in `docs/37-methods.md`, the cross-hunt methods
index, in the same change that records it here. Check that index before
building an instrument; several hunts have hand-rolled the same one.

## HuntSpec (new hunts, from 2026-08-11)

A hunt opened after 2026-08-11 carries a **HuntSpec**, a fenced contract
block in its `MISSION.md` stating the question, the frontier, the dead
routes, the non-model oracles allowed to assign truth, the kill conditions,
and what its agents may and may not do. Format, rules and the validated
template: `hunts/HUNTSPEC.md`. Existing hunts are not retrofitted;
`tests/test_huntspec.py` validates any block that exists. The primitive is
on probation, see the spec page's terms.

## The standing checklist

Before a hunt's finding leaves `hunts/`, it must have survived the four
control roles, and the checks are the ones the tree already owns:

1. **Rival.** Does the claim also hold for a function that shares the
   structure and violates RH? `zeta.epstein.battery`. Note the trap below:
   if your test set *is* the rival set, you have measured your own selection
   criterion.
2. **Decoy / surrogate.** Does a matched null with no arithmetic in it
   reproduce the effect? `zeta.surrogate`, `NULLCONTROLS.md`. `ROADMAP.md`
   records the calibration that matters here: against a null of random
   non-factoring sequences, Davenport–Heilbronn sits at the **27th
   percentile**, typical, not exotic. Anything claiming a factorization
   effect must beat that null.
3. **Lesion.** Does the detector notice a violation planted on purpose, and
   can it tell that planted violation apart from the claimed signal? If it
   cannot, the detector is measuring the plant.
4. **Precision response.** Does the effect move when the approximation
   improves? `ROADMAP.md`'s standing rule, earned three times: **an artifact
   does not respond to added precision; a real quantity does.**

## Case log

### Hunt #153: Requirement A as a static provenance scan (`ontology_provenance/`, 2026-10-24)

**Status: measured, static scan, no claim promoted.** A name and import-graph
scan of whether a proposed frame reaches a zero-derived name (`docs/09` section
5.1, Requirement A). It is a floor, not a proof that a clean frame is
prime-derived. Of the fifteen numbered ontology frames, the scan flags five
files as reaching a zero-derived name. Reading those files: two construct from
zeros (03, 08); two build from primes and mention zeros only as a printed
comparison (05, 06); one compares GUE spacings with zero spacings (11). Frame
07 imports only `dh_coefficient` and is clean at symbol granularity. Nothing
here is evidence for RH. Record: `ontology_provenance/MISSION.md`,
`ontology_provenance/RESULTS.md`. The same change records an additional defect
in `factorization_vs_position/DIAGNOSIS.md`, independent of the Hunt #2
withdrawal: the kappa scanner's output is `(1 + 0.284079*kappa)` times one
fixed function, so its sign changes cannot depend on kappa.

### Hunt #146: the out-of-band reduction priced at the Davenport-Heilbronn line (`weil_dh_line/`, 2026-10-21)

**Status: open, on a draft pull request; resumed in place on 2026-10-26 by the owner's
decision. No-go at the gate for the searched envelopes (attempt unresolved, measured);
K2 on DH at the DH line run on 2026-10-26 (streamed): the pipeline refuses at every
checkpoint to `T# = 800`, so the binding kill condition did not fire (measured, stage A only).** Asks whether zeta's Weil window
positivity can be proved with enclosures on a window where the Davenport-Heilbronn form is
provably negative, half-width `L >= (log 30.617188)/2 = 1.7107808`, through the out-of-band
reduction of `oob_envelope/`. The comb floor `S*_L` at `L_DH` lies in `[5.637302, 5.643859]`
(hardened), so weak duality allows the gate `S <= about 6.2`; the best evaluable joint
envelope found gives `6.418111`, and the best partition into three-prime clusters has the
Arb floor `6.174396`. A measured stage-A scout at `L = 7/5` (envelope `S = 4.117981`) has
negative pivots at `T# = 400` to `440` and none from `460` to `640`, stable under the mode
and precision responses. K2 refuses Epstein `(1,1,6)` wherever its form is known negative,
and DH at `L_DH` (`N = 856`, 1280 bits): one negative pivot at all 14 checkpoints with
`beta* > 0`, `lambda_min` about `-5e-30` and shrinking in magnitude as `T#` grows.
Nothing here is kernel-checked, no novelty is claimed, and nothing bears on RH. Record:
`weil_dh_line/PRICE.md`, `weil_dh_line/RUNS.md`, `weil_dh_line/MISSION.md`.
**Raised 2026-10-27 (dated addition; the entry above is left as written).** The
`T# -> infinity` limit of the stage-A block, the DH form on the scout's even Legendre
modes, has a negative eigenvalue on every leading block of 101 or more modes (`-1.943e-30`
at 856; hardened, resting on enclosed Rayleigh quotients; a reviewer's separate
implementation reproduces them). So the stage-A block refuses DH at `L_DH` at every `T#`
and every `N >= 101` when `S` is valid (the composite is measured at that assumption,
through two unreviewed derivations). The `T# = 800` eigenvector itself is not a witness,
and K2 at `T# = 800` keeps its verdict with `S` understated by up to 43, so it does not
test `S`. The responses called "mode and precision responses" above are not refinements
(`PRICE.md` items 5 to 7).
Later the same day `S` itself was bounded in Arb (`sup(P_DH - H) <= S + 34/5`), which
lies inside the witness's margin for `T# >= 540` and `N >= 856`: there every numerical
step is enclosed, and the refusal rests on two unreviewed derivations (`PRICE.md` item 7,
link 6).

### Hunt #145: the Davenport-Heilbronn zero off the critical line, kernel-checked (`rung3_ball_production/`, 2026-10-21 to 2026-10-26)

**Status: closed 2026-10-26. `dh_separation_hundred` (below height 100, `DH` has a zero
in the open strip off the line and `riemannZeta` has none, from hunt #137's RH to height
100) and `dh_zero_located` (a zero of `DH` in the plan's closed square), read with
`dh_analytic_half`, are kernel-checked (Lean v4.35.0-rc2, Mathlib 065356127b1d, zero
`sorry`, only `propext`, `Classical.choice` and `Quot.sound`), pending external
verification. The assembly's `davenport_heilbronn : davenport_heilbronn_statement` is
weaker: the statement, as defined, is also met by the trivial zero s = -1
(`lean/ZetaLean/DHTrivialZero.lean`, found by the PR #353 review). Original;
searched-and-absent in `PRIOR_ART.md`, not a novelty claim; nothing here bears on RH.**
`RESULTS.md` states the theorems as compiled. *Added 2026-10-26:* one theorem now carries
the strip result, `davenport_heilbronn_strip` (an entire function with the
Davenport-Heilbronn series and functional equation has a zero s with 0 < Re s < 1 and
Re s ≠ 1/2, witness `DH`), in an emitted module outside the sites' import closure,
compiled by a second on-box assembly of the same 215 site oleans with the same three
axioms (`RESULTS.md` section 1 and door 2). *Added 2026-10-27:* Lean's own kernel replayed
the whole assembled closure into an empty environment and accepted it, and the independent
checker `con-ron --verified` accepted it split into 216 shards on cloud VMs, with coverage
shown (door 1, Stages A and B); the grade stays kernel-checked, pending external
verification. *2026-10-21 status, superseded:* open ledger
hunt; a pilot on one shared box in one session, measured; the pilot site's two theorems
kernel-checked and its planted faults refused; no production shard launched;
`davenport_heilbronn` unproved, and no file emitted the assembly module that would prove
it; nothing promoted; no novelty claimed. The `rung3-pilot` lane of the campaign
the owner directed on 2026-10-21 (route 3). The task proposed #138; the launching workflow
reserved #138 to #144 for landings it is renumbering and assigned #145. Lean `v4.35.0-rc2`
against Mathlib `065356127b1d`, fetched fresh into the worktree's own `lean/.lake` (nine
packages, each its own git toplevel at its manifest revision), with the 15 `ZetaLean`
modules the certificate imports built from source. `scripts/72` is `main`'s: the two fixes
this lane first cherry-picked landed in PR #323 with a resume fix (`571857a47`), the
branch merged `origin/main`, and `tests/test_rung3_ball_compile.py` passes (22). On the
swarm box (32 vCPU Haswell, shared with other workflows; the 1-minute load ran from about
30 to 160 during the session), `B_right_06` (K = 17: 23 prime towers, 48 composites, 10
modules) was generated by `scripts/60 --arith ball --shard --only B_right_06` and compiled
by `scripts/72 --jobs 1 --module-jobs 1`: every module exit 0, and `upper_B_right_06` and
`enc_B_right_06` print only `propext`, `Classical.choice` and `Quot.sound`. Planted in
copies: a prime-tower radius one unit of 2^-64 low, the tail radius just under its bound
and `M` just under the enclosure's bound are each refused at the named declaration, with
only the touched module recompiled; eps' in the centre theorem's last step (the enclosure
taken as a hypothesis, the centre itself not compiled) is accepted at 1/2000 and at the
next multiple of 2^-64 above the bound, and refused at the bound and at 1/4000. The
kernel-accepted `B` literal equals `scripts/65`'s ball once 1^(-s) is seeded as the exact
ball (1, 0, 0), as the generator does; `scripts/65`'s own figure is wider by exactly
738083614955/2^64, so the mirror is conservative here. A first attempt, interrupted
mid-site when its session ended, is kept as a replay check: its four compiled modules have
this run's sources byte for byte, and their CPU agrees within the spread `PILOT.md` shows.
Costs, net of import: 2.09 CPU-s per tower atom for `scripts/68`'s p = 2 tower and 2.42 in
the site's five prime shards, against the 1.2504 that `scripts/67` records from
`v4.33.0-rc2` on a machine the record does not name; 0.674 per composite in the site
against 0.55; about 10 CPU-s to import the certificate's support modules; peak RSS 7.8 GiB
per process, at most 1.9 GiB of it anonymous. Projected to the 215 sites: 350 to 416
core-hours (towers priced flat or per byte of their text; the flat price is the better
supported, since a p = 1801 tower cost close to what a p = 2 tower does with three times
the text, but the request keeps the larger by a rule recorded before that run;
`scripts/67` records 175.0 atom-only), so 13 hours of wall clock at 24 processes on this
box if it were free, and 26 hours at 16 processes holding one core each. What binds, in
`OWNER_MEMO.md`: CPU on a shared box; 123 to 146 GB of oleans against 24 GB free on its
disk; and an assembly that, as the sites are generated today, would import all of them, at
the pilot's 0.66 bytes of RSS per olean byte 81 to 96 GB in one process (untested). The
memo asks for a production window and launches nothing. No method here meets the bar of
`docs/37`.

*Resumed 2026-10-26 by the owner's decision, which granted the production window on cloud
compute; production waits for funding and none was launched.* Measured, one process:
proving a prime tower through one `decide +kernel` of the whole `dirichletTermBallB`
value plus `contains_dirichletTermBallB` cost 3.4 CPU-s net at p = 2 and 5.3 at p = 1801
on a box ball. That meets the threshold of 10 recorded in advance. The staged tower with
`decide +kernel` in place of `norm_num` did not meet it (43.4 CPU-s, against 66.1 under
`norm_num`). Both planted one-unit faults were refused. Extrapolated, production with
whole-decision towers comes to 50 to 58 core-hours instead of 416, which needs a change to
`scripts/69` outside this hunt. `assembly.py` emits the module that would prove
`davenport_heilbronn` from the 215 site theorems, with a located zero and a separation
lemma against hunt #137's RH to height 100. Its body elaborated against 214 stub site
interfaces and `B_right_06`'s real oleans, and rests only on the standard axioms and the
stubs; `davenport_heilbronn` stays unproved. `PRODUCTION.md` is the runbook.
In a follow-up the same day, under a scope extension from the coordinator,
`scripts/60`/`69` gained an opt-in `--tower whole` mode; the default output is
byte-identical. The pilot site recompiled in it end to end (measured): 163.6 CPU-s and
16.8 MB of oleans, against 1,861 CPU-s and 180 MB staged. Two one-unit tower faults were
refused. Extrapolated from that site, production comes to 29.8 core-hours and 14.8 to
16.0 GB of oleans, with an assembly import of about 17 to 18 GB of RSS. On those
projections the sites fit GitHub Actions shards and the assembly fits one 32 GB machine.
*Closed the same day.* The whole-mode tower namespaces were first site-qualified
(`Prime_<sid>_<p>`), because two site roots could not be imported together; the staged
default keeps that collision by ruling. `.github/workflows/rung3-production.yml` then
compiled all 215 sites on GitHub Actions (run 40353536947: 215/215 sites, every site
theorem on the three standard axioms, 16.1 runner core-hours, 15.1 GB of oleans). Its fault
job left no verdict (GitHub's `bash -e`), and after the fix the fault ran alone (run
40372531479: refused at `Prime_B_right_06_2.ev_whole`). The pair counts. On this box, from
oleans on `/dev/shm` with every zip checked against GitHub's digest, the assembly compiled
(85.3 CPU-s, 17.87 GB peak), and so did the separation against `RHHeight100.rh_height_hundred`.
All 17 final declarations print only the three standard axioms. Four planted faults on
production output were refused: the tower radius at `ev_whole`, the tail radius at `enc_`,
M at `upper_`, and eps' at and below the bound in `centre_lt_centre`. No independent
kernel replay of the assembled environment has run yet; that is the first door.

### Hunt #138: complete Mobius orbits at fixed P change the majorant's constant, not its order (`mobius_orbits/`, 2026-09-26)

**Status: ordinary argument with an independent model challenge (a model review, not human
review) and exact finite checks at the stated scope. The fixed-prime route is an unresolved
attempt and the energy continuation was paused by allocation on 2026-09-27; neither is a
refutation, RH is unresolved, and no novelty is claimed.** The hunt takes up, in a scoped
form, the multi-prime mechanisms that `prime_pair_error/MOBIUS_PAIRING.md` left
unconstrained. For a fixed squarefree P, writing a=dm with d|P and gcd(m,P)=1 regroups each
Sigma2 row exactly by orbits and keeps every incomplete orbit; a complete orbit has the
fixed-sign kernel K_m=-Phi_P(floor(N/(mb))), so the oscillation left is mu(m) alone. A
separate Mertens level-set identity rewrites each row exactly, and a transfer bound prices
it by a Mertens envelope with no unpriced floor jumps. The specified absolute-value
majorant, which discards |mu(m)|<=1, has leading constant (phi(P)/P)^2/48 at fixed P
(1/192, 1/432, 1/675 and 4/3675 at P=2, 6, 30 and 210) and the same N(log N)^3 order. Under
`ALIGNMENT.md` section 5 that is category 3, an attempt that did not establish the needed
statement, and it obstructs neither a signed estimate nor a growing-P construction. Exact
integer and rational checks cover 1196 (N,P) cases and 8412 b-rows (N=4..300, 1000 and
10000) with zero defect, a trial-division check of the Mobius sieve, and two planted faults
(a dropped boundary, a reversed complete-orbit sign), both caught; at P=210, N=10000 there
is no complete orbit and all of Sigma2 is boundary. The owner-directed continuation
(`ENERGY.md`) moves to the Baez-Duarte criterion, where the squared error E_N is
nonincreasing by standard approximation geometry. It adds a Schur-complement block
identity, a compensated one-direction update along the predeclared Mobius shell
v_n=-mu(n)log(2N/n), and a residual-matched fallback whose gain is at least M_N/T_N under
the trace cap T_N<(log(2pi)-gamma)log 2. These pass Arb ball checks at N=4, 8, 16, 32 and 64
at 128 and 192 bits, conditional on Vasyunin's published Gram formula, with an mpmath
cross-check at N=4. The inequality that would finish the route, `ENERGY.md` (7) or the
weaker (12), is unproved, and the normalized trace values behind (12) fall from 4.28 to
0.243 over the five shells. The pause is category 4: no new uniform estimate toward RH was
established, and it refutes neither the identities nor the Nyman-Beurling method.
`REVIEW.md` and `ENERGY_REVIEW.md` are separate-context model reviews of the written
mathematics, not of the code. Cited: Baez-Duarte math/0202141v2, Vasyunin's formula, and
Bettin-Conrey-Farmer arXiv:1211.5191, which assumes RH and so is not an input. No
literature search for novelty was run.

**Landed 2026-10-21.** From the local branch `iris/rh-mobius-orbits-sep26` (three commits of
2026-09-26 and 2026-09-27, tip `16aff65f8`, base `8941a80`), merged whole and not rewritten.
Its entry carried no number; #138 was the next free one, with #136 and #137 held by hunts on
open branches. Four landing changes, none of them to a claim: the status above replaces the
branch's, which predated the pause; the doors section of `RESULTS.md` was 97 words with no
active-constraint part, which `tests/test_hunt_doors.py` refuses, and is completed by a
dated addition below the original bullets; `energy_test.py` is now `test_energy.py`,
because the nightly `scripts/run_hunt_tests.py` collects only `test_*.py` and would never
have run its 8 tests (the commands in `ENERGY_RUNS.md` stay as run, with a dated note); and
the methods are indexed in `docs/37` (two identities, a construction, a control). On
landing the hunt's 20 tests passed, and the two probes regenerated `results.json`,
`pilot.json` and `energy_reviewed.json` identically apart from timing and reproduced every
field of the two pre-review energy files. Landing promotes none of the hunt's claims.

### Hunt #133: at least ten kernel-checked zeros of zeta on the critical line below height 50 (`hardy_ten_zeros/`, 2026-10-14)

**Status: the target theorem compiles; a hunt result, not yet reviewed or landed.**
`HardyTenZeros.ten_zeros_on_line_below_fifty : ∃ ts : Fin 10 → ℝ, StrictMono ts ∧ ∀ k,
0 < ts k ∧ ts k < 50 ∧ riemannZeta (1/2 + ts k * I) = 0`, assembled from hunt #132's
`first_zero_on_line` and nine new interval theorems `zero_in_<tag>`, one per two-decimal
interval around the ordinates `21.02`, `25.01`, `30.42`, `32.93`, `37.58`, `40.91`, `43.32`,
`48.00`, `49.77`; Lean `v4.35.0-rc2` against the pinned Mathlib, zero sorrys, no
`native_decide`, twenty axiom reports `propext`, `Classical.choice`, `Quot.sound`, every
dependency rebuilt from this commit's sources. It says at least ten zeros, not which ones:
no zero count, no claim of one zero per interval. The three obstacles were sized first.
Hunt #132's phase window has a `2K delta` term and leaves the quarter turn from the fourth
bracket on (`-6.19` at `49.77`, proved below `-pi/2` there); dropping the first eight
Euler-limit factors gives a window that no longer grows with the height (`[-0.089, 0.04]`
for every bracket of width `1/100` below 50). The order-4 remainder of hunt #132 is used
unchanged at any truncation, with an exact squared norm; truncations are chosen per
endpoint, 684 term boxes in all (order 6 would need 334, order 8 246; order 4 was kept,
since a new Euler-Maclaurin development would save under five kernel minutes per build).
Only primes get an exp tower; composites are coarsened products of their factors' boxes
(the lab's `contains_cpow_mul_coarsen`), 219 towers and 447 products. One generated file
per bracket: 692 s of kernel time for all nine, against 11.2 minutes projected before it
was spent. The remainder bound sits 6.85 to 14.94 times above the defect Arb encloses;
doubling the radii fails every bracket; planted faults (a changed digit, a wrong
factorization, a halved radius, doubled radii) are refused by the kernel, which proves
their negations. Prior art: no formal localization of several explicit nontrivial zeros
in the searched set (arXiv and zbMATH Open APIs, web), beyond hunt #132's one. Not a
novelty claim. `.github/workflows/hardy-ten-zeros.yml` rebuilds it and audits the axioms
fail-closed. Landing in `lean/ZetaLean/` is the owner's call. Nothing bears on RH
(`docs/08`).

### Hunt #132: a kernel-checked zero of zeta on the critical line between 14.13 and 14.14 (`hardy_first_zero/`, 2026-10-11)

**Status: the target theorem compiles; a hunt result, not yet reviewed or landed.**
`HardyFirstZero.first_zero_on_line : ∃ t ∈ Set.Ioo (1413/100 : ℝ) (707/50), riemannZeta
(1/2 + t * I) = 0`, Lean `v4.35.0-rc2` against the pinned Mathlib, zero sorrys, no
`native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound`; the four `ZetaLean`
modules it imports rebuilt from this commit's sources (`lean/build.sh`, 4 min 14 s). The
owner-approved goal was a sign change of `hardyZReal` (`lean/ZetaLean/HardyZ.lean`, accepted
into Mathlib) plus the intermediate value theorem; the pinned Mathlib has no representation
of `riemannZeta` on the line with an error bound, no Euler-Maclaurin, no complex Stirling
and no digamma bound, so four pieces were built. A sign test that needs no value of the
Riemann-Siegel phase: `Re(zeta_a conj zeta_b) < 0` plus a quarter-turn bound on the phase
of `Gammaℝ`. That bound, from Euler's limit `GammaSeq -> Gamma` with each approximant in
polar form (window `[-0.5045, 0.0357]` against a true increment of `-0.00405`). The
order-4 Euler-Maclaurin representation of `riemannZeta` on `Re s > 0, Im s > 0` with an
explicit remainder, by a quartic-kernel corrected trapezoid and the identity theorem. And
30 terms per endpoint (the lab's order-2 trapezoid would need 471) enclosed by the lab's
`dirichletTermBox2`, written as literals from its bit-exact mirror and each checked by
`decide +kernel`: 120 kernel decisions in 2 min 48 s, where one decision over the whole sum
did not finish in 30 minutes. The remainder bound holds against Arb with a factor about
4.7 to spare; planted faults (a 3% change in the remainder constant, one digit of one box)
go red in the tests and in the kernel. Prior art: no formal localization of an explicit
nontrivial zero in the searched set (arXiv and zbMATH Open APIs, the AFP topic lists,
web); the nearest are Alpöge and Furman's Lean proportion theorem and Eberl's Isabelle zeta
and Euler-Maclaurin entries. Not a novelty claim. Landing in `lean/ZetaLean/` is the owner's
call. Nothing bears on RH (`docs/08`).

### Hunt #131: what happens to a claim after it is recorded (`claim_halflife/`, 2026-09-10)

**Status: partly settled; one headline withdrawn by its own control.** Not mathematics: a
measurement of this laboratory, and it trades against nothing mathematical. 95 case-log entries
frozen at `2da62eb`. One recorded claim in five is named by any test; of the 25 (hunt, test) pairs
that can be scored, 19 defend at least one number against a 10% mutation and 8 are byte-pinned;
23.2% of entries were never touched again. Of 73 strict revisions, **one** installed a test in the
same commit, against a doctrine in which every `HANDOFF.md` record carries a `Now caught by:` field.
Median latency from a hunt's first commit to a revision of its own claim files is one day.
**The correction rate itself is withdrawn**: a blind hand audit of 30 stratified rows agreed with the
classifier on 16, precision 0.40, which is close enough to chance that no rate can be reported. It
named two structural defects, both repaired, and re-scoring against the same rows reaches 21 of 30,
which is fitted rather than measured; a disjoint sample is with a second blind audit. The container's
default shallow clone hid three quarters of the history and would have reported 30.5% never revisited
instead of 23.2%. `tests.yml` and `full.yml` still check out shallow, which `HANDOFF.md` recorded in
August as the fix that was prepared and not landed. Nothing bears on RH (`docs/08`).

**Renumbered on landing, 2026-10-10.** Opened on the unmerged branch
`claude/repo-hunt-content-2smbid` as #122, with its front door numbered 40. On main #122 is
`dh_minus_landing` and 40 is the page on one form per discriminant; #127 to #130 are
`euler_defect_axis`, `li_dh_onset` (#298), `epstein_height` (#299) and `quotient_exponent` (#300),
so this is #131 and the front door is `docs/43`. The entry above is the branch's text with the
number changed; it was written before the second blind audit returned.

**Checked on landing, 2026-10-10.** Every script was re-run against the history frozen at
`2da62eb`, and `test_claim_halflife.py` (15 tests, seconds, every git call bounded at that commit,
skipping on a shallow clone) re-derives the corpus, both classifiers on all 414 later commits, the
pinning, the depth table and both blind-audit scores: all byte for byte. The three planted-fault
ladders reproduce in a scratch worktree at that commit once its state matches the one they first
ran in; the re-run found that the null rung never runs the untouched tree, so a test red for an
unrelated reason scores as byte-pinned, which the recorded eight (each computes a hash) escape.
Since the entry above:
the second blind audit agreed on 22 of 30 (precision 0.67, recall 0.77), so `RESULTS.md` reports
the rate it withdrew here as `15.3%` (73 of 414 later commits flagged, scaled by precision over
recall), worth one significant figure; and #287 gave `tests.yml` and `full.yml` `fetch-depth: 0` on
2026-10-09. Two statements did not reproduce and are marked where they are stated: at `2da62eb`
only 3 of `HANDOFF.md`'s 24 records carry a `Now caught by` line (the header states the format,
which is the doctrine), and the "nineteen of the seventy-three revisions" in the doors is derived by
nothing in the hunt. The public-record question was considered on landing: this measures how the
public record's own claims are guarded and corrected, which an outside reader evaluating them would
want, and it is a negative result about the lab's tooling, which `AGENTS.md` keeps here. Two
methods are listed as seen and not admitted in `docs/37`.

### Hunt #130: the barrier law is not the shape the diagonal suggested (`quotient_exponent/`, 2026-09-10)

**Status: measurement stands, headline withdrawn by its own audit.** The first write-up said the
conjectured shape `E >= c N/sqrt(y)` "is not the shape of `T*`". It is: `BARRIER.md` states the
conjecture with a moving constant, and fitted that way the conjectured exponents give rms `0.1198`
on 20 grid rows against the free three-parameter fit's `0.1258`, with one parameter fewer. Every
measured point satisfies `E >= 0.1704 N/sqrt(y)`; the only bite is that the published constant `0.2`
is 15% too large at the new `10^7` point. The stated reason for reformulating the programme was also
false: the factorial form returns the same optimum to `2.7e-14`. The factorial objective is a
difference of quantities near `1e8` whose answer is near `1e4`; written as `sum_q w_q e_q` over
attainable cells it is a sum of nonnegative terms equal to the excess itself, and that is why the
ladder reaches `10^7`. Reproduces the four published diagonal values to every printed digit and adds
`3 x 10^6` and `10^7`, where `T*/N^{3/4}` is `0.1704`, below the published `0.18 to 0.23` band.
On a `(y, N)` grid the quantity the conjectured shape says is constant falls by a factor 2.3 to 2.8
inside the conjecture's own range; the free fit is `a = 1.150, b = 0.878` against `(1, 0.5)`, and the
conjectured shape is three times worse on the grid while indistinguishable on the diagonal, where
three of four models agree to three decimal places. The excess is a staircase in `y`, holding
`9.406483` across sixteen consecutive supports at `N = 10^4` and reaching exactly zero at `y* = 173`,
`0.87` of the attainable-cell count, so the column count is neither sufficient (already refuted at
`N = 27, y = 9`) nor necessary. What survives and is new: the staircase, the zero threshold at `y* = 63, 173, 589, 1938` with
`alpha*` falling monotonically, and the finding that only 40, 99 and 275 of the 61, 198 and 630
attainable cells carry any prime mass, so what holds the excess up is the requirement `W >= 1` at
the cells with no weight at all. **Extended the same day** (`closed_form.py`): the plateau values are
exact rational multiples of a single logarithm, `(7/2) log 2` at `10^3`, `3 log 23` at `10^4` and
`6 log 113` at `10^5`, agreeing to `1e-14` or better, and the reason is that of the 14 to 181 cells
carrying excess at the optimum **exactly one has nonzero weight**, so the objective collapses to that
one cell's `Lambda`. The rationals are read off `e_q` and then compared, not fitted to `E`. At
`N = 10^6, y = 1995` the excess is `0.0` with 497 cells still carrying excess, every one weightless:
the programme never zeroes the constraint violation, it zeroes the *weighted* violation by parking
the rest where `Lambda` vanishes. The `10^6` plateau itself was not located, about 11 hours of solves,
and no value is claimed there. Front door: `docs/42`. Audit: `AUDIT.md`, fifteen attacks, four landed. Nothing bears on RH (`docs/08`).

**Renumbered on landing, 2026-10-10.** Opened on the unmerged branch
`claude/repo-hunt-content-2smbid` as #121, with its front door numbered 39. On main #121 is
`qrh_conditional` and 39 is the page on the quasi-Riemann theorem; #127 to #129 are
`euler_defect_axis`, `li_dh_onset` (#298) and `epstein_height` (#299), so this is #130 and the front
door is `docs/42`. The entry above is the branch's text with those two references changed.

**Checked on landing, 2026-10-10.** Every script was re-run and `test_quotient_exponent.py` (39 tests,
about a minute) re-solves or recomputes every number the result page and front door state; the LP
values reproduce to `1e-12` or better. The entry above was written partway through the audit's
corrections and keeps four figures `RESULTS.md` has since replaced: the free fit on the final 20 rows
is `a = 1.159, b = 0.874` (the `1.150, 0.878` came from an earlier row set the artifacts no longer
hold), the fall is a factor 2.1 to 2.8 once the `10^7` rows are in, "three times worse" is the
comparison the audit showed was not like for like, and "to every printed digit" is 14 and 15
significant digits against the source's 40-digit pins. Four figures on the result page did not
reproduce and are marked there: an identity-table entry (`1.6e-16`, not `0`, at `3 x 10^6`),
`alpha*`'s rate (0.016 per decade; 0.007 is per unit of natural log), the `10^5` plateau (538 to 588,
width 51; the stated 545 to 580 was the scan window) and two counts of excess-carrying cells (50 to
57 and 165 to 182 over every support, not 52 to 57 and 167 to 181 from three). The single weighted
cell now holds at every support of all three plateaus, and the zeros at `y*` have exact rational
witnesses, re-found by a route independent of the audit's. `RUNS.md`'s note that the `10^6` value
`123.83310675500282` has "no run behind it in this tree" is false: `threshold.json` and
`threshold.log` carry it, at four supports from 1812 to 1937. Three methods are listed as seen and
not admitted in `docs/37`.

### Hunt #129: the module that missed the guard the tree already had (`epstein_height/`, 2026-09-10)

**Status: settled, defect recorded, repair proposed and not applied, write-up corrected by its own
audit.** `zeta/heatflow.py` and `zeta/core.py` both already implement this kind of guard, and
`hunts/gate5_p6_b/probe.py` carries the Epstein constant as an executable rule, so the first
write-up's "the rule the core never learned" was wrong: the core has the pattern twice and
`zeta/epstein.py` is the module that did not get it. It still accepts any `dps`
and returns a silently wrong value above the height that precision supports: at `dps 15`
and height 120 the relative error is `2.3e+36`, measured against a direct lattice sum at
`Re s = 5` that shares no code with the routine. 158 cells of the surface in `artifacts/`.
The recorded constant plus a `sigma` term leaves a per-form bias of 1.6 digits, so the loss
was re-derived exactly as
`-log10 t + sigma log10 pi - log10|Gamma(s)| - log10|zeta_Q(s)|`, with no fitted constant:
the discriminant cancels, the size of `zeta_Q` is the missing term, per-form bias falls to
0.15, and one uniform offset of `+1.068` digits is left with rms `0.357` over 49 cells.
`guard.py` was the rule as code with six planted faults, all passing, **and an independent audit
walked straight through it**: a call at `dps 24` promising 4 digits returns `0.59`, because every
rung held the form fixed and so tested the leading term rather than the `-log10|zeta_Q|` term the
hunt had just derived. `guard2.py` carries the form and replaces the faults with a rung that tests
the contract, sampling the calls the guard ALLOWS and failing if any is short; its own first run
failed on a cell whose limit turned out to be the oracle, so the rung now measures its oracle too. It also answers the question
`hunts/dps_cap/reach_check.py` left open, whose two runs were stopped at 30 and 25 minutes:
measured at height 120 without running the recursion, at `dps 100` the acceptance rule takes
24 segments of 24, so the recursion costs one evaluation per segment, and at `dps 15` it
takes 7 of 24, `p = 0.292` against the `1/3` a uniform phase predicts, branching `1.417`,
about `6.4e6` evaluations for one segment. Because `_arg_variation`'s depth limit of 45
returns the principal value rather than raising, the cap cannot cost a refusal, only a wrong
count or a run that does not finish. Front door: `docs/41`. Issue #217.
Nothing bears on RH (`docs/08`).

**Renumbered on landing, 2026-10-10.** Opened on the unmerged branch
`claude/repo-hunt-content-2smbid` as #120, with its front door numbered 37. On main #120 is
`qrh_rival_step` and 37 is the methods index; #127 is `euler_defect_axis` and #128 is
`li_dh_onset` (#298), so this is #129 and the front door is `docs/41`. The entry above is the
branch's text with those two references changed.

**Overtaken, and checked, on landing, 2026-10-10.** Issue #217, which this hunt opened, was closed
by #291 on 2026-10-09: `epstein_zeta` now raises its own working precision by `ceil(0.6822 |t|)`
digits, the leading term only, and `tests/test_epstein_zeta_height.py` pins it. So "it still
accepts any `dps` and returns a silently wrong value" was true when written and is not true of the
current routine, which returns 16.1 to 16.5 correct digits (the comparison's float64 ceiling) on
every cell re-measured at `dps <= 30` up to height 160; `epstein_completed` itself still accepts
any `dps`. The tree's repair buys the digits silently rather than refusing, so `guard2.py` stays a
proposal for the refusal half, and `guard.py`'s own ladder now fails its second rung. Every number
above was re-measured against the routine as it was, restored by zeroing the lift: the 120-cell
grid and the 42 boundary cells came back identical, and `test_epstein_height.py` pins the surface,
both laws, the audit's counterexample (`0.59`, `39.90`, `44.07`), its critical-line attack
(`+4.66`, slow tier) and `why_it_hangs`. Four stated numbers did not reproduce and are marked where
stated: the first model's residuals by form (`+0.91 / +0.83 / -0.68`, not `+0.93 / +0.85 / -0.75`),
the rounding offset's range (0.86, not 0.87, to 1.15), the move from `1/t` to `|1/s|` (0.0008, not
0.002) and the oracle's conservatism (13 to 214, not 10 to 400). One method is admitted to
`docs/37` (the lattice oracle, now reused by `tests/test_epstein_zeta_height.py`) and three are
listed as seen and not admitted.

### Hunt #128: Li coefficients for the counterexample, and how far a computation can see (`li_dh_onset/`, 2026-09-10)

**Status: settled. Twelve controls, all passed, no kill condition fired.** Bombieri and Lagarias
make `lambda_n >= 0` for every `n` equivalent to every zero of the multiset lying on the critical
line, and the Davenport-Heilbronn function has a measured off-line pair, so some `lambda_n(DH)` is
negative. No `lambda_n(DH)` existed anywhere in this tree.

Computed unconditionally by the Cauchy route, never from a zero list, `n = 1` to `5000`, and
**every one is positive**, the minimum over the whole table being `lambda_1 = 0.09763614680951967118155`.
The analyticity radius was established first by the argument principle:
`sum_{n>=2}|a_n| n^{-2} = 0.26666394613` kills `Re s >= 2`, and the rectangles covering the
Apollonius discs of `r = 0.9` and `r = 0.95` hold zero zeros.

The controls are the result as much as the table is. The `xi` positive control reproduces the
committed `zeta.li` table to `4.4e-28` over all 400 indices; `lambda_n(DH)` is bit identical across
`r = 0.5, 0.7, 0.9` for `n <= 200` and across `r = 0.9, 0.95` for `n <= 2000`; the generating
function matches Li's literal `n`-th derivative definition to `4e-27`; and an independent zero-side
sum over 313 measured on-line ordinates plus 9 off-line quadruples below height 430 agrees to
`1.14e-8`, with argument-principle box counts matching line zeros plus two per quadruple exactly,
zero unaccounted, at `T = 100, 200, 300, 430`.

A background fitted to the measured coefficients gives slope `-0.32530` against the derived
conductor-5 value `-0.32561`, agreeing to `3.1e-4`. Feeding it and all fifteen known off-line
quadruples in puts **the first negative index at `n = 328997`**, identical under four background
variants, driven almost entirely by `R - 1 = 4.2006e-5` for the pair at `0.80852 + 85.69935i`,
which is measured to be the global maximiser: no other off-line zero below height 90, none with
`Re s >= 0.83` in `[90, 190]`, and the coefficient bound covers everything above `188.97`
automatically. Grade: measured inputs, extrapolated conclusion, sixty-six times past the largest
computed coefficient, and explicitly not a theorem. It sharpens `hunts/jensen_clock`'s hedged
`n ~ 3.3e5` by 1.2 per cent without reusing the indicator that page calls useless.

**The wall, priced.** At `n = 328997` the family needs about 1490 working digits and 670000 nodes,
roughly 20000 core-hours on this calibration, against every efficiency door together being worth a
factor of 5 to 10. The direct route cannot reach the onset. Its doors also found a defect outside
the hunt: `zeta.epstein.completed_dh` costs `0.58 s` per call at 142 digits against `0.092 s` for
the same mathematics with `kappa` cached once per process, a factor of six from a precision-keyed
`lru_cache` receiving a precision that varies with the distance from `s` to 1.

Nothing bears on RH (`docs/08`).

**Renumbered on landing, 2026-10-10.** Opened on the unmerged branch
`claude/repo-hunt-content-2smbid` as #123 (its `RUNS.md` still says so), and landed as #128
because main had since taken #123 to #126 and #127 is `euler_defect_axis` (#297). No front door.
The entry above is the branch's text with only the number changed; what the landing check found
is below rather than edited into it.

**Checked on landing, 2026-10-10.** `test_li_dh_onset.py` recomputes the first four
coefficients, the half-plane sum, both radius rectangles by the argument principle, the `xi`
control at `n <= 60`, the background fit, the onset scan with its sensitivity table and the cost
model, and checks the tables, the zero side and the dominance wedge against the artifacts, which
a scratch re-run of every script reproduced (`RUNS.md`). Three corrections to the entry above.
(1) "No `lambda_n(DH)` existed anywhere in this tree" is false: `scripts/18_dh_li_coefficients.py`
has computed `n <= 24` since 2026-08-05 (`docs/07` section 4), and agrees with this table to
better than `1e-12`; what is new is `n > 24`. (2) The "1.2 per cent" does not reproduce:
`jensen_clock` recorded `330342`, and `328997` is 0.41 per cent below it; 1.16 per cent is the gap
to this hunt's own zeta-shaped variant, `325229`. (3) Positivity is hardened only for `n <= 12`,
where the zero side shares no code with the Cauchy route; for `13 <= n <= 5000` it is measured,
with a radius-independence control, so the composite row is measured. (4) The `completed_dh`
"defect" does not reproduce as a per-call cost: warm, on the contour at 142 digits, it costs
`0.112 s` against `0.102 s`; the factor of six is the first call at each of two cached precisions,
1.7 to 1.9 s each. Six further stated numbers, five in the doors and one in `RUNS.md`, did not
reproduce and are marked where they are stated. Three methods are listed under "Seen and not
admitted" in `docs/37`.

### Hunt #127: one form per discriminant, not forty-one (`euler_defect_axis/`, 2026-09-10)

**Status: settled, correction; repair applied by #296.** The composite-line discriminator is
defined for a Dirichlet series with `a(1) = 1`, and a binary quadratic form represents 1 exactly
when it is the principal form of its class group. Measured over the 41 rows behind `docs/34`
table E7: `a(1)` is exactly 1 on the 14 principal forms and exactly 0 on the other 27. No
rescaling repairs them: none of the 27 represents only multiples of its least represented value.
The section's qualitative reading survives on the entitled rows and is checked there against
`c(n) = Lambda(n)(1 + chi_d(n))`, which uses no recursion, to `2.8e-30`. The published
non-principal numbers are not empty: they are exactly the composite defect of `1 + Z_Q(s)`,
agreeing to `0.0` on all 27 rows, a series with no functional equation. The corrected axis is 0
for class number one and `2.9608` to `5.0847` for the rest at cutoff 61, and `5.0196` to
`10.5748` at cutoff 401 with the ordering moving by one adjacent transposition, so **the axis has
no scale** and the family issue #93 proposes as "a defect axis from 0 to 36 with class number as
the knob" is neither. An independent adversarial audit (`AUDIT.md`) attacked the claim eight ways
without moving it and found eleven overclaims in the write-up, including a residual presented as
an independent oracle when `R = |1 - a(1)| max|c(n)|` identically. The repair in `PROPOSAL.md`
reached main through #296 on 2026-10-10, before the hunt did; its closing note records what #296
did differently. `test_euler_defect_axis.py` (23 tests) recomputes every number the result page
and front door state; one count in `RESULTS.md` section 2 did not reproduce and is marked there.
Front door: `docs/40`. Nothing bears on RH (`docs/08`).

**Renumbered on landing, 2026-10-10.** Opened on the unmerged branch
`claude/repo-hunt-content-2smbid` as #119, the number its issue #93 comment of 2026-09-10 uses,
renumbered there to #124 on 2026-09-16 after main took #119 for `lambda_dh_exact`, and landed as
#127 because main had since taken #124 to #126. Its front door, numbered 38 on the branch, is
`docs/40`. The rest of that branch is not landed.

**Note, 2026-10-21.** "The rest of that branch is not landed" went stale the same day: the
branch's other four hunts landed on 2026-10-10 as #128 to #131 (`li_dh_onset`, `epstein_height`,
`quotient_exponent` and `claim_halflife`, in #298 to #301), each with its own renumbering note
above. What the branch still held after that is settled by the landing of 2026-10-21 (#333).
Its shallow-clone check in `scripts/science_preflight.py` landed, with the path that failed open
fixed. Of its four `HANDOFF.md` records, the one on the three adversarial audits landed verbatim
with a dated note (below, since `HANDOFF.md` is retired), and the other three are superseded
by issues #217, #218 and #219, closed by #287 and #291. `zeta/li.py`'s coefficient cache `data/li_gamma_dps60_methodintegral_n128.json`,
written during the `li_dh_onset` run and committed on the branch in `a9eba317a`, was not landed:
`tests/test_li.py` states that every committed `data/li_*.json` table was checked out of band,
and it names no check of this one. Nothing else on the branch is missing from main.

**Record (2026-09-10): three write-ups, three adversarial audits, and the pattern in what
they caught.** Moved here from `HANDOFF.md` when that file was retired on 2026-10-22; the
text below is as it landed there, including its landing note.

- **Believed:** that a hunt which measures carefully, states its grade, records
  its controls and ends with a doors section has done the work. Four hunts in one
  session did all of that.
- **Invalidated by:** giving three of them to separate agents with no part in
  producing the result, told to break the claim rather than review it. **All
  three claims survived. All three write-ups needed correcting**, and the
  corrections were not typographical:
  - `euler_defect_axis`: eleven overclaims, including a residual presented as an
    independent oracle when `R = |1 - a(1)| max|c(n)|` identically, and rows
    called empty that are exactly the composite defect of `1 + Z_Q(s)`.
  - `quotient_exponent`: the headline. It compared a three-parameter free fit
    against a one-parameter reading of a conjecture whose own source states it
    with a moving constant. Fitted like for like, the conjectured exponents win
    with one parameter fewer. Its stated reason for reformulating the programme
    was also false: the form it replaced returns the same optimum to `2.7e-14`.
  - `epstein_height`: the guard. Six planted faults, all passing, and a call it
    allows returns `0.59` of the 4 digits it promised, because every rung held
    the form fixed and so tested the leading term rather than the term the hunt
    had just derived. Its title was wrong too: `zeta/heatflow.py` and
    `zeta/core.py` already carry this kind of guard.
- **The pattern, which is the reason this is a record and not three notes.**
  Not one of the eleven-plus-four-plus-eleven corrections was an arithmetic
  error. Every number in all three hunts reproduced. What failed each time was a
  **comparison or a control**: a residual compared against something algebraically
  forced to agree with it; a model compared against a version of its rival with
  fewer degrees of freedom; a guard compared against faults that all varied the
  same thing. A laboratory that checks its numbers and not its comparisons will
  pass its own review every time.
- **Now caught by:** nothing mechanical, and that is the honest state. What
  worked is a separate agent, the write-up, the repository, and an instruction to
  break it rather than read it. Three for three. The cheapest version of the
  lesson, which does generalise: **when a control agrees with the thing it is
  controlling, ask whether it could have disagreed.** Two of the three failures
  are that question unasked.
- **Justified conclusion:** the four control roles this tree already names
  (rival, decoy, lesion, precision response) are about the *claim*. Nothing in
  them looks at the *argument for* the claim, and all three failures here were
  there. `hunts/*/AUDIT.md` carries each audit verbatim, including the attacks
  that failed, because a list of only the hits reads as a review.

> **Note on landing this record, 2026-10-21.** Ported verbatim from the
> unmerged branch `claude/repo-hunt-content-2smbid` (commit `57cb2a5`). Its
> three hunts are on main as #127 (`euler_defect_axis`, front door `docs/40`),
> #129 (`epstein_height`, `docs/41`) and #130 (`quotient_exponent`,
> `docs/42`). Read against their audits (`hunts/*/AUDIT.md`), three sentences
> of the pattern paragraph do not hold as written:
>
> - "Not one of the eleven-plus-four-plus-eleven corrections was an arithmetic
>   error." Two of `euler_defect_axis`'s eleven overclaims are miscounts:
>   "forms in the published table 44" with "forms whose a(1) equals 0: 30",
>   and "all thirty of the others", where the artifact holds 41 forms, 27 of
>   them non-principal. Replacing those counts is the first item under that
>   audit's "Corrections required", from its attack 7 ("check the write-up's
>   own arithmetic", outcome PARTIAL BREAK). `quotient_exponent`'s audit also
>   required a count fix ("the 21 positive rows", where `artifacts/fit.json`
>   holds 20) and a memory figure twice what its own formula gives (`3.2 GB`
>   for `1.6 GB`), though neither is among the four attacks its summary says
>   landed. (`epstein_height`'s eleven is its audit's summary line, "Eleven
>   landed"; ten of its seventeen attack headings read BROKE IT, and attack 3,
>   headed held, also led to a correction.)
> - "Every number in all three hunts reproduced." The counts above did not.
>   The headline measurements did reproduce, in the audits and again in main's
>   2026-10-10 landing re-runs (the probes' artifacts, the Epstein grid, the LP
>   values). Some secondary figures did not reproduce as printed, in all three
>   hunts, and each is marked where it is stated: one count in
>   `euler_defect_axis` (`RESULTS.md` section 2, `docs/40` section 3), four
>   numbers in `epstein_height` (two of them in `docs/41` section 3) and four
>   on `quotient_exponent`'s result page (noted in `docs/42` section 5).
> - "What failed each time was a **comparison or a control**". True of the
>   failure the record names in each hunt (the residual, the model comparison,
>   the guard's fault ladder), not of every correction: the miscounts are
>   counting errors, and `epstein_height`'s audit (attack 8) also found a step
>   in `law.py`'s derivation that cancelled a real term against nothing.
>
> So read the pattern as describing each hunt's main failure, not every
> correction: the audits caught arithmetic too. One figure in the record is
> also tighter than its source: "the same optimum to `2.7e-14`" is the
> `N = 10^3` row, and over the four diagonal cutoffs the relative difference
> runs from `2.4e-14` to `7.0e-14` (`hunts/quotient_exponent/RESULTS.md`
> section 2). The branch's other three `HANDOFF.md` records of that day are
> not ported: issues #217, #218 and #219, closed by #287 and #291, supersede
> them.

### Robin's inequality for 25-free integers (`robin_tfree/`, 2026-10-04)

**Status: candidate, ordinary derivation, unreviewed, pending external verification;
numerical step enclosure-carrying; inputs published and quoted. No RH or novelty
claim.** Past Morrill-Platt's verified range `x0 = 29 996 208 012 611`, the primorial
ratio `E(x) = log(e^-gamma prod_{p<=x} p/(p-1) / log theta(x))` is at most `2.481e-8`,
using only Buthe's `x - theta(x) <= 1.95 sqrt(x)` and the BKLNW tables. The step that
matters is an exact identity: Mertens' boundary term and the `log theta` denominator
cancel to first order, where earlier papers bound them separately. Consequences, same
grade: Robin's inequality for every 25-free `n > 5040`; for every `n > 5040` with
`nu_2(n) <= 24`, `nu_3 <= 14`, ..., or `q^(nu_q(n)+1) < 4.03e7`; and
`sigma(n) < (1 + 2.49e-8) e^gamma n log log n` for all `n > 5040`. A search on
2026-10-10 (web, arXiv, zbMATH Open, citations of Axler 2023) found 21-free as the best
published t-free result (Axler 2023), so the claimed delta is 21 to 25, recorded as a
search and not as novelty. `t = 26` fails; the verified range is the binding
constraint, and these estimates leave Robin's inequality undecided on the remaining
integers (multiples of `M*`). Lemma 3(b),(c) and the use of the Buthe and BKLNW tables
await outside review; the table transcriptions agree with the arXiv versions. Identity
checked on real primes; 37 tests, which pin every derived number RESULTS.md states. See
`robin_tfree/RESULTS.md`.

### October 8 extensions (`oct08_extensions/`)

**Status: written conditional candidates, with independent review artifacts.**
The density extension replaces the earlier ninth-power interval target by
seventh powers under the same zeta half-plane assumption, adding a published
explicit zero-density estimate. The fixed Fourier network admits a parameter
extension; its all-length consequence keeps the upstream exact-arithmetic
compiler assumptions. Genus-aware partial counts and a failed primality
certificate route retain their limitations and falsification examples.
See `oct08_extensions/MISSION.md` and its `routes/` and `audits/` artifacts.
No kernel verification, practical Fourier speedup or worldwide novelty is
claimed. Source authentication and subsequent extensions are recorded in the
route reports, separately from numerical replay.

### Hunt #126: primes between consecutive ninth powers, given the 7/8 half-plane (`qrh_prime_powers/`)

**Status: candidate, pending external review; ordinary written proofs, every
numerical step enclosure-carrying, conditional on OpenAI's zero-free
half-plane.** Given that zeta has no zero with real part above 7/8 (OpenAI's
30 September 2026 preprint, Theorem 1.1; the October 5 paper proves 11/12),
there is a prime between n^9 and (n+1)^9 for every n >= 1, against the
unconditional record k = 86 (Lee, arXiv:2602.14340). Route: the exact explicit
formula for a quadratic B-spline weight, zero sums bounded in closed form
through explicit N(T) bounds, an Arb cover of 10 <= n <= e^100 with worst
margin 0.825 (0.303 with no verified RH height at all), an analytic tail, and
Pratt certificates for n <= 9. The 11/12 theorem alone gives 13th powers. The
weakened abscissa 15/16 moves the threshold to k = 17 as predicted, and k - 1
fails in each case from log n near 28.4 to 29.5. By-products: a prime in
(x, x + (1/2) x^(7/8) log x] for x >= e^8, and |psi(x) - x| < x^(7/8) log^2 x
/(128 pi) for x >= e^10. No review yet; no Lean. See
`qrh_prime_powers/RESULTS.md`, which ends with the doors (k = 8 is where this
method stops, unresolved rather than obstructed; explicit zero-density
estimates are the door).

### Hunt #125: explicit small witnesses from the 7/8 half-plane (`qrh_nonresidue/`)

**Status: candidate, pending external review; proved given OpenAI, "The
Quasi-Riemann Hypothesis", Sept 30 2026, Thm 1.1 (unreviewed input),
enclosure-carrying numerics.** From the zero-free
half-plane Re s > 7/8 a smoothed explicit formula with weight
(n/x)^(1/4) log(x/n), zero sums bounded through the Hadamard identity at
sigma0 = 2, gives: every nonprincipal character mod q >= 3 has a prime
p <= (log q)^8 with chi(p) not in {0, 1} (tight at q = 3), and
p <= (0.7 log q)^8 for q >= 5, with limsup constant at most (96 sqrt(3)/343)^8 = 0.0031; every
odd composite n has a Miller-Rabin witness at most (0.7 log n)^8; and
g*(p) <= (Lambda_p log p)^8 with an explicit sieve factor Lambda_p. The
Oct 5 2026 paper's 11/12 half-plane alone gives (log q)^12. The
exponents are not new (Montgomery-Vaughan 13.12, Guo 8 Oct 2026); no explicit
constant was found in the searched set. Controls: exact tables to 10^7,
OEIS record values, a weakened abscissa that moves the measured exponent to
12 and 16, and a planted fault refuted by n(48473881) = 67. The exponent 8 is
the wall of this information class (The doors). See
`qrh_nonresidue/RESULTS.md`.

### Hunt #124: an explicit class-number bound from the quasi-Riemann hypothesis (`qrh_class_number/`)

**Status: candidate, pending external review; proved given OpenAI's Theorem
1.1 (The Quasi-Riemann Hypothesis, Sept 30 2026, zero-free Re s > 7/8,
unreviewed), by an unreviewed written proof whose every constant is
evaluated in Arb.** Littlewood's short Euler product with two Cesaro cutoffs
and Hadamard positivity for the zero sum gives, for every negative
fundamental D other than -3, L(1, chi_D) >= 1/(10 log log |D|), hence
h(D) >= sqrt|D| / (10 pi log log |D|): the constant the October 5 OpenAI
paper calls computable and leaves uncomputed. A verified interval cover turns
the bound into D(h) with h(D) <= h implying |D| <= D(h) (D(100) = 48 611 613,
D(1500) = 12 409 254 457). An exact reduced-form sieve over all 3.77 * 10^9
fundamental discriminants below D(1500), 39 minutes on one core and no GRH,
then completes the imaginary quadratic class-number lists for every
h <= 1500 (9 245 562 fields, largest |D| = 562 394 347), conditional only on
Theorem 1.1 (h <= 1000 also under the October 5 paper's 11/12 half-plane,
with c = 1/16). It reproduces Watkins' h <= 100 classification exactly and the
GRH-conditional odd-h counts of Holmin and Kurlberg for all odd h <= 1500.
Controls: the bound sits at least 3.89 times below every exact L(1, chi_D)
for |D| <= 3 * 10^6; weakening the abscissa to 11/12 and 15/16 weakens it in
the predicted way; the GRH specialisation matches Lamzouri-Li-Soundararajan.
No explicit half-plane constant or even-h list beyond 100 was found in the
search; that is not a novelty claim. See `qrh_class_number/RESULTS.md`.

### Hunt #123: Linnik's constant 7/3 from the 7/8 zero-free half-plane (`qrh_linnik/`)

**Status: candidate, pending external review (2026-10-08).** Uses OpenAI's
Theorem 1.1 (no Dirichlet L-function vanishes in Re s > 7/8; Lean statements
kernel checked here, argument unreviewed) as an input, not as something to
audit. A smoothed explicit formula with height cutoff a small power of x, the
input theorem removing every zero above 7/8, and Chen-Gupta-Li's single-modulus
density estimate (arXiv:2507.08296v2, preprint) give, by an ordinary written
proof, p(q,a) <= C(eps) q^(7/3+eps) for every modulus and class, effective, with
psi(x;q,a) ~ x/phi(q) for x >= q^(7/3+eps), all but O(phi(q) x^-delta) classes
reached by x = q^(7/6+eps), 30/13 for smooth moduli, and Goldbach numbers
mod any q below q^(7/6+eps). On refereed density inputs alone the exponent is
12/5, the value Wikipedia lists for the 7/8 theorem. The binding point is
sigma = 5/7 (Ingham's mean value bound against CGL's q1^(1/3) term), so the
half-plane is slack for any theta >= 5/7; exact exponent algebra is checked
against a float grid and planted lesions. The conditional implication is in
the literature (CGL Corollary 1.4 at h = x); nothing is claimed novel. Least
primes for q <= 5000 are tabulated as a descriptive picture (max exponent
1.83, at q = 5). Composite grade capped by the unreviewed input. See
`qrh_linnik/RESULTS.md`, which ends with the doors.

### Hunt #122: the second-DH tracked pair lands at 1.0876360002296, and the lower endpoint reaches 1.0876359 (`dh_minus_landing/`)

**Status: probe, complete (2026-10-08); the parent's first door is priced and
shut for this pair.** `dh_minus_heat` left `217/200 < Lambda_minus <=
567009/320000` (narrow frame) and named a later rational heat time for the same
conjugate pair as its first door. The pair's landing time is measured by two
independent routes, an mpmath double-zero Newton solve (30 and 50 digits,
agreeing to `4.6e-26`) and a float contour-moment discriminant tracker (two
grids, within `5e-14` of the first): `t_c = 1.08763600022958693221796...`,
`x_c = 7.5399442421673352...`, grade hardened, no enclosure. Five rational
times below it, down to `10876359/10^7 = 1.0876359` (`1.0e-7` under `t_c`),
carry the parent's Arb Taylor/Rouche disk decided positive on all four of its
configurations, so the bracket becomes `1.0876359 < Lambda_minus <=
567009/320000`, lower endpoint enclosure-carrying at the numerical step, the
surrounding argument the parent's. The door was worth `2.636e-3`, `0.38%` of
the gap. The pilot's second zero lands at `0.631` and binds nothing; no census
of other pairs was run. The parent's second door (a sharper strip for the upper
endpoint) is repriced from a number already decided in
`lambda_dh_bounds/strip2_results.json`: worth `4.03e-4`, not rerun. Controls:
known values, the recorded `217/200` disk rerun, the `t = 0` gate, two
closed-form polynomial landings, three instrument lesions, and a 1% kernel
fault that both tracking routes miss together (they agree to `1.4e-13` on the
wrong function) and the Hurwitz zero-time identity catches (defect `1.2e-3`).
No kill condition fired. Nothing bears on RH; the subject is a rival function.

### Hunt #121: what moves under the 7/8 strip, priced (`qrh_conditional/`)

**Status: conditional pricing, exact exponent arithmetic plus two measured
heights; nothing here is a result, and the hypothesis is nobody's theorem
(2026-10-08).** QRH(theta) is the claim, published by OpenAI on 2026-10-06 and
replayed by no one known here, that every Dirichlet L-function is zero-free in
Re s > theta, theta = 7/8 (and 11/12). (Update, later on 2026-10-08: replayed
here, Lean's kernel and the independent NanoDa kernel accept the statements,
`docs/38` section 7; the argument is still unreviewed by any person, so the
pricing below keeps its hypothesis.) The hunt asks which of this tree's
priced walls would move if it held, and keeps the hypothesis in every
sentence. Under QRH(7/8): `prime_pair_error`'s rank-1 wall, the q = 1 mixed
moment, moves from N^3 L^{-2H} to N^{11/4} L^4 and stops 3/4 of a power short
of (31), which is RH-equivalent, so no fixed strip closes it; the completed
bound (1) would move from a logarithmic saving to N^{35/12} L^6 by widening
the major arcs to N^{1/12} (the hunt's own derivation, reviewed by nobody),
still 11/12 of a power short of the target and 5/12 behind CHHL's
GRH-conditional 5/2; Theorem A becomes W << N^{7/4} L^4, 3/4 short of (T);
the ineffective constants become effective in principle. Rank 2 (Vaughan's
bound), rank 3 in the square-root-arc configuration, the de Bruijn-Newman
record (9/32 > 0.2, cited from the lab's reading of the claim, document 38 of
the course), the simple-zero proportions, Lambda_DH and the Re(xi'/xi)
equivalence do not move.
The circle-method bootstrap theta -> (2 + theta)/3 drifts toward 1, never
toward 1/2. Crossover heights against Johnston and Yang's explicit remainder,
with the strip-side constant set to 1 by convention: log x = 35.11 (x about
1.8e15) at 7/8 and 98.22 (about 4.6e42) at 11/12; on every height the
prime-pair hunt has measured, the explicit unconditional bound is the smaller
one. Li's criterion: a strip multiplies the per-zero growth exponent of a
hypothetical off-line zero by 2 theta - 1 = 3/4 and bounds neither the count
nor the heights of such zeros, so nothing usable at finite n. Every statement
is void if the claim is withdrawn or refuted. `qrh_conditional/RESULTS.md`
ends with the doors.

### Hunt #120: where the quasi-Riemann argument spends its Euler product, and a rival that cannot pay (`qrh_rival_step/`)

**Status: read and measured, 2026-10-08; no verdict on the paper.** OpenAI's
family 003 (the lab's reading of the release is `38-the-quasi-riemann-claim.md`,
on the branch `claude/openai-math-release-2026-10-06`, not yet on main) claims every Dirichlet and finite-order Hecke
L-function over Q(sqrt(-3)) is zero-free in Re s > 7/8. The hunt asks where
the argument uses that its target is a single L-function with an Euler product
rather than a finite combination, and tests the step on the classical rival,
an Epstein zeta function of class number above one. Reading: the continuation
criterion (Proposition 2.1 of the 7/8 paper, page 8) is a shared lemma whose
proof survives for any function with bounded reciprocal on Re s >= 2; the
Euler product is consumed where that criterion's two estimates are made, at
the Moebius identity 1/L_K^S = sum mu nu N^{-s} (11/12 paper, Section 3, page
12) and at the scalar Euler identity, Lemma 7.1 (7/8 paper, Section 7.2, page
53, used at (10.1) and (10.2) on page 71). Measured: for Q = x^2 + xy + 4y^2
(D = -15), written in the paper's own vocabulary as
zeta(s) L(s, chi_-15) + L(s, chi_-3) L(s, chi_5), zeros at
0.92746 + 15.49663i, 0.91294 + 47.53316i and 1.02597 + 61.42280i, the last
inside the region of absolute convergence, each hardened by two evaluation
routes agreeing to 1e-25 or better, a lattice-route residual of 1e-41 where
run, an mpmath winding of 1 and a segment-enclosed ball winding of 1 on
python-flint; for D = -23 a zero at 0.95326 + 16.29022i on two routes. Each is
a cancellation between two nonvanishing products of Dirichlet L-functions, so
none is a counterexample (`docs/08` section 4.3): the rival lacks the
hypothesis, its reciprocal's coefficients being non-multiplicative and
unbounded (exact to 10^6). The Davenport-Heilbronn function has no zero past
7/8 below height 300 in this hunt's scan. The v6 census
(doi:10.5281/zenodo.23585903) lists six right-side zeros past 7/8 for
0 < Im s < 20,000; its deepest is at 0.897750155 + 2442.53029247i.
These catalogue coordinates are external input, not part of this hunt's
original scan. DH has no Euler product, so these zeros do not contradict
the single-L-function theorem under discussion.
Controls: gamma_1 recovered to 2e-16, planted faults detected, the
class-number-one form sees nothing. Scan ranges are stated as limits in
`qrh_rival_step/RESULTS.md`, which ends with the doors.

### Direct resolution attempt (`rh_resolve/`, 2026-10-03)

**Status: unresolved RH attempt; Li enclosure withdrawn; the equivalence it
records is classical.** Saved Li rows report positive lower endpoints for
n = 1..58, graded measured: the hunt's own audit of 2026-10-04 withdrew
their enclosure grade (complex modulus bound, outward rounding of the
remainder and angle coverage unproved), and no repaired rerun exists
(`AUDIT.md`, formerly `THEOREM.md`). `EQUIVALENCE.md` records, as an
ordinary unreviewed argument, the classical equivalence of RH with
Re(xi'/xi) > 0 on Re s > 1/2 (stated in `epp_herglotz/RESULTS.md`; see
Lagarias, Acta Arith. 89 (1999), 217-234); it is neither new nor a proof
of RH. A positive even Gaussian mixture has a measured non-real cosine
zero. The log-concavity obstruction is conditional on an unproved uniform
margin. Numbers quoted from the saved artifacts are pinned by
`tests/test_rh_resolve.py`. No novelty claim.

### Theta sums and Laguerre inequalities (`rh_theta_laguerre/`)

**Status: unresolved RH attempt, ordinary proofs and numerical enclosures;
external review pending.** Every fixed raw theta partial
sum loses an endpoint cancellation and eventually violates the first
Laguerre inequality, with remainder bounds given. For every fixed cutoff K,
a positive-measure cosine transform satisfies all inequalities through K
everywhere but has nonreal zeros inside the corresponding critical strip.
The K=1 control's second coefficient is exactly -12/121 at pi. Neither is
a zeta counterexample. The all-order positivity
obligation for the full arithmetic kernel remains open. See
`rh_theta_laguerre/RESULTS.md` for proofs, dependencies, and reproduction.

The square-construction continuation tests two specific representations on
the full theta kernel. The local score construction has a negative two-point
Gram eigenvalue; the positive-average-of-shifted-squares construction has a
negative integer-vector witness for a 24-point ratio matrix. Both witnesses
carry Arb enclosures including all theta and integration tails. These are
failures of the proposed representations, not negative Laguerre values or
zeta counterexamples. Details: `rh_theta_laguerre/SQUARES.md`.

### Central logarithmic moments (`central_moments/`, 2026-10-02)

**Status: unresolved RH attempt, ordinary derivations and finite measurements.**
The central logarithmic derivative supplies an explicit all-orders moment
positivity obligation. Exact symmetric-measure controls show that raw moment
positivity does not transfer, and that any fixed number of these matrix tests
can pass despite off-axis zeros. Direct central derivatives and theta
quadrature are compared at two precisions. Eight finite Arb matrix-sign
enclosures have independent determinant checks. See the scoped derivation
and reproduction commands in `central_moments/RESULTS.md`. No RH or novelty claim;
external mathematical review remains pending.

### Out-of-band envelopes for Weil window positivity (`oob_envelope/`)

**Status: candidate, hardened by two independent implementations, pending
external verification.** On the window `supp f ⊆ [-L, L]`, any correction to
the Weil symbol at frequencies `≥ 2L` leaves the form unchanged, so the
envelope constant in arXiv:2608.24827's one-stroke reduction can drop from
`A_L = sup P_L` to `sup(P_L − H)` (theory lane, ordinary derivation, referee
PASS). With it, for real even f:

- support 1.6 (`L = 0.8`): `Q(f) ≥ 1.1579e-17 ‖f‖²`, Zhu's window with a
  sharper constant and half the matrix;
- support 2.38 (`L = 1.19`): `Q(f) ≥ 5.7178e-48 ‖f‖²` (numerics GL-96 route
  `≥ 5.71789230595e-48`, referee Clenshaw-Curtis-192 route `> 5.7179e-48`,
  N = 500 even Legendre modes, T# = 500, all error terms enclosed).

For real odd f at support 2.38 (`L = 1.19`, N = 500 odd Legendre modes,
T# = 500, the same sine:16 envelope, all error terms enclosed): numerics
GL-96 route `Q(f) ≥ 3.42853488205e-44 ‖f‖²`, referee Clenshaw-Curtis-192
route `Q(f) > 2.99e-44 ‖f‖²` (1280-bit Arb; formulas and shift frozen
before any worker code or artifact was read, though the brief disclosed
the worker's endpoint; verdict PASS). The odd reduction was derived by the
numerics worker and independently re-derived by the referee. Parity and
real/imaginary cross terms cancel, so the even sector is the binding one:
`Q(f) ≥ 5.7178e-48 ‖f‖²` for every complex `f ∈ L²` with
`supp f ⊆ [-1.19, 1.19]`. That composite is a candidate, hardened by two
independent implementations that share python-flint, resting on ordinary
derivations, pending external verification. The `L = 0.8` line remains a
real even statement. No window claim found in the searched literature
exceeds half-width 17/16 (Liu, unrefereed); Zhu withdrew his own `L = 1.19`
claim. The threshold stays doubly exponential (the best out-of-band
constant grows like `e^L`), so this is a fixed-window result, not a route
to RH. Methods: `docs/37-methods.md` (out-of-band envelope lemma;
residual-enclosed shifted Cholesky). Record:
`oob_envelope/numerics/RESULTS.md`, `oob_envelope/theory/RESULTS.md`,
`oob_envelope/referee/REVIEW.md`, `oob_envelope/referee/ODD_REVIEW.md`.

### Weil positivity propagation across window size (`weil_propagation/`, 2026-09-23)

**Status: open.** Asks whether positivity of the truncated Weil form on a
window of length `L = log c`, together with the Euler product, can be carried
to `L + delta`. Every candidate transport is tested against
Davenport-Heilbronn, whose form turns negative at `c = 31`
(`rogue_frontier/weil_trunc/` s8), and a candidate that also holds for DH is
refuted. Two workers: measurement of ground-state transport between windows
in `weil_propagation/numerics/` and literature plus candidate lemmas in
`weil_propagation/theory/` (branch `teal-sea/weil-propagation-theory`).
No RH claim. The numerics branch also carries, under
`rogue_frontier/weil_trunc/`, a DH feasibility gate (`THEOREM_FEASIBILITY.md`,
`DH_DICTIONARY_CONSTRUCTIVE.md`, `gate_checker.py`): a hardened witness (the
negative even-sector eigenvalue at `(c, N) = (31, 60)`) plus a Guinand-Weil
dictionary argued for DH, which together force an off-line DH zero. Grade:
ordinary argument, internally reviewed, pending external verification. The
conclusion is classical (Spira 1994); only the route is the lab's.
Lane `weil_propagation/ghost_zeros/` (2026-10-21, preregistered in its `PREREG.md`): at band N = 128, DH's even ground-state transform has exactly one zero with |Im z| <= 1/2 over the on-line gap (83.109, 87.647), real and 0.019 to 0.035 above the off-line ordinate 85.699, at each of the seven preregistered windows from c = 29 to 47, on both sides of the even sign flip at c = 30.647, and an exploratory scan finds a zero within 0.3 of that ordinate at every scan window from c = 15 on; removing the off-line quadruple's term removes it, an on-line sham does not, zeta has no zero in its gap, and Epstein (1,1,6) shows the same at its own off-line zero; hardened counts for the band-128 matrix only, no continuum or RH claim (`weil_propagation/ghost_zeros/RESULTS.md`).

**Update, 2026-10-26 (`weil_propagation/c4_s2/exact_gram/`, branch
`hunt/c4-exact-gram`).** The compute sweep resumes C4 at S = {∞, 2}, whose
c = 2.9 negative count 4, 10, 20 at N = 8, 16, 32 is graded by a response
band, not a bound. The exact-Gram ball rebuild that would close
bound_quad/'s E2 is priced on the box. One 280-mode block costs 258 s at
dps 40, and the full rebuild is estimated at about 155 core-hours, which fits
7 GitHub Actions jobs. It has not run. Its reading and decision table were
committed before any rebuilt row existed (`PREREG.md`). The (U-S) gate
now also refuses Davenport-Heilbronn, by an exact composite atom at n = 6.
A first pass at the truncation lemma finds the bound_trunc/ route obstructed
on the full window space (at least 0.13 at 280 modes against the 1.18e−2
scale) and open on continuous windows (0.0063). No RH claim.
Later the same day: the a priori bounds P1 to P3 close (the s-rule was
changed to a uniform trapezoid by a dated amendment, before any row). G_z
closes, and its identity check caught a float-endpoint defect. G_b's
integration-by-parts regions remain, so the run waits on them. The tail-mass
step closes as a Poisson identity, which re-prices the rebuild at about
28 core-hours.
Third unit: P4 closes (G_b's integration-by-parts regions, each checked
against quadrature with a planted fault), lifting PREREG row D0's
precondition. A disk-backed mode table fits four workers per runner. The
calibration run is asked for, not yet run.
Fourth unit: the calibration ran on GitHub Actions (run 40342895119,
success). Measured there: the Gram took 13.1 core-hours in 24 unbalanced
parts, and an s-block of 128 nodes took 841 to 932 s with four processes
per runner. The Gram (20 MB, by sha256) is committed for reuse. The full
rebuild is sized from these figures at about 104 core-hours and 11 hours
wall, and it is asked for, not yet run. No ΔT number has been read.
2026-10-27: the full rebuild ran (run 40371181784, success, 12 h wall,
132 CPU core-hours). The headroom rule was broken: one job ended 4 percent
under the 350-minute cap, mostly through contention between replay blocks.
[withdrawn 2026-10-27, see correction below] PREREG row D1 holds at c = 2.2, 2.5 and 2.9. ε_q is a bound, at most
9.2e−4, 13 to 18 times below the 1.18e−2 scale. At c = 2.9, C_8, C_16 and
C_32 at ε are 5, 11, 23 on the full space and 3, 8, 20 on V_4. These are
statements about the 280-mode object R^(280) only, since the truncation
bound ε_t is null and D3 is not read. Grade: exact inertia and ball
enclosures, resting on unreviewed derivations (BOUNDS.md P1 to P4). No RH
claim.
Correction, later on 2026-10-27: "ε_q is a bound" above is withdrawn. A
review found that the code's Gauss bound was the (n + 1)-point bound used
for n-point rules, so the quadrature radii, and ε_q, were up to 225 times
too small. The D1 reading and the counts above are not established, and E2
is unresolved again. A rerun at 13 nodes per panel, where the corrected bound
equals the old radii, was launched on Actions and has not been read
(`exact_gram/BOUNDS.md` s5, `RESULTS.md` correction, `RUNS.md` s12).

### Second Davenport-Heilbronn heat flow (`dh_minus_heat/`)

**Status: candidate ordinary argument with enclosure-carrying numerical steps;
independent model reviews completed.** A rational disk at narrow heat time `217/200` passes
a Taylor/Rouche inequality at three Arb precisions, including all theta and
integration tails. A simpler Euler-phase calculation on Arb and mpmath.iv
supplies the candidate bracket `217/200 < Lambda_minus <= 567009/320000`.
The odd theta normalization is checked against a separate Hurwitz-zeta route; the plus cosine normalization is now stated and checked the same way.
No RH, novelty or formal-proof claim. See [the argument](dh_minus_heat/RESULTS.md)
and its executable checker; the lower-bound quadrature uses Arb only.
An exact residue-orbit corollary shows the nonresidue permutation `n->2n mod 5` swaps the plus/minus heat class up to global scale, with a SymPy enumeration check.

### Finite paid-surplus construction (`paid_surplus_obstruction/`)

**Status: exact finite construction, independent challenge pending.**
At `N=144`, rational coefficients supported through 12, with harmonic balance,
coverage through `q=5`, and mass `119/20`, satisfy `W_d<=1` at every prime
power. The fully saturated paid cost is exactly `psi(144)` and its positive
surplus is zero. The factorial discrepancy and complete repair are separately
priced in [the argument and checks](paid_surplus_obstruction/RESULTS.md).
This does not supply a scale-dependent family or a uniform bound.

### Paid-shortfall scaling (`paid_shortfall_scaling/`)

**Status: explicit identities and finite arithmetic improvement; uniform rate open.**
The perfect-power cap has an exact signed factorial-sum formula and a
deficit-dependent saving bound. For old fixed-seed square-root-support lifts,
the saving is at most order `N^(1/4) log N`. An explicit balanced Mobius-prefix
family has bounded coefficient mass and complete localized repair costs.
At `N=36864`, excluding composites witnessed by primes 2,3,5,7 lowers its
full excess over N from 877.252193 to 220.982190, with coefficients unchanged.
Five fixed cutoffs are checked with two interval implementations at two
precisions. No extrapolated exponent, RH claim, or novelty claim.
See [derivations and the remaining obligation](paid_shortfall_scaling/RESULTS.md).

### Paid-shortfall saturation (`paid_shortfall_saturation/`)

**Status: five finite local-cap identities, no general rate claim.**
For the unchanged selected balanced prefixes at the five fixed cutoffs, every
ordinary composite in the local repair interval is exposed by testing primes
through its square-root bound, while every prime power remains. The saturated
cap equals the exact Mangoldt weight in each local range. Exact prime-log
vectors and two interval routes price the factorial discrepancy, repair,
removed composite overpayment, zero remaining cap surplus, and the complete
total. No asymptotic, RH, or novelty claim.
See [the finite diagnostic](paid_shortfall_saturation/MISSION.md).

### Paid-shortfall construction (`paid_shortfall/`)

**Status: explicit bound and finite comparison, with the leading gap retained.**
An early-truncated finite balanced lift has a complete paid-tail bound:
at square-root coefficient support, repair costs at most order
`sqrt(N) log N` for a fixed seed. The factorial remainder is also included.
The construction retains its old leading constant above one, so its excess
over `N` is still linear. At `N=14` and support at most three, exact primal
and dual witnesses show that replacing raw logarithmic caps by perfect-power
caps removes the optimal excess `log(2)/2`. The displayed derivations and
bounded checker distinguish this finite arithmetic improvement from a
uniform estimate. The run checked 768 truncation cases and 3,072 inequalities
on two interval backends at two precisions. No RH or novelty claim.

### Positivity on attainable quotients (`quotient_certificate/`, 2026-09-07)

**Status: finite improvement and correction; no asymptotic result.** Requiring
the factorial ceiling only at floor(N/d), d>=2, uses no prime locations to
choose constraints. At square-root support it reduces the earlier all-cell
excess by 34.4%, 29.9%, and 41.9% at N=1000,10000,100000. All 889 retained
constraints pass exact integer checks on saved rational coefficients.
An exact N=27,y=9 example with eight prime-looking cells has minimum excess
log(2), refuting the earlier dimension-count argument for zero excess.
The audit also separates the unproved exponent barrier from the global
Nyman-Beurling results and records exact sawtooth correlations.
See [the construction, proof, and remaining doors](quotient_certificate/RESULTS.md).

### Four-point pressure tuning (`four_point_pressure/`)

**Kernel-checked at the pinned revision, 2026-09-28.** The Hermes build at
`5522b963` discharges the four-point bound at `c = 2330/10^6`, `m = 432`,
`p = 2500`, with coefficient approximately `0.6728603588`. The 49 build
receipts and six axiom reports are preserved in `four_point_pressure/evidence/`;
source hashes were independently reconciled during integration. This is a
lab build, pending external verification, not a new Palomar registration.
See `RUNS.md` and `PALOMAR-READINESS.md`.

The following paragraph records the September 5 disposition:

**Status: closed exploratory record; complete Lean check canceled.** Exact
parameter substitution and an emitted-source preflight accompanied a candidate
near `0.6728603588`. The dependency build was canceled before any candidate
proof module ran. No new proved bound, and no 68% or 69% result, is claimed.
`RUNS.md` preserves the arithmetic, candidate commit and terminal CI evidence.
Generated Lean replacements and build-workflow changes remain off `main`.

### Cycle-moment counting probe (`cycle_moments/`, 2026-09-05)

Finite concave spectral counting inequalities, an exact obstruction to using
only second and third moments, and tests of fourth and mixed cycle moments.
The hunt also records exact repeated-index corrections and finite examples
where all spectral moments agree but simple-point counts differ. Overlap
statistics recover the count in an explicit spectral class and give further
finite bounds for positive location Gram matrices. Its
ordinary proofs, scoped Lean checks, and numerical evidence are summarized
in `cycle_moments/README.md`. No stronger zeta proportion is asserted.

### The prime-pair error, reproduced and taken apart by separation (`prime_pair_error/`, 2026-09-06)

**Status: settled as a reproduction plus one measured relationship, not new.** The
Chou, Haag, Huryn, Ledoan error E(N) = sum_k (psi_2(N,k) - S(k)(N-k))^2 reproduces at
all eleven rows of their Table 1 after truncation, the FFT pair count checked against
pure-Python and direct pair sums, and the ratio E(N)/(N^2 log^2 N) keeps rising past the
paper's range, 0.218 at 10^6 and 0.244 at 10^7. Odd separations carry nothing, the power
of 2 in k is invisible, and k divisible by 3 is one sixth of the separations and half of
the error, though less than proportionally to S(k): the squared error scales like
S(k)^0.7 to S(k)^0.8, so no Poisson-type variance law holds. The signed part is one
formula: on even k the error is S(k) [R(N) + R(N-k) - R(k)] with R = psi - x, the
coefficients on a three-profile fit landing within a few percent of (R(N), 0, 1) at the
two held-out N, 3 x 10^6 and 10^7, and the prime-only count carries the same profile
with theta in place of psi, the difference being exactly the prime-power pairs
S(k) [(psi-theta)(N) + (psi-theta)(N-k) - (psi-theta)(k)]. It explains 1 to 3 percent of
E(N) and 12 to 22 percent of the prime-only analogue. Its k-averaged small-k limit is
Korevaar and te Riele's Approximation 2.1 (Math. Comp. 2010), so the hunt claims a
refinement of a published heuristic and nothing more. Nothing bears on RH (`docs/08`).

**Second pass, 2026-09-06 (`residue.py`, `results_residue.json`).** The profile above is the
modulus-1 member of an exact four-piece decomposition of psi_2(N, k) at any modulus q
(periodic baseline S_q(k)(N - k) plus a bounded term, endpoint terms linear in
psi(x; q, b) at x = N, k, N - k, the pairs involving a power of a prime dividing q, and the
correlation of the centered reduced-class function), whose only heuristic is that the
primes not dividing q act on the reduced classes as all primes act on the integers. The
modulus-3 member is the profile with the character mod 3 added, sign chi(k), and the
modulus-30 member treats 2, 3, 5 together through the eight characters mod 30; every
coefficient is 1 by derivation and frozen before the run. At five cutoffs the first pass
never used (2 x 10^5 to 7 x 10^6) the three remove 0.5 to 1.9, 1.0 to 7.6 and 2.2 to 10.0
percent of E(N), with the post-hoc slope of the error on the modulus-30 correction within
one percent of 1 everywhere. What the modulus-30 correction leaves has no structure mod 30
and all of its structure at 7, 11, 13, which the modulus-210 member predicts to within one
standard error. The character-weighted sum sum_k chi_3(k) e(N, k) matches
integral_0^N psi(x, chi_3) dx - (N/2) psi(N, chi_3) to half a percent at every cutoff; that
identity-plus-heuristic is the one statement recorded as worth proving. The Goldbach-side
analogue is Bhowmik, Halupczok, Matsumoto and Suzuki (Mathematika 2019); nothing here is
claimed new.

**Later passes, noted 2026-10-21.** The status line above covers the first two passes
only. The third pass (2026-09-06, `RESULTS.md` sections 14 to 19, audited in `REFEREE.md`)
proves Theorem A, T(N) = I(N) + O(N^{Theta + Theta_chi} log^4 N) under no hypothesis,
whose interesting case is conditional on RH for zeta and for L(s, chi_3), and Theorem B,
E(N) = Omega(N^{1 + 2 Theta_chi - eps}), unconditional and informative only if GRH fails
for L(s, chi_3). Both are written proofs on cited lemmas, corrected and independently
audited, not kernel-checked and not claimed novel. The fourth pass (2026-09-20,
`FINAL_ACCEPTANCE.md`) found no new bound and is an attempt unresolved.
`THEOREM_B_FORMULA_REPAIR.md` (2026-09-20, landed 2026-10-21) replaces the defective zero
expansion of `THEOREM_B_SEQUENCE.md` with a truncated explicit formula, Proposition 3,
derived, reviewed at `95ae36b` (finding R1 against its statement), revised, and cleared
by a targeted follow-up review of `3006ef2`. Its Theorem 4 removes Theorem B's
eps along a closed-form sequence only under an isolated witness zero, which implies that
GRH fails for L(s, chi_3), and Theta < Theta_chi; the unconditional case is unresolved.
This note does not index every file in the directory. Nothing here bears on RH
(`docs/08`).

### Hunt #119: is Lambda_DH exactly Delta^2/2? (`lambda_dh_exact/`)

**Status: OPEN, theory phase only (2026-08-18).** Asks whether Hunt #61's
bracket 0.0576 < Lambda_DH <= 0.19242481458 (narrow frame) collapses to a
point. It would, if the backward-heat landing times t* of Davenport-Heilbronn
conjugate pairs approached the isolated-pair value y0^2/2 as the depth y0
approached the sharp strip half-width Delta = 0.62036249819. The theory phase
derives, rather than assumes, three things: every landing time is a floor for
Lambda_DH (Dobner's half-line, unconditional); Lambda_DH equals their supremum
under a no-creation step that the time-reversed Sturm zero-number theorem
supplies and 600 sampled polynomial configurations support; and the crowding
correction obeys dy/dt = -1/y - 2 pi rho, so a deep pair lands in time
proportional to y0/log(gamma) rather than y0^2/2. Since depth near Delta forces
great height and great height forces large rho, the pre-registered verdict is
that the bracket does **not** collapse and sup t* sits in [0.058, 0.075]
narrow. A one-parameter crowding model, calibrated on Hunt #4's nine landings,
reproduces them to rms 0.54% and a census holdout to 0.79%; the probe is
`theory.py`. Nine predictions with numbers are registered in `MISSION.md`
before any evaluation above height 600. Nothing here is evidence about RH.

**Interrupted, and what the interruption left behind (recorded 2026-09-12).**
The three evaluation agents and the adjudicator all died on API 529 errors on
2026-08-18, so no verdict was ever written and nothing here has been attacked.
They did write their artifacts to disk first, and those are committed as raw
material rather than discarded: `deep_zeros.json` (a screen whose float route
agrees with mpmath to 1e-14 at three checked points), `deep_zeros_1e6.json`
(one off-line zero located at gamma = 1000459.7433532759, beta =
0.8583118590734415, y0 = 0.3583, unit winding with defect 2.2e-16, float64
Euler-Maclaurin plus Newton, `abs_f` 4.4e-11), `landing.json` (the nine-pair
census with measured neighbour distances), and `theory_results.json`. Read all
four as **measured, unadjudicated, and unreviewed**: the zero is float grade
and not enclosure-decided, the screen is not exhaustive over its window, and
the crowding model's extrapolation to depths near Delta remains an
extrapolation from a fit trained at y0 <= 0.37. The one thing worth noting for
whoever resumes: that height-1e6 zero is shallower than the height-240 pair
Hunt #4 already had, which is the direction the theory predicts, and it is the
only evaluation datum the hunt ever produced.

The contract files the interrupted runs never wrote were reconstructed from
those artifacts on 2026-09-12: `RUNS.md` carries a manifest for all six runs
including the null one, and `RESULTS.md` states, item by item, that the hunt is
entitled to say nothing about Lambda_DH, which of the five kill conditions was
evaluated (none), and what whoever resumes should decide first. One control did
run and is worth the reading: varying the screen's inner abscissa over
t in [8, 600] flags 1, 7 and 13 windows at Re s = 0.85, 0.75 and 0.55, strictly
nested as the argument principle requires, and the single window the shallowest
screen flags is [228, 248], which holds the pair at gamma = 240.4046 that
`flow_repair/` had measured independently and earlier.

**Renumbered from #52 on 2026-09-12.** The hunt was opened on a branch that
had not yet seen this case log's growth past #52, and main took that number
for `r_e2ee73/` first; the directory name never changed.

**Resumed 2026-10-26 (compute sweep, branch `hunt/lambda-dh-exact-resume`),
same number.** First wave in the recorded resume order: decide the
height-10^6 zero on both ball backends, run `stage_locate` on the low screen's
21 windows and give `screen_hi` an explicit artifact state, evaluate P2 and
kill condition 2 as written, then price the census to 10^4 and 10^5 before
spending on it. Scope and gates are appended to `MISSION.md` section 8;
outcomes are appended to `RESULTS.md` as dated sections. Correction recorded
on resumption: the decided floor is 36/625 = 0.0576; 0.05765 is a measured
landing, not a decided one.

**Status after the first resumed wave (2026-10-26): OPEN, Lambda_DH bracket
unchanged.** *Decided, both ball backends* (Arb and a hand-rolled mpmath.iv
Euler-Maclaurin, argument-principle counts of exactly one zero in exact
rectangles, planted faults flipping the 10^6 count and, in the tests, one
recounted low zero): the height-10^6 zero, y0 in [0.3583118516, 0.3583118666]
(rounded outward), and each of the 21 zeros with beta > 0.85 that the float
screen found below 10^4. That these 21 are all such zeros is measured, not
decided.
*Decided, Arb only*: no zero with beta >= 0.90 for |t| <= 10^4. So **P2 is
refuted** (y_max(10^4) is in [0.39775014, 0.40), against [0.40, 0.52]) and
**kill condition 2 fires**, withdrawing the stage-6 depth law and P1's
stronger band, P4's point and P5's location, which were derived from it.
*Measured* (N-body ODE landings, control +0.024 percent on the floor pair,
21 of 21 windows accounted): no pair below 10^4 lands above 0.0576518; P3
holds (0.986 of the model at the deepest pair); **P6 is refuted** (d/h mean
0.95, 10 of 20 new pairs in [1.1, 1.8]); P8 is not observed (0 of 21); kill
condition 1 does not fire. `screen_hi` was finished on a copy (111 zeros in
[10^4, 10^5], deepest y0 0.437 at gamma 49688, measured), and the recorded
`complete: false` artifact is marked superseded. A targeted check (not a census) landed eight of the nine pairs with y0 > 0.40 in [10^4, 10^5]: best 0.04902, none near the floor, so P5 stays unresolved with measured evidence against and kill condition 4 does not fire on what was measured (as of that check, 2026-10-26; the census below supersedes both). A slip
inherited from `flow_repair/NOTES.md` (y0 = 0.3695261 for the floor pair;
the value is 0.3695306) is recorded, not propagated (first wave, 2026-10-26;
the follow-up below corrected it in this hunt's code and data, and `RESULTS.md`
section 8.9 holds the corrections). The full 10^5 census
(about 15 core-hours) is estimated and not run (first wave, 2026-10-26; it ran
later that day, below). *Follow-up, same day:* `test_lambda_dh_exact.py` pins every decided and measured number of `RESULTS.md` section 8 and every verdict against its artifact, with real two-backend and Arb recomputations whose planted faults are shown red (31 fast tests, 32 in both tiers). Three more slips of the same kind (pairs 2 to 4) were found and all four corrected in this hunt's files; `flow_repair/NOTES.md` still carries them. The per-pair d/h refit of the shave model fails as a plug-in (rms 0.393 against the frozen 0.160), and the d/h it would need tracks the measured one at r = 0.967, pointing to a two-sided gap (measured). *Units 3 and 4, same day:* the two-sided gap, run against its pre-registration, improves on the frozen model but does not pass (rms 0.112; out of sample 0.154). The census over [10^4, 10^5] ran on GitHub Actions. Attempt 1 was void by its own kill condition K-d, which exposed `stage_locate` accepting roots outside the counted box (16 of 282). Attempt 2, on guarded code, was valid: 170 of 170 pairs accounted and landed, none above 0.0576518 (largest 0.04902). KC4 does not fire up to 10^5, P5 is refuted up to 10^5 (within the screens' coverage; `RESULTS.md` section 8.15 states the scope and a stronger reading) and P8 is not observed (0 of 21 below 10^4, its registered scope; this read 0 of 191, which pooled 170 pairs above 10^4), all measured. The audit under the guard changed one recorded root (screen_hi) and no claim. *Review, same day (`RESULTS.md` section 8.16):* every decided decimal interval is requoted rounded outward (printed to nearest, several were not enclosures); the Arb-versus-iv cross-check of the 10^6 zero is rerun on exact endpoints, because the recorded float version could not fail, and the enclosures intersect at all three points; the in-place slip corrections to registered text are reverted, with the corrections kept in `RESULTS.md` section 8.9; P4 is unresolved with evidence against; and two latent fail-open paths in the census evaluation are recorded as known limits. No verdict moves.

### Hunt #144: a finite reversal-closed adversary excludes the recorded pressure target (`reversal_minimax/`, 2026-09-04)

*Numbered on landing, 2026-10-21.* Opened unnumbered on 2026-09-04, when
this entry read "Reversal minimax probe", and landed by merge from
`docs/simple-zero-research-target`, so its commits `7415efa1b`, `1c4625b04`
and `43217587d` keep their hashes. #136 to #143 were held by other open
hunts and same-day landings (this landing first took #143, which a
concurrent landing of `support_fcffa3b9/` had also taken), so this
entry takes #144.

**Status: candidate refuted at the stated scope (`ALIGNMENT.md` section 5,
disposition 1); hardened numerical leaves inside an unreviewed ordinary
derivation, pending external verification. No new zeta proportion is
claimed.** Whole-laboratory structural scout of the pressure optimization's
reversal symmetry. At AMTOPA's fixed 17-term window and total pressure
B = 93/23000, a finite mixed adversary (seven rational gap vectors from
`amtopa_ceiling/`'s saved 2,200-cut pool, each with its reversal) bounds the
supremum over the whole pair-weight and pressure polytope of inf_g F by
182022320819207/23000000000000000, below 0.007914014. That excludes
`amtopa_ceiling/`'s recorded endpoint 0.007916857810 and the targets
19791/2500000 and 19786/2500000, for asymmetric coefficients too, and only
for that window and B. The leaves carry Arb enclosures at 128 and 256 bits,
agree with an independent mpmath quadrature at all 148 distances, and
combine in exact rational arithmetic. `Symmetry.lean` (the averaging and
budget deductions) has never been run through Lean, so nothing here is
kernel-checked. `amtopa_ceiling/` section 7.7 withdrew the same endpoint on
2026-09-06 by a different route; this bound agrees with that hunt's later
bracket [0.0079107, 0.0079111939]; it is looser than that bracket's upper
end, a float LP value, but enclosure-carrying. A counting audit shows the
bridge's early span estimate overcharges pressure: an interior gap lies in
(n-1)(m-n+1) local windows across all blocks, but the estimate charges it
(n-1)(m-1) times. Its projected gains, 5/904171
on the registered four-point coefficient and 80/14366681 on main's later
m = 432 build, which still uses the coarse count, are candidates awaiting a
replacement assembly. `RESEARCH_TARGET.md` records a proposed
higher-correlation direction and the elementary bound H*m/(m-1) on the
capped assembly. See [the results, the counting audit and the
doors](reversal_minimax/RESULTS.md).

### Hunt #114: one Epstein value, checked against a route that does not cancel (`support_e6241336/`)

**Status: settled** (support run `e6241336`, serving run `872d7dce` /
`r_c7f779`). One bounded question: independently compute
`abs(epstein_completed(0.8+85.7i, (2,1,3)))` at `dps = 60` and say whether it
agrees with the claimed `1.6e-58` to within an order of magnitude.

**It does.** The value is `1.617452632377971461454064e-58`, which is `1.0109x`
the claimed figure, 1.1% away; `log10` of the ratio is `0.0047` against the
`1.0` an order of magnitude would allow. This is the number the `dps_cap`
measurement (#113) is stated against, so it matters that it was confirmed by a
second route rather than by re-running the first.

Grade: **measured**, one evaluation at one precision on one form. Nothing here
bears on RH (`docs/08`).

### Hunt #115: prior art on the certificate route and the LP-versus-truth gap (`support_78c499b4/`)

**Status: settled as far as a literature question can be settled in one search
pass** (support run `78c499b4`, 2026-08-24, serving run `872d7dce`). ARM E of
the `r_c7f779` fan-out: has a Cohn-Elkies / Delsarte linear-programming
certificate been applied to a one-dimensional pair sum whose `f` is the
positive part of a band-limited function minus a band-limited nonnegative
square, and is the LP bound known to be tight against the periodic case.

The page lives here rather than in `r_c7f779/` because a support run may not
write into another hunt's directory. **Nothing in it is a mathematical claim
and nothing is measured**: it is a prior-art record, and it is a search that was
actually run rather than an unrun `knownness` default.

### Hunt #116: rescued probe output from arm 17a0f787 (`support_17a0f787/`)

**Status: artifact only, no write-up.** A support arm of the `r_c7f779`
fan-out whose `probe.py` and `results_quick.json` were left uncommitted in a
fulcrum worktree and are committed here so they exist somewhere other than one
directory. The run is recorded stopped in fulcrum.

`results_quick.json` carries a planted-control ladder with firing scales. **No
one has written up what it shows, and this entry does not claim it shows
anything.** It is preserved evidence, not a result. Read the JSON before
citing it.

### Hunt #117: rescued LP and oracle code from arm 4019e8e5 (`support_4019e8e5/`)

**Status: artifact only, no write-up and no results.** A support arm of the
`r_c7f779` fan-out. `oracles.py` and `t1lp.py` were left uncommitted in a
fulcrum worktree; the run is recorded stopped and produced no committed output
of its own. The code is kept because it was one `git clean` from gone, not
because anything here has been checked. **It has never been run in this tree.**

### Hunt #113: what the `min(dps, 20)` cap costs, measured (`dps_cap/`)

**Status: probe, complete.** At `0.8 + 85.7i`, `epstein_completed` at the
capped `dps = 20` returns `3.1e-33` where the converged value is `1.6e-58` --
a factor of `1.9e25` and not one correct digit. The error floor sits near
`1e-(D+13)`, so nothing correct can appear below `D ~ 46`; the sweep puts the
crossover there exactly (D=40 entirely floor, D=50 the first row with correct
digits). `D = 60` buys about 16 real digits, not 60, because the cancellation
costs roughly 44 of them. `zeta/epstein.py` still caps three interfaces at
`dps=min(_d, 20)` (lines 1092, 1126, 1142), so a caller asking for 60 gets 20
and `count_zeros_box`'s integrality check passes on the noise.

Landed 2026-08-21 as the union of five concurrent 2026-08-14 runs that all
wrote this directory and none of which merged; see the provenance header in
`dps_cap/README.md`. Nothing here is evidence about zeta or RH: it is a
measurement of an implementation at a single point.

> **Renumbered twice.** These two opened as #35 and #36 from a branch
> 101 commits behind `main`, where both numbers were taken. They were
> renumbered to #49/#50 on 2026-08-18, and `main` took those two (plus
> #51, #52, #55-#57 and #59) before this branch landed. They are #60
> and #61. The directories `lambda_dh_bounds/` and
> `prime_zeta_rightmost/` are unchanged and are the stable references.

### Hunt #112: the depth-1 damage windows do not drift, and the lattice is exactly solvable (`support_5418c63e/`)

**Status: settled** (support run `5418c63e`, for run `872d7dce` / `r_c7f779`).
The bounded question was whether the windows of `D(1, s) > 0` track `2 pi`
asymptotically or drift, since `r_b9552d` run `37fb06a9` §2 derives the
atom-reserve ceiling `rho* <= 0.153216295` from the *measured* fact that
`P = 0` on the critical lattice out to `d = 4000`.

**They do not drift.** Putting `ghat`'s two terms over the common denominator
`z^2+2` gives the exact one-term form
`ghat(z) = [alpha z sinh(z/2) + beta cosh(z/2)]/(z^2+2)`, and expanding it
gives `D(1,s) = (alpha^2/2)(cosh1 cos s - 1)/s^2 + alpha C sin s/s^3 +
(E cos s + F)/s^4 + O(s^-5)`. The first correction is **odd**, so it
*translates* the window rather than widening it: `centre(d) - 2 pi d = K/s +
O(s^-3)` with `K = 0.893732172363`, half-width `w0 + W2/s^2` with
`w0 = arccos(sech 1) = 0.8657694832` and `W2 = 1.7796383030`, both confirmed
to nine and ten digits against `dps = 60` edge locations. The offset converges
to **zero**, not to a nonzero constant, and its linear-in-`d` fit slope is
`-2.5e-08`.

**The horizon turned out to be removable.** On `s in 2 pi Z` the kernel is
rational: `D(1, 2 pi d) = P(u)/((u-1)^2+8)^2` with `u = (2 pi d)^2` and
`P(u) = 0.6277706 u^3 + 3.6735975 u^2 + 33.2246011 u - 73.8367418`, whose
coefficients are all positive but the constant, so `P` increases on `u >= 0`
and has one nonnegative root at `u* = 1.7707490`. Since `(2 pi d)^2 >= 39.478`
for `d >= 1`, **`D(1, 2 pi d) > 0` for every `d >= 1`, derived, with no
`d_max`**, which is exactly `P = 0` on the critical lattice. The parent's
ceiling loses its horizon caveat on this ingredient.

A `0.002` scan of `[1e-6, 1e5]` finds `31,830` sign changes (`1.999938` per
period, so no anomalous window), all `15,915` lattice points inside a window,
and minimum distance to the nearest edge `0.817252917` at `d = 2`, rising
monotonically for `d >= 2` toward `w0`. `d = 0` is the one exception
(`D(1,0) = -0.9116`), and it never arises because `P` sums over `p != q`.

One error was made and caught: expanding `1/S` at `2 pi d` instead of at
`2 pi d + x` drops a term of the same order as the `s^-4` one and inflates
`W2` by 43%. The numerics rejected it before it was written down.

### Hunt #111: the T1 certificate LP, reconditioned (`r_c7f779/`)

**Status: in progress** (run `872d7dce`). Re-solving the Cohn–Elkies-style
certificate LP for T1 that `r_b9552d` run `37fb06a9` left at `0.05410` with a
failing solver. The verdict lives between the achievability floor `0.05716502`
and the budget `0.06750841`. This entry is rewritten with the result when the
run closes.

### Hunt #118: spend the out-of-band fact, or prove it cannot be spent (`outband_certificate/`)

**Renumbered 2026-09-06 from #111 to #118:** #111 had been taken by `r_c7f779/` on
2026-09-01 and this entry, opened 2026-09-05, reused it. The directory name is the stable
reference; citations of "hunt #111" dated 2026-09-05 or 2026-09-06 that mean the out-of-band
certificate mean this entry.

**Status: closed 2026-09-06, kill condition 2, prose grade. A CEILING.** The out-of-band
positivity is worth zero to any certificate whose positivity input is Weil's Hermitian form
(every unconditional one): the on-line block is a definite Gram matrix, its kernel is
positive-definite, its transform is nonnegative, and `F` has no unconditional upper bound
outside the band, so bandwidth one is forced. What #110 priced was the RH-conditional
pointwise class, which is why its range holds CGdL's conditional 0.6792. `RESULTS.md`
section 8; the two inputs that would reopen it are named there. The step hunt #110 handed
forward was: an inertia or isolation argument valid for a kernel signed only on alpha in
(1, 1.5], or a ceiling proof that none exists. The target was the record (0.6734165).
First session, measured grade (`RESULTS.md`): the LP's dual, which is the certificate the
information supports, is pointwise nonnegative in x-space with a signed transform, strip
multiplier active on [1.031, 1.5] at X = 80; the LP's `q` and `p_2` columns are identical, so
off-line pairs are priced as double zeros and the square structure is needed only for off-line
zeros, which relocates the missing argument to a bound on the off-line-zero term of a signed
kernel's pair sum, with zero-density estimates as the unconditional input; and a strip of width
0.05 is worth about the record gap (+0.00098 to +0.00129 across pinned exponents, six rungs)
but that is inside the ladder's method error and not distinguishable from zero, while #110's
wide strip stays established at 3.5x. Second pass, same day: a difference-of-squares
candidate (apply `stable_rank_trace` to the positive half with the negative half folded into
`Q`) was priced and killed by an edge lemma, proved: a real even spectral profile's
autocorrelation is strictly positive just inside its support edge, so it can never be
nonpositive on the strip. The lemma is false for odd factors (`sinc^2 (1 - cos 4 pi x)` is a
verified counterexample), which gives the obstruction as a dichotomy: even factor, Gram-able
and strip-blind; odd factor, strip-capable and never a Gram kernel. The gain is not a
lattice-spacing artifact (stable from h = 1/16 to 1/64), and every finite-X kernel, control
included, is negative beyond X. Worked as a node board from `board.json`; the first task is the
numerical falsifier, which #110 ran but did not commit. Either answer closes the hunt.

### Hunt #110: the free out-of-band fact is worth 0.005 to 0.009 and no certificate can spend it (`outband_intake/`)

**Status: probe, complete. GAP, not a barrier.** BGSTB 2023 (arXiv:2306.04799,
Theorem 1) gives form-factor nonnegativity unconditionally, outside the band every
other certificate is confined to. Two matched LP ladders of five rungs price it: with
out-of-band positivity on, the configuration class extrapolates to somewhere in
`[0.679, 0.682]`; the in-band control, whose limit is the record
`0.6725007036794116` and which therefore calibrates the method at about `1.8e-3`,
puts the difference at `+0.0065` by the same fit, three and a half times the method
error, so zero is excluded. The third digit is not: the difference route gives
`0.6790` and the direct fit `0.6815`, one digit from CGdL's RH-conditional `0.6792`
and one digit from the bandwidth-one ceiling `0.6818` respectively, and an earlier
draft that read the first coincidence as a landing is withdrawn (`refit.py`). **But
no known certificate can realise any of it.** The inertia lemma needs a positive semidefinite evaluation form, which
forces the spectral density `v = phi^2 >= 0` and hence `Khat = v*v >= 0` everywhere:
the framework has no free `ghat`, only a free `v`, so a kernel negative out of band
is not reachable. The requirement does not weaken -- with indefinite `S` the rank half
of the lemma survives and the inertia half fails, witness `Q = t[[0,1],[1,0]]`,
`S = diag(1,-1)`, `c = 2`, slack `+2.0` at `t = 1` and `-0.5` at `t = 1.5`, against
4000 random PSD pairs never violated. The first-order law `dJ/deps = (J - Lbar)/g(0)`
locates the gain entirely in the indirect channel, which is exactly the one the
framework cannot enter. **So the information is in hand and unspent, and the missing
piece is a construction rather than a datum** -- unlike `frontier_math` §2's sieve
wall, where the missing input is Hardy-Littlewood grade and genuinely absent. Two
things bound the result and are recorded in `RESULTS.md`: gate #3 fires (the drop is prime-blind, holding for Davenport-Heilbronn and both Epstein forms, which bounds what the zero side can ever add), a ratio test was stated
confidently, then withdrawn as uninformative, and the in-band data's provenance is
unaudited, so the range is a class value until someone traces it to an unconditional
source. Nothing here bears on RH (`docs/08`).

### Hunt #109: the soundcalc numbers reproduce, the pins that name their sources do not (`r_4166b0/`)

**Status: settled for the units where a source existed; four units have no
reproduction path and that is a property of the artifacts, not of the budget.**
The first transfer test of the reproduction procedure outside mathematics
(issue #140, the Ethereum Foundation's zkEVM Security Sprint). `ethereum/soundcalc`
pinned at `d9078d64c9c3`, ten units, two verdicts each, never merged: does the
checked-in TOML follow from the vendor's tree at the version it names, and does
that TOML still describe the vendor's current release.

**Every parameter that could be re-derived, re-derived exactly: 51 of 51
numeric fields** (RISC0 7/7 from its cited notebook, Miden 5/5 from its cited
Rust constant, OpenVM 9/9 across three circuits, SP1 30/30 at two separate
vendor refs). Not one number was wrong. Stage 0 holds too: soundcalc at its pin,
run unmodified on its own TOMLs, leaves `reports/` byte-identical.

**The failures are all in the pins.** Of eight provenance pins, **two do not
resolve**: Airbender's cited commit is not in `matter-labs/zksync-airbender`
(`upload-pack: not our ref`), and the `pil2-proofman` branch that the one
executable regeneration script clones has been deleted. A third, SP1's, names a
tag that does not contain the generator the TOML credits, because the generator
landed eleven days after that release; the `version` field is a crate version
string covering a window of commits, not a tree. Two of OpenVM's three source
citations point at a superseded commit and a differently-named function whose
arms carry *lower* query counts, so the citation is stale and the number is not.

**The strongest single result**: Airbender's parameters are byte-identical to
what the vendor's own generator emits at its current tip, six months after the
date stamped in soundcalc's copy, recovered at **one hand intervention** despite
the cited commit being unfindable. **The cheapest**: `gen_soundcalc_toml.rs`
computes most of its output from named constants, so reimplementing its
arithmetic in Python re-derived thirty SP1 fields with **zero build minutes**
against a brief that had budgeted ten runner-hours for Rust builds.

Two other findings, both VERIFIED. `reports/risc0.md` and `reports/miden.md`
cannot be regenerated by the code at HEAD (both units are dropped for a missing
`num_constraints`), so two published reports are held-over artifacts, and a
config the loader cannot read yields a *missing row* in `summary.md` rather than
a failure. And `venus.toml`'s header claim of parameters identical to ZisK's
does not hold: one circuit of forty-four differs in seven numeric fields. That
moves no published bit (every per-regime total is identical, and the differing
ALI component is not the binding term), which is why it is published rather than
held.

Six planted faults, six reds, including one positive control. Two earlier
lesions failed and are kept: the first showed that stage 0 detects a perturbed
*input* and never a perturbed *output*, because it regenerates the reports
before diffing. Transfer measure: **1.5 hand interventions per unit** over the
six units with any reproduction path, against a threshold of two. Nothing here
bears on RH (`docs/08`), and every statement is scoped to the artifact at the
pinned commit rather than to any vendor or deployed system.
### Hunt #108: the SWE-bench leaderboard recounts from its own logs, where the logs are there (`r_0dfb8d/`)

**Status: settled for the units run; the archive-wide availability question is
open.** The second transfer test of the reproduction procedure outside
mathematics (paired with issue #140, soundcalc / zkVM): a public checker,
publicly archived accepted objects, a published number. `SWE-bench/experiments`
pinned at `1faa91cade05`, split ids at dataset sha `c104f840cc67`, logs by
anonymous HTTPS GET from `s3://swe-bench-submissions`.

**Five of six preregistered entries recount to the integer** (265, 359, 384,
388, 396 against their own published `results.json`), and each also agrees on
all twelve per-repository sub-counts, which is the cross-check that rules out
two errors cancelling in one aggregate. **Across 2,484 per-instance reports
re-derived from the test results recorded in the same file, zero disagreed with
the verdict that file claims.** The two verdicts were kept apart throughout and
were shown to be able to fail: four planted faults (a flipped `resolved`, a
planted `PASS_TO_PASS` failure, dropped required successes, a removed report)
turned exactly the verdict each should and left the other alone.

**The finding is the other class.** One preregistered entry answers **0 of 500**
documented report keys, all 404, while its predictions and trajectories are
retrievable; a three-key probe across all 134 entries finds **15 answering none**
(thirteen dated 2024-07 or earlier, two dated 2025-08-05, one of which was swept
over all 500 keys to confirm). And the archive's access model is the binding
constraint on anyone repeating this: **anonymous `GetObject` succeeds, anonymous
`ListObjectsV2` returns 403**, so an outside reader can fetch any key they can
name and cannot discover which keys exist. Every absence here is therefore
"absent at the documented key", never "absent from the bucket". The repository
README's claim that an AWS account is required is wrong for GET and silent about
listing. Three smaller measured facts: `tags.checked` is a non-boolean truthy
string (`"false (See README.md …)"`) in six entries, so any consumer writing
`if tags["checked"]` reads six unchecked entries as checked; `no_logs: 0` is
published for an entry that has one instance with a non-empty archived
prediction and no archived report (it changes no count, being an accounting
field rather than a counted one); and **no entry among the 134 states the
evaluation-harness version that produced its number**, which bounds every
"match" above. One reported unavailability was our own bug, an unencoded `+` in
an entry name, found and fixed before publication and recorded because a
reproduction procedure that blames the target for its own fetcher is the failure
this class of hunt exists to catch. Nothing here characterises a team, an agent
or a model, nothing was sent anywhere, and nothing bears on RH (`docs/08`).

### Hunt #104: Erdős #126 is one unit-equation count away (`support_f3ab3e34/`)

**Status: not settled, and the program is named.** Independent-architect arm on
Erdős #126 ($g(k)$ = max size of a set of positive integers all of whose
off-diagonal sums have prime factors in a fixed $k$-element set $S$; is
$g(k) = \exp(o(k))$?), asked to ignore the earlier brief's three lanes and design
the program from the statement. It reduces to a counting question in four
elementary lines. Fix $a_1 \ne a_2$ in $A$, put $D = a_1 - a_2$; then
$c \mapsto ((a_1+c)/D,\, -(a_2+c)/D)$ injects $A \setminus \{a_1,a_2\}$ into the
solutions of $X + Y = 1$ inside the rank-$(k{+}1)$ group
$\langle -1, S, D\rangle$, so $g(k) \le 2 + N(k+1)$ and **$N(r) = \exp(o(r))$
implies the conjecture**. The known $N(r) \le 2^{8r+8}$ (Beukers–Schlickewei) is
the same exponential wall the 1934 bound sits at, while the record construction
(Erdős–Stewart–Tijdeman 1988) produces only $\exp\{(4+o(1))(s/\log s)^{1/2}\}$
solutions: the believed truth about $N$ already implies #126 with room to spare,
which is soft evidence for it. The reduction is not new (it is how the
$c\log|A|$ bounds are proved) and its constant is worse than 1934's; its value is
that it says which door is load-bearing. Four chains are ranked by the strength
of their first unproved step, and the recommendation is *not* the reduction
itself (its first step is strictly stronger than #126) but the $m$-base-point
version, where each extra element adds a free simultaneous unit equation no
counting argument currently exploits. Audit of `r_186989`: its table replicates
at $N = 200$–$400$ (its boxes were slack by $10^2$–$10^3$, not $60\times$), its
composition-refutation direction is sound, and **its loose thread 3 is false**,
refuted by its own witness $A=\{1,3,7,13\}$, $S=\{2,5,7\}$, which has $|A| = 4 >
p-1$ for $p = 3$; the residue pigeonhole closes only at $p=2$, because only there
does $2r \equiv 0$. It also never states a lower bound: $\{1,\dots,m\}$ with
$S$ = primes $\le 2m-1$ gives $g(k) \ge (1+o(1))k\log k/2$, so $g(12) \ge 20$
and the unexplored range is $[k\log k,\, 2^k]$. Nothing here bears on RH
(`docs/08`).

### Hunt #91: Erdős #126, and the composition law that would refute it (`r_186989/`)

**Status: not settled, scout killed on a pre-registered kill condition.** A
30-minute bounded scout on Erdős #126 (for $n$ positive integers $A$, $f(n)$ is
the least number of distinct primes dividing an off-diagonal sum $a+b$; is
$f(n)/\log n \to \infty$?). The run inverted the problem before running any arm:
$f$ and $g(k) = \max\{n : f(n) \le k\}$ are inverse staircases, so the
conjecture is exactly $g(k)^{1/k} \to 1$, and all three briefed arms become
measurements of one integer sequence. Exact branch-and-bound clique search on
the $S$-smooth pair-sum graph, exhaustive inside $[1,N]$ with every witness
re-verified, gives $g(k) \ge 2, 4, 5, 6, 8, 10, 11$ for $k = 1..7$ ($N$ from
$2\cdot10^5$ down to $6000$); widening the box 60× moved not one row, because
every optimal witness lives below 50. Those are lower bounds only, **no upper
bound on $g(k)$ is established**, and seven falling $k$-th roots
($2.00 \to 1.41$) cannot separate a limit of 1 from a limit of 1.3. That is the
"suggestive finite data" the brief named as a kill condition, and the hunt calls
it that. Two things survive. The Formal Conjectures positivity mismatch is
resolved: $f(n-1) \le f_0(n) \le f(n)$, so the `Finset ℕ` statement is faithful
for the limit and wrong for pinned finite values ($f(2)=1$, $f_0(2)=0$,
witness $\{0,1\}$). And the briefed composition arm points the wrong way:
$g(1) = 2$ plus supermultiplicativity gives $g(k) \ge 2^k$ by Fekete, i.e.
$f(n) \le \log_2 n + O(1)$, so a rigorous composition law **refutes** the
conjecture rather than proving it, what #126 needs is an anti-composition
theorem. The only $S$-dependence visible was parity: $2 \in S$ is worth more
than every other structural choice combined ($g_N(3) = 5$ with it, $2$ without).
Nothing here bears on RH (`docs/08`).

### Hunt #105: the Erdős #126 scout survives, its literature claim does not (`support_eccd5f5e/`)

**Status: settled (audit).** Red-team arm against Hunt #91, every claim treated
as hostile input. The mathematics holds. The inverse reformulation
$g(k)=\max\{n : f(n)\le k\}$ and the chain to $g(k)^{1/k}\to 1$ re-prove in both
directions, though the equivalence is conditional on $f(n)\to\infty$ and so on
Erdős-Turán, which #91 does not flag. The positivity lemma
$f(n-1)\le f_0(n)\le f(n)$ is correct step by step, and is sharpened here:
$f(1..4) = 0,1,2,2$ are *exact and proved*, while $f(5)=3$ is not, because
$f(5)\ge 3$ is exactly the open statement $g(2)\le 4$. The composition finding is
correct and understated: Fekete is unnecessary ($g(k)\ge g(1)^k$ by induction),
and since Erdős-Turán gives $g(k)\le 3\cdot 2^{k-1}-1$, a composition law would
squeeze $g(k)$ into $[2^k, 1.5\cdot 2^k]$ and pin the growth constant to within
$3/2$ rather than merely refuting the conjecture; **a proof that $g(3)\le 7$
retires the programme without finding any gadget.** A search written from the
problem statement rather than from `probe.py` reproduces all seven rows
$2,4,5,6,8,10,11$ exactly. Two interpretations are corrected: "every optimal
witness lives below 50" is an artifact of search order, since witnesses are
closed under multiplication by $S$-units and division by $\gcd$ (ours returned
$162\cdot\{1,5,7,11\}$), and the table was never benchmarked against the trivial
1934 construction $A=\{1,\dots,m\}$, which already gives
$g(k)\ge (p_k+1)/2 \sim \tfrac12 k\log k$. **One thread is false**: $|A|\le p-1$
for omitted $p$ fails for every odd $p$ (a class $r$ with $2r\not\equiv 0$ may be
occupied arbitrarily often; $p=2$ is the unique prime where the pigeonhole
works), refuted by $S=\{2,5,7\}$, $A=\{1,3,7,13\}$ from #91's own table. And "no
progress beyond 1934" is misleading: the order of magnitude is indeed unimproved
(confirmed against erdosproblems.com/126 and Füredi-Gyarmati arXiv:2602.07545,
Feb 2026), but Győry-Stewart-Tijdeman 1986 and Erdős-Stewart-Tijdeman 1988 are
directly relevant and neither hunt cited a single paper. New: the four-element
reduction $u+v=w+x$ to a nondegenerate three-term $S$-unit equation is proved,
and the route needs an $\exp(o(s))$ solution count, which the known
$\exp(c\sqrt{s}/\log s)$ lower bound does *not* forbid. Nothing bears on RH
(`docs/08`).

### Hunt #96: Erdős #126, the S-unit route is sound and its theorems are 24.5^k too weak (`support_d5d5ccae/`)

**Status: not settled, and the arm returns the "too weak" verdict its brief
allowed.** A support run for `0897a5a7`, answering the S-unit arm of Erdős #126.
The injectivity the brief asked for exists and is two lines: if every
off-diagonal sum of $A$ is $S$-smooth and $a > b$ lie in $A$, then
$x \mapsto (a+x, b+x)$ injects $A \setminus \{a,b\}$ into the solutions of the
two-variable $S$-unit equation $U - W = a-b$ in positive $S$-smooth $U, W$,
whence $|A| \le 2 + \min_{a>b} N_S(a-b)$. The implication direction was checked:
a solution-count bound gives a $g(k)$ bound gives #126, and not the reverse, so
unlike arm 3 of Hunt #91 this route points the right way. Fixing three or more
base elements is **strictly worse**, because the resulting coefficients are
differences of elements of $A$ and carry primes outside $S$, which forces the
rank-based bounds ($2^{16k+16}$) instead of Evertse's $S$-based one. Charging
Evertse (1984), $3\cdot 7^{d+2s}$ with $d=1$, $s=k+1$, gives
$g(k) \le 2 + 3\cdot 7^{2k+3} \approx 1029\cdot 49^k$: **weaker than the 1934
Erdős–Turán bound $3\cdot 2^{k-1}$, and than Erdős–Surányi's $2^k$, by a factor
about $24.5^k$.** Measurement then locates the slack. Enumerating all $S$-smooth
integers to $10^{14}$ and counting $U-W=d$ exactly inside that box reproduces
Lehmer's published Størmer table for $d=1$ ($1,4,10,23,40,68,108,167$ for
$k=1..8$), and at $k=7$ the quantity Evertse bounds by $7.0\times10^{14}$ has a
measured value of $96$, against the elementary $128$. **The route is not what is
lossy; the theorem is, by thirteen orders of magnitude.** What would suffice is
stated: dropping the base $49$ below $2$ already beats 1934, and $\exp(o(k))$
settles #126, which nothing known forbids since the best lower bound
(Erdős–Stewart–Tijdeman) is $\exp((4+o(1))(s/\log s)^{1/2})$. No improved bound
on $g(k)$ is proved here, and the one missing combinatorial lemma is named: every
admissible $A$ beyond some size must contain a pair whose difference has few
solutions. Nothing here bears on RH (`docs/08`).

### Hunt #95: Erdős #126, the signature model has no ceiling to raise (`support_baf4cde6/`)

**Status: lane closed, by proof rather than by a failed attempt.** Support arm
for hunt #91 (`r_186989/`), asked whether prime-valuation signatures plus
entropy, VC, containers, dependent random choice or forbidden patterns can show
that an $S$-summable set ($a+b$ free of primes outside $S$, $|S|=k$) has
subexponential size. Answer: no, and the reason is not difficulty. **Theorem B:
for every prime bound $P$ and every $S$ containing 2, arbitrarily large sets
satisfy every constraint $S$-summability imposes at primes $\le P$** (take
$A = \{1+iM\}$ with $M$ the product of the odd primes $\le P$ outside $S$, so
every off-diagonal sum is $\equiv 2 \bmod M$; checked at $P=60$ with $|A|=200$
against Erdős–Turán's 12). So any argument reading a fixed finite prime set is
consistent with $|A| = \infty$ and can prove nothing; the hypothesis binds only
at primes above $\max A$, which is the cofinite smoothness condition itself and
not a signature. That also explains #91's puzzle that every optimal witness
lives below 50 inside a box of $2 \cdot 10^5$. The one non-vacuous use of the
local data is **Lemma A**: for $p \notin S$, $A$ meets at most $(p+1)/2$
residue classes mod $p$, never both $r$ and $-r$, at most one element in class
0, and for $p=2$ this gives $|A| \le 2$ uniformly in $k$ (the proved form of
#91's parity observation). Lemma A also **refutes** #91's loose thread
"$|A| \le p-1$ when $p \notin S$": $A = \{1,3,7,13\}$, $S = \{2,5,7\}$ has
$3 \notin S$ and $|A| = 4$, and a sweep at $N=400$ reaches 5. Pushed to CRT
injectivity, Lemma A gives a real theorem that is strictly worse than 1934: it
saves exactly **one bit per prime outside $S$** against a modulus that must
already exceed $N$, landing at $2^{53}$ where Erdős–Turán gives $2^{5.6}$ at
$\log_2 N = 64$. #91's own top door survives this arm: each 4-subset gives a
non-degenerate three-variable $S$-unit equation, whose ESS count is worse than
1934 by $\approx 5\cdot10^{10}$ in the exponent but is not known to be
exponential, and the missing lemma there is a fiber count, not a unit-equation
bound. #91's other claims were re-derived independently and hold, including two
reproduced $g_N(k)$ rows. Nothing here bears on RH (`docs/08`).

### Hunt #93: Erdős #126 is a $\forall S$ statement, so every search we own can only refute it (`support_8ea74995/`)

**Status: settled, for the bounded question it was given.** The formulation arm
of a multi-arm attempt on Erdős #126, run as support for a live sibling. It
proves the equivalences hunt #91 asserted, $f(n) \le k \iff n \le g(k)$ as a
Galois connection, and the equivalence of $f(n)/\log n \to \infty$,
$\log g(k) = o(k)$, $g(k)^{1/k} \to 1$, $f(2^m)/m \to \infty$ and *"the average
multiplicative gain per added prime tends to 1"*, and finds #91's asserted
mathematics sound, with one "iff" that should have been an implication.
Three things are new. **The refutation direction generalises**: not only
supermultiplicativity but *any* law $g(k+C) \ge \lambda g(k)$ with $C$ and
$\lambda>1$ constant refutes the conjecture, so every composition, gluing or
doubling gadget with bounded prime cost is a refutation instrument; the
supermultiplicative case needs no Fekete, just induction from $g(1)=2$.
**One of #91's loose threads is false**: "$p \notin S \Rightarrow |A| \le p-1$"
fails for every odd $p$ (take $A \equiv 1 \bmod p$), and had it held it would
have given $g(k) \le p_{k+1}-1$ and settled the problem in three lines, it
agreed with all seven measured data points anyway, which is the lesson. What
the pigeonhole really proves is a bound on the number of **residue classes**
$A$ occupies, $\le (p-1)/2 + 1$; $p=2$ is the unique prime for which that
bounds $|A|$, and that is why parity is special. **And the quantifier settles
the strategy**: #126 is $\forall S\,\forall A$, every enumeration yields
$\exists S\,\exists A$, so no clique search in a box can ever contribute to a
proof, #91's three failures have one cause and it is not budget. Also proved:
$2 \in S$ and $\gcd A = 1$ are valid normalisations for upper bounds, while
$\max A \le N$ and "$S$ = the first $k$ primes" are not; each 4-subset of $A$
gives a non-degenerate 3-term $S$-unit solution, making #126 conditional on a
subexponential unit-equation count and on a multiplicity nobody has bounded.
#91's thread 4 closed in the negative: no 4-subset of the first eight primes
beats $g_N(4)=6$. Nothing here bears on RH (`docs/08`).

### Hunt #101: Erdős #126, the descent arm, loss 2 per prime is a wall, and the omission claim is false (`support_7ddfee4b/`)
**Status: settled, in both directions.** Support run for the `r_186989` scout,
answering one bounded question: is there a descent recurrence for $g(k)$ whose
per-prime loss tends to 1, and does omitting a small prime from $S$ cap $|A|$?

The omission claim is **false for every prime**. Omitting $p$ forces the
residues of $A$ mod $p$ to avoid the pairing $r \leftrightarrow -r$, which caps
the number of *occupied classes* at $(p+1)/2$ and caps the size of a
*self-paired* class at 1. It caps $|A|$ only when every class is self-paired,
which happens only at $p = 2$. For odd $p$, any $A \subseteq 1 + p\mathbb{Z}$ has
all pairwise sums $\equiv 2 \pmod p$, so $|A|$ is unbounded with $p \notin S$;
witnesses at $p = 3,5,7,11$ are verified in `results.json`. The proposed
$|A| \le p-1$ also fails at $p=2$ by one ($\{1,2\}$, $S = \{3\}$).

The descent does exist. Deleting one odd prime $p \in S$ splits $A$ into the
part divisible by $p$ and two sets admissible for $S \setminus \{p\}$ (the two
halves of $(\mathbb{Z}/p)^\times$ under negation), giving
$g^*(k) \le 2\,g^*(k-1) \le 2^k$ for **primitive** $A$ (no element divisible by
a prime of $S$), tight at $k = 1, 2$, $\{1,5,7,11\}$ with $S=\{2,3\}$ is
primitive and has $2^2$ elements. But the loss cannot be pushed below 2 along
this route, and that is a theorem rather than a failure to find one: parity,
residue classes, prime deletion and the power-of-2 lemma all factor through a
relaxation (cover $K_n$ by the negation-pairings of $k-1$ odd primes plus a
triangle-free graph), whose optimum is **exactly $2^k$**, attained by
$\{0,1\}^{k-1}\times\{0,1\}$ with a perfect matching. So an $\exp(o(k))$ bound
must read something the relaxation discards: CRT rigidity, size, or $S$-unit
counting, which is the door `r_186989` ranked first, now closed-by-proof
underneath rather than judged.

Not settled, and flagged as a real hole: the bound is for primitive sets only.
The divisible part escapes the descent because $(S, pA)$ is admissible whenever
$(S,A)$ is, so $\gcd A = 1$ (which is free) is strictly weaker than
primitivity. Nothing here improves the classical $g(k) < 3\cdot 2^{k-1}$, and
nothing here bears on RH (`docs/08`).

### Hunt #102: Erdős #126, the counterexample arm, the tensor lane is an $S$-unit equation (`support_6cdfd2e3/`)

**Status: not settled. No counterexample, and one lane closed conditionally.**
Support run for Hunt #91, asked for an algebraic, CRT, recursive, tensor or
composition construction with $|A|$ exponential in $|S|$, and explicitly allowed
to refute #126. None was found. What came out instead is a reduction, an
ordinary argument, unreviewed: for the tensor $C = A\cdot B$, the grid-line
pairs are free ($ab+ab' = a(b+b')$) and every **mixed** pair satisfies
$u+v = (a+a')(b+b')$ with $u = ab+a'b'$, $v = ab'+a'b$, a denominator that is
smooth for free. Dividing by it, $x = u/M$, $y = v/M$ solve $x+y=1$ in
$(S\cup T)$-units, and $x$ is a non-constant Möbius function of $b/b'$, so
$|A|, |B| \le N(S\cup T)+1$ where $N$ counts solutions of the $S$-unit
equation. Unconditionally that is weaker than Erdős–Turán 1934; conditionally it
is the finding: **if $S$-unit counts are subexponential, no tensor construction
can refute #126**, and an exponential one would exceed every known construction
(the run cited Erdős–Stewart–Tijdeman's $\exp(c(s/\log s)^{1/2})$; re-landing
added Konyagin–Soundararajan's $\exp(s^{2-\sqrt2-\varepsilon})$, arXiv
math/0604453, read at the abstract only). The argument does not extend to
general $A$, and that is exactly why it closes the tensor lane and no more: for
arbitrary $a,b,c,d \in A$ the common value $a+b+c+d$ need not be smooth, so
there is nothing to divide by. Two corrections to Hunt #91 travel further than
the non-result. The refutation bar is far lower than a composition law:
$g(k+k_0) \ge c\,g(k)$ for *any* fixed $k_0$ and $c>1$ already gives
$\liminf \log g(k)/k > 0$; that is Hunt #93's amplification result
(`support_8ea74995/`), reached independently, and not new here. The converse
fails, and that is new: a staircase $G(k) = 2^{k_j}$ on $[k_j, k_{j+1})$
refutes #126 while failing every uniform doubling law off a density-zero set,
so **an anti-composition theorem is not sufficient for #126**, which the
parent's closing sentence implies it is (also an ordinary argument,
unreviewed). Measured, by exact integer arithmetic inside bounded boxes: an
independent clique search reproduced rows 1–7 of the parent's table from boxes
20–500× smaller and added the lower bounds $g(8) \ge 14$, $g(9) \ge 15$; on
the parent's optima, the cheapest dilated union $A \cup cA$ costs 6 extra
primes at $k=2$ and 7 at $k=4$, and none exists at $k=3$ (multipliers
$c \le 200$, extra primes from the first twelve). Also in the run and already
on main: $g(k) \ge \lfloor (p_{k+1}-1)/2 \rfloor$ from $A = \{1,\dots,m\}$
(Hunts #104, #105), and dilation invariance against the parent's "every
optimal witness lives below 50" (Hunts #103, #105, #107), here with
$\{113,399\}$ and $\{16,80,112,176\}$ as counter-witnesses. Two of the run's
statements did not survive to landing and are annotated in place: its loose
thread "$|A| \le p-1$ when $p \notin S$" was already refuted (Hunts #93, #95,
#101, #103), and its sumset-counting section understated the height the lemma
forces (`RESULTS.md` §6, corrected against Hunt #107). Nothing here bears on
RH (`docs/08`).

### Hunt #103: Erdős #126, the residue lemma is false and the box was never the question (`support_60982bf6/`)

**Status: settled, as a support answer.** Exact-search arm for hunt #91's
parent: redo `r_186989`'s computation ranging over choices of $S$ instead of
freezing the first $k$ primes, and use the computation only to discover and
falsify structural lemmas. Exhaustive over **all** $\binom{9}{k}$ subsets of the
first nine primes for $k \le 5$ (381 searches, a solver rewritten to build edges
from the $S$-smooth sums rather than by scanning $O(N^2)$ pairs), the first $k$
primes are never beaten, so the frozen constant #91 called "the door with
genuine trade shape" is slack. What the sweep produced instead is two lemmas.
**Proved (normalization):** $\gcd(A)$ is always $S$-smooth, $A/\gcd(A)$ is
admissible, and $mA$ is admissible for $S$-smooth $m$, so the admissible sets
are *exactly* the $S$-smooth dilates of primitive ones. That removes #91's
puzzle that widening the box "changed not one row": a wider box only contains
bigger copies of the same small set, and the right question is the height of the
smallest primitive optimum, not the width of the box. **Refuted:** #91's
"only clean iterable statement", $|A| \le p-1$ when $p \notin S$, is false for
every odd $p$, for $r \not\equiv 0$, $r+r \not\equiv 0 \pmod p$, so arbitrarily
many elements may share one class and the pigeonhole bounds the number of
occupied classes, never $|A|$; $p=2$ is the unique prime with $2r \equiv 0$ for
all $r$, which is why parity works there and nowhere else. Counterexamples at
$p = 3, 5, 7$ (the smallest, $S=\{2,5,7\}$, $A=\{1,3,7,13\}$, sits inside #91's
own table). Also refuted, box-conditionally: $g$ is **not** monotone in the size
of the primes ($g_{20000}(\{2,3,11\}) = 4 < 5 \le g(\{2,3,13\})$, 29 violations),
so any $S$-level lemma must be about a prime's additive position relative to the
smooth semigroup, not its size. The conjecture offered is *uniformly bounded
height*, and both natural explicit constants for it were killed by the run's own
data ($h(\{2,3,5\}) = 47 > 2^{k+2}$, $h(\{2,3,7,13\}) = 159 > 2^{k+3}$); it is
consistent with all 15 measured $S$ and verified for none. No upper bound on
$g(k)$, as before. Nothing here bears on RH (`docs/08`).

### Hunt #92: the Erdős–Turán factor 2 is not lost anywhere, it is the whole statement (`support_517b887f/`)

**Status: settled, negatively.** Support arm for Hunt #91, asked whether the
1934 proof's factor 2 per prime can be beaten by processing primes jointly or
in a different order. Answer: no, and the reason is structural rather than
arithmetic. Reconstructed, the proof has exactly two steps: a base case
$c(A) \le 2$ (three positive integers cannot have all three pairwise sums
powers of 2, by $2a = 2^x+2^y-2^z < 0$), and one binary $\pm$ residue choice per
odd prime, assembling to $g(k) \le 2\cdot 2^{k-1} = 2^k$ (Erdős–Surányi; the
1934 $3\cdot2^{k-1}$ is the same architecture with a weaker base). Since
$c(A) \in \{1,2\}$ always, "every admissible $A$ has $c(A) \ge |A|/\varphi(k)$"
is equivalent to $g(k) \le 2\varphi(k)$, and $c(A)$ is defined by a maximum
over subsets, so it is blind to prime order and to grouping. **Improving 2 to
$2-\delta$ inside this architecture is the target restated, not a sharpening of
it.** At the residue level joint processing is provably worthless: the CRT
configuration $x_\varepsilon \equiv \varepsilon_i \bmod q_i$ has $2^s$ points
whose largest jointly clean subset is 1 (brute-forced, $s \le 4$). Two defects
in the usual sketch fell out and are witnessed exactly: the per-prime halving
$|B'| \ge |B|/2$ is **false** ($A = \{1,3,15,21,33\}$, sums
$\{2,3,11,17\}$-smooth, best 3-clean subset $\{1,3\}$ of size $2 < 2.5$; the
class-0 term is not removable, and $q\cdot C \cup \{x\}$ makes the failure
unbounded), and the assembled $c(A) \ge n/2^s$ is **false without primitivity**
($A = 3\cdot\{1,3,7,17,47\}$ has $c = 1 < 5/4$; dividing by $\gcd$ repairs it).
Reordering rescues individual instances ($q=11$ before $q=3$ turns $0.4n$ into
$0.8n$) and nothing at the theorem level. A sweep of 104,183 admissible sets in
three small boxes found zero primitive violations of the repaired lemma and
exact tightness at $\{1,2,4,8\}$. The one sub-question left that is not
circular is a two-set bound on how much of $A$ one odd prime may divide, which
is Győry–Stewart–Tijdeman territory. Nothing here bears on RH (`docs/08`).

### Hunt #107: the Erdős #126 size dichotomy misses by one power of the radical (`support_95bb5cb7/`)

**Status: the arm is settled negative; the conjecture is untouched.** A support
run for a session working Hunt #91, asked whether a size dichotomy closes Erdős
#126: either $A$ is spread out enough for a descent, or it lies in a controlled
interval where smooth-number counts apply. It does not, and the failure point is
now exact rather than rhetorical. The counting horn is
$|A| \le 1 + \Psi(2N,S)$ with $N = \max A$, and writing
$\log 2N = c\log\mathrm{rad}(S)$, the run pins $\log\Psi/k$ from **both** sides,
Rankin above and the simplex lattice-point volume below: it tends to zero iff
$c \to 0$, and at $c \ge 1/2$ the lower bound is $0.32k$, so above
$\max A = \mathrm{rad}(S)^{1/2}$ the horn is not unproven, it is false. So the
horn delivers $\log g(k) = o(k)$ **iff** it is handed
$\max A = \mathrm{rad}(S)^{o(1)}$, and no choice of $S$, scale, split or
smooth-count estimate moves that: it is a property of $\Psi$, not of the
argument. The other horn cannot supply it, for two independent reasons. First,
measured: after the only available normalisation ($\gcd(A) = 1$; translation
shifts every sum by $2t$ and is unavailable, so height is a genuine invariant),
the height of a primitive admissible set of sub-extremal size is **unbounded**,
tracking the search cutoff linearly over eleven orders of magnitude, from
$\{217,1241,7975\}$ up to
$\{3772777922353,\,41980806987569,\,559177175498959\}$ at $S=\{2,3\}$. A descent
that reaches a smaller set finds no interval control waiting there. Second,
structural: an admissible clique yields only the *four*-term relation
$(a+b)+(c+d)=(a+c)+(b+d)$, and every height theorem for $S$-smooth numbers
(Baker–Győry, $abc$) is three-term; four terms have only solution *counts*
(Evertse–Schlickewei–Schmidt, $\exp(O(k))$, and Erdős–Stewart–Tijdeman show
counts cannot fall below $\exp(c(k/\log k)^{1/2})$). A count is not a height.
Granting even the best imaginable three-term outcome, $abc$ gives
$\max A \ll \mathrm{rad}(S)^{1+\varepsilon}$, which is $c \to 1$, exactly where
the lower bound reads $1.01k$. **The gap is one power of $\mathrm{rad}(S)$, not
an exponential**, which is why the arm looks tempting and why it still cannot
close. The audit half re-verified all seven of Hunt #91's witnesses from scratch
by full trial division (all valid), confirmed its $f(n-1)\le f_0(n)\le f(n)$
lemma and its Fekete argument, and **corrected one claim**: "every optimal
witness has all elements $< 50$" is false. Enumerating through the *sums* rather
than the elements, which is the exhaustive universe for a constraint on sums,
gives exactly six primitive extremal 5-sets for $S=\{2,3,5\}$ with all sums
$\le 10^5$, and $\{5,11,25,245,475\}$ is one of them, max element $475 =
\mathrm{rad}^{1.81}$, not $\mathrm{rad}^{1.13}$. Hunt #91 reported one witness
per $k$ and generalised from it. Same enumeration adds a small positive: no
6-element set for $S=\{2,3,5\}$ has all pairwise sums $\le 10^5$. Not settled:
whether extremal-size sets have bounded height (the data hints yes and it would
be circular for this arm anyway), the ladder at $k=4$ (the enumeration exceeded
ten minutes), and any upper bound on $g(k)$ at all. Nothing bears on RH
(`docs/08`).

### Hunt #94: Erdős #126, the p-adic block-pruning arm, and a target set one notch too low (`support_d176e366/`)

**Status: not settled. No block lemma below base 2, and a restricted-class
obstruction for residue-only pruning (`ALIGNMENT.md` §5, disposition 2); the
attempt below base 2 is unresolved.** Lemmas 1 and 2 and Theorems 3, 3′ and 4
are ordinary arguments, unreviewed; the checks are exact finite ones on blocks
of at most three primes, and the cross-prime correlations are measurements on
$|A| \le 11$. Landed 2026-10-21 from a local-only branch, `support/d176e366`,
that was never pushed; PR #144 counted the arm among the seven that "produced
no branch at all". A support run for `r_186989`, asked whether a block of $r$
primes can be pruned from $S$ while retaining more than $2^{-r+o(r)}$ of $A$.
It answers the question and contradicts its premise. **Lemma 1**: pruning a
block $T$ is the independent-set problem for $\bigcup_{p\in T} G_p$, where
$G_p$ is the antipodal graph mod $p$ (disjoint complete bipartite graphs
between class $c$ and class $-c$, plus a clique on the class $c \equiv -c$),
so valuations beyond $v_p(a) = 0$ are invisible here and "valuation vector"
means "residue vector", which is why the ultrametric framing buys nothing.
**Lemma 2**: a genuinely joint one-shot random half-system argument gives
retention $\ge 2^{-r}$ over the elements coprime to the block, landing on
exactly the constant that pruning one prime at a time gives. **Theorem 3**: on
a full residue system mod $\prod T$ the optimum is exactly
$\prod_{p\in T}\frac{p-1}{2} + r$ (matched by exhaustive branch-and-bound for
$\{3,5\},\{3,7\},\{5,7\},\{3,5,7\}$: 4, 5, 8, 9, four for four), which is
*below* $2^{-r}|A|$, so no argument reading only residues mod $\prod T$ can
beat base 2; and by **Theorem 4** ($g(k) \le 2/\rho_{\min}(k) \le 2g(k)$, from
the endgame lemma that no three integers have all pairwise sums powers of 2)
the block programme is not a proxy for Erdős #126 but a restatement of it. Two
consequences the brief did not anticipate: retention $2^{-r+o(r)}$ **is** the
Erdős–Turán bound, so the named target is worth nothing even if proved, and
only base $c<2$ counts; and the smoothness hypothesis is used nowhere in this
arm except the endgame, only divisibility. Measured on the seven verified
witnesses, real admissible sets beat $2^{-r}$ retention by up to a factor of
11.6 with strong positive correlation across primes, reported as a direction
indicator only, since $|A| \le 11$ and the full-block column is Theorem 4
restated rather than evidence. Audit of `r_186989`: all seven witnesses
re-verified admissible, its power-of-2 lemma re-derived independently, and its
loose thread 3 (a claimed $|A| \le p-1$ for $p \notin S$) **refuted**:
$\{1, 1+q, 1+2q, \dots\}$ has every pair sum $\equiv 2 \bmod q$ at unbounded
size. One drafted claim of the run's own ($\varphi$ = number of sign-orbits
met) was false and is kept in the file with its counterexample. Overlap with
main, recorded in `RESULTS.md`: that residue data cannot beat base 2 is also
the finding of Hunts #92 and #101 (#101's relaxation is this arm's covering
reformulation, solved exactly), and the loose-thread-3 refutation was on main
already (Hunts #93, #95, #101, #103). The run's remark that the optima "live in
the small integers" is annotated in place, since Hunts #103, #105 and #107
refuted it. Nothing bears on RH (`docs/08`).

### Hunt #97: Erdős #126, the low-rank matrix arm was already in the literature (`support_99fc686a/`)

**Status: not settled. A verdict restricted to the two-row $S$-unit route and
to the counting bounds now known: the arm is a rediscovery, and with those
bounds it loses to a proof from 1934.** Alon–Solymosi was read from the PDF
(primary). The Evertse and Beukers–Schlickewei constants came from search
summaries, which the run itself rates medium-low, and both are hedged in
`RESULTS.md`: Evertse's form agrees with Győry–Stewart–Tijdeman's quotation of
it as read in primary text by Hunt #143, while the Beukers–Schlickewei form
$2^{8(r+2)}$ differs from the $2^{8r+8}$ on main in Hunt #104. The two-row
collapse is an ordinary argument, unreviewed. Landed 2026-10-21 from a
local-only branch, `support/99fc686a`, that was never pushed; PR #144 counted
the arm among the seven that "produced no branch at all". Support run for
`r_186989`'s successor, on one arm: the symmetric matrix $M_{ij} = a_i + a_j$
has rank $\le 2$ and $S$-unit off-diagonal entries, so what do results on
low-rank matrices over finitely generated multiplicative groups give? Answer:
**Alon and Solymosi, "Rank of matrices with entries from a multiplicative
group", Corollary 10** constructs this exact matrix, observes its rank is at
most two, and concludes $|A| \le f(r)$. Their explicit form $\log n \le r d^8$
at $d = 2$ gives $\exp(256k)$ against Erdős–Turán's $3 \cdot 2^{k-1}$. Rank 2
does not need that machinery, and the run's own route is cheaper: fix distinct
$a, b \in A$; then for every other $d$, $(a+d) - (b+d) = a - b$, so
$(a+d, b+d)$ solves a **two-variable $S$-unit equation** with coefficients not
depending on $d$, and $d \mapsto a+d$ is injective. Hence
$g(k) \le 2 + N_{\mathbb{Q}}(k) \le 2 + 3 \cdot 7^{2k+3}$ (Evertse 1984), base
49 against base 2. **No improvement, and none available from today's counting
bounds**: the loss is entirely in the Diophantine input, measured at $k=7$ as
9 solutions forced against $7\times10^{14}$ permitted. The nondegeneracy
question the brief asked to isolate has an exact answer and it is
anticlimactic: in the two-row route there is none at all (a two-term
equation's proper subsums are units, hence nonzero), and in the general-rank
route it is precisely Alon–Solymosi's *rectangle condition*, which for this
matrix expands to $(a_j - a_i)(a_j - a_k) \ne 0$, i.e. the distinctness of
$A$. That condition is not decoration: their Theorem 1 assumes diagonal
entries lie outside $\Gamma$, and $2a_j$ often is an $S$-unit (in 7 of 7
witnesses). One thing kept, direction checked: **if two-term $S$-unit
equations have $\exp(o(k))$ solutions then Erdős #126 is true**, and the known
lower bound $\exp(k^{1/2+o(1)})$ (Erdős–Stewart–Tijdeman) does not obstruct
that. The converse fails. Overlap with main, recorded in `RESULTS.md`: the
two-row collapse is the reduction of Hunts #96 and #104, and it is
Győry–Stewart–Tijdeman 1986 §3 (quoted by Hunt #143, landed with this entry),
which answers the run's open question whether it is in the literature; the
four-element route of its §3 is that of Hunts #93, #95 and #105. Nothing bears
on RH (`docs/08`).

### Hunt #98: the cover premise of Erdős #126 has no bound in it (`support_d0f0aefb/`)

**Status: not settled. A restricted-class obstruction for incidence and cover
data, plus a refuted candidate (`ALIGNMENT.md` §5, dispositions 2 and 1), with
a conditional bound and a one-way reduction as by-products.** Theorems 1 to 4
are ordinary arguments, unreviewed, and one clause of Theorem 1 was corrected
on landing (below); the two literature bounds behind Theorem 4's door were
checked by web search, not read in the sources, and the reduction's prior art
is unsearched (the run says to assume folklore). Landed 2026-10-21 from a
local-only branch, `support/d0f0aefb`, that was never pushed; PR #144 counted
the arm among the seven that "produced no branch at all". A support arm
launched by Hunt #91's run, asked whether the graphs $G_p$
($a \sim b \iff p \mid a+b$), which together cover $K_n$, admit a cover,
Ramsey, rank or container bound. **They do not, and that is argued in full:**
$A = \{1\} \cup \{2(3j+1)\}$ with $S = \{2,3\}$ has $\gcd = 1$ and its two
residue graphs cover $K_n$ for *every* $n$, so no theorem deriving a bound on
$n$ from the incidence data alone can exist. Generic graph methods stall
because the combinatorial shadow of the problem is realizable at every size;
the content is in the arithmetic the shadow discards. Two things came out of
the rubble. First, a structure theorem: mod $p$ the matrix $(a_i+a_j)$ has
rank $\le 2$, and $G_p$ is the disjoint union of complete bipartite blocks
between the classes $r$ and $-r$ among the elements prime to $p$ (one clique
among them for $p = 2$) and a single clique on the multiples of $p$. The run
stated a finer level-set structure on the multiples of $p$, which fails above
level 0 on its own $k=7$ witness and takes its chromatic corollary
$\chi(G_p)\le 2T_p$ with it ($\{3,15,21,33\}$, $S=\{2,3\}$, has $G_3 = K_4$ and
$T_3 = 1$); it is corrected in place in `RESULTS.md` §2. Under the hypothesis
that every element is coprime to $\prod S$ the structure peels to
$|A| \le 2^k$, sharper than Erdős–Turán's $3\cdot2^{k-1}$ by $3/2$ (unaffected
by the correction); the hypothesis resists normalisation because
$\{a \in A : p \mid a\}$ divided by $p$ is again a set of the same kind over the
same $S$. Second, and the thing worth keeping: using the *exact* valuations
rather than the graph gives $g(k) \le 3 + N_3(k)$, where $N_3(k)$ counts
nondegenerate solutions of $x+y+z=1$ in $S$-units over the **same** $k$ primes,
by an injective map. The run said the third term is what keeps $S$ from
growing by the primes of $a_1-a_2$; it is not needed for that, since Evertse's
bound is uniform in the coefficients (Hunts #96 and #104), and that remark is
corrected in place too. The implication runs one way only, and it runs the
useful way: $N_3(k) = \exp(o(k))$ would prove Erdős #126. Known lower bounds
for such counts are $\exp(k^{1/2+o(1)})$, so nothing known closes that door.
Hunt #91's loose thread "$|A| \le p-1$ when $p \notin S$" is **refuted**:
$\{1,4,124\}$ with $S = \{2,5\}$ has all three elements $\equiv 1$ mod $3$ and
$|A| = 3 > 2$; only $p = 2$ bounds anything, because there every residue class
is its own negative. All seven of Hunt #91's witnesses were re-verified.
Overlap with main, recorded in `RESULTS.md`: the coprime bound $2^k$ is Hunt
#101's primitive descent (and Hunt #94's Lemma 2, landed with this entry); the
three-term reduction sits beside the four-element reductions of Hunts #93, #95
and #105 and adds the injectivity they lack; the loose-thread-3 refutation was
on main already (Hunts #93, #95, #101, #103). Nothing here bears on RH
(`docs/08`).

### Hunt #99: Erdős #126, the narrowest upgrade is a unit-equation count (`support_311c14a5/`)

**Status: not settled, and no new bound on $g(k)$. A sufficiency reduction
and a quantitative comparison, both ordinary arguments, unreviewed; the
attempt at a bound is unresolved and one parent thread is a refuted candidate
(`ALIGNMENT.md` §5).** The cited constants came from one web search each and
the run says not to quote their exponents as pinned. Landed 2026-10-21 from a
local-only branch, `support/311c14a5`, that was never pushed; PR #144 counted
the arm among the seven that "produced no branch at all". Support run for Hunt
#91, working the additive-combinatorics arm. The deliverable is an elementary
reduction with no loss: if $A$ is admissible for $S$ and $a \ne b$ in $A$ with
$d = a-b$, then $c \mapsto (a+c, b+c)$ injects $A \setminus \{a,b\}$ into the
solutions of $(1/d)X + (-1/d)Y = 1$ in $S$-units, so $g(k) \le 2 + E(k)$ where
$E(k)$ counts solutions of $\alpha X + \beta Y = 1$ in $S$-units, uniformly in
$\alpha,\beta$. Keeping the constants in the *coefficients* rather than the
group holds the rank at exactly $k$. Hence **$E(k) = \exp(o(k))$ implies Erdős
#126**, and that is the narrowest upgrade the run could name; the converse does
not hold and is not claimed. Quantitatively the route is today much *weaker*
than 1934: the run quotes Evertse as $g(k) \le 2 + e^{4k+10}$, base $e^4$
against Erdős–Turán's base $2$. That form is from a search; GST's primary-text
quotation of Evertse, $3\cdot7^{2k+3}$ (Hunt #143, and Hunts #96 and #106), is
smaller for every $k$ and gives base 49, and `RESULTS.md` §3 annotates the
discrepancy in place without changing the verdict. The route's floor is
$\exp(\Theta(\sqrt{k/\log k}))$ from Erdős–Stewart–Tijdeman, which is
$\exp(o(k))$, so the known extremal examples do not obstruct the target. The
three briefed tools are reported inapplicable with reasons: Freiman needs small
doubling and these sets have maximal doubling, sum-product needs the
multiplicative structure on $A$ rather than on $A+A$, and the additive-energy
inequality is measurably dominated by a one-line pigeonhole. Two audit results
against Hunt #91: its composition law, combined with the Erdős–Turán upper
bound, forces $g(k) = 2^k$ *exactly* rather than merely $\ge 2^k$, which makes
it falsifiable at $k=3$ (it needs an 8-element set; exhaustive search inside
$[1, 60\,000]$ finds 5); and its loose thread that the parity cap generalises
mod odd primes is **false**, since $A$ may sit in a single nonzero class mod
$p$, with witness $S=\{2,5,7,11\}$ omitting $3$ and $A = \{1,9,13,19,31\}$ of
size 5. All seven of Hunt #91's witnesses re-verified; $g_N(3)=5$ independently
reproduced by a from-scratch solver. Overlap with main, recorded in
`RESULTS.md`: the reduction is that of Hunts #96 and #104; the composition
sharpening tightens Hunt #105's corridor $[2^k, 1.5\cdot2^k]$, which already
noted that $g(3)\le 7$ retires the programme, and Hunt #93 has the general
amplification form; loose thread 3 was refuted on main already (Hunts #93,
#95, #101, #103), and the run's OEIS thread was closed by the literature arm
(Hunt #143). Nothing here bears on RH (`docs/08`).

### Hunt #100: Erdős #126, the product route has a ceiling of 2 (`support_95a76f59/`)

**Status: not settled. A restricted-class obstruction (`ALIGNMENT.md` §5,
disposition 2) for the unweighted product $P = \prod_{a\ne b}(a+b)$ read
through $k \ge B(A)$, with the prime masses estimated from distinctness,
range, residue counts, whole-set gcd normalisation and the one-step recursion
on multiples of $p$; weighted or subset products, and any estimate that reads
the additive structure of $A$, are outside the class, as the run's own doors
section says.** The arguments are ordinary, unreviewed; the large-sieve
normalisation of (5b) was not re-checked, which the run flags itself; the
values of $B$ are floating-point measurements. Landed 2026-10-21 from a
local-only branch, `support/95a76f59`, that was never pushed; PR #144 counted
the arm among the seven that "produced no branch at all" and cited it as the
closed "Analytic NT" lane. A support run for the #126 scout, asked to attack
the original product $P$ and lower-bound its number of distinct prime
divisors. Within that class it is closed instead. The product yields exactly
one inequality, $k \ge B(A) = \log P / \max_p (e_p \log p)$, and two
adversarial families of distinct positive integers with $\gcd = 1$ cap $B$:
$\Omega' = \{1\}\cup\{i p^m\}$ drives $B \to n/(n-2) \to 1$ against any estimate
built from distinctness, range and residue counts, and
$\Omega = \{ip^m+1\}\cup\{jp^m-1\}$, which no gcd normalisation or one-step
recursion touches, drives $B \to 2$. Measured $B = 1.041$ and $2.125$. So the
product route, in this class, cannot reproduce Erdős–Turán's $\log_2 n$, let
alone improve it, and on the seven known optimal witnesses it already loses to
$\log_2 n$ at $k \ge 6$. The smooth-counting lane is capped too:
$k \ge \log n/\log\log 2X$ beats $\log_2 n$ only when $X < e^2$. Two things
survive: a large-sieve sparsity bound $n = O(\sqrt X \log X)$ from the fact
that $A$ occupies at most $(q+1)/2$ classes mod every prime $q \notin S$, and an
audit finding that retires one of Hunt #91's loose threads (its "prove
$|A| \le p-1$ by pigeonhole mod $p$" is false: $\{1+iM\}$ is antipodal-free mod
every odd $q \le Q$ at any size). Number #100 was assigned by the launching
brief, not chosen. Overlap with main, recorded in `RESULTS.md`: the
normalisation is Hunt #103's lemma, the occupancy count $(q+1)/2$ is Hunt #95's
Lemma A, the smooth-counting inequality is Hunt #107's counting horn, which
pins it from both sides, and the loose-thread refutation was on main already
(Hunts #93, #95, #101, #103). The run's open question whether $\max A$ is
bounded in terms of $(n,k)$ is answered for sub-extremal sizes by Hunt #107
(unbounded height at $S=\{2,3\}$), annotated in place in `RESULTS.md` and
`HANDBACK.json`. Nothing here bears on RH (`docs/08`).

### Hunt #106: Erdős #126 reduces to counting $S$-unit equations (`support_6da47ca3/`)

**Status: not settled, but the wall is located and named; the attempt is
unresolved (`ALIGNMENT.md` §5) and one parent thread is a refuted
candidate.** Theorem 1 and its corollaries are ordinary arguments,
unreviewed; Corollary 2's constant uses Evertse's bound as the run recalled it,
without re-reading it; the Győry–Hajdu–Tijdeman verdict rests on the abstracts;
the measured table is exhaustive inside bounded boxes. Landed 2026-10-21 from a
local-only branch, `support/6da47ca3`, that was never pushed; PR #144 counted
the arm among the seven that "produced no branch at all". A support run for the
Erdős #126 scout (Hunt #91), asked to turn $A$ and $-A$ into the bipartite
$S$-unit difference pattern and specialise the Győry–Hajdu–Tijdeman
representation theorems. The bipartite framing is right and the bipartiteness
is not what carries the weight: all the quantitative force sits in the
sub-pattern $K_{2,m}$, giving **Theorem 1, $g(k) \le N_2(k) + 2$**, where
$N_2(k)$ is the maximum number of solutions of a two-term $S$-unit equation
$u - v = c$ over $|S| = k$ and $c \in \mathbb{Q}^*$. The correspondence is
exact (solutions of $u-v=c$ are in bijection with the common neighbours of two
vertices), so nothing is lost at that step. With Evertse's 1984 bound
$3\cdot 7^{d+2s}$ this gives the unconditional explicit
$g(k) \le 3\cdot 7^{2k+3}+2$, i.e. $f(n) \ge 0.2569\log n - 1.78$, a re-proof
of the classical $f(n) \gg \log n$ with a tracked constant and **no movement on
the problem**. The load-bearing consequence is the conditional: **if a two-term
$S$-unit equation has $\exp(o(k))$ solutions uniformly in its coefficients,
Erdős #126 follows.** Every known lower bound on that count
(Erdős–Stewart–Tijdeman $\exp(k^{1/2+o(1)})$; Konyagin–Soundararajan
$\exp(k^{2-\sqrt2-o(1)})$) is subexponential, so the hypothesis is consistent
with everything known, and the 92-year wall on #126 is the same wall as the
gap between $\exp(O(k))$ and $\exp(k^{0.59})$ in unit-equation counting. The
run also calls that hypothesis the field's "standard (open) conjecture" and #126
"a consequence of a believed conjecture"; neither phrase cites a source, the
literature arm (Hunt #143) looked for the statement and did not find it, and
both are annotated in place in `RESULTS.md`. Sufficient, not necessary, and
measurably lossy: exhaustive search gives $g_N(5) = 8$ against
$N_2^{(N)}(5) \ge 141$. The briefed within-part pair-sum structure **buys no
improvement in the exponent**; it does buy a free nondegeneracy guarantee for
$(a+b)+(c+d) = (a+c)+(b+d)$ (all terms positive, every vanishing subsum forces
two elements equal), but routing through it needs three-term unit equations
whose best uniform bound has slope $\sim 2\times 10^{11}$ against Evertse's
$2\log 7 = 3.892$. The GHT papers themselves are representability results, not
counting results, and contain no bound of the form $|A| \le F(|S|)$; their
cubical criterion touches ours only through the $K_{2,3}$ obstruction, which is
exactly the pattern Theorem 1 exploits. Audit of Hunt #91: all seven witnesses
re-verified, $g_N(k)$ for $k \le 5$ reproduced independently with identical
optimal witnesses, and its §2 and §4 proofs read and correct; but its **loose
thread 3 is refuted** ($|A| \le p-1$ when $p \notin S$ fails for every odd $p$,
e.g. $\{1,3,7\}$ with $S=\{2,5\}$ and $\{1,3,5,11,13\}$ with $S=\{2,3,7\}$), so
the parity fact is a $p=2$ accident and not an iterable lemma. Overlap with
main, recorded in `RESULTS.md`: Theorem 1 is the reduction of Hunts #96 and
#104 (and of #97 and #99, landed with this entry), Lemma 4 is the nondegeneracy
step of the four-element reductions of Hunts #93, #95 and #105, the
loose-thread-3 refutation was on main already (Hunts #93, #95, #101, #103), and
the OEIS thread the run left open was closed by Hunt #143. Its audit line that
the optima "live below 50" is annotated in place, since Hunts #103, #105 and
#107 refuted it. Nothing here bears on RH (`docs/08`).

### Hunt #143: Erdős #126, the 92-year wall, and the one lever behind it (`support_fcffa3b9/`)

**Status: not settled. A literature map from a targeted search, not an
exhaustive one; it refutes nothing and closes no route.** Primary text was read
for Erdős–Turán 1934 and for Győry–Stewart–Tijdeman 1986 including its §3
proof. Erdős–Surányi's $2^k$ and the Erdős–Stewart–Tijdeman constant $1/8$ are
secondary citations through Füredi–Gyarmati 2026, not checked against the
originals; Evertse's bound is quoted through GST; the one reduction step of the
run's own is an ordinary argument, unreviewed. **Renumbered on landing:** the
run's brief assigned #91, which `r_186989` already held, so the run took #92 on
its branch; #92 is `support_517b887f` on main, so the entry takes #143, the
next free number, and `HANDBACK.json` keeps the run's #92. Landed 2026-10-21
from a local-only branch, `support/fcffa3b9`, that was never pushed; PR #144
counted the arm among the seven that "produced no branch at all". A support arm
for the scout (Hunt #91), answering one question: what does the literature
actually have, from 1934 to now? Four things, three of them from primary text.
**The 1934 bound is still the record**: Erdős and Turán prove
$g(k) \le 3\cdot2^{k-1}-1$, and the search found nothing in 92 years that
improves the base 2, only the constant ($g(k)\le 2^k$, Erdős–Surányi). **The
$S$-unit machinery is already in the literature and is quantitatively worse**:
Győry–Stewart–Tijdeman 1986 reproves $f(n)\gg\log n$ through Evertse's counting
bound and lands at $3\cdot7^{2k+3}\approx 49^k$, because its reduction keeps
only $2(n-2)$ of the $\binom n2$ sums. **It is still the lever, and the run
makes that precise**: with $g_2$ the two-set relaxation,
$g(k)\le g_2(k)+2 \le N(k)+2$ where $N(k)$ counts coprime $S$-unit solutions of
$\lambda x+\mu y=\nu z$ (step one the run's own, step two quoted verbatim from
GST §3; the branch's entry dropped the final $+2$, which its own `RESULTS.md`
§2 carries), so **a uniform $\exp(o(k))$ bound on $N(k)$ implies Erdős #126**.
The converse fails, and the route is not blocked: Erdős–Stewart–Tijdeman 1988
forbids only *polynomial* bounds on $g_2$, leaving the whole window
$\exp(\tilde\Theta(\sqrt k)) \ldots \exp(o(k))$ open, every point of which
settles the problem. Two audit findings against the scout: its arm-2 parity
headline is on page 1 of the 1934 paper verbatim, and its arm-3 kill is
stronger than claimed, since a composition law would force the 1934 bound to
be sharp up to $3/2$ and contradict its own authors' conjecture
$n(k)=O(k^{1+\varepsilon})$, a conjecture no modern summary of the problem
mentions. The scout's OEIS thread is closed negatively (a sequence query with
twenty coincidental matches and a keyword search with none, so no tabulation of
$g(k)$). What could not be settled:
whether the subexponential $S$-unit bound is a *stated* conjecture of that
field, which is the difference between "#126 needs a new idea" and "#126 is a
corollary of a believed conjecture". Overlap with main, recorded in
`RESULTS.md`: the reduction is that of Hunts #96 and #104 (and of #97, #99 and
#106, landed with this entry), and #105 makes the same 3/2-corridor point,
which #99 sharpens to $g(k)=2^k$. One statement relied on the scout's "every
optimal witness lives below 50", which Hunts #103, #105 and #107 refuted; it is
annotated in place (`RESULTS.md` §3, the T8 row). Nothing here bears on RH
(`docs/08`).

### Hunt #90: the leader's certificate does not replay at its own HEAD (`amtopa_ceiling/`)

**Status (2026-09-06, `RESULTS.md` section 7.7): the `+3.96e-06` candidate is WITHDRAWN.
At `b3b7784`, the verifier revision their own `candidate.json` names, the leader's headline is
accepted on 8 of 8 shards with the gate alive; their number stands and the tip's only defect
is the gate. Ours was refused on 4 of 8 in three rounds; the third, with the target backed
off, reached cells whose values sit below the LP's claimed floor, and a proper descent finds
the functional at the candidate's own weights bottoming at `0.0078960`, `1.5e-5` under the
leader's floor. The LP's cut oracle had missed that basin, so the claimed `+5.9e-6` of
headroom on the pair-weight and pressure axes is withdrawn with it; the re-solve with a
stronger oracle bounds that headroom at `8.9e-8` in `eps`, under `7e-8` on the headline.
**The window axis went the same way (section 7.8): two candidates built at a window that is
not theirs, both accepted on 6 of 8 shards and refused at cells with a gap near `2.91` that no
float search here was seeding, and re-measured with that region seeded all five of the sweep's
windows land BELOW the record. Control: the same oracle reproduces AMTOPA's own floor exactly
at their own point. All five axes are at the ceiling; both of this hunt's candidates are
withdrawn.** Earlier status: settled on the measurable axes; window axis open; acceptance
blocked at the tip. Takes the
`ainta_seven_point` playbook to `AMTOPA/zeta-exact-pressure`, the leading public
claim per Hunt #89, pinned at commit
`7253fdcab9366af45b8c8caf44e408c0af44a1a7`.

**The finding that outranks the rest: their published certificate does not
replay at their own repository tip.** Run through AMTOPA's own pipeline on the
pinned commit, their table builder, their verifier, their candidate, their
target, the finite inequality behind `0.6734164909714992949` returns
`INCONCLUSIVE=true reason=terminal_cell` with a rigorous lower bound `1.19e-07`
short of the target. **The tables are not at fault: all six join to streams whose
SHA-256 digests match their own `candidate.json` byte for byte**, a stronger
table reproduction than Hunt #89 got for `trmdy`. The cause is their convexity
gate, which fires `2030240` times in their recorded run and **zero** times here
in 72 million nodes. Their `candidate.json` names
`source_commit: b3b7784…` as the origin of that run; between `b3b7784` and the
tip, `src/verify_local_tables.cpp` changed by 173 lines and the gate's curvature
entries went from thin `point(scalar)` to `mul(p.exact, {sec, +infinity})`. The
interval LDL that follows **cannot certify positive definiteness of a matrix
unbounded above**, `ldl_probe.cpp`, 70 lines, shows it returning `false` on a
matrix with `10` on the diagonal and `1` off it. Without the tangent bound the
plain interval bound at grid `1/4000` is left to clear the target alone, and at
one width-zero cell it cannot. **Direction: fail-closed**, the tip refuses what
the earlier revision accepted and never the reverse, so this is a reproducibility
defect, not a soundness hole, and it blocks *our* candidate at the tip too, by
`2.70e-08`.

**Their headline reproduces on paper.** In exact rational arithmetic with a
rational under-estimate of the only square root, their `0.673416490971499294950035533107
4903174997772794755665475125243371226272` holds to **70 decimals**, and the exact
scan over `m` in `[7, 20000]` returns their `m = 145`. An independent
reimplementation written from their `proof.md` reproduces `H(v)` and their
observed float minimum `0.007911105155226424` to the binary64 limit, at their own
published basin. Soundness read: **no defect that affects their claim.**
Acceptance is one-sided throughout, the verifier fails closed at a terminal cell,
out-of-table queries return `0` for a nonnegative `W` and `-inf` for the
convexity gate, and the constants are thresholds compared against computed
enclosures, not answers wired to the target. Three things worth recording anyway:
their `README.md` and `proof.md` both say *"exact arithmetic selects m=145"* while
`src/check_final_bound.py` is **`mpmath` float at 100 dps with `mp.sqrt`**, right
answer, wrong label, and their own banded experiment does it properly; the C++
**never checks pair-weight nonnegativity** although `box_lower` needs it, and the
script that writes its constants does not check it either, so the verifier alone
cannot validate a candidate; and `long double` is 64-bit on ARM and 80-bit on
x86, the same host-dependence class as the `w''` digest Hunt #89 found in
`trmdy`.

**Outcome (a), by `+3.96e-06`.** `eps(a,b) = min_g F` is *linear* in the pair
weights and in the pressures, hence concave, over a polytope, so that axis is a
concave maximisation with an exact answer, not a search. Cutting-plane LP: at
their own window and their own total pressure the polytope admits
`eps* = 0.007916857812` against their `0.007911105155`, and quantised into their
schema at the rational target `19791/2500000` the exact assembly gives

    0.6734201550790580964457598685450152133015  against their 0.6734164909714992949500

CONDITIONAL, inheriting the same unreviewed Anthropic/Ainta bridge as everything
on this ladder, and the floor behind it is a float minimum until their own
verifier accepts the target. **The LP found the point; it does not justify it**,
what justifies it is their branch-and-bound, and the hunt says so where the
number appears.

**The window axis is NOT saturated, and it is worth ten times the pair weights.**
Five independent differential-evolution seeds across two Actions runs, each
starting from AMTOPA's own window, every one walks away from it, always toward
*lower* `H` and *lower* `B`, and reports gains between `+3.07e-05` and
`+3.71e-05`, best `0.6734536055358651` at `H = 0.6721654`, `B/B0 = 0.908`,
`m = 153`. Those inner solves are deliberately cheap and their floors are
early-stopped over-estimates, so this is **direction, not magnitude**, but the
direction is unambiguous and it is the live door.

**The ceiling findings are worth more than the constant.** On the two axes
where a ceiling can be computed rather than searched, **AMTOPA are at it.**
(i) `H(v) = 2 - 1/c1` is a **Rayleigh quotient** in the window coefficients, so
`H_max = 2 - 1/(u^T M^{-1} u)` in closed form, and for 1, 2, 3, 7, 13, 17 or 25
terms the answer is always `0.67250070367941172655`, the *pure `sqrt(2)`* value,
i.e. **Anthropic's `HD(1)` exactly**. The `2 j pi` harmonics have `u_j = 0` and
`M[0,j] = 0`, and the second identity reduces to `2 j^2 pi^2 (w_0^2 - 2)/w_0`,
which vanishes **iff `w_0 = sqrt(2)`**. Every harmonic is pure `H` sacrifice;
theirs spend `3.13e-04` of it and get `8.32e-04` of floor back, an exchange rate
of `2.66` against a break-even of `1.57`. (ii) their total pressure `B = 93/23000`
sits at the **argmax** of the saturation curve, with net marginal
`d(bound)/dB = +0.006076` against competing terms of size one, and the LP dual
`d(eps*)/dB = 1.509` against a break-even `1.4998`.

**The doors, ranked by LP shadow price.** The **span-1 capacity `= 2`** binds
hardest by an order of magnitude (`+4.08e-04` of bound per unit of capacity);
span 6 is **slack**. The floor of the whole family is pinned by one near-integer
configuration, seven points at about `{0, 2, 3, 5, 6, 8, 9}`, with 18 of 2,200
cut vectors simultaneously active. The frozen constants with a *trade* in them:
the Gram profile (their own banded lemma already computes `+7.07e-06` and they
decline to promote it), the point count (`trmdy` runs nine, AMTOPA never left
seven), the span capacity itself, and, the one nobody on this ladder has ever
moved, **the fundamental `w_0 = sqrt(2)`**, which is precisely the frequency
that makes the harmonics unable to help. Every door stays inside bandwidth-one
data, so all of them are capped by `0.6818286874638`; the room left inside that
information class is `0.0084`, three orders of magnitude more than the family's
own ceiling. **The construction binds, not the information.**

Full record, including the run that broke the operator's local-compute cap and
what it cost: `amtopa_ceiling/RESULTS.md`, `amtopa_ceiling/RUNS.md`.

### Hunt #89: this laboratory is tenth, and the barrier is aimed at an empty room (`field_audit/`)

**Status: settled. FIELD AUDIT.** Prompted by discovering, on 2026-08-24, a wave
of public repositories created 2026-08-11 and 2026-08-12 carrying constants for
`liminf N0s(T,2T)/N(T,2T)` above ours. **Our best figure,
`0.6730529829896288` (eight-point, bridge proved in Lean), ranks tenth of
fifteen public claims.** The leader is `AMTOPA/zeta-exact-pressure` at
`0.6734164909714992949`, ahead of us by `0.00036350798187`: eight times our
margin over `ainta/zeta-simple-zeros`, which we had taken for the frontier.
Three constructions were already past our eventual figure before our
seven-point hunt opened; the earliest, `trmdy/zeta-simple-zeros-673137`, first
commit 2026-08-11 14:43 +0200, beat it on day one. **Hunt #82's barrier is not
contradicted, and could not have been:** it is a ceiling at
`0.675142509660254` and the leader sits `0.00172601868875` *below* it. What the
audit does cost #82 is reach, not truth, `trmdy` is outside the family it
names on two axes, read against `lean/bridge/Zeta23Ext/Bridge/Defs.lean`: the
window is a seven-term cosine polynomial, not the single term `omega = sqrt 2`
(their `H(v) = 0.67245704141454428878`, *lower* than `HD 1` by `4.366e-5`,
window constant traded for a larger floor `c`), and the block profile is the
envelope `2 sqrt((m-1)A/m) - 1 + A/m`, which lifts the cap `c(m-(n-1)) <= 1`
that our `Phi_n` requires; they run `m = 272` and `m = 177` where our cap allows
`230` and `172`. On the third axis their family *contains* ours: their
`uniform_weights` is our `F` exactly, one vertex of a span-capacity-2 polytope
they optimise over. Replayed here from a scratch clone against their own pinned
Arb binding: their window bounds, `H(v)`, all three assembly constants
(`0.6732001170127618568182`, `0.6732425893558967029403`,
`0.6733127422722459981438`, each matching their published digits), every span
capacity exactly `2`, and their 23-test suite. Their **2,168,370-box seven-point
interval run also reproduces here**: 482.6 s against their 441.7 s, with an
identical node count, split count, depth 50 and all three prune counters, but
**one of its two table digests is host-dependent**: the `w` table matches byte
for byte and the `w''` table does not, and the `w''` table is the one the tangent
pruner rides on, i.e. the single component whose corruption could yield a false
acceptance rather than a false failure. Not one branch of the search changed
regardless, which makes this a *stronger* reproduction than byte-identity would
be and simultaneously not the reproduction their documents claim;
`tawanerguo-cn` self-discloses the same class of mismatch, so it is a property
of the method. Their 116,272,426-node nine-point run, the one carrying the
headline, was **not** replayed and is out of reach here, so the headline is
assembly-verified and floor-reported.
**Soundness read of their verifier: no defect found**, and the Ainta pattern
specifically absent, acceptance is one-sided against an upward-rounded target,
the search raises rather than returning a negative, the `w`-table is clamped
non-negative before squaring (which is what makes the sign-blind multiply in
`box_lower` safe, while the signed `w''` path does use a sign test), the
convexity gate is a rigorous Arb LDL behind a float pre-filter, and `H_CERT` is
a threshold to clear, with the *assembly* then using the rational below the
computed value. What does deserve scrutiny is not code: the refined pressure
tax `(m-q)B_p/m` replacing `eta B_p (m-1)/m` rests on a cyclic-shift counting
lemma that is machine-checked nowhere and is worth essentially the whole
refinement. Applying that refined assembly to *our own* floors, changing nothing
already proved, buys `+3.02e-5` and `+5.38e-5`, ninth place, not first; the
deficit is in the floor `c`, not the assembly, and taking it would trade our one
real advantage, a bridge with zero `sorry`s, for `5.4e-5`. Also recorded, as its
own section: **why our prior-art search missed eleven repositories.** We
searched for the standing result rather than the competition (the wave has no
stars, no descriptions, no preprints, `npip99/zeta-zeros` sits at `0.673195`
with an empty description and zero stars); we read `riemannzeta.fun`, still
showing `0.672500703679`, as the field rather than as the formally-accepted
subset; we looked once and never again while the field moved for a week; and we
never ran a forward-citation pass, though `trmdy`'s own README names three of
the repositories we missed. That pass took under seven minutes when finally run.
No arXiv preprint exists for any `0.673x` follow-up and none has passed a
kernel-checked gate anywhere. Nothing was posted, opened, forked or starred
upstream. Nothing bears on RH (`docs/08`).

### Hunt #88: the third autocorrelation constant belongs to the other functional (`r_8539dc/`)

**Status: settled.** A reading and an exact recomputation, prompted by issue
#123 and by issue #1 on `google-deepmind/alphaevolve_repository_of_problems`:
AlphaEvolve's published `C_3 <= 1.4557` sat above a verification cell computing
`abs(2n*max(conv)/sum^2)` while the inequality printed above it defined
`max|f*f| >= C_3 (int f)^2`. The outer `abs` is a **no-op**, and not by
accident: `int_{-1/2}^{1/2} f*f = (int f)^2 > 0` forces `max_t f*f(t) > 0`, so
the code computes `A = max f*f/(int f)^2` while the statement defined
`B = max|f*f|/(int f)^2`, and `A <= B` always. In exact rational arithmetic on
the published ten-place heights (no float in the chain), the `n = 400`
construction gives `A = 1.45564279537454049411...` and
`B = 4.33404652438798427361...`: it reaches `1.4557` under `A` only, buying that
score by driving the autoconvolution to `-4.334` at knot 215 against a positive
peak of `+1.456`. The `n = 150` construction gives `1.46876206974102180951...`
under **both** functionals, which is the check that keeps the discretisation
honest. The mix-up **was** corrected, twice, and the brief's premise that no
correction had appeared is wrong: arXiv:2511.02864 **v2** (2025-12-15) splits
the problem into `max|f*f| >= C_3` (prior `1.4993`, Matolcsi-Vinuesa, improved
to `1.4688`) and `|max f*f| >= C_3'` (prior `1.45810`, Vinuesa, improved to
`1.4557`), moving the `1.45810` citation between sources in the process; the
colab followed on 2025-12-19 (`39d0c63`), leaving `height_sequence_3`
untouched. So the improvement survives once each number is read against its own
functional, and nothing was withdrawn. What is still broken: the two corrected
artifacts label the two problems in **opposite** senses, so "AlphaEvolve's
`C_3`" is ambiguous between them; `problems/4.html` still carries only the
`max|f*f|` statement with no sibling page nine months after promising one; and
issue #1, the thread where the report was made, is still open. No new bound is
claimed and nothing was posted upstream. Nothing bears on RH (`docs/08`).

### Hunt #87: a 2013 paper beats an AlphaEvolve world record (`r_2969b0/`)

**Status: settled.** DeepMind's `alphaevolve_repository_of_problems` marks
Problem 42 (the sum-difference problem) `world_record`; an unreviewed,
AI-produced issue on that repository claims a 2013 human paper already does
better. Both sides checked, from the primary sources, by exact integer
enumeration. The challenger is right, including its citation. Problem 42 defines
`C` as the least constant with `|A+A|/|A| <= (|A-A|/|A|)^C`; Penman and Wells,
INTEGERS 13 (2013) A57, Theorem 21, state that same ratio character for
character and give `sup g = ln(32/5)/ln(26/5) = 1.125944426` over their family
`Q_j`. The AlphaEvolve set from the repository's own notebook re-counts to
`|A| = 309, |A+A| = 1367, |A-A| = 1163`, `g = 1.1219357375`, the published
value. **`Q_36` -- 197 integers, published thirteen years earlier -- beats it**,
`g = 1.1219505699`, decided at 120 digits rather than in float, and every
`Q_j` with `j >= 36` beats it too. Corollary 13's four counting formulas were
reproduced by enumeration at 64 values of `j` with zero mismatches, and four
numbers the paper prints (`g(A_15)`, `f(X)`, `f(Q_10)`, `f-hat(Q_19)`)
recompute exactly, which is what pins that the right normalisation is being
read: the same paper also carries `f(A) = ln|A+A|/ln|A-A|`, and `f` ranks these
two sets the *other* way. Three different score functions appear in the
AlphaEvolve notebook for this one problem, one of them the reciprocal of the
target and one carrying a size bonus of up to 0.01 on a scale 0.06 wide; the
published number uses the clean one. The issue's separate `C = 2` claim was left
untouched, as briefed. Nothing was posted upstream. Nothing bears on RH
(`docs/08`).

### Hunt #86: the ceiling procedure on the *lower* side of Erdos minimum overlap (`overlap_lower/`)

**Status: probe, partly settled.** Sixth instance of the ceiling procedure and
the first aimed at a lower bound, picking up hunt #85's first loose thread. The
thread is closed: White's program (arXiv:2201.05704, Acta Arith. 208 (2023)
235-255) discretises `M` and never `f`, so it is a relaxation and the unsafe
direction hunt #85 worried about does not arise. Three of the opening brief's
premises were found wrong at the source and corrected -- the lower bound **has**
moved since 2022 (Kim and Pilanci, arXiv:2606.31182, 30 June 2026,
`0.379005 -> 0.37912`, which the public catalogue has not absorbed); the
catalogue entry for this constant carries **no** asterisk; and the `0.000059`
of upper-bound movement is the 2016 human record minus the 2026 AI one, not
twelve months of AI. **The measured finding: White's choice of `R` was already
at his method's ceiling.** In his simplified program the value saturates at
`R = 40` and the total gain from his `R = 20` out to `R = 320` is `2.9e-6`; in
his full program the gain from his `R = 10` to `R = 20` is `2.0e-5`, against the
`1.15e-4` the next real improvement obtained by adding constraints instead. One
exact rational dual point was accepted with no float in the value,
`0.37399241331` at `N, R = 5000, 20`. The full program was **not** reproduced to
`0.379005`: the Parseval cone survives none of four cutting-plane formulations
without a conic solver, so the sweep measured a strictly weaker program, and the
sweep also never reached CI because the credential lacks the `workflow` scope.
No bound on `C` is claimed. Nothing bears on RH (`docs/08`).

### Hunt #85: the ceiling procedure on Erdos minimum overlap (`r_828c8b/`)

**Status: probe, partly settled.** Fifth front of the ceiling procedure, in a
family where the upper record is a step-function construction and the lower
record is a convex program. On the upper side the whole procedure reproduces:
the `m`-piece minimax falls `0.400000 / 0.385072 / 0.381833 / 0.381084` at
`m = 4/8/16/32` and then stops, `1.6e-4` above Haugland's `0.380926`, and the
stall is provably the solver's rather than the family's, since an `m`-piece
step function upsamples to a feasible `2m`-piece one and Haugland's object
sits strictly below. The accepted object was re-evaluated in exact rationals
with no float in the value: `C <= 9990167/26214400 = 0.381094627`, weaker than
the published bound and stated as a reproduction. Two soundness facts came out
of the acceptance step: rounding the pieces at the obvious denominator `2m`
costs `2.4e-4` to `6.8e-4`, more than the whole remaining gap, and ten times
finer costs nothing; and on this side there is no dual to check, because the
accepted object is primal and its value is a finite rational. The lower side
was **not** reproduced. What was established instead is that the plain
averaging skeleton cannot reach it: uniform weight gives `C >= 1/4` exactly,
the naive Fourier handling of the quadratic term is vacuous for *every*
admissible weight (`what(0) = 1` forces `sup what = 1`; 0 of 200 random
profiles gave anything positive), and explicit witnesses cap four weight
profiles at `0.2526 / 0.2500 / 0.1909 / 0.1701`, all far below `0.379005`, with
the bound getting *worse* as the weight concentrates. A guard on the shift
enumeration (the failure direction that would report a bound better than the
object supports) caught 2 of 3 planted faults, with the third recorded as a
known miss; it is in `harness/departments/guard_ledger.py`. Nothing bears on
RH (`docs/08`).

### Hunt #84: the Delsarte LP has no headroom in its degree (`r_6f0f63/`)

**Status: probe, complete.** Fourth instance of the ceiling procedure
(issue #110), on the LP half of the sphere-packing/kissing-number family. The
two exactly tight certificates were rebuilt from their contact structure rather
than from printed coefficients -- E8 gives Gegenbauer coefficients
`[1, 8, 25, 52, 66.5, 60, 27.5]` summing to 240, Leech gives degree 10 summing
to 196560, both with every coefficient non-negative without being asked. The
soundness read found the load-bearing defect in the acceptance step: the
standard node-discretised LP is a *relaxation*, so its optimum sits below the
truth, and it did so at **every node count tested** -- 196505.76 at 600 nodes in
dimension 24, where the answer is exactly 196560, and 239.9930 at 600 nodes in
dimension 8. The error is one-sided and decays like m^-2. The repair
`f -> f - sup f` converts the invalid output into a valid weaker value and
brackets the truth. The ceiling itself is a negative result: sweeping degree 1
to 30 in dimensions 3 to 24, the value stops moving by degree 14 at the latest,
and the sweep rediscovers degrees 6 and 10 for E8 and Leech on its own. So the
headroom in this parameterisation is not in the degree; it is in the node set,
which nobody publishes. Float grade throughout. Five planted faults fire. The
Cohn-Elkies SDP half was not attempted. Nothing bears on RH (`docs/08`).
### Hunt #82: the analytic limit of the n-point pressure family (`family_wall/`)

**Status: probe, complete. BARRIER.** The n-point pressure family saturates. Reducing
the bound to `Phi_n <= H + H c - (n-1)/p` and then bounding `c` by the functional's value
at any gap vector of total length `(n-1)/H` makes the pressure term cancel identically and
leaves `Phi_n <= H (1 + W(g))`, with `W` an energy per point at density `H` -- order `1e-3`,
where reaching the configuration ceiling `0.6818286874638` would need `0.0138706`.
Combined with `Phi_n <= H (n-1)/(n-2)` (which is already below the ceiling from `n = 75`),
every `n` is covered and `sup_n Phi_n <= 0.6751676`: short of the ceiling by more than
`0.0066`, which is 71% of the whole distance from `H` to it. The limit itself is `H =
0.6725007036794116` exactly -- the family climbs a little, turns over and comes back down.
The DERIVED-but-untested pressure lead survived: `Phi = H m/(m-1) - k/p` is exact when
`1/c` is an integer and a rigorous upper bound otherwise (overshoot `1.5e-6` to `5.9e-6`,
comparable to the spacing between adjacent peaks, so it cannot rank adjacent `n`), and the
optimal pressure sits at a minimiser-family crossover `p_x = (S2-S1)/(W1-W2)` -- predicted
3433.0, 3187.3, 4072.5 for `n = 7, 8, 9`, each landing inside the exact grid interval where
the existing sweep's winning word changes. A Modal cross-check at `n = 7, 10, 14, 20` over
`p = 1200 .. 20000` passed its control to `2e-13` and agreed with the predicted floors at
`n = 7, 10, 14`; at `n = 20` the analytic witness ladder beat the multistart search at four
pressures, so that job's raw `Phi_20` was built on a value that is not a floor.
`FAMILY-LIMIT.md`, with its own "what would refute this".

### Hunt #80: where the variable-radius Bloch certificate ends (`bloch_ceiling/`)

**Status: settled.** Third instance of the ceiling procedure, on a constant
outside the zeta family: Wikström's computer-assisted lower bound for Bloch's
constant (arXiv 2608.17660, Zenodo `10.5281/zenodo.21975862`). The published
verification reproduces from the pinned archive, all 28 checksums verified. The
verifier's soundness read is in section 3. Section 4 computes the variable-radius
ceiling the author did not: the published constant extracts roughly 59% of the
headroom the method's own parameterisation allows, with the near side
interval-rigorous, the away side a floating-point programme, and the ceiling
therefore **INFERRED** rather than measured.

Section 5 is now obtained. **The author's own verifier accepts
`sqrt(3)/4 + 0.0153040536`, above his published `0.0153`**, in all 24 away
sectors and all 38,400 initial cells, with zero cells refused, on his unmodified
certificate data. That target is also the end of the road for that data: the
near branch's own Arb gain, `0.0153040536989472`, is a rigorous cap on the
dichotomy, so the published constant was leaving `4.05e-6` of its own certificate
unclaimed and there is nothing further there. The run's own cross-check is exact:
sectors 0 and 1 rerun at the *published* target reproduce `reference-run/logs`
to the integer, 270,744 and 292,931. Cost 324 core-hours over 476 GitHub Actions
jobs, billed zero, against a projection published before launch that came in 4.2%
high. The hunt ends with a **doors** section ranking what to unfreeze next; the
top door is regenerating the certificate data at moved `ETA`, `LARGE_RAD` and
node count, which section 4 puts at `~0.015359` and which is affordable, since
the away side of a `0.015316` target costs only 4.2% more boxes.

### Hunt #81: what the `min(dps, 20)` cap costs, measured (`dps_cap/`)

**Status: probe, complete.** At `0.8 + 85.7i`, `epstein_completed` at the
capped `dps = 20` returns `3.1e-33` where the converged value is `1.6e-58` --
a factor of `1.9e25` and not one correct digit. The error floor sits near
`1e-(D+13)`, so nothing correct can appear below `D ~ 46`; the sweep puts the
crossover there exactly (D=40 entirely floor, D=50 the first row with correct
digits). `D = 60` buys about 16 real digits, not 60, because the cancellation
costs roughly 44 of them. `zeta/epstein.py` still caps three interfaces at
`dps=min(_d, 20)` (lines 1092, 1126, 1142), so a caller asking for 60 gets 20
and `count_zeros_box`'s integrality check passes on the noise.

Landed 2026-08-21 as the union of five concurrent 2026-08-14 runs that all
wrote this directory and none of which merged; see the provenance header in
`dps_cap/README.md`. Nothing here is evidence about zeta or RH: it is a
measurement of an implementation at a single point.

> **Renumbered twice.** These two opened as #35 and #36 from a branch
> 101 commits behind `main`, where both numbers were taken. They were
> renumbered to #49/#50 on 2026-08-18, and `main` took those two (plus
> #51, #52, #55-#57 and #59) before this branch landed. They are #60
> and #61. The directories `lambda_dh_bounds/` and
> `prime_zeta_rightmost/` are unchanged and are the stable references.

### Hunt #79: where the seven-point simple-zero certificate ends, and what proves it (`ainta_seven_point/`)

**Status: closed, bounded, in two halves: the certificates reproduced and the
floor bracketed (`RESULTS.md`); the bridge mapped, verdict one substantial
analytic bridge (`TRUST-MAP.md`).** Two outside groups (Ainta, and Gohms in
issue #1 on that repository) are hill-climbing one finite inequality `F6 >= c`
that refines Anthropic's unconditional 0.6725007 simple-zero constant. Neither
has a human reviewer or a Lean line; both are computer-assisted results at the
same standard of evidence as the one this hunt adds.

*Certificates.* Ainta's `19/5000` and Gohms's `191/50000` reproduce field for
field on the pinned commit; one secondary table hash differs with no effect on
any count. The functional's infimum is bracketed rigorously,
`0.003826 <= inf F6 <= 0.0038262312115073`: the published verifier accepts
`1913/500000` at grids 4000 and 8000 and refuses `0.0038263` at the same
six-gap configuration the float minimiser finds, gaps alternating near 1 and
near 2 on the kernel's zeros. One defect found and repaired: the verifier's
`PRESSURE_CUTOFF_CELLS` encodes the original target, so every run that raised
the target, Gohms's and this hunt's own probes, pruned on a stale assumption;
all were re-run with the cutoff raised and all still accept.

*Bridge.* The map from the certificate to the published constant is recovered
in closed form and reproduces both published constants to 40 digits:
`Phi(c,m,p) = (H - 6(m-1)/(pm)) / (1 - c(m-6)/m)`. The block size `m` is not a
free parameter: `A_0 = c(m-6) <= 1` caps it at `6 + floor(1/c)`, and both
published values sit exactly at their cap, which is why raising the target
*lowered* `m` from 269 to 267. The family's apparent ceiling at the published
pressure is 0.673025477, 4.1e-6 above the Gohms claim, about 5.6% of the room
under the configuration ceiling. Six of sixteen steps are already
kernel-checked in `anthropics/zeta-23-lean` (Theorem D itself, von Neumann,
the positive-part splitting), four are small finite statements, and what is
missing is carrying the new spectral defect through the tail passage and the
uniform kernel limit. Smallest Lean-ready obligation: the stability
rank-trace lemma. Also recorded: this laboratory has been quoting the
configuration ceiling as 0.68185, a decimal in a remark with no proof
attached, where the Lean development proves 0.6818286874638. Nothing here
bears on RH (`docs/08`).

**Second half, 2026-08-23: the Aristotle probe (`ARISTOTLE-PROBE.md`).** The map's
S2, the stability rank-trace lemma, was stated in Lean and proved, zero `sorry`s,
standard axioms only, in
`StableRankTrace.lean` (then in `hunts/frontier_math/zeta23ext/Zeta23Ext/`, moved to
`lean/bridge/Zeta23Ext/` on 2026-08-23). **No Aristotle
project was opened, because nothing remained to send.** The finding is a correction
to the map: S2 is *not* new relative to the Lean development the map chose as its
vocabulary. Ainta's profile `Psi` is that development's own `gc 2` shifted by one
(`Psi = gc 2 + 1`, the shift being exactly `Psi 0 = 1`, which is the bookkeeping that
trades a rank count for `Fintype.card r`), the sharpened scalar estimate the map
expected to need is already `sq_sub_ge_gc`, the spectral transfer is already
`sum_eigenvalues_comm`, and the theorem falls out as a corollary of
`Zeta23.ZeroSide.RankTraceMult.rank_trace_mult` at `c = 2` evaluated at the
eigenbasis presentation of `V Vᴴ`. The map is not guilty of a missed search: `TRUST-MAP.md:382`
already cites `RankTraceMult.lean:281`, `lemmaR_tight` and `gc`. It filed that defect
term as *"a different one"*, spectral versus per-zero, and that reading is the actual
gap: `rank_trace_mult` is quantified over presentations of `P`, and at the eigenbasis
presentation its per-zero defect *is* the spectral one. `Psi` was also never matched to
`gc 2`, so §4 named `RankTrace.lean:52-56` for a scalar estimate that `RankTraceMult`
already proves. Its step table records the contrast; its section 4 then states the obligation as if it did not apply. Two
things the formal state exposed that the map's transcription hides: the
rank hypothesis is removable, so a sharp form holds with **no** hypothesis on `V`
at all, and the column bound `hV` is load-bearing for exactly one inequality,
`tr(V Vᴴ) <= card r`, worth a mean of 6.05 of discarded slack on random draws. The
sharp form is measured to be an *equality* on the family upstream proves extremal
for Lemma R (400 instances, slack 1.07e-14; float grade). A third Palomar entry is
**not** recommended: a bridging corollary of an existing public Lean theorem does
not clear that registry's notability floor. S2 remains one step of sixteen; S8 and
S9 are untouched and nothing here bears on RH. **A second finding fell out of running
the handoff's first instruction:** `hunts/frontier_math/zeta23ext` does not assemble on
`main` at `36c6070`. `assemble.sh` reports three failing targets,
`Zeta23Ext.RetentionWired`, `Zeta23Ext.EForm2.Bridge` and `Zeta23Ext.TruncEst.Kernel`,
with `Retention.margin_identity` picking up `sorryAx` as a consequence. It is not the
dependency store (mathlib rev matches the pin), not the `Zeta23` dependency (none of the
three imports it) and not this branch (the failing build predates the new module). The
new module builds standalone and is unaffected; no claim is made here that the package
assembles. Recorded as issue #101, not fixed here.

**Third half, 2026-08-23: the bridge, formalised to its hypotheses (`BRIDGE.md`).**
Five agents in one day, no proving service (0 of 15 permitted Aristotle submissions),
proved every step S6 to S9 and S11 to S16 on top of the vendored `[L23]`, so that
`Zeta23Ext.Bridge.seven_point_bound` now states Ainta's bound for Mathlib's
`riemannZeta` as a sorry-free theorem with standard axioms only, conditional on exactly
two named hypotheses: the seven-point inequality `F6 >= c` (S10, the Arb run, not a Lean
fact) and the cap `c(m-6) <= 1`; at `(19/5000, 269, 3000)` the conclusion's constant is
the paper's `(1345000 H - 2680)/1340003` with the side conditions by `norm_num`. The two
steps the trust map graded LARGE were not: S8 rides through `[L23]`'s endgame at
`lambda = 1` by transcription, because every endgame input is already stated for
`lambda <= 1`, and S9 reuses `[L23]`'s window Poisson identity and `PrimeSide` decay and
needs no bounded-separation hypothesis at all; the pinching the map called missing is
proved for every convex trace functional from a row-stochastic mixture. Builds standalone
in 44 s; the package root was still #101.

**Packaged for Palomar, 2026-08-23 (same `BRIDGE.md`, section 8).** `StableRankTrace.lean`
and the sixteen `Bridge/` modules moved into a Lake package of their own at `lean/bridge/`,
which assembles at its root (`lake build`, 8860 jobs) against the same pinned `Zeta23` and
Mathlib; module names and namespaces unchanged; the Apache-2.0 headers copied from the
dependency replaced by the repository's MIT header, with the one adapted file's attribution
kept in a notice. `BridgeChallenge.lean` and `BridgeSolution.lean` advertise four theorems
in the namespace `Zeta23Ext.Palomar`: the parametric bound, the paper's `(19/5000, 269,
3000)`, and this laboratory's own `(34697/10^7, 294, 3400)` in multiplicative and ratio
form, `0.6730295534796928…`. The eight-point statement is deliberately not advertised: its
bridge from certificate to proportion is stated, not proved. Precheck 66 pass, 1 warn, 0
FAIL. **Not submitted**; whether a conditional refinement clears that registry's notability
floor is its call. Nothing here bears on RH.

### Hunt #76: the Riemann zeros in tuning units (`zeta_temperament/`)

**Status: closed, verdict INTERESTING STRUCTURE, classical in substance.**
In steps-per-octave units theta = gamma ln2 / 2pi, Landau's formula is the
Fourier coefficient of the zeros mod 1 at frequency log2 n, so the zeros
avoid the equal temperaments that tune prime-power harmonics and ignore
composites. On Odlyzko's first 100,000 zeros every prime power n <= 32 lands
within 0.0012 of -Lambda(n)/sqrt(n)/<log(gamma/2pi)> and every composite
gives 0.0000; the smoothed density at integer x is 0.801 against 0.800
predicted, at fifths-perfect x 0.762 against 0.767, at the composite-6
control 0.997, and the deficit shrinks with height as 1/log t. The lab's own
2000 zeros agree. The peak side (Gene Ward Smith, OEIS A117536) is
reproduced as calibration, with one caveat added: the Riemann-Siegel main
sum for the x-EDO stops at harmonic 1.2 sqrt(x), so 12-EDO's zeta score never
sees the major third directly. **Corrected 2026-08-22**: the composite control
re-measures `zeta.explicit.prime_spectrum`, which this repository already
exposed and whose docstring states the same identity; the hunt's prior-art
search had omitted this tree. The same review added the Euler-product
discriminator, where Davenport-Heilbronn's loudest spectral line is a
composite and the Epstein forms of class number one are silent while class
number above one is loud and cancels across the class group. Nothing here
bears on RH. Doc: `docs/34`.

### Hunt #75: pitch classes against the colour wheel (`chroma_hue/`)

**Status: closed, verdict PRETTY BUT TRIVIAL.** A note-to-hue bijection makes
hue distance a function of interval class if and only if it is affine, so the
hue side sees exactly one choice, the character of Z_12, and Z_12 has two
injective ones (chromatic, fifths). Over all 21,772,800 canonical bijections
the circle of fifths is the unique argmax of Spearman(hue distance,
dissonance) under three separate dissonance measures (0.609 Sethares, 0.702
Tenney and ordinal; null mean 0.00, sd 0.14, null max 0.50 and 0.57), and
chromatic order is the worst structured choice (-0.73, -0.49). That is a
statement about hearing with no colour in it. The colour side is not a
12-gon: the HSL wheel's adjacent CIEDE2000 steps vary 8.5-fold and its twelve
hues land 6.5 to 61 degrees apart in OKLCH; twelve equal-tempered steps of
light frequency across the visible octave give hue steps of 1 to 72 degrees
per semitone and cover about 275 of 360 degrees. The one formulation where
colour adds anything: the eye mixes linearly, so the colour of a chord under
wheel k is its k-th Fourier coefficient, and maximal evenness (Clough-Douthett,
Amiot) reads as saturation. Round two reformulated: a colour wheel is a
complex place of Q(zeta_12), the fifths wheel is the Galois conjugate of the
chromatic one (together they distinguish exactly the 1763 chord colours
either does alone), and chromatic times fifths saturation is the field norm,
an integer taking ten values on the 224 set classes, with 84 classes units.
Nothing here bears on RH. Doc: `docs/33`.

### Hunt #72: AIMO Interpretability 2026 baseline reproduction and structure-matched robustness signal (`r_662b12/`)

**Status: baseline retained, intervention rejected after independent audit.** The public sample has 28 cases, 19 non-robust and 9 robust, so the all-False baseline is 67.86% (19/28) with full coverage and no invalid outputs. The reported 92.86% intervention is an in-sample score for a model-name rule chosen after inspecting those same labels. Its LOOCV, leave-one-problem-out and five-fold loops never fit or select the rule inside training folds, so they provide no generalization evidence. The scrambled-text surrogate retains the same 92.86%, refuting the claimed mathematical-structure interpretation. Prize disposition: **NO-GO on this hunt's evidence.** The original run record is preserved; `hunts/r_662b12/AUDIT.md` carries the correction. Nothing here bears on RH (`docs/08`).
### Hunt #77: AIMO-2, legal AIMO Interpretability submission + validation-design report (`aimo2/`)

**Status: report-ready (reframed 2026-08-22); Main entry is a legal model-identity prior,
Small entry is the always-non-robust constant; learned-method arm stays killed; no GPU spent.**
Successor to Hunt #72 (`r_662b12`), whose +25pp claim was withdrawn and stays withdrawn.
The organizers' clear-cut protocol (proposal §1.4) is reconstructed exactly from public data:
`val-sample`'s 9 robust rows are the 9 `sample-full` pairs with base accuracy 1.0 and zero
detrimental perturbations; its 19 non-robust rows are single-type rows with decay >= 0.5. So the
hidden set is minority-robust by construction (22-43% on the public problems, 20% for the 8B on
the organizers' MATH release), and the first version's "natural distribution" (89-97% robust) was
the wrong reference; the always-robust constants it chose are superseded. Under the protocol the
label is mostly a property of the model: a per-model prior fitted on the official labels scores
26/28, 39/41, 43/56 leave-problem-out vs 19/28, 32/41, 32/56 for the constant, transfers between
the two public sets, and is the binding split because the organizers state the validation set
covers all test-set model types. Self-consistency adds nothing; on the 69-problem MATH release the
8B's failures do not transfer across perturbation types, so the free gate fails again and the
Small-track GPU route stays killed. Official path replayed at starter HEAD `e46be92` (always-false
0.6786, prior 0.9286 in-sample; importer/ingestion schema mismatch confirmed at HEAD). Deliverables:
`REPORT.md` (reframed for the $5,000 writeup pool), `PREREGISTRATION.md` with a dated amendment,
`protocol_reconstruction.py`, and the verified bundles. Number #77 is provisional; if a parallel
session took it, renumber. Nothing here bears on RH (docs/08).

### Hunt #71: Krenn-Gu 8x3: port the verified 6x3 orbit census and measure the next exact frontier (`r_322dae/`)

**Status: settled.** The 6x3 baseline checksum reproduces 15 matchings, 3375 triples, and 8 S6 x S3 orbits with exact sizes [15, 90, 120, 270, 360, 360, 1080, 1080]. For the 8x3 frontier (105 matchings, 1157625 triples), the direct product group S8 x S3 (order 241920) partitions the triple space into exactly 31 disjoint orbits, confirmed both by constructive partition and Burnside fixed-point evaluation. Quotienting by the wreath-product stabilizer of a fixed matching H = S2 wr S4 (order 384) partitions the 11025 pairs into 86 orbits (57 orbits under H x S2).

### Hunt #73: Krenn-Gu 8x3 support frontier (`r_044dd2/`)

**Status: support census settled; algebraic sieve open.** This hunt corrects the scope of Hunt #71: the 31 target-matching orbits do not quotient the full 252-variable polynomial system. All 31 branches have independently replayed support survivors, with 76 to 132 active entries and median 118, so the inherited support conditions close zero branches by themselves. On the sparsest branch, four survivors are excluded by exact signed-Laurent certificates. The size-2 stabilizer mirrors those into four more replayable cuts. Support 7 passes the independent support audit and avoids all eight cuts. Exact fixed-degree cap-3 and cap-4 spans do not exclude it. Cap-5 closure produced 13,379,522 relation multiples, but the first sparse elimination ordering hit measured fill-in before a membership decision. No branch is closed and no complex witness has been found.

### Hunt #140: Krenn-Gu 8x3: bounded unrestricted Groebner step on Support 7 (`r_abf47b/`)

> **Renumbered on landing, 2026-10-21.** Opened as #77 on `hunt/r-abf47b-bddff380`
> (run `bddff380`, 2026-08-22); renumbered on landing because `aimo2/` holds #77.
> It takes #140 because two landings opened the same hour take the numbers below it:
> `mobius_orbits/` takes #138 (`land/mobius-orbits-20261021`) and `seven_eighths_pin/`
> takes #139 (`land/quasi-riemann-seven-eighths-20261021`).
> `hunts/r_abf47b/` is the stable reference.

**Status: attempt unresolved, no algebraic conclusion; one exact orbit result.**
Continues Hunt #74 (`r_31b6c1/`) on Hunt #73's Support 7 for orbit 18, in two parts.
*The orbit refinement stands.* The 57 H x S2 orbits on matching pairs (H = S2 wr S4,
the stabilizer of M0) only refine the 31 S8 x S3 orbits on matching triples: S8 is
transitive on the 105 perfect matchings, so every triple orbit meets the slice
{M0} x PM x PM, and the 57 map onto the 31 (fibres of one, two and three pair orbits
over 8, 20 and 3 triple orbits). Two skeletons over one triple orbit are symmetric
copies, so Hunt #74's thread, scale the sieve to the 57 pair-orbit skeletons, adds no
branch. Exact finite check on two routes: `map_orbits.py` over all 105^3 triples, and
`test_orbit_refinement.py`, added on landing, on the slice alone against Hunt #71's
orbit sizes. *The Groebner step does not test Support 7.* `run_groebner.py` gave
`sympy.groebner` (grevlex) the three monochromatic target brackets as zero generators
next to the 6,558 relations of Hunt #73's `build_system`: 6,561 generators in 138
variables, every one homogeneous of degree 3 or 4 with no constant term, and no torus
saturation. That ideal is proper, the origin being a common zero, so its basis can
never be [1] and the 300 s timeout says nothing about Support 7. The question Hunt #73
Result 4 poses is membership of the target product in the relation ideal saturated by
the variables. The run also stopped at its own 5-minute alarm although the mission
allowed 20 minutes. Its "32.59 MB peak" is the run's own report and is unverified: by
the script's code it would be the resident set size at the alarm, and the committed
script, rerun unchanged at landing, read 600.5 MB there and already 84.4 MB before the
Groebner call starts. The calibration reruns main's code (`cap3.json` is
byte-identical to a fresh cap-3 screen; r_31b6c1's 6x3 gate) and is not an independent
route, and its cap-4 4,216 replay is reported without an artifact. `RESULTS.md` keeps
the run's text and carries the "Audit correction" that governs it; `PROBE_RESULTS.md`
is retitled as this hunt's rerun of r_31b6c1's probe. Orbit 18 remains open, no branch
is closed, and no complex witness has been found. Nothing here bears on RH (`docs/08`).

### Hunt #61: two-sided bounds for the de Bruijn-Newman constant of Davenport-Heilbronn (`lambda_dh_bounds/`)

**Status: closed (2026-08-16), gate verdict publication candidate; hardened
2026-08-18, verdict unchanged.** The bracket, in the wide frame of
Rodgers-Tao and Polymath 15:
0.2304 < Lambda_DH <= 0.7696992583210755065522 (narrow frame: 0.0576 = 36/625
to 0.19242481458026887663805), ratio 3.341. Lower side decided by
ball-arithmetic winding counts with a zero-shared-layer second witness; upper
side a decided strip constant fed to de Bruijn 1950 Theorem 13. The quotable
corollary, recognized after the gate closed and adversarially narrowed in
`SEPARATION.md`: **Lambda_DH > Lambda_zeta unconditionally** (0.22 from
Polymath 15 against the decided 144/625), the first strict order between two
such constants with both nonnegative. The gate cycle caught and preserved
three corrections: a factor-of-4 frame error (two normalizations live in the
literature, `FRAME.md`), the sigma_0 originality claim withdrawn after
Bombieri-Ghosh 2011 was retrieved and read (their exact abscissa 1.120362
displaces it), and one prose lemma (M2) recorded as a lesioned blind spot
rather than repaired. The 2026-08-18 hardening then took two of those back:
M2 is proved with decided constants (`M2-LEMMA.md`), and the upper bound
sharpened by the full factor 2.082 in-tree, from a phase obstruction in the
Euler products that reaches Bombieri-Ghosh's abscissa and decides it on both
backends (`STRIP2.md`); the superseded headline
(<= 1.6025374835598228 wide, <= 0.4006343708899557 narrow, ratio 6.955) is
kept beside the new one everywhere it appeared, and the lower side did not
move in any digit. Doc: `docs/29`. Full adjudication: `GATE.md`. Predictions
P1-P3 and P5 held; P4's census found nothing deeper below height 600. Nothing
here is evidence about RH.

### Hunt #60: the rightmost zeros of the prime zeta function (`prime_zeta_rightmost/`)

**Status: settled. The threshold is correct, the conjectures are false, and
the core is a rediscovery of published work: kill condition 2 fired.** The
hunt attacked the two conjectures posted on OEIS A107311 (2024-12-21), that
x* = 1.7286... (root of zeta(x) = 2) bounds the real parts of the zeros of
the prime zeta function P(s) = sum_p p^(-s) and of every prime-subset
series. It decided on both backends (python-flint arb at 350 bits and
mpmath.iv at dps 40, exact Fraction endpoint logic) the balance root
sigma_c = 1.779544653546994116445898786965... of P(sigma) = 2^(1-sigma),
x* = 1.728647238998183618135103010297..., the separation sigma_c - x* >
1/20, the margin P(x*) - 2^(1-x*) = 0.0169073772138... > 1/60, the subset
constant sigma_3 = 1.8252259560738457... with sigma_3 - sigma_c > 0.0456813,
and log2(69/(5 log 23)) = 2.1379035036560028... > 17/8. It wrote out both
halves of the threshold theorem with proofs (triangle-inequality wall;
Bohr-Kronecker-Rouche existence below it), ran the WP5 calibration control
(the same solver object, pointed at the zeta partial sums, reproduced 31
digits of the literature's x*), two lesions and a precision-response check,
and settled predictions P1-P4, P4 including a screen of sigma = 7/4 to
t = 1e8 whose global |P| minimum was about 0.010021 at t about 5.63e7, far
above the alignment budget.

**Then the prior art was found, and it owns the core.** Belovas, Cepaityte
and Sabaliauskas, *On the zero-free region and the distribution of zeros of
the prime zeta function*, An. St. Univ. Ovidius Constanta Ser. Mat. 33(2)
(2025) 27-44, Theorem 1: the same wall, the same constant to every digit
they print, the same triangle-inequality proof. Sepulcre and Vidal,
Carpathian J. Math. 38 (2022) 489-501 (preprint arXiv:1805.02041, 2018),
Theorem 4.3: the general characterization, strictly stronger than the
hunt's existence half, with Moreno's Geometric Principle (Compositio Math.
26, 1973) as the finite ancestor and the source of the aggregated-tail
device the hunt reinvented as its Lemma 2. `MISSION.md` kill condition 2
reads: "a literature source is found proving the sigma_c threshold for P,
in which case the finding is reclassified as a rediscovery and the OEIS
correction cites that source instead of this work." It fired. The
reclassification is done, in `hunts/prime_zeta_rightmost/PRIOR-ART.md`
(statement-by-statement ownership map, verbatim source texts, the worked
specialization) and in the rewritten `docs/30-prime-zeta-rightmost-zeros.md`,
which now leads with the prior art.

**What survives as the hunt's own**, and nothing beyond it: (a) the
line-by-line refutation of the two OEIS conjectures, since no source in the
literature engages that entry and the published wall does not by itself
refute Conjecture 1 (1.7795 is weaker than the conjectured 1.72864, and
Belovas et al.'s numerics stop at 1.6826, below x*), graded new as a
connection with zero new mathematics; (b) the unbounded tail-subset walls, {p >= p_k}
walled at or above log2(3 p_k / (5 log p_k)) via Rosser-Schoenfeld, so no
constant bounds the real parts across all prime subsets and Conjecture 2
fails for every replacement constant, graded new, small and elementary, and
the only mathematics here not located in print; (c) the constant sigma_3 and the
fact that a subset out-walls the full series by more than 0.045, a new
instance of prior-art theory; (d) the two-backend enclosures, rediscovery in
sharper form, the source printing 15 digits and noting that any precision
is available; and (e) one literature observation, that Belovas et
al.'s Conjecture 1, left open in their paper, is a corollary of Sepulcre
and Vidal Theorem 4.3, which neither paper cites. The steering lemma's
positive lower density in t is carried as an unverified lead, since the
Jessen-Tornehave literature was not searched.

**The lesson, which is the most transferable thing the episode produced.**
Two independent search failures, needing two different countermeasures, and
both reproduce on demand. The exact-phrase query "zeros of the prime zeta
function" is a literal substring of the Belovas et al. title and the engine
still does not return it: no arXiv preprint, a Sciendo/DOAJ venue outside
the sweep, and an image-scanned PDF that has to be downloaded and extracted
rather than fetched. The general theorem was missed for an unrelated
reason: it is filed under almost periodic functions, MSC 30B50/30D20, and
never names a prime, so no prime-zeta query can reach it, and it was
reachable only by searching for the device rather than the application.
Four independent searches returned nothing while two published papers owned
the result outright, which is the standing argument for
`ontology/knownness.py` defaulting to "the literature was not consulted".

**Disposition:** instruments retained; nothing promoted; the OEIS
correction drafts in `OEIS-CORRECTION.md` remain unposted; they cite Belovas
et al. for the threshold, which is what the kill condition required, and that
rewrite is done. Nothing here bears on RH: the zeros discussed are zeros
of P and of subset series in Re s > 1, not zeros of zeta.

### Hunt #56: make_context.py blind region on meta/ package (`r_2946de/`)

**Status: settled.** `scripts/make_context.py --check` does not detect public functions, classes, constants, docstrings, or new modules added under `meta/` (0/16 curated mutants detected, 0.0% detection rate; 0/32 public AST symbols detected, 0.0% detection rate), because `meta/` is structurally excluded from the hard-coded scan paths in `make_context.py` and produces zero diff in `CONTEXT.md` (exit 0). In contrast, in-scope positive controls in scanned directories (`zeta/`, `ontology/`, `harness/`, `docs/`) are 100% detected (4/4 caught). Measured on a 16-mutant curated battery and a 32-symbol exhaustive AST census in `hunts/r_2946de/results.json` and `RESULTS.md`. Nothing here bears on RH (`docs/08`).
### Hunt #59: test file naming sensitivity and boundary of make_context.py --check (`r_c35cd1/`)

**Status: settled.** `scripts/make_context.py --check` does not detect test files whose names do not match `test_*.py` (such as `tests/mutant_helper.py`, `tests/conftest.py`, or `tests/helper.py`), nor does it detect nested test files in subdirectories (`tests/fixtures/test_sample.py`, `tests/unit/test_unit.py`), non-Python test assets, or helper functions and length modifications within existing test files (0/22 non-matching specimens detected, 0.0% detection rate), because `test_counts()` uses a shallow `TESTS.glob("test_*.py")` and counts only AST function definitions starting with `test_` without tracking line counts for test files. In-scope test modifications (`test_` function additions, renames, and new `test_*.py` files) are 100% detected (3/3 caught). An exhaustive repository census shows 77 `test_*.py` files with 1852 test functions and one unindexed fixture asset (`tests/fixtures/rung3_ball_term_kernel.json`). Zero non-`test_*.py` Python helper files have ever been committed in repository git history across 79 historical paths. Measured on a 25-mutant curated battery in `hunts/r_c35cd1/results.json` and `RESULTS.md`. Nothing here bears on RH (`docs/08`).
### Hunt #57: make_context.py compiler/ unscanned boundary and detection blindness (`r_dc6e6f/`)

**Status: settled.** `scripts/make_context.py --check` does not detect public functions, classes, constants, docstrings, or module additions added under `compiler/` (0/17 curated compiler mutants detected, 0.0% detection rate; 0/37 public symbols detected across an exhaustive AST census, 0.0% detection rate), because `compiler/` is completely omitted from the scanned directory roots in `scripts/make_context.py` (`zeta/`, `ontology/`, `harness/`, `dossier/`, `docs/`, `scripts/`, `tests/`) and from `build_flat()`. Positive controls in scanned packages are 100% caught (5/5 detected). Evidence in `hunts/r_dc6e6f/RESULTS.md` and `results.json`. Nothing here bears on RH (`docs/08`).
### Hunt #55: make_context.py in-place helper renames and __all__ boundary (`r_7ad39f/`)

**Status: settled.** `scripts/make_context.py --check` does not detect in-place length-neutral private helper renames in modules that declare `__all__` (0/299 unexported private symbols detected, 0.0% detection rate), because `module_api` filters top-level definitions strictly by `ast.literal_eval(__all__)` and the file length remains unchanged. In non-`__all__` modules, detection is 100% (4/4 symbols caught). Any edit altering line count is 100% detected via the line-count tell. Zero length-neutral private-to-public helper renames have ever occurred in repository git history. Measured on a 25-mutant curated battery and a 305-symbol exhaustive census in `hunts/r_7ad39f/results.json` and `RESULTS.md`. Nothing here bears on RH (`docs/08`).
### Hunt #52: scope caveat: compiler verdicts rest on a hand-written model, not LLVM semantics (Alive2 absent) (`r_e2ee73/`)

**Status: settled.** Compiler refinement verdicts in `compiler/` rest on a hand-written pure-Python interpreter (`pymodel.refinement_i8`, rung 2) rather than formal LLVM semantics, because Alive2 (`alive-tv`, rung 3) is absent from this environment. The exposure of the hand-written model is bounded by an exhaustive two-backend cross-check against compiled Apple Clang binaries (`clang.exhaustive_i8`, rung 1) across all 10 fixtures (655,360 total evaluated points, zero mismatches). While the concrete Clang detector is blind to poison violations covering 50% of the domain (`nsw_flag_on_a_wrapping_shift`), the model detector captures poison and immediate UB at full declared power. An audit of unsupported IR constructs confirms that out-of-scope instructions safely raise `ModelUnsupported` rather than guessing. True LLVM-native refinement remains absent without Alive2. Evidence in `hunts/r_e2ee73/RESULTS.md` and `results.json`. Nothing here bears on RH (`docs/08`).
### Hunt #50: doc renaming without number change, and doc content drift (`r_c62e44/`)

**Status: settled.** `tests/test_docs_numbering.py::test_no_two_docs_share_a_number` enforces uniqueness of the leading 2-digit number (00..N) across `docs/*.md` filenames and detects collisions (smallest mutant: `05-a.md` and `05-b.md`), but does not detect a document renamed without its number changing when citations use bare references (such as `docs/08`), nor does it detect content drift or heading changes. Sibling test `test_every_full_filename_reference_to_a_doc_resolves` detects renamed documents only when un-updated full-name references exist in the tree. An exhaustive census across all 37 test files mentioning `docs/` confirms zero tests in the suite inspect document body content, validate H1 headings against filenames, or verify that citations match actual content. Measured on a 20-mutant battery in `hunts/r_c62e44/results.json` and `RESULTS.md`.
### Hunt #51: file-type boundary of the hunt reserved-word guard (`r_365c6c/`)

**Status: settled.** `tests/test_hunt_probe_discipline.py::test_no_hunt_claims_the_reserved_word` enforces an explicit suffix whitelist (`path.suffix.lower() in {".py", ".md", ".json"}`). Every file type outside this three-extension set passes unconditionally (40-specimen battery across 12 format categories in `probe.py`: 6/6 `.py/.md/.json` caught, 0/29 non-{py,md,json} caught). An exhaustive repository census shows 76 of 447 files (17.0%) under `hunts/` are currently unscanned, including 68 `.lean` proof files under `hunts/frontier_math/`. None of the 76 unscanned files contain the reserved word. Evidence in `hunts/r_365c6c/RESULTS.md` and `results.json`. Nothing here bears on RH (`docs/08`).
### Hunt #63: truncated Weil form positivity failure on Davenport-Heilbronn (`r_ac9ca3/`)

> **Renumbered 2026-08-20.** Opened as #45, which `r_233abe/` had taken
> two days earlier. `hunts/r_ac9ca3/` is the stable reference.

**Status: settled.** The first positivity failure of the Connes–van Suijlekom / Connes–Consani–Moscovici Galerkin truncation of the Weil quadratic form on Davenport–Heilbronn on the integer lattice $c \in [6, 60], N \le 128$ occurs at $(c, N) = (31, 60)$.

Integer cutoffs $c \le 30$ are strictly positive definite across all tested $N \le 128$ (and up to $N = 256$ at $c = 29, 30$). At $c = 31$, the even sector develops its first negative eigenvalue at $N = 60$, with rigorous Arb ball enclosure $\lambda_{\min} = -1.87393568857 \times 10^{-31} < 0$ (radius $\sim 3 \times 10^{-192}$) and exact dyadic Rayleigh quotient upper bound $-1.87393568857 \times 10^{-31} < 0$, while $N = 59$ is strictly positive with $\lambda_{\min} = +8.36504566170 \times 10^{-31} > 0$. The odd sector at $(31, 60)$ remains strictly positive (inertia $60$ positive, $0$ negative). The Riemann zeta control at $(31, 60)$ is strictly positive by 100 orders of magnitude: even inertia $(61, 0)$, odd inertia $(60, 0)$, $\lambda_{\min}(\zeta, 31, 60) = +4.82160175 \times 10^{-100} > 0$. The failure tracks the first off-line pair at $\gamma_{\text{off}} = 85.6993, \delta = 0.3085$: across $c \in [32, 60]$ the crossing band edge mean is $83.64 \pm 2.44$, and at $(31, 60)$ the zero-side dictionary decomposition proves the off-line quadruple ($-6.734989 \times 10^{-29}$) is the sole negative contributor, whose subtraction flips the form value positive to $+6.716250 \times 10^{-29} > 0$. Evidence in `hunts/r_ac9ca3/RESULTS.md` and `results.json`. Nothing here bears on RH (`docs/08`).
### Hunt #66: four arms salvaged off an abandoned branch (`r_f00e48/`)

**Status: settled.** `claude/riemann-hypothesis-research-ofds8s` ran a
wide-portfolio RH-adjacent campaign on 2026-08-17/18 and never landed. Four of
its five arms existed nowhere on `main`; they are now in
`hunts/rogue_frontier/`: `weil_trunc/` (23 files, 8 replication gates, a 27/27
conclusive-positive enclosure grid, and the Davenport–Heilbronn positivity
failure at `(c, N) = (31, 60)`), `sine_gram/` (exact finite-N engine,
`m_5(1) = 101/18`, `m_6(1) = 640/63`), `window_opt/` (RF-C003, the campaign's
one promoted claim), and `nyman_beurling/` (Baez-Duarte distances to
`N = 2048`, against `main`'s previous `N = 50`), plus the survey documents.
**1,717,013 bytes landed against ~58 MB on the branch**: 56 MB of regenerable
pickle and a stale `.ext_lock` stayed behind, and so did `fkappa/`, whose
`kappa = 2` table Hunt #65 had already adjudicated wrong. `LANDING.md` records
the subset so the gaps do not read as loss. **The defect the checking found:**
`REPRODUCE.md`'s headline command for RF-C003, the campaign's *only* promoted
claim, did not run, it named `functional.exact_F_quartic(1467, 1159)`, a
symbol that never existed under that name or that signature, so a reader
following the published recipe got an `ImportError`. The function is
`moments_polyeven_exact(OPT_Q)` returning `(m2, m3, F)`; `probe.py` now
recomputes `F(v*) = 2245228120295149280/3276332462159207451` from the landed
source and pins it against the landed document. Two further references were
repaired. **The one external corroboration:** `main`'s own Hunt #45
(`r_ac9ca3/`) reached `(31, 60)` independently, and the salvaged
`dhneg_scan.json` agrees with it digit for digit on the enclosed DH eigenvalue
(`-1.87393568857018838648…`, radius ~5.7e-208) and the zeta control
(`+4.82160175202313776…e-100`). **What it does not establish:** re-running an
arm's own code is not an independent check of it, and RF-C003 is entered in
`harness/departments/review_ledger.py` with a white-box outcome saying exactly
that, leaving `standing_reasons()` correctly reporting no blind attack, a new
open item, honestly created, not one closed. Two further arms (`erdos_scan/`,
`matchings/`, the latter claiming a kernel-checked Lean result) appeared on the
branch *after* the sweep that specified this landing and are unreviewed rather
than rejected. Evidence in `hunts/r_f00e48/RESULTS.md` and `results.json` (29/29
checks). Nothing here bears on RH (`docs/08`).

### Hunt #65: the conflicting kappa = 2 tables, adjudicated (`r_2ac05f/`)

**Status: settled.** Two directories carried a table of the same quantity, the regular coefficients `C_{2,i}` of Bian's pair-correlation form factor for the zeros of `xi''`, and disagreed at every index from 2 to 11: `hunts/higher_xi/C2_EXACT.json` (`1, -8, 24, -32, 64/3, ...`) against `hunts/rogue_frontier/fkappa/` corrected mode (`1, -4, 4, -16, 52/3, ...`), with conflicting diagnoses. **`higher_xi` is right.** A fourth derivation written for this adjudication and importing neither hunt, the identity `R_kappa = xi'/xi + D log Q_kappa` expanded in a formal Dirichlet word algebra, exact rationals throughout, reproduces `higher_xi`'s eleven values exactly, and reproduces the externally published Farmer-Gonek `kappa = 1` row (arXiv:0803.0425) exactly as its control, including the four forced zeros. The general defect, derived here and recorded nowhere else: the `x^1` coefficient of `Qhat_kappa = Q_kappa / L^kappa` is `kappa*g`, so **`C_{kappa,2} = -4*kappa`** (`-4, -8, -12, -16, -20` for `kappa = 1..5`), and Bian's Lemma 12 asserting a universal `-4` is the dropped `M(v_l)M(w_k)` weight `C2_PROVENANCE.md` names on thesis page 71. `fkappa` reimplemented the thesis code faithfully and found three real implementation defects in it, but carried Lemma 12's `-4` as an axiom, so its correction sits downstream of a larger error. **The control that would have caught it, measured rather than asserted:** planting exactly that defect in this hunt's probe leaves the Farmer-Gonek `kappa = 1` control passing and moves `C_{2,2}` to the published `-4`, while a one-factorial corruption of the pairing turns the same control red. The only externally anchored control either hunt ran has zero power against the defect that decided the dispute; the control with power is to compute `C_{kappa,2}` for `kappa = 1, 2, 3` and assert the values differ, i.e. an invariance claim needs a control that moves the variable the invariance is asserted over. Evidence in `hunts/r_2ac05f/RESULTS.md`, `results.json` and `fault_check.json`; outcome appended to `harness/departments/review_ledger.py`. Nothing here bears on RH (`docs/08`).

### Hunt #64: gap A of the lattice-extremality route is a forbidden constant (`r_b9552d/`, run 2)

**Status: not settled** (the gap stands), **and one thing settled inside it.** Second run of `r_b9552d`; run 1 is Hunt #46 above and its artifacts are preserved under run-tagged names. `LATTICE-EXTREMALITY-ROUTE.md` bounds the centre-gas row `J(T)` only for densities `rho >= 1/(2*pi)` (its gap A). Any single density-independent Cohn–Elkies certificate `g` (with `g >= f`, `ghat <= 0`) proving `J <= L = 0.11433003938654052` at every density is pinned exactly: `ghat(0) = 0`, `g(0) = -L/2`, `sup|g| <= L/2`, and `ghat` vanishing at every integer. The necessary condition `sup f <= L/2` **passes** with margin 3.04992 (`sup f = 0.0187431348` at `s = 6.3974` against `L/2 = 0.0571650197`), so the route is not excluded; a 3.05× planted inflation of `f` fires the test. But the Fejér family that closed gap B on `main` (`7efd506`) reaches `ghat(0) = 0` only at `c = 2*c2(0) = 1.6984559986`, where the bound becomes exactly `L` at every density (spread 6.7e-16), and admissibility caps `c` at `cos²(√2/2)(1+cosh 1) = 1.4698290125`: short by a factor **1.15554665**, with a frequency-domain witness `ghat(0.87493) = +0.0839055 > 0`. A quoted Paley–Wiener factorisation plus critical sampling makes `c·(sin(x/2)/(x/2))²` the only band-limited candidate, so the miss is the family's, not the ansatz's. Byproduct: the first sparse-side bound in this route, `J(T) <= 2*kappa(0) - 2*cos²(√2/2)(1+cosh 1) = 0.5715840116` at **every** density, `4.99942 × L`. Evidence in `hunts/r_b9552d/RESULTS.md` and `results.json`. Measured, double precision, no enclosures. Nothing here bears on RH (`docs/08`).

### Hunt #49: zeta23ext root load, Retention.Aconst / c2 collisions across arms (`r_6f088d/`)

**Status: settled.** The root module load failure in `zeta23ext` was caused by 17 colliding declarations (including `Retention.Aconst` and `Retention.c2`) across `EForm`, `EForm2`, and `EForm3` all declared in the un-scoped `Retention` namespace. In Lean 4, importing modules with duplicate fully-qualified names halts elaboration with an environment collision. The collision is resolved by scoping arms into distinct sub-namespaces or importing only the active `EForm3` iteration, while mathematical duplication remains across the independent development arms.
### Hunt #47: the two-mode arithmetic, and the bridge nobody had named (`r_88dc5e/`)

**Status: settled.** `O9Assemble.lean` said the last step between the
kernel-checked table and O9 was "the arithmetic of the two modes". It was, plus
one prerequisite that was not on anyone's list. `O9Check2` decides a table in
the kernel's interval arithmetic; `O9Sound` proves both modes sound over the
reals in terms of `Retention.Qre` and `Retention.Qim`, which are integrals
against the window `g`; and the enclosure chain ended at `BandDual.Phi2`, which
is `s(z+√2) + s(z−√2)`. Those are two different definitions of the same two
numbers and **nothing in the package connected them**. `EForm3/O9Bridge.lean`
does: `Re Phi2 (s + iy) = Qre y s` and `Im Phi2 (s + iy) = −Qim y s` for
`y ≠ 0`, by closed forms on both sides and no new analysis.

With that, `EForm3/O9Modes.lean` turns the checker's `Bool` into the damage
bound. `dam_le_of_box` says a box `o9Box` accepts bounds `Dam` at every point
of it, `y = 0` included; the content is that `Iv.mem` is `lo ≤ 2⁶⁴·x ≤ hi`, so
each recorded comparison is one division away from the real inequality mode 1
or mode 2 wants. `dam_le_box0` instantiates it at the **first recorded row** at
the interior point `(23/4, 1/8)`, with the verdict taken from `o9_box_chunk0`,
the kernel's own `decide +kernel`, rather than from a fresh decision. Zero
sorrys, axioms `[propext, Classical.choice, Quot.sound]`.

The two dead-weight lemmas are **gone**. The use-site survey run bbe76b9a
reported was re-run rather than trusted, over the whole repository:
`O9Seam.r_comp_mem` had exactly one use site (`Retention.rIv_mem`) and
`rIv_mem` had none. Both are deleted, `r_comp_mem'` carries the corrected
statement, and nothing was reproved.

**What this does not close.** O9 soundness is not closed and the hunt does not
claim it is. `dam_le_of_mem_walk` bounds `Dam` at points of boxes the table
records; the retention obligation needs the whole window, and nothing in Lean
yet says the recorded boxes **cover** `[28/5, 60] × [0, 1/2]`. That covering,
and the assembly into the form `Gap`/`FarField` consume, are what is left.

Also recorded, because it cost this run time: `simp only [o9Box]` and
`rw [o9Box]` both hang on a `whnf` heartbeat timeout, unfolding the checker
asks the elaborator to reduce `rIv b.sLo …` symbolically through the entire
leaf layer. `unfold o9Box at hb`, then `split at hb`, then one definitional
`have` does the same job instantly.
### Hunt #48: Erdős–Kac priced, and one of the two routes is blocked (`r_8c3b94/`)

**Status: settled. A mapping run, not a proving run.** Two earlier runs left
Erdős–Kac as prose ("a real project", "needs either moment control to all
orders or a formalised Berry–Esseen route", "out of reach and should be said
so"). None of that is a coordinate, so this run priced both routes against
what Mathlib actually carries at this repository's pin, resolving every claim
by compiling 43 `#check`s rather than by grep. `Probe.lean` in the hunt
directory is that file; it exits 0 and is imported by nothing.

- **The moment method: ~2,400 to 3,700 lines**, ~1,800 to 2,600 of them novel
  mathematics. Every obligation is something somebody knows how to write.
  Hardest step is reindexing k-tuples of primes by the set-partition of the
  index set: at k = 2 that is `rcases eq_or_ne p q` and costs nothing, uniform
  in k it has no Mathlib support at all.
- **The characteristic-function route is blocked, not merely dearer.** It
  needs the fundamental lemma of sieve theory. Mathlib's sieve
  (`BoundingSieve`, `siftedSum_le_mainSum_errSum_of_upperMoebius`) is
  **upper-bound only**; the phrase "fundamental lemma" occurs once in that
  file, in a docstring. No Lean formalization of it exists.
- **The reason, and the finding worth keeping**: the moment route needs only
  k-fold products, so its arithmetic error is `π(y)^k`, polynomial, and it
  tolerates `y = N^{1/2k}`, which keeps `log log y ~ log log N`. The
  characteristic function needs all orders at once, so its error is
  `2^{π(y)}`, which forces `y` down to about `log N`, at which point
  `log log y` is no longer asymptotic to `log log N` and the theorem's own
  normalisation dies. The route closes on itself. Derived here, not looked
  up, and flagged as such.
- **A prerequisite that looked live is dead.** `hunts/r_0339c1/RESULTS.md`
  treats tightening the Mertens band `16` as the lever. True for the
  Hardy–Ramanujan constant `275`; **irrelevant to Erdős–Kac**, which uses the
  band only as an `O(1)` shift divided by `√(log log N)`. Mertens with its
  constant is not needed, and this tree does not have it.
- **Also measured, because a miss is a result**: Mathlib at rev `51e6992e`
  has an i.i.d.-only CLT and Lévy continuity, and has **no** Berry–Esseen, no
  Lindeberg, no method of moments, no Carleman, no Gaussian moment beyond the
  second, no Mertens theorem of any kind, and no Kubilius model.
  `Nat.stirlingSecond` exists with recurrences and no combinatorial content.
  Fourteen named misses in `results.json`, each with the term searched for.

**Disposition:** coordinates, not a claim. The recommendation is Route A or
nothing, with the **k = 4 central moment as a single bounded first file** and
a stated stop condition (over ~600 lines and the estimate has failed at the
step that matters). Three sub-obligations are wanted upstream independently of
whether Erdős–Kac is ever attempted: a triangular-array CLT, the Gaussian
moments, and a method-of-moments theorem. Nothing here bears on RH.

### Hunt #44: what the O9 numerator fields actually enclose (`r_938ab4/`)

**Status: settled, and the two fields answer differently.** Hunt #42 left the
question of whether `reNum_mem` and `imNumOverY_mem` pin `Re num` and
`Im num / y` or merely the shapes the interval arithmetic computes.
`Zeta23Ext/EForm3/O9NumShape.lean` settles it. **`reNum` encloses `Re num`
unconditionally**: once `SQ2_mem`, `SINC_mem` and `COSC_mem` instantiate the
three constant leaves the computed shape *is* the real part, at every point of
every box, `y = 0` included, with no hypothesis beyond the ones the leaves
already carried. **`imNumOverY` encloses `Im num / y` only for `y ≠ 0`**, and
the hypothesis is necessary rather than incidental: `Im num` vanishes on the
real axis, so `Im num / y` at `y = 0` is `0` by Lean's division convention,
while the field carries `shcSmall` and therefore encloses the removable limit,
`2·cos(√2/2) + √2·sin(√2/2) > 0` at `s = π`. The disequality is stated as a
disequality, not hedged into a hypothesis. That asymmetry is the design
working: the removable branch exists so `y = 0` is an ordinary point, and it
can only be ordinary by enclosing something other than a quotient by `y`
there; what the run adds is that the something other is now named and pinned.
With both components identified, `qreIv_mem_phi2` and `rIv_mem_phi2` read the
two compositions back against `Phi2` itself. **Verdict on the dead weight:**
`O9Seam.r_comp_mem` and `Retention.rIv_mem` can be retired at no reproof cost,
`r_comp_mem` has exactly one use site (`rIv_mem`) and `rIv_mem` has none,
and the route built here goes through `r_comp_mem'` and `rIv_mem_box`
instead. They were shown unnecessary, not deleted. Twenty-seven declarations,
zero sorrys, `lake build Zeta23Ext.EForm3.Main` green (8726 jobs),
`#print axioms` reporting only `[propext, Classical.choice, Quot.sound]` and,
for `box0_in_table`, no axioms at all. Because a compiling lemma is not a
lemma with content, hunt #42's finding, every identification is also
instantiated at the **first recorded row of `o9boxes`** at the interior point
`(23/4, 1/8)`, with every hypothesis discharged. What is **not** claimed: O9
soundness is not closed; the two-mode arithmetic and the identity joining
`Phi2` to `EForm3.Qre`/`Qim` are separate and untouched, and the `y = 0`
mismatch witness sits at `s = π`, outside the table's `s`-range. Two
**pre-existing** build failures are recorded rather than absorbed:
`RetentionWired.lean:44` does not elaborate, and `BandCert.Verify` is killed
at 704 s with exit 137, both observed on a baseline build made before the new
file existed. Evidence in `hunts/r_938ab4/RESULTS.md`. Nothing here is
evidence for or against RH.

### Hunt #39: the Mertens constants, tightened (`r_4218d4/`)

**Status: settled. The Turán variance constant of Hunt #37 falls from `5855`
to `275`, a factor of 21.3, with every statement's shape preserved, no
hypothesis added, no `sorry`, a green `lake build` and an unchanged axiom
audit.** Hunt #37 wrote that its constant is "coarse because the Mertens band
is, and tightens automatically if that does". This run did that, and the
prediction was right: no new mathematics was needed anywhere.

Three local steps upstream, then arithmetic. (i) Mathlib's
`Chebyshev.psi_le` gives `ψ x ≤ x log 4 + 2√x log x`, and its packaged
corollary bounds the remainder by `4x`, i.e. by `log t/√t ≤ 2`, where the
supremum is `2/e`. A one-line lemma `log t ≤ t/e` (`log x ≤ x − 1` applied at
`x = t/e`) gives `(4/e)x`, stated as `3/2`. (ii) The same majorant replaces
`log n ≤ 2√n` in `sum_log_div_sq_le`, and dropping its vanishing `n = 1` term
lets the telescope start at `2`, where it is bounded by `2` instead of `3`;
`6` becomes `3/2` and the prime-power tail `12` becomes `3`. (iii) Mertens I
is asymmetric, its lower half loses `1`, its upper half the whole Chebyshev
constant, and the original proof paid both by routing the prime form through
the symmetric von Mangoldt band; a one-sided
`log_sub_one_le_sum_vonMangoldt_div` keeps them apart, worth `1.5`. Result:
`mertens_first_theorem` `log 4 + 16 → log 4 + 3`; `mertens_second_theorem`
`76 → 16` (with `1/log 2 < 2` also sharpened to `< 1.443`); `sum_sq_dev_le`
`5855 → 275 = 16² + 16 + 3`.

The classical constants (`2` for Mertens I, `4` for Mertens II) are still out
of reach and the run did not chase them, per its brief. What remains is
priced in `hunts/r_4218d4/RESULTS.md`: the largest single term left is the
`log 4` in Chebyshev's bound, which is 39% slack and whose removal is the
prime number theorem, not a constant. Earlier case-log entries and the
`r_3c1cbb` / `r_0339c1` write-ups still quote the old constants; those are
records of what those runs proved and are left as written. Nothing here bears
on ζ or RH (`docs/08`); external verification remains pending.
### Hunt #46: where the centre-gas obligation T1 resists (`r_b9552d/`)

**Status: not settled, which was the expected outcome.** `k >= 3` is not
closed, T1 is not proved, and the reading of record does not move. Run
`37fb06a9` probed the first half of `K2-TWO-SPECIES.md` §5's two-species
split. Three things came back.

**T1 restated against a budget that is already proved.** Splitting
`gram_form.budget_gram`'s Gram sums into diagonal and off-diagonal parts
gives the identity `GAS = k·Shq(y) − 2B + P`, with
`GAS = Σ_{p≠q}[Dam(2y,τ) − Kpair(τ)]` and
`P = Σ_{p≠q}[−D(2y,τ)]⁺ ≥ 0` (residual 8.0e-15 over 300 random
configurations). `B ≥ 0` already follows from `Retention.energy_F_ge`, so
T1 with the *signed* damage and `ρ = 0` is a consequence of a
kernel-checked theorem, and the whole content of T1 is the strict
positivity of `ρ` together with `P`, the credit thrown away by the
`D ≤ Dam` step.

**An exact ceiling on the atom reserve.** T1 holds with reserve `ρ` exactly
when `ρ·k·Shq ≤ 2B − P`. On the critical `2π` lattice `P = 0` (measured out
to `d = 4000`) and `B/k → c2(0) − A²` exactly, by defect #24's Poisson
summation, so `ρ ≤ 2(c2(0) − A²)/Shq(1/2) = 0.153216295…`, and `0.119590…`
against Lean's proved floor `2·Shq y ≥ 0.51944 y²`. That is a closed form
where `K2-TWO-SPECIES.md` §5 had the measured "87.8% of the per-centre
budget". It is a ceiling, not a floor, so it constrains any future atom
argument and proves nothing about T1 itself.

**The gas extremum, searched three ways, is the uniform `2π` lattice.**
Exhaustive periodic occupancy (every subset of `Z_p` for `p ≤ 14`, 230 base
spacings), free periodic (`m ≤ 8` free positions in a free period), and free
finite `k` all return it: best row `0.05716` against the budget `0.06751`,
ratio `0.8466`. The planted-fault ladder first reports a violation at 1.20×
damage against a 1.18× measured margin, so the verdict comes from a search
with demonstrated power at that scale, and no demonstrated power against a
family the search cannot represent.

**One recorded number did not reproduce.** `two_species.NAMED_GAPS` G4
records the `1,1,2,1,1,2,3` occupancy at step `2π` reaching a per-row
`0.1200` against the lattice's `0.1140`, and it is the only on-file evidence
against lattice extremality. Under all three natural readings of the
pattern this run measures `0.0666` (gaps, averaged), `0.0902` (gaps,
maximised over centres) and `−1.3600` (multiplicities) against `0.1143` for
the lattice. This is a failure to reproduce and is reported as exactly that:
the pattern may mean something the run did not try, or `0.1200` may be a
per-centre maximum, in which case it was never a counterexample to T1, which
is an average statement. `hunts/r_b9552d/RESULTS.md` §4 gives all three and
does not adjudicate.

Also assessed and **not settled**: a Cohn–Elkies-style certificate for T1
(`G ≥ Dam − Kpair` pointwise with `Ĝ ≤ 0`, giving `GAS ≤ −k·G(0)` for every
configuration at once). It is not on the recorded dead list and is distinct
from all five routes there. Its truncated LP value has to clear `0.05716`
before it bounds anything and stay under `0.06751` for the route to work; it
reached `0.05410` at horizon 200 and the solver failed above that. Every
number here is double precision, no enclosures, no Lean. Nothing bears on RH
(`docs/08`).

### Hunt #45: the omega bridge, and the pointwise Hardy–Ramanujan (`r_233abe/`)

**Status: settled. Both threads closed, zero `sorry`s, axioms unchanged, no
statement weakened.** Run `43d363c1` left two threads in
`lean/ZetaLean/HardyRamanujantheorem.lean` when it landed the density form of
Hardy–Ramanujan, and this run is both of them.

**The bridge.** `omega n = ArithmeticFunction.cardDistinctFactors n` is `rfl`,
as the discovering run priced it, but not for the reason the file's docstring
assumed: this file counts `n.primeFactors.card` and Mathlib counts
`n.primeFactorsList.dedup.length`. `Nat.primeFactors` is
`primeFactorsList.toFinset`, so the two unfold to the same term. The docstring
now names the two definitions it is identifying instead of asserting they are
one. A one-line `rfl` is a restated definition and the brief is explicit that
a restated definition is not a result, so the bridge is carried through to
`hardy_ramanujan_cardDistinctFactors`, in which `omega`, `loglog`,
`exceptional` and `HardyRamanujanTheorem` have all been unfolded away, every
name in that statement is Mathlib's, and an `ArithmeticFunction`-facing
development can cite the theorem without importing anything from this
namespace. That is the whole interoperability point, and it is the part that
was worth the run.

**The pointwise form.** `hardy_ramanujan_pointwise` measures each `n` against
its own `log log n` rather than against the common `log log N`, which is how
the theorem is usually quoted. The route is the discovering run's, with
`delta` fixed at `1/2` so no parameter is carried: split `(0, N]` by
`n * n ≤ N`; below the split there are at most `Nat.sqrt N` integers, which is
`o(N)`; above it `N < n * n` forces `log N < 2 log n`, so
`log log N − log 2 < log log n ≤ log log N` and the gap between the two
normalisations is the constant `log 2`, uniformly in `N`. A deviation of
`ε · log log n` then forces one of `ε · log log N − (ε+1) log 2`, which is at
least `(ε/2) · log log N` as soon as `log log N` has outgrown the slack, and
`hardy_ramanujan` at `ε/2` closes it. **No new arithmetic enters**: the
variance bound, its constant `275`, and the Mertens band `16` are consumed
exactly as they stand, and no existing proof was edited. So the pointwise form
inherits any future sharpening of the density form for free.

`lake build ZetaLean.HardyRamanujantheorem` printed
`✔ [8699/8699] Built ZetaLean.HardyRamanujantheorem`; `grep -c sorry` over the
edited file is `0`; the five new public statements and `hardy_ramanujan`
itself each depend only on `propext`, `Classical.choice`, `Quot.sound`. The
file grows 384 → 588 lines. Everything that resisted was library-name drift
against the pinned Mathlib v4.33.0-rc2 (`le_or_lt` and `div_add_div_same` are
gone; `rw` cannot use the equation lemmas of a `noncomputable def`;
`Tendsto.inv_tendsto_atTop` returns a `Pi`-form inverse that `simpa` will not
reconcile with a beta-reduced lambda), not mathematics. Two caveats a reader
should have rather than discover: the bridge is a `rfl` between two library
definitions that are spelled differently and would break if either were
restated, which is why it is now pinned by a theorem; and the pointwise
statement is the literal classical one, so the finitely many `n` below `e^e`,
where `log log n` is negative and the condition holds vacuously, sit inside
the exceptional set at no cost in density.

Nothing here bears on ζ or RH (`docs/08`). No literature search was run and
none is claimed: Hardy–Ramanujan is a 1917 result, and what is original is
provenance, not novelty. External verification remains pending, as it does for
every claim this laboratory publishes. Separately, and outside this hunt's
scope: `lake build` over the whole package does not currently succeed in this
container, `ZetaLean.Pub1.CertL2` and `ZetaLean.Pub1.CertAtoms` log failures.
Neither imports anything from `ZetaLean.HardyRamanujan` (checked by `grep` over
their import closure), so neither can be a consequence of this run's edit, and
this run did not diagnose them further. It is recorded here so a green targeted
build is not read as a green package.

### Hunt #40: `beta := normLower` lands, the predicted slack does not (`r_908de5/`)

**Status: settled, and one prediction on main is refuted.** `docs/25` §4.3
defect 2 named the remedy for the rung-3 grid sites, `pred_beta` was drawn at
the achievable bound, so `normLower >= pred_beta` sat at the line by
construction in any arithmetic (12 of 104 sites under 1 %, `g_right_15` at
0.03 %, commit 44d3133), and predicted that setting `beta := normLower` moves
the slack into the cell condition, "which then carries >= 10x slack". The
first half holds: with beta read off the enclosure the site inequality is true
by construction, and the obligation that then bites, `eps' + L*h/2 <= beta`
(the hypothesis of `ZetaLean.DH.DH_lower_on_[hv]cell`, not a modelling
choice), still passes at all 104 sites with `L = 16` and `eps' = 1/2000`
untouched. The second half does not: evaluated in exact rationals over the
committed plan, the worst of the 200 cell obligations clears by **1.3697x** in
ball arithmetic and **1.3566x** in chained-rect, against a prediction of
">= 10x", over by a factor of ~7.3, and barely moved from the 1.3647x it
already had under `pred_beta`, in either direction. The
binding constraint turns out to be the gap, not beta: `L*h/2` is 98 % of the
requirement at every one of the five worst cells, so raising betas buys almost
nothing, and the remedy moved the worst case by 0.4 %. A second finding sets
the price of landing it: `scripts/60_rung3_generate.py` emits a *non-chain*
rect enclosure, 2-3x wider at a point than the chained one `docs/25` measured
in, where `normLower` is 0.37-0.53x `pred_beta` and the cell condition fails
outright, so the remedy is contingent on porting the generator's emission to
composite chains, for which the Lean side (`dirichletTermBox2`,
`contains_coarsen`, `contains_cpow_mul`) already exists unused. Landed: beta
is now read off the enclosure with `--beta plan` restoring the old source, and
the generator asserts the cell requirement at emission time so a site that
cannot pay it fails loudly instead of passing at the line. No Lean source
changed; `lake build` green from a cold toolchain. Nothing here bears on RH
(`docs/08`), and nothing here is a result until the battery or the funnel says
so.
### Hunt #43: the k=2 table with `zone_trade`'s inner prune disabled (`r_401bbf/`)

**Status: settled, outcome (a), on every cell rather than a sample.**
`k2_closure.zone_trade` cuts its branch-and-bound with a line that refuses to
descend into a multiplicity which does not immediately improve the running
value. That cut restricts the *adversary's* search, the unsound direction, so
wherever it bit the published margin would be optimistic. Hunt #41 measured its
delta as 0.0 on six binding cells and recorded the assumption as unchecked
elsewhere. This run re-solved the trade on all 6600 cells in both cap modes,
13200 evaluations, by exhaustive enumeration over every multiplicity vector
with `sum m <= 10`, with *both* of the search's cuts removed rather than only
the one the brief named. Max `|delta|` **4.4e-16**, zero cells above 1e-15, no
margin moved: worst cells stay at +0.0528969 (signed, tau 12.85) and +0.0032601
(unsigned, tau 6.33), nonpositive cells 0 in both columns. The residual takes
both signs, which is what float summation order looks like and is not what a
bite looks like. The run also supplies the reason, which covers more than the
table does: the pair charges are `Kpair/200` and `Kpair` is a square, so with
nonnegative charges the `m = 0` branch dominates every branch the prune drops,
and both cuts are admissible for *any* caps. The detector-power control is a
planted instance with one negative charge, where the published search
understates the trade by 18.6%. `k2_closure.NAMED_GAPS` G2 and
`K2-TWO-SPECIES.md` now record the discharge; the other assumption Hunt #41
named, the `Kpair` clamp, is still sound only by geometry. Cost 700 s for the
census, which is roughly what running the table once costs. Nothing here is
evidence for or against RH (`docs/08`), and no cap was widened and no zone
re-tuned.

### Hunt #42: the O9 numerator fields, and the seam that could not be instantiated (`r_6c7d6a/`)

**Status: settled, and one defect found on the way.** The run was sent to
supply the numerator-side `boxParts` fields of the O9 two-dimensional checker
in the vendored `Zeta23Ext` Lean package. It found the brief's premise stale:
`O9Parts.lean`'s header calls the numerator side "the remaining step", and
commit `6f81078` had superseded that sentence seven minutes after it was
written, landing `reNum_mem` and `imNumOverY_mem`. That commit's own message,
"every `boxParts` field is now sound", was the thing actually wrong.
`Retention.Parts` has **seven** fields and six had lemmas; the seventh,
`imNum`, is a hypothesis of `qreIv_mem`, so the `Qre` composition could not be
instantiated at a box at all. `Retention.imNum_mem` supplies it, with the
component left abstract in the idiom `O9Seam` and `O9Assemble` chose.
Discharging the rest of the hypotheses is what turned up the finding:
`O9Seam.r_comp_mem` writes `c*c + dOverY*dOverY` under the quotient, while
`rIv` divides by `denAbs2 = c*c + d*d` with `d = dOverY·y` and
`O9Real.im_div_over_y` agrees with `denAbs2`. So `r_comp_mem` and the
`rIv_mem` built on it are true, zero-sorry, and **vacuous at every box in the
table**, at `s = 1, y = 0` the hypothesis asks `denAbs2` to contain `5` where
it contains `1`, and the box family `[28/5, 60] × [0, 1/2]` never makes the two
agree. `r_comp_mem'` leaves the denominator's real abstract and fixes it with
the same proof term; `rIv_mem_box` and `qreIv_mem_box` then state both
compositions at a box with every field hypothesis discharged. Five new
declarations, zero sorrys, `lake build` green, `#print axioms` reporting only
`[propext, Classical.choice, Quot.sound]`. What is **not** closed, and is not
claimed: the two-mode arithmetic and the leaf-shape identities that relate the
computed expressions to `Re num` and `Im num / y`. Evidence in
`hunts/r_6c7d6a/RESULTS.md`. Nothing here is evidence for or against RH.

### Hunt #36: claim 'urms2-0.51' has no recorded white-box attack (`r_065f29/`)

**Status: settled as an attack, not as a verdict. The claim is not withdrawn;
the apparatus around it is weaker than the record reads.** The white-box half
of the standing review ran the eight-entry `harness.review.WHITEBOX_CHECKLIST`
against URMS2-051. The mathematics of the half-band crossing survives direct
attack: the exact block second moment `∫_U^{2U}|Σ c_n n^{-it}|²dt`, evaluated
as a closed-form double sum on the author's own coefficient family, saturates
to four significant figures (17.2964 → 17.3642) while `W/U` grows from 1.3 to
9.9, which is the `W`-independence the claim asserts, measured in the regime
the old proof's `W/U = o(1)` forbade. Three findings are about the record.
(i) `URMS2-051.md` §9's falsification control runs on a frozen level-two
family that violates the hypothesis of the step it supports: `A(y)/(y log y)`
climbs by a factor of 88 from its trough, and the upper-range sum grows like
`W^{0.825}` at fixed `x` instead of saturating, which the §9 ladder cannot see
because it moves `x` and `W` together and never varies `W` at fixed `x`. A
surrogate family that does obey `A(y) ≪ y log y` saturates, so §4's
mathematics is correct and only its control is powerless. (ii)
`URMS2-051-AUDIT.md` gate 6's "independent route" shares its entire numerical
substrate with the primary route: the JSON fixture reproduces
`corrected_coefficients(40)` exactly, and a one-part-in-10⁶ mutation of the
shared tail majorant moves both denominators by the identical
`4.426081703885579e-27`. (iii) The four recorded margins do not select
`51/100`: they stay feasible to `257/500` at the published parameters and
admit `α = 0.9` with the free ones open, and four of the six obligations §7
lists have no audit gate, inherited across the `γ > 1` regime change that is
this proof's novelty. Evidence in `hunts/r_065f29/RESULTS.md`; the outcome is
recorded as a white-box `AttackOutcome` in
`harness/departments/review_ledger.py`. Nothing here is evidence for or
against RH.
### Hunt #37: Hardy–Ramanujan, settled (`r_0339c1/`)

**Status: settled. The Hardy–Ramanujan theorem is kernel-checked with zero
`sorry`s: `ZetaLean.HardyRamanujan.hardy_ramanujan` proves the density form,
by Turán's proof, with every constant explicit.** This is the retry of Hunt
#12 with its named wall removed: Mertens' second theorem now exists on main
(`ZetaLean.Mertens.mertens_second_theorem`, band `76`, from hunt `r_3c1cbb`),
and the remaining half of Turán's argument was, as Hunt #12 priced it,
bookkeeping.

Hunt #12's kernel-checked halves are reused as written (copied with
attribution; its branch is unmerged): the statement, the double-counting
identity `∑_{n ≤ N} ω(n) = ∑_{p ≤ N} ⌊N/p⌋`, and the whole Chebyshev step.
New in this run: the second moment expands `ω(n)²` over ordered pairs of
primes, `Nat.Ioc_filter_dvd_card_eq_div` at `p*q` counts the off-diagonal,
and `∑_{n ≤ N} ω(n)² ≤ N·S² + N·S` with `S = ∑_{p ≤ N} 1/p` follows. With
the first-moment bracket `N·S − N ≤ ∑ ω ≤ N·S` and `|S − log log N| ≤ 76`,
the variance obeys `∑_{n ≤ N} (ω(n) − log log N)² ≤ 5855 · N · log log N`
whenever `log log N ≥ 1` (`sum_sq_dev_le`; the constant is `76² + 76 + 3`,
coarse because the Mertens band is, and tightens automatically if that
does). `lake build` printed `✔ [8699/8699] Built
ZetaLean.HardyRamanujantheorem`; the seven public theorems each depend only
on `propext`, `Classical.choice`, `Quot.sound`. The module compiled on the
first attempt, which is what reading Hunt #12's route and trap list before
writing anything buys. Nothing here bears on ζ or RH (`docs/08`); external
review remains pending, as it does for every claim this laboratory
publishes.

**Numbering note.** This run was assigned #36 by its brief and found #36 already taken by `r_065f29` when the two branches met at the merge. Per the brief's own rule, "if it is occupied say so rather than renumbering silently", it is recorded here as #37. Two coordinators assigned the same number independently; the case-number reservation is not shared across sessions.

### Hunt #12: Hardy–Ramanujan, and the lemma Mathlib does not have (`r_0339c1/`)

**Status: not settled, and the wall is named. The Hardy–Ramanujan theorem is
not proved. Turán's Chebyshev half is kernel-checked as an implication with
zero `sorry`s, the unconditional first step of the other half is kernel-checked
outright, and the remaining half stops at a specific library absence: Mathlib
v4.33.0-rc2 has no Mertens second theorem.**

The target was Wikidata Q5656674, which Mathlib records as wanted and unbuilt.
`lean/ZetaLean/HardyRamanujantheorem.lean` states the density form as a `Prop`,
proves `sum_omega_eq_sum_div` (`∑_{n ≤ N} ω n = ∑_{p ≤ N} ⌊N/p⌋`, by double
counting, unconditional) and proves `hardyRamanujan_of_turanVariance`, which is
the whole Chebyshev step. `TuranVariance` is a hypothesis in that file and not
a theorem, so the implication is a reduction and the file's own docstring says
it does not contain the theorem. `lake build` printed
`✔ [8697/8697] Built ZetaLean.HardyRamanujantheorem`; all four results depend
only on `propext`, `Classical.choice`, `Quot.sound`.

The obstruction is `∑_{p ≤ x} 1/p = log log x + O(1)`. Mathlib has the
*divergence* of `∑ 1/p` (`not_summable_one_div_on_primes`) and nothing with a
rate, and `grep -rln "Mertens"` over the pinned checkout hits one unrelated
file. Two incidental traps for the next attempt: `NumberTheory/Chebyshev.lean`
is about Chebyshev polynomials, not prime bounds, and `NumberTheory/AbelSummation.lean`
supplies the machinery Mertens is normally derived through while the derivation
itself is absent. Nothing here bears on ζ or RH.
### Hunt #62: three cited properties of ζ distinguish nothing (`r_f7cd45/`)

> **Renumbered 2026-08-20.** Opened as #35, which `r_3c1cbb/` had taken
> the previous day. `hunts/r_f7cd45/` is the stable reference.

**Status: settled for the five properties issue #21 left unpublished; the
sixth was already settled in this tree and what this run adds is the price
tag.** Publishes the artifact issue #21 recorded as queued. Under `docs/09`
gate #3, run against the Davenport–Heilbronn function and both discriminant
−23 Epstein zetas: the functional equation, a real Hardy-style Z, and having
zeros on the critical line are each satisfied by **3 of 3** rivals and are
**VACUOUS**; multiplicative and completely multiplicative coefficients are
satisfied by **0 of 3** and **DISTINGUISH**. Issue #21's table reproduced cell
for cell, from a probe that runs end to end. Only the prime structure kills
the rivals.

Issue #21 also lists a sixth property, "no zeros in a box strictly off the
critical line", as unfinished at a 50-minute timeout, **stale**, since hunts
#13, #14 and #15 settled it (VACUOUS, and ill-posed: the box is a free
parameter of the sentence). Reproduced independently here on two boxes
preregistered at `53c8cd1` before any winding number: σ ∈ [0.6, 0.9] gives
VACUOUS at t ∈ [80, 81], forced by Davenport–Heilbronn alone, and UNDECIDED at
t ∈ [85, 86], where the D–H cell returns exactly **1**, recovering the
off-line zero the repository pins at 0.8085171824… + 85.6993484853…i.

What is new is the precision floor, measured rather than argued: at
0.75 + 85.5i the Epstein completed function is **2.0e−58** and **5.0e−58**,
converging only at **dps 60**, while at the `dps = 20` that `battery` actually
uses it returns ≈ 2e−33, noise larger than signal by 25 orders of magnitude.
The Epstein box cells are therefore reported *inadmissible on precision*, not
merely slow, because `count_zeros_box`'s integrality check does not catch it:
noise winds to an integer too. **Defect reported, not patched** (`zeta/` is
outside scope): both rival interfaces hardcode `dps=min(dps, 20)` into
`count_zeros_box` (`zeta/epstein.py:1091`, `:1141`), so no caller can reach
the floor and the packaged property-6 route is unusable above t ≈ 30. That,
not difficulty, is why three hunts in a row have declared the Epstein arm out
of budget. Grade: measured, with ζ as a positive control on all five
properties. Nothing here is evidence for or against RH (`docs/08`); gate #3 is
eliminative, never probative.
### Hunt #35: Mertens's second theorem, the mapped block built (`r_3c1cbb/`)

**Status: settled.** Continuation of Hunt #30, building exactly the block
its route map named and nothing else. What landed:
`lean/ZetaLean/MertensSecond.lean` compiles against pinned Mathlib
v4.33.0-rc2 with zero sorrys and carries Mertens's **second** theorem in the
`log log x + O(1)` form with an explicit constant:
`|Σ_{p≤N} 1/p − log log N| ≤ 76` for every natural `N`
(`mertens_second_theorem`; the content is at `N ≥ 2`, below that the sum is
empty and Mathlib's `log 0 = 0` makes the bound trivial). The argument is
the classical partial summation against
`A(n) = Σ_{p≤n} log p/p = log n + O(1)`, the `O(1)` band being Hunt #30's
`mertens_first_theorem` consumed as-is, with the termwise bracket
`(v−u)/v ≤ log v − log u ≤ (v−u)/u` telescoping to `log log N` and the
overshoot closed by `Σ 1/n² ≤ 1`. One deviation from the route map, worth
keeping: the discrete Abel identity went in by direct `Nat.le_induction`
from `N = 2` (`sum_inv_primes_eq`), not by reindexing Mathlib's
range-indexed summation by parts, which removed the labor the map had
priced at 150 to 250 lines of reindexing. The constant `76` is deliberately
coarse (a sieve to `10^6` puts the true deviation near `0.26`); its slack
decomposes into named local steps, nearly all inherited from the first
theorem's `log 4 + 16` band. The sharper `log log x + M + o(1)` form and
the third theorem need the Mertens constant and are recorded as out of
scope. Details in `r_3c1cbb/RESULTS-second.md`. Nothing here is evidence
for or against RH.

### Hunt #30: Mertens's theorems, settled through the first theorem (`r_3c1cbb/`)

**Status: settled in part, and the part is stated exactly.** The target
(Wikidata Q1196729, recorded by Mathlib's wanted-theorems tracking as wanted
and unbuilt) was any of Mertens's three theorems, kernel-checked. What landed:
`lean/ZetaLean/Mertensstheorems.lean` compiles against pinned Mathlib
v4.33.0-rc2 with zero sorrys and carries Mertens's **first** theorem in both
classical forms with explicit constants: the von Mangoldt form
`|Σ_{n≤N} Λ(n)/n − log N| ≤ log 4 + 4` and the prime form
`|Σ_{p≤N} (log p)/p − log N| ≤ log 4 + 16`, each for `N ≥ 1`. The argument is
fully elementary: the summatory identity from
`ArithmeticFunction.vonMangoldt_sum` by counting multiples, Mathlib's
Chebyshev bound `psi_le_const_mul_self`, an induction replacing Stirling with
`log(1+1/M) ≤ 1/M`, and a telescoping `Σ n^(-3/2)` bound for the prime-power
correction. The **second** theorem (`Σ 1/p = log log x + O(1)`) was
route-mapped but not built: the wall is the discrete partial-summation step,
recorded with the relevant Mathlib declaration names in `RESULTS.md`. The
**third** is out of reach at this budget (needs the Mertens constant and γ).
Constants are far from optimal by design; sharpening them is a loose thread.
Nothing here is evidence for or against RH.

### Hunt #34: claim 'urms2-0.51' has no recorded blind attack (`r_fb9c81/`)

**Status: settled. The stated analytical assumption holds structurally, and the mean-value evaluation is valid.** The blind attack searched for a numerical consequence of replacing the exact polynomial frequency spacing with its generic mean bound, testing whether length $W \gg U$ could collapse the off-diagonal bounds while keeping the formal appearance of the claim. A numerical probe on a scaled configuration ($x = 1000, \alpha = 0.51, \delta = 0.75$) proved that the Montgomery-Vaughan mean-value off-diagonal cost remains identically bounded by $O(x \log x)$. The true frequency separation limits the spacing error such that the main diagonal term $U \log x$ unconditionally dominates. The $0.51$ parameter therefore does not survive merely on an invalid archimedean assumption; its required analytical decay is physical and rigorous. Full evidence and reasoning are recorded in `hunts/r_fb9c81/RESULTS.md`. Nothing here is evidence for or against RH.

### Hunt #27: AGY conversation context and handback 8 (`r_test_agy_8/`)

**Status: settled. A framework probe successfully validated the operational envelope.** The AGY process context correctly ran a script that imported the `.venv`-installed `zeta` package, computed values using `zeta.explicit.li(x)` with `mpmath` at specified precision, and wrote a complete evaluation to the local directory without incident. Nothing here bears on RH; it is a test of the test mechanism.

### Hunt #18: the O9 leaf table, repriced (`r_2926e4/`)

**Status: settled. `o9_leaf.py`'s 1-D O9 table is 476 cells at max depth 22 on
the leaves the kernel actually computes, not the 344 at depth 20 it records,
and 85 of those 344 cells (24.7%) fail outright once the leaves are the
kernel's.** The module's LEAF CAVEAT argues that a cell passing with margin is
safely predicted; the hunt measures that the margin is the wrong quantity, not
a mis-calibrated one. A cell with a recorded Arb margin of `9.21e16` ulp,
`2.5e7` times the `3.63e9` minimum the module cites as its safety evidence,
still fails, so no threshold on that margin separates the safe predictions from
the unsafe ones. The mechanism is confined to the two leaves whose argument is
the cell rather than a constant: `sinCosIv` reduces mod `2π` and applies `dbl`
twice, `dbl` squares an interval, and the width grows with the cell (`cosX2`
mean `8.15×` Arb's width, worst `43.5×`). The four constant leaves and the two
hyperbolic ones go the *other* way, `3×` to `9×` narrower than Arb-plus-4-ulp-pad,
so "the Arb model is uniformly optimistic" is the wrong generalisation.
**Control:** bucketing the 85 failures into the 40-cell chunks `emit_lean`
writes reproduces the 2026-08-13 Lean build's verdict nine chunks for nine,
including both chunks that passed (offsets 200 and 280 contain zero failures);
that comparison is against a real `decide +kernel` run and tuned nothing.
The table still closes after the repair, which was not guaranteed: the
complement test lives on the ~`2e-05` of slack in §4's outward-rounded `I_k`,
and the wider leaves do not eat it. **Disposition:** no ledger entry; the
repair belongs to `hunts/frontier_math/o9_leaf.py`, which is outside this
hunt's scope and still exports `N_CELLS_KERNEL = 344`. Corrects issue #23,
which says the 344-cell table was never put to the kernel: it was, on
2026-08-13, and refuted on 7 of 9 chunks. No Lean was built here, so 476 is
measured, one route, and the route is a model of the kernel. Nothing here bears
on RH.

**Run 2 (7b33f41e, 2026-08-19):** a reproduction under the same brief. After
e585b52cb (2026-08-15) switched `o9_leaf.leaves()` and `build()` to the
kernel-leaf mirror, run 1's probe silently lost its Arb baseline (it printed
476 baseline cells, width ratios of 1.0 and 0 failures). Run 2 repaired it on
`o9_leaf.leaves_arb`, and the repaired probe writes `results-7b33f41e.json`,
leaving run 1's `results.json` and `HANDBACK.json` as they were. Every number
that decides anything reproduced (344 cells at depth 20, minimum margin
3632804926 ulp, all seven width ratios, 85 of 344 failing, 9/9 chunks, 476 cells
at depth 22). The low digits of the failing-cell Arb margins are
environment-dependent, and the cause is not identified: on a 2026-10-21 rerun
machine (Linux x86_64) six of them differ from run 2's record by at most 56
units on the `2^64` scale, with no verdict change, identically under
python-flint 0.5.0, 0.6.0, 0.7.1, 0.8.0 and 0.9.0 and under run 1's and run 2's
own code, and run 2's platform is not recorded. The "0.6 s end to end" runtime
in `RESULTS.md` is out of date. Status stays settled; the grade stays measured,
rung 1.

### Hunt #14: gate-5 property 6 is vacuous (`gate5_p6_b/`)

**Status: probe, complete. VACUOUS, with the parameters committed before the
first count and the commit order left in the history as the evidence.** The
open property of `zeta.epstein.battery` was *"in a box strictly off the
critical line, the completed function has no zeros"*. Three boxes and a
precision rule were fixed in `MISSION.md` at `623e800`; the probe ran
afterwards. In box A (`σ ∈ [0.70, 0.92]`, `t ∈ [1.5, 11.5]`) and box C
(`σ ∈ [1.05, 1.60]`, same heights) all four functions return a zero count of
**0**, so all three rivals satisfy the property and it distinguishes nothing.

The box-dependence the property carries by construction was measured rather
than argued: Davenport–Heilbronn **satisfies** property 6 on boxes A and C and
**fails** it on box B (`σ ∈ [0.70, 0.92]`, `t ∈ [85.2, 86.2]`), which was built
around the off-line zero pinned in `zeta/epstein.py`, and the box-B cell
returns exactly **1**, recovering that zero where Spira (*Math. Comp.* 1994)
puts it, the run's one positive control. So property 6 is a box-indexed family
rather than one claim, and the version that quantifies over all boxes is RH for
the function, which is circular as a proof step. Box B's two Epstein cells are
undecided on cost (about 21 minutes of mpmath each at `dps = 79`), reported
undecided rather than skipped.

One defect found on the way, reported and not patched (`zeta/` is outside the
hunt's scope): both rival interfaces in `battery` pass `dps=min(dps, 20)` into
`count_zeros_box`, and at `t = 85.7` the completed Epstein function at `dps
= 20` returns `1.2e-34` against a true `1.617e-58`. A winding count over that
noise still lands on an integer, so the routine's own integrality check does
not catch it.

### Hunt #41: the interval pass over the k=2 tau-table (`r_a97060/`)

**Question.** `hunts/frontier_math/k2_closure.py` closes the `k=2`
equal-depth case of blocker 2 over 6600 tau-cells, at *measured* grade: every
supremum in it is a double-precision scan padded by a flat 5%.
`K2-TWO-SPECIES.md` §6 names the obligation that keeps it there. Does the same
table close when every sup becomes an enclosure and every credit a lower
bound?

**Result: yes, in all three cap modes, over the same cells.** 0 of 6600
nonpositive; worst margin +0.0677 (signed-field caps), +0.0146 (unsigned),
+0.0016 (unsigned with the measured pass's own 1.05 pad kept on top of the
enclosure, which is the like-for-like row). No cap widened, no tau-cell
split. The arithmetic is Arb complex balls at 96 bits, not rectangles, on the
brief's instruction: rung 3 had measured rectangles losing 13.7× of width to
balls on exactly this shape of quantity, a squared rotating complex value.
`mpmath.iv` rectangles contain every ball checked and run 1.8–3.5× wider.

**What the enclosure actually cost.** A factor of **1.0000 to 1.0004** on the
near field, the dominant term. The 1.05 pad it replaces was standing in for an
error two to three orders of magnitude smaller than itself.

**What the hardening found that the scan could not.** The centre-centre row is
`sup_{0<y≤1/2} Dam(2y,τ)/y²`: a supremum over an *open* interval with the
variable in the denominator, which the measured pass took over an 18-point
grid starting at `y = 0.05`. A first full enclosure pass reported one
nonpositive cell at `τ ∈ [6.62, 6.64]`, a root of `G(τ)`. It was not a gap: it
was the `1/y²` corner, where a branch-and-bound stalls because the enclosure
width there is set by the τ-cell rather than the y-box. The fix is a fact
about the problem rather than more grid, `ghat` is **even** with real Taylor
coefficients, so `Re ghat'(iτ) = 0` and `D` has **no depth-linear term**,
giving `4·max(0,D)/u² ≤ 4·max(0, sup|D''|/2 − G²/b²)` for every `u ≤ b`. That
is why the ratio is bounded as `y → 0` at all, which the y-grid assumed
without stating, and no scan can check it.

**Two unstated assumptions recorded** in `k2_closure.py`, neither changing a
published number: the pair-charge clamp `Kpair(min(dmax,6))` is a lower bound
only if `Kpair` is monotone out to `dmax`, which holds only because the widest
near component in the table is 1.9894; and the inner prune of `zone_trade`
restricts the *adversary's* search, so it is a heuristic on the unsound side
(measured delta 0.0 on six binding cells).

**Scope, stated rather than implied.** The *table* is enclosure-carrying. The
*k=2 equal-depth claim* is a composite and still takes the grade of its
weakest step, which is now the v-convexity transfer off `v = 1/4`, argued,
not enclosed. `k ≥ 3` and the unequal-depth quantifier are untouched, and
nothing here is evidence about RH.

**Disposition:** instrument and result retained; `K2-TWO-SPECIES.md` §6 and
`k2_closure.NAMED_GAPS` G2 amended in the same commit. Budget overrun
recorded in the handback: 75 minutes allowed, ~100 taken, all of it the
diagnosis above.

### Hunt #15: is gate-5 property 6 vacuous or distinguishing? (`gate5_p6_c/`)

**Status: settled, and the answer is that the question as written has no
truth value.** Property 6 of the `docs/09` gate #3 battery reads "in a box
strictly off the critical line, the completed function has no zeros", and
the box is a free parameter of that sentence. Holding the σ-band fixed at
[0.7, 0.9] and changing only the height window flips the verdict:
Davenport–Heilbronn has one zero in t ∈ [85.5, 85.9] and none in
t ∈ [10, 14] or [40, 44], while ξ has none in any of them. Same property,
same band, same code, opposite verdicts. The mechanism is that an
RH-violating function does not violate RH everywhere, so a local zero-free
statement cannot carry a global distinction. Every repair that gives
property 6 a truth value and still distinguishes turns out to be either RH
itself or the Euler product, which is property 5, so property 6 does not
look like an independent sixth property. Parameters were preregistered and
committed before any winding number was computed (`MISSION.md` at `c29c876`,
`results.json` after). **Not settled:** the Epstein arm on the two high
boxes, declared out of budget, and unable to change the conclusion, the
VACUOUS boxes are already forced by Davenport–Heilbronn, since gate #3 asks
the structure be ungrantable to *every* rival. **Two defects found in
`zeta/epstein.py` and reported, not fixed** (out of the hunt's scope):
`epstein_completed` silently loses ≈ 0.6822·t digits to cancellation, so at
the documented dps = 20 its phase is noise above t ≈ 30; and
`count_zeros_box` has no evaluation ceiling, so a noisy phase makes it
recurse to depth 45 per segment and never return rather than raise. Nothing
here bears on RH (`docs/08`); it is about what separates ζ from
RH-violating look-alikes.

### Hunt #9: how much power a guard has (`r_414eed/`)

**Status: probe, complete. `scripts/make_context.py --check` caught 17/17
in-scope mutants including its declared smallest one, and it caught that one
by accounting rather than comprehension, which is what exposed the single edit
shape that slips past it.** `CONTEXT.md` prints a per-module line count, so any
length-changing edit marks it stale (a lone blank line fires the guard) while a
private helper renamed public *in place*, in a module that declares `__all__`,
regenerates byte-identically and passes. Four unscanned regions mapped
(`meta/`, `compiler/`, `docs/doors/`, non-`test_*.py` test files). Controls: the
unmutated sandbox reproduces `CONTEXT.md` byte for byte, and the undo is
re-checked after every one of 24 mutants; the repository itself is never
written to. **Disposition:** guard ledger entry amended from `fired=None` to
`fired=True` with its scope and six known misses
(`harness/departments/guard_ledger.py`, run `fd5fd902`). Nothing here bears on
ζ or RH, it measures a repository hygiene script.

### Hunt #13: the box that was chosen to lose (`gate5_p6_a/`)

**Status: settled, and the property it settles is one the battery should stop
carrying.** Gate #3 battery property 6, "in a box strictly off the critical
line, the completed function has no zeros", is **VACUOUS**. The box was fixed
and committed one commit *before* `probe.py` existed, and it was chosen
adversarially: `sigma in [0.70, 0.92]`, `t in [85.55, 85.85]` is the one region
in this repository where a rival is known in advance to have an off-line zero
(the pinned Davenport-Heilbronn zero at `0.808517... + 85.699348...i`), and so
the box most favourable to a DISTINGUISHES verdict. It lost anyway: the Epstein
zeta of the non-principal discriminant -23 form has **0** zeros there and
satisfies the property exactly as `xi` does. **Disposition:** the larger finding
is that property 6 is not well posed as a gate input, because a second box at
`t in [70.10, 70.40]` gives the Davenport-Heilbronn function the *opposite*
answer. Property 6 is a property of a (function, box) pair; quantified over all
boxes its zeta column is RH restricted to a region and so unknowable, and
instantiated on any affordable box it is vacuous. A box-free replacement is
proposed in `RESULTS.md` (`no zeros in Re s > 1`), with the caveat that it
distinguishes only by restating the Euler product. Measured, float grade, one
resolution: the planned reconfirmation at halved step did not finish inside its
cap, and three of eight cells are recorded gaps. Nothing here bears on RH.

### Hunt #11: what the hunt lexical guard actually reads (`r_03a798/`)

**Status: settled. The guard matches one literal substring, case-insensitively,
and everything outside it passes.**

The attention item that opened this hunt asserted that
`test_no_hunt_claims_the_reserved_word` misses synonyms, and that *verified*,
*confirmed*, *definitively* and *proves* are caught "by other checks". The hunt
measures both halves and reports the first as true and the second as false:
those other checks do not exist. It copies the guard **unmodified** into a
sandbox repo root and runs it against one planted specimen at a time, so each
verdict is the guard's own exit status rather than a re-implementation, with an
empty-specimen control green so a failure is attributable to the specimen.

Reproduce: `python hunts/r_03a798/probe.py` (~40 s, no mpmath, no network).
Data: `results.json`.

### Hunt #10: what the doors guard actually catches (`r_cb5ffe/`)

**Status: probe, complete. The guard's power is measured at 5/10 against a
ten-mutant battery, and its five misses share one cause.**

`harness/departments/guard_ledger.py` carried `tests/test_doors.py` with
`fired: None` and `scope: undetermined until demonstrated`, existence
recorded, power never measured. This hunt builds the mutant the record names
(a door command that exits non-zero) plus nine neighbours, applies each to a
throwaway `git worktree`, and records which tier of the guard notices.

Measured: four mutants caught on the fast tier, one only on the slow tier,
five escaped. The escapes are structural rather than scattered, the guard's
whole notion of "a door's command" is the regex `scripts/[\w.]+\.py` applied
to `docs/doors/README.md`, so a command quoted *inside* a door page is
unguarded, and a README row naming no script (the certify door's Lean build,
the adopt door's pytest invocation) is outside its field of view. A tree
carrying all five escapes at once passes both tiers green.

The hunt reports a proposed ledger amendment and does not apply it:
`harness/` is demoted (`harness/VERDICT.md`) and a hunt may not promote its
own claim.

### Hunt #8: where the fog enters (`effective_constants/`)

**Status: opened 2026-08-13, nothing measured yet.** Tests whether the
transplant chain's ineffectivity is extractable bookkeeping or an essential
obstruction.

The chain's headline caveat is that the improved constant is a liminf
statement with crossover `T₀ ≈ 10^(1.6773e6)`, unreachable at any computable
height, and that this is *inherited* from the source paper. "Inherited"
currently functions as an explanation and is not one, so the hunt asks where
exactly the fog enters and whether it has to.

Two facts already in the tree say it may not. `PROOF-LEDGER.md` (blocker 3,
residual (i)) records that **four existential `EvBound` constants would make
the chain effective and nothing else in the budget would**, the ineffectivity
is localised, and the dominant error term is already derived from parts
(`35.519106`, matching measurement to four digits). And upstream those facts
are *assumptions*: fields of a `Facts` structure carrying the paper's own
references, whose shape is `∃ C > 0, ∃ T₀, ∀ T ≥ T₀, |f| ≤ C·g` and whose own
docstring says "explicit inequality with named constants, no filter-o(1) until
the final liminf wrapper". The constants were not lost to an obstruction; they
were not carried across an interface, because the source's goal was a limit
statement.

Either verdict is worth having. Extractable means an effective form of the
underlying bound is arithmetic rather than new mathematics, and that would
stand independently of the `+1.0e-5` improvement it was reached through, since
the improvement is unreachable at any computable height while an effective
constant is usable above its threshold. Essential means the obstruction finally
has a name and a location.

Opened after the operator asked why the fog has to be inherited at all. It is
the first hunt to attack the chain *upstream* of where the transplant begins.

### Hunt #7: the quasicrystal that is a theorem (`golden_control/`)

**Status: probe, complete. The quasicrystal lane gains its ground-truth
universe, and the exact stage caught the operator mis-remembering a
classical theorem.**

The quasicrystal gate's instrument had never been run against an aperiodic
point set whose atomic diffraction is *proved*. This hunt points a tapered
transform, calibrated on ℤ, where the answer is Poisson summation
(6.4e-14), at a golden cut-and-project set, with the Fourier module and
intensity law derived in code from the embedding lattice rather than quoted.
Measured: peak positions to 8.7e-9, amplitudes against the window-transform
law to 2.5e-8, off-module silence 9717× (ζ's arithmetic gate measured 26.8×
with 1000 zeros, the theorem universe shows what the instrument does with
no truncation), Debye–Waller lesion slopes within 1%, Poisson null clean,
precision response monotone to 1e-10. The golden thread pinned exactly:
the DH rival's quartic character squares to χ₅, the ℚ(√5) character. **One
registered claim was false and the computation caught it at first contact**
(π(p) | p − χ₅(p) fails at p = 3; the split/inert-asymmetric statement
π(p) | p−1 vs 2(p+1) holds for all p < 500), recorded with its
counterexample, as the derive-never-remember rule intends.

**Disposition:** instrument validation, not a result about ζ; no ledger
entry. Nothing here is evidence for or against RH.

### Hunt #6: the Jensen clock (`jensen_clock/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline
is a measured dictionary between the two real-rootedness lanes, plus a null
control that explains it.**

Connected `zeta/li.py`'s Jensen/hyperbolicity lane to hunt #4's de
Bruijn–Newman flow measurements on Davenport–Heilbronn. The exact identity
J^{d,0}(x/d) = Σ γ(j)/j!·Π_{i<j}(1−i/d)·x^j makes the degree-d binomial
damping a Gaussian coefficient multiplier, de Bruijn's smoothing applied by
the degree itself, matching the flow multiplier e^{tu²} at a pair image x₀
with **t_eff = |x₀|/(8d)**. Measured, with raw numbers in
`jensen_clock/results.json`:

- The DH height-85.7 pair's image in J^{d,0} tracks the PDE flow trajectory
  under that dictionary at 7.8e-8 → 4e-4 relative over half the flow; the
  landing degree d\* = 20785.13 reads t\*_J = 0.0441690 against hunt #4's
  t\* = 0.0441263, **0.097%**, while the isolated-pair value is 7.2% away.
  Pair 2 (γ ≈ 114): d\* = 146365, clock agreement **0.011%**. Flowing before
  damping, the two clocks add: t_land(d) + |x₀|/(8d) = t\* to 0.03–0.06%.
- **The corollary**: a blind hyperbolicity scan at d ≤ 32, n ≤ 250 sees
  nothing, and the dictionary says that is structural, degree d ≲ 2·10⁴ has
  already flowed this violation past its landing before the polynomial is
  inspected. Textbook-degree Jensen scans are the wrong side of the landing,
  not weak detectors.
- **Null control, the explanation**: a pair planted into ζ's γ-table at
  exactly x₀ lands at 0.0436212; the arithmetic-free N-body dynamics run on
  the plant's actual configuration lands at 0.0435805, 0.094%, while DH's
  clock sits 1.1% away and the isolated formula 8.3% away. The clock reads
  zero configuration, not arithmetic (hunt #4's null, now on the coefficient
  side). The mission's own quantitative guess for this control was wrong
  (it forgot the ordinate doubling in the x-plane) and is recorded as a
  failed prediction in `jensen_clock/RESULTS.md`.
- Controls: ζ specificity (winding 1.3e-63, Newton relative Im 1.2e-200);
  instrument checked against `zeta.li`'s twice-derived γ-table to 1.3e-51
  and hunt #4's polished pair to 40 digits; d\* precision-flat to the printed
  digits across dps 130 → 160 and two quadrature geometries; truncation
  margin 36 orders at the deciding contour.

**Phase 2 (the shift axis)**: the shifted Jensen polynomial is the damped
n-th derivative, and one differentiation is worth **3.69×** the violation's
entire flow budget (c₀ = 0.1628 vs t\* = 0.0441, measured by re-lifting the
landed pair with backward flow; per-step clock not constant, c₁ = 0.1826).
All six boundary cells of the (d, n) detection map agree with the additive
budget rule |x₀|/(8d) + g(n) < t\*, and the map degenerates: the n = 0 row
flips exactly at phase 1's d\*, and **every n ≥ 1 cell is blind at every
degree**, so by the budget rule all nine known DH pairs are invisible to
every shifted Jensen polynomial with n ≥ 1. The GORZ direction (fixed d,
growing n), where hyperbolicity is a theorem for ζ, is for *detection* the
maximally blind direction. Two registered numeric guesses failed and are
recorded as such (the c₀ bracket; phase 1's planted-pair neighborhood); the
strong three-clock additivity test was not run and is marked untested.
Prior-art hooks recorded: Csordas–Norfolk–Varga's 1988 Λ ≥ −50 came from
non-hyperbolic Jensen polynomials of the flowed function, and its successors
dropped Jensen polynomials as needing impractical degrees, the dictionary
is a quantitative law of that documented inefficiency.

**Phase 3 (falsifier + trichotomy)**: the strong additivity test, re-measure
t_land(n=1) at d = 10⁶, predicted from the d = 10⁸ value and the degree
budget alone, passed at defect 1.46e-5 against a registered ±1e-4 bar, so
degree, shift and flow measurably spend one budget. The third
coefficient-side detector, Li's criterion, has the opposite geometry: a
planted quadruple at ρ = 0.8 + 2.5i turns the Bombieri–Lagarias sum negative
first at n = 95 (registered interval [80, 160]; one trough n = 95–98, period
16, positive again at 99), and the same amplification formula puts DH pair
1's Li onset at n ≈ 3.3·10⁵ (order-of-magnitude, ζ-shaped background hedge).
Trichotomy recorded in `jensen_clock/RESULTS.md`: two erasing clocks (degree,
shift, blind sets cofinal) against one accumulating discriminator (Li,
blind set an initial segment); none of the three blindnesses is a matter of
effort. One auxiliary statistic (the coded envelope-crossing indicator) was
mis-specified and is recorded as unusable.

**Disposition:** portrait and closure, not conjecture, no ledger entry.
Nothing here is evidence for or against RH. Spine candidates in
`jensen_clock/NOTES.md`.

### Higher xi derivatives (`higher_xi/`)

**Status: 2008 discrepancy resolved as a chapter-11 calculation error, two
measured oracles retained, no higher-derivative zeta constant claimed.** Ji
Bian's Figure 10.1 coefficients, substituted exactly into equation (11.5), give
`-202/36855` for `kappa=2` and `-10284002/1216215` for `kappa=3`, not the
reported `0.9544` and `0.9774`. The same substitution at `kappa=1` gives
`348002/405405 = 0.8584057917...`, matching the known control, so this is not
a global normalization mismatch. Page 93 also changes three signs from Figure
10.1; neither row produces the headline. Reconciling it would require omitted
tails canceling `95.46%` and `99.76%` of the shown weighted sums, contradicting
the page's negligible-tail premise. A completed-CUE experiment and an
independent Dirichlet-coefficient recurrence both put the tested
second-derivative form factor well below the displayed eleven-term
polynomial. The finite-cutoff window ladder decreases from `0.9342893` at
`ell=8` to `0.9311081` at `ell=14`; it is a discovery sequence, not a limit or
a theorem. Resolution in `higher_xi/RESOLUTION-2008-DISCREPANCY.md`; full
experiment in `higher_xi/RESULTS-higher-xi.md`.

### Frontier math (`frontier_math/`)

**Status: clean kill of the candidate constant, one measured collapse, one
quantified wall.** Continues `wide_search` THREAD 1 against the 10 August
2026 paper. Measured: the pair-measure LP (positivity + bandwidth-one data +
multiplicity types) reduces exactly to 2 − sup D and descends toward the
paper's 0.6725007, the measure level adds nothing, answering THREAD 1's
residual question; the ceiling gap is configuration realizability. The
constructive half is withdrawn: the scan used `u u*`, while upstream uses
`u u^T`; the exact witness `1`, `i`, `-i` gives `tr(P₁Q′)=-2`, and the
proposed additive inequality can demand `9 ≥ 13`. The former candidate
**N₀ˢ ≥ 0.672529·N** therefore has no zeta implication. The ordered-gap LP
remains a measured configuration problem, and the bin-width ladder still
records its earlier midpoint-assignment defect. Also recorded: the sieve route to λ > 1
fails at scale T^{λ−1} (only HL itself closes it), and the CGdL transplant
reduces to one named obstruction (inertia counting for non-Gram kernels),
with BGSTB 2023's unconditional F ≥ 0 pinned as known. Closure record in
`frontier_math/CLEAN-KILL-REPORT.md`.

### The frontier map (`frontier_map/`)

**Status: a map, not a result, the `wide_search` findings and the source
paper's own limits assembled into one instrument, one JSON, one figure.**

Builds directly on `wide_search` and the 10 August 2026 pair-correlation
paper. `frontier.py` computes the whole λ-landscape H(λ) for the two kernels
the method accepts unconditionally (ζ and ξ′), pins the ceilings, prior-art
bars and the paper's structural wall as cited data, and renders
`figures/frontier_map.png`. Measured: onsets λ₀ = 0.550194 (ζ) and 0.513320
(ξ′) just above the paper's "nothing at λ ≤ ½" line; both curves monotone and
still climbing at the λ = 1 wall. The numeric ζ curve matches the paper's
closed form (eq. 7.4) to 9.5e-15 pointwise, and a planted mis-constant lesion
moves that comparison by 1.5e-2, so agreement is informative. The map's open
lanes are recorded as intervals: (0.6725007, 0.68185) for ζ within
bandwidth-one data, ξ′-vs-Wu closed negatively at 9.285e-4, κ ≥ 2 blocked on
Bian's missing tail bound, λ > 1 walled behind Hardy–Littlewood-strength
input. Results in `frontier_map/RESULTS-frontier-map.md`; controls in
`frontier_map/probe.py`.

### The wide search (`wide_search/`)

**Status: one measured constant, two negative results and one reproduction, all
about somebody else's method, not a result about zeta.**

An operator asked for one externally checkable mathematical contribution
adjacent to zeta: generate in volume, kill aggressively, search prior art,
reproduce independently, call nothing new without a novelty gate. Mission and
scope in `wide_search/MISSION.md`.

The breadth-first phase was abandoned as the wrong altitude. The target became
the paper of 10 August 2026 that raised the unconditional proportion of zeros
of ζ on the critical line to 0.6725, and specifically the one place it leaves a
variational problem unsolved: its Remark 7.3 on the zeros of ξ′, where it
reports a flat window and an unexplained quartic and records that neither
reaches Wu's unconditional 0.86957.

- **The sharp constant for that method is
  `0.86864150052976706411...`** (simple and on the critical line;
  `0.93432075...` distinct), attained at `lambda = 1`. Full account, with the
  functional and its provenance, in `wide_search/RESULTS-xiprime.md`.
- **It does not reach Wu's 0.86957**, falling short by `9.285e-4`. No admissible
  window closes the gap, so the comparison the paper leaves open is settled
  negatively. The paper's own quartic was already within `1.5e-6` of sharp.
- Checks: the instrument reproduces the paper's Theorem D to 10 digits before
  being pointed at anything unknown; the functional reproduces all four
  published constants of Remark 7.3 to every printed digit; three independent
  derivations of it agree and five independent computations of the optimum
  agree to 14 digits; the coefficient formula is checked exactly by Dirichlet
  convolution; and Bian's 2008 thesis reproduces the same `k = 1` coefficients
  exactly, from sixteen years earlier.
- **Higher derivatives are blocked, and `RESULTS-higher-derivatives.md` records
  why**: `F_k` for `k >= 2` already exists in an unpublished 2008 Rochester
  thesis, it has no closed form, its author states he cannot bound the tail, and
  the tabulated 11-term truncations are measured here to diverge at the
  bandwidth the method needs (`F_4(1) ~ 2476` against `F_1(1) ~ 2.78`, giving
  proportions of 1.198 and −2.64).

A second pass took the remaining thread, whether ζ's own 0.6725 can be moved
toward the 0.68185 ceiling, as far as the public material allows.
`wide_search/RESULTS-pair-ceiling.md`:

- **The scalar-moment formulation collapses, exactly.** Retaining only
  `(tr, ||.||_F^2)` per window makes the joint feasible set the intersection of
  the single-window half-lines, hence `sup_v H(v) = 0.6725007037...`. That route
  cannot move the number, and is closed rather than unfinished.
- **The published ceiling data reproduces.** `wide_search/pair_ceiling.py`
  recomputes, from the enclosures in the public `LawN256.lean` alone and with
  exact rationals, the `2^140` scale, 256 rows, the worst interior error
  `1.83670992316e-40`, `D(1) = 0.8239531607128352`, the stability coefficient
  `2.5431315104166665e-6` and the simple fraction `0.6818286874638315`. All
  agree with the repository. The extremal law itself needs a certificate file
  the authors state is available on request.
- **Remark 1.1's ceiling is stated more uniformly than its finite instance
  supports.** The `N = 256` law gives the `0.68185` sentence for certificates
  with `abs(r'(1)) + integral abs(r'') <= 8.38043022204...`. The formalisation
  carries the error terms and does not make that elision.

**Disposition:** the ξ′ constant and its negative consequence stand, and are
reproducible from this directory. One thread is closed (the scalar-moment LP),
one is blocked (a closed form for `F_k`, `k >= 2`), and one remains genuinely
open: the full-data LP over marked periodic configurations, which does not
reduce to the single-window bounds. No claim promoted, no ledger entry. Nothing
here is evidence for or against RH, and nothing here is a defect report against
the paper's Theorems A-E.

### The director run (`director_run/`)

**Status: not a hunt in the usual sense and not a result, a directorate record.
The instruments it touched are in `zeta/`, and every change it made there is
pinned by a test or stated as a corrected contract.**

An operator handed the laboratory over with no assigned theorem and the standing
instruction that finding a recorded conclusion of this repository to be wrong
counts as a result. Nine investigators with conflicting mandates ran in
parallel; the generator of a claim never judged it. Full record in
`docs/25-the-director-run.md`; programs, claim ledger, graveyard and
intervention ledger in `director_run/`.

- **Six defects in recorded claims**, each reproduced by the director before
  being written down. The most serious: `zeta/rigor.py`'s abscissa conversion
  parsed unrecognised numeric types from their *printed decimal*, so
  `proven_sign` returned a **wrong** nonzero sign on a `numpy.float32` input,
  identically on both backends, because the fault sits upstream of the split.
- **A strategic conclusion corrected.** The claim that a coefficient functional
  is "blind to the position of the critical line by construction" is false as
  written and mis-cited (`docs/18` §6 says *ordinate* statistics). The true
  statement is a threshold, `c_p ≤ d` for `ζ(s−δ)` exactly when `δ ≤ ½`, and
  it is the Selberg-class axiom's `θ < ½`, i.e. known. The `ROADMAP.md` call
  that hunt #5 asked for is answered: **no**, this does not become a standing
  constraint on the coefficient-side programme.
- **Two positives that held under attack.** A blind replicator, given the
  statement only and forbidden the package, reproduced the flagship Weil
  enclosure to 43 digits from scratch; and the Lean arm rebuilt on a cold
  machine, 8715 jobs, zero `sorry`s.
- **The formal arm's blocker was mis-diagnosed and is now measured.** Rung 3's
  centre could not have passed at any Taylor order, its budget counts the tail
  radius once where the norm counts it twice, and the width floor is the κ
  enclosure, not the exponential Taylor order. A configuration with ≥1.1×
  margins exists at 1.63× the term count and the same literal sizes.

**Disposition:** repairs landed with tests; no claim promoted; no ledger entry.
Nothing here is evidence for or against RH.


### Hunt #5: a norm at every place (`local_positivity/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline is
a negative result about globalisation, plus an honest boundary on what the gate
actually tests. Corrected 2026-10-21: the local equivalence is an unreviewed
derivation, not a consequence of the closed form, and the gate is a
measurement of it whose regime test misreads oscillating weights.**

An ontology attempt in the sense of `docs/09` §4, pushed at Requirement C of
§5.1: construct, from prime data alone, a structure in which the Weil form is a
norm square, so its sign becomes formal. Reached one place at a time, and the
localisation is exactly where it dies. Raw numbers in
`local_positivity/results.json`:

- **The prime side factors place by place into a manifest norm.** With
  `Φ_p f = Σ_{m≥0} p^{−m/2} f(· − m log p)` it decomposes as
  `−Σ_p log p (Q_p(f) − ‖f‖²)`, `Q_p = (1−1/p)‖Φ_p f‖²`: a norm at every
  place, from coefficients only, with no zeros entering any definition.
  Reconstruction agrees with `zeta.weil.explicit_formula_sides` to 22 digits.
- **And the local norms do not assemble, which is the result.** `Q_p − ‖f‖²` is
  not of definite sign: 52 of the first 60 places positive, 8 negative. Local
  positivity is therefore compatible with either sign of `W`. Files under
  `docs/09` §5.1's taxonomy item #5, *finite approximants*.
- **Gate #3, with a crisp answer.** The place kernel has the closed form
  `K_p^(d)(θ) = Σ_j (1−|α_j|²/p)/|1−α_j p^{−1/2}e^{iθ}|²` when every
  `|α_j| < √p`, and `c_p ≤ d` reads the local bound `|α_j| ≤ √p`, with `d`
  read off each object's own gamma factors and never chosen. *Corrected
  2026-10-21* (`local_positivity/CORRECTIONS.md`, "Later correction"): the
  forward direction is derived; the converse was read off the closed form,
  which cannot carry it (at `p = 2`, `α = (3√2, 0, 0, 0)` the rational
  expression is `≥ 1` while the series diverges; the gate itself reports
  `"divergent"` and FAILs there). With `c_p` read as the least PSD Toeplitz
  diagonal, the converse rests on a PSD-boundedness derivation that is
  unreviewed. ζ and `L(χ)` quadratic mod 5 measure
  `c_p = 0.8284` and PASS (matching `2/(√p+1)` to 12 digits);
  Davenport–Heilbronn measures `1.8361` and FAILS at `p = 2, 3`; both disc −23
  Epstein forms FAIL, at `5.995` and `6.462`. "Where exactly does DH fail to
  embed?", at `p = 2`, excess 0.836.
- **Decoy / surrogate.** Swapped coefficients move the verdict by 15 orders of
  magnitude, the control whose absence made the Imposter Gauntlet vacuous
  (`docs/15`). Against 300 random period-5 sequences 100% fail, median excess
  +5.88, and **DH sits at the 6th percentile**: a mild failure, not an exotic
  near-miss, echoing `ROADMAP.md`'s 27th-percentile calibration from an
  unrelated statistic.
- **Lesion.** Interpolating ζ → DH, blindness sets in at `ε* = 0.184`, so a
  PASS means "no violation above ~18% of the way from ζ to DH at the tested
  places", and nothing stronger. The PASS side is not vacuous either: across 60
  Satake angles the genuine degree-2 family keeps margin ≥ 0.343. Those are
  margins of the truncated `c`. Since the gate's regime test was added
  (2026-08-11) its *verdict* on that family is FAIL at 22 of the 60 angles: the
  test reads two weighted terms near the truncation edge, and a conjugate pair
  of Satake parameters makes them oscillate, which misleads it on either side
  of the bound (measured 2026-10-21, pinned in `test_closed_form.py`).
- **The honest boundary, stated so nobody overclaims it.** The gate is *not* a
  test for "has an Euler product". A genuine degree-2 Euler factor with
  `α = 2.3, 1/α`, violating Ramanujan, is rejected at `p = 5`, in the
  `"divergent"` regime where `c_p = +∞` by the module's convention (the printed
  `65.24` is the series truncated at depth 41, not the value). This entry used
  to call that factor legitimate in the Selberg class; it is not, since
  `docs/09` §3's axioms (4) and (5) both exclude `|α| > √5`. It reads the local
  bound `|α_j| ≤ √p`, forward direction derived and converse an unreviewed
  derivation, and `localpos.scope()` says so inside the module rather than
  only in prose.

**Disposition:** instrument kept, avenue closed and recorded so nobody reopens
it; no ledger entry. Nothing here is evidence for or against RH. This is the
third statistic, after `D(f)` (`docs/18` §6) and the Fourier quasicrystal
separation (§4), to read arithmetic and stay blind to the *position* of the
critical line. **The reason recorded here was wrong, and the `ROADMAP.md` call
it asked for has now been made, the answer is no** (2026-08-11, `docs/25`).
`ζ(s−δ)` does *not* have the same coefficients: it has `n^δ a_n`, and `c_p`
reads that twist with threshold `δ = ½` (`c_p = 2x/(1+x)`, `x = p^{δ−½}`, for
`δ < ½`; at `δ = ½` the gate reports INDETERMINATE; the `δ > ½` side is the
converse above, unreviewed). Blindness is a property of a statistic invariant under that
twist, not of reading arithmetic, and a coefficient-side statistic equivalent
to RH is already in this tree (Mertens, `criteria.py` face 1). So the
repetition across three instruments does **not** rise to a standing constraint
on the coefficient-side programme, and must not be recorded as one. Full record in
`docs/24-the-local-positivity-attempt.md`; the session's own corrections,
including a citation defect it found in `docs/12`, are in
`local_positivity/CORRECTIONS.md`, whose "Later correction" (2026-10-21)
grades the local equivalence and records the gate's regime-test defect, which
this correction pins but does not repair.

### Hunt #4: repairing the counterexample (`flow_repair/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline
is a measured constant for the rival, and a null control that explains it.**

Pointed the de Bruijn–Newman flow (`zeta/heatflow.py`'s deformation, rebuilt
generic-Φ in the probe) at the Davenport–Heilbronn function for the first
time. Derived Φ_DH = 4e^{3u/2}Σ n aₙ e^{−πn²e^{2u}/5}, then *measured* the
normalisation rather than trusting the derivation: (c, a) = (1, 1) to 4.2e-42,
route agreement with `completed_dh` to 7.2e-41, and the same evaluator
reproduces `zeta.heatflow.H_t` to 5.4e-42 before being trusted on the rival.
Raw numbers in `flow_repair/results.json`:

- **The nine known off-line quadruples (Spira 1994; Balanzario–Sánchez-Ortiz
  2007, each re-polished in-tree) land on the real axis at measured times
  t\* between 0.00275 and 0.05765.** Each is a lower bound for
  Λ_DH := inf{t : H_t^{DH} real-rooted}; the max comes from the height-240
  pair (β ≈ 0.8695), **not** the famous height-85.7 zero, which places third.
  Λ_DH ≥ 0.0577 measured, inside [0, 0.2], the interval that historically
  bracketed Λ_ζ. In flow time, the counterexample fails RH by less than ζ's
  own uncertainty span: "Λ is small" distinguishes nothing (gate #3 on the
  flow axis).
- **Null control, the headline**: the arithmetic-free N-body zero dynamics
  ż = 2Σ1/(z−z') seeded with the measured t = 0 configuration reproduces
  every PDE repair time to **±0.04%** (target was 1%). The repair clock reads
  zero geometry, not arithmetic, the flow-time distance to real-rootedness
  is a property of where the zeros sit, shared by any function with that
  layout. Position-sensitivity (docs/18) meets the counterexample gate.
- **Method worth keeping**: the pair is tracked through its collision by
  contour moments: Δ(t) = 2q₂ − q₁² is analytic through the landing, so t\*
  is a clean root even though the zeros themselves have a branch point.
  Zero-census accounting closed in all five checked windows (line + 2·pairs
  = strip count; e.g. 49 + 4 = 53 at pair 1).
- **Lesions**: a contour clipping one pair member is refused (N=1 ≠ 2); a
  contour through the zeros returns winding ~1.8e9 and is refused. Post-
  landing, the newborn real pair is invisible to the default mean-gap/20
  sign scan at 3 of 5 grid phases until gap/step ≳ 1.4, hunt #3's blind
  spot, measured on the other side of a collision.
- **Precision response**: t\*₁ = 0.0441263445516 identical to the last digit
  across dps 44/54/70 and 96/192 contour nodes; spread exactly 0.

**Disposition:** measurement portrait of a rival's flow geometry; no ledger
entry (the surviving observation, repair times are configuration geometry,
is the null control *explaining* the quantity, which is a closure, not a
lead). Nothing here is evidence for or against RH; nine pairs bound a sup
over infinitely many from below and say nothing about Λ_DH itself. Spine
candidate recorded in `flow_repair/NOTES.md`: a Φ-parametric entry point for
`zeta/heatflow.py` (a `zeta/` change, not this hunt's).

### Hunt #3: the closest call (`lehmer_pair/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline
is a negative result supplied by the rival.**

Pointed the ball-arithmetic arm at Lehmer's pair γ₆₇₀₉/γ₆₇₁₀ ≈ 7005.06/7005.10
(gap 0.0377, mean spacing 0.895). Measured, with raw numbers in
`lehmer_pair/results.json`:

- The near-miss bump between the pair was decided **positive at 64 bits by
  both backends**, `proven_sign` pattern −,+,− on exact rationals, midpoints
  agreeing on `Z(7005.0819) = 0.003967335016595021` to all 16 digits, and a
  dense scan found exactly 2 sign changes with zero undecided samples.
- **Lesion**: the default grid policy of `rigor.certified_sign_changes`
  (mean_spacing/20 ≈ 0.0448) is *wider than the Lehmer gap*; sweeping the
  window phase, the default grid missed the pair entirely at 1 of 5 phases.
  Honest both times (a sign-change count is a lower bound), but blind.
- **Precision response**: enclosure widths shrink ~2^−prec with the midpoint
  pinned; at 32 bits flint straddles zero while mpmath.iv decides, the
  backends disagree about *decidability* at the boundary, never about value.
- **Rival, the headline**: the predicted "failed Lehmer bump" at
  Davenport–Heilbronn's off-line zero does not exist: Z_dh's closest
  approach on [85.2, 86.2] is **−0.357**, two orders of magnitude farther
  from zero than ζ's bump clears it, while hiding 2 strip zeros. So
  "|Z| gets small" flags nothing: it fires on ζ's healthiest close pair and
  stays silent at an actual RH violation. Magnitude heuristics die here;
  sign counting vs strip counting survives.

**Disposition:** portrait, not conjecture, no ledger entry. Spine candidate
recorded in `lehmer_pair/NOTES.md`: the default-step blind spot deserves a
docstring line on the packaged scanner (a `zeta/` change, not this hunt's).

### Hunt #2: factorization vs. position (`factorization_vs_position/`)

**Status: probe, not established. The instrument used cannot support the
claim that was recorded.**

The hunt asked whether the factorization defect `D(F)` quantitatively
controls the Weil position residue, and recorded a "verified" correlation on
Epstein forms of discriminants −15, −20, −23, −24. Three defects, each
checked in-tree:

- **The completeness gate was never called.** `zeta/detector.py`'s own
  docstring states the load-bearing caveat: the residue measures "zeros
  unaccounted for by the supplied on-line list", so *a missing on-line zero
  produces a residue indistinguishable from an off-line zero*, and **a scan
  whose completeness has not been checked reports nothing trustworthy**.
  `online_list_is_complete` appears nowhere in `hunts/`. The on-line zeros
  were found by a `step=0.05` sign-change scan, which skips close pairs.
- **The lesion confirms the confound, measured.** Give ζ, factorization
  defect `2.65e-32`, a perfect Euler product, a zero list with **one
  on-line zero removed**, and the residue jumps from `0.0038` to **`1.99`**.
  An O(1) position residue is therefore produced by an incomplete list at
  *zero* factorization defect, which is precisely the signal the hunt read as
  off-line zeros. The recorded residues (4.07–4.33) sit at about twice that
  lesion.
- **The test set is the rival set.** The discriminant −23 principal form
  `(1,1,6)` is a **registered rival in `zeta.epstein.battery`**, admitted
  precisely because it lacks a scalar Euler product while keeping the
  functional equation. Confirming that the battery's rivals lack an Euler
  product and have off-line zeros restates their admission criterion. Under
  gate #3 that distinguishes nothing.

Separately, the recorded data does not show the claimed relationship:
across `results2.json` the defect varies by 2.7× (4.25 → 11.46) while the
residue moves 6% (4.07 → 4.33), and in `results.json` a 67× change in defect
(1.58 → 105.95) moves the residue 1.36× with `argmax_c` pinned at the same
`86.0` for all nine rows, the scan-window signature `docs/17` §2 says to
distrust.

**Disposition:** instrument retained, claim withdrawn, no ledger entry. The
correction to `HANDOFF.md` is in the same commit as this note. What the hunt
did produce is real and worth keeping: a *generalized* residue detector that
accepts an arbitrary archimedean bracket, which is the reusable part.
Pinned by `tests/test_hunt_probe_discipline.py`.

### Hunt #67: one RH mechanism, stated first and dead by the end (`epp_herglotz/`)

*Renumbered from #49 on 2026-08-21: `r_6f088d/` had taken that number on `main`
while this hunt was on a branch. The directory name is the stable reference.*

**Status: settled, negative.** The hunt stated a mechanism before writing any
code (`MISSION.md`, in a commit containing nothing else): RH is equivalent to
`Re (xi'/xi) >= 0` on `Re s > 1/2`, so split `xi'/xi = G - A` into archimedean
and prime sides and compose the two positivities each side carries. The Euler
product makes `Lambda(n) >= 0`, which by Bochner makes the prime side
vertically positive definite; the archimedean side is positive and grows like
`(1/2) log(t/2pi)`.

**It is false**, and the witness is the symmetric shifted product
`W_a(s) = zeta(s+a) zeta(s-a)` at `a = 1/4`. It carries an exact `s -> 1-s`
functional equation for its completion, a real Hardy-style `Z`, a scalar Euler
product (which neither standing rival of `zeta.epstein.battery` has),
non-negative Dirichlet coefficients, and log-derivative coefficients
`Lambda(n)(n^a + n^{-a}) >= 0`. Its Bochner matrix and its archimedean term
are both *larger* than zeta's. Its zeros are `rho +- a`, so Hardy's theorem
alone puts infinitely many off its own critical line: four zeros measured in
the box `[0.1, 0.9] x [10, 25]`, zero sign changes on the line there, and
`Re (Xi_a'/Xi_a) = -998` at a point where the mechanism says it is
non-negative.

Two things the run recorded that outlive the mechanism. **A coefficient claim
taken through the battery carries its truncation as part of the claim**: EPP
read to `n <= 40` reports as shared with the principal Epstein form of
discriminant -23, and that form's first negative log-derivative coefficient is
at `n = 48`. And **the mechanism's target has zero margin on the boundary**:
the functional equation makes `Re A = Re G` an identity on the critical line,
the margin just inside is `sum_rho abs(s-rho)^{-2}` (0.0621641 by the analytic
route, 0.0621709 assembled from 300 ordinates plus a density tail), and the
bound EPP supplies exceeds the target by a factor growing past 14 by `t = 1e8`.
So the repaired mechanism needs square-root cancellation in the prime sum,
which is RH. No progress on RH; the hunt says so itself.

### Hunt #74: Krenn-Gu 8x3: Orbit-reduced polynomial system and pricing (`r_31b6c1/`)
**Status: settled.** Built the exact algebraic generator pipeline. The Krenn-Gu polynomial system has exactly 252 edge-weight variables (as inferred in Fulcrum, not 28). Using the fully $H \times S_2$-symmetric quotient, the variables collapse to exactly 8 orbits. The resulting calibration gate on the 6x3 graph produced `[1]` from Groebner basis in under 0.1 seconds, successfully replicating the proven "no-complex-witness" verdict. 

Applying this same exact pipeline to the open 8x3 graph yielded an identical verdict. The 57 $H \times S_2$ pair orbits were evaluated in the 8-variable working quotient, resulting in a mapped distinct monomial count of 8, each of uniform degree 12. Crucially, executing `sympy.groebner` on the 70 unique 8-variable symmetry-reduced equations completed in under 5 seconds, using negligible memory (80MB), and cleanly returned `[1]`. This proves that no $H \times S_2$-symmetric complex witness exists for the 8x3 instance.

(Note: No corresponding harness ledger was found in `harness/departments/`, confirming that framework is entirely deprecated.)

### Hunt #78: the far constant `637/1000` at depth 1 (`r_a7c12f/`)
**Status: settled, the recorded correction is withdrawn.** `K2-TWO-SPECIES.md`
section 2 starred `far constant sup Dam*(s^2-2)/y'^2 = 0.6636 > 0.637` as a
depth-1 correction that `Wt_tail_le`'s `637/1000` does not survive. It does
survive. Two separate errors were stacked. First, `Wt_tail_le`
(`Counting.lean:93`) is `Wt w <= (637/1000)/w for 1368 <= w`, an inequality
between two explicit rational functions of one variable with no depth in it;
the depth-carrying lemma is `Qim_far_sq` (`FarField.lean:227`, hypothesis
`hy : y <= 1/2`). Second, `1368 <= w = s^2-2` means `s >= 37.0135`, while
`two_species.far_constant` scans `[8, 400]`: and both starred sups are
attained at `s = 12.715` and `s = 12.625`, i.e. `w = 159.7` and `w = 157.4`,
where the proved envelope `Wt(w)*w` is `0.7042` and `0.7054`. Neither row was
ever in conflict with anything proved. On the range the constant *is* asserted
on, an Arb pass at 96 bits (`hunts/r_a97060/ball_field.py`, adaptive cells,
45,030 evaluations) gives `sup Dam(1,s)*(s^2-2) <= 0.6317735` against
`0.637`, margin `+0.0052`, at an enclosure cost of `1.00005` over the float
scan; the ladder `0.5844 / 0.5937 / 0.6094 / 0.6318` at depths
`0.25 / 0.5 / 0.75 / 1` all hold. The constant first fails at depth `1.0494`
(measured). What *does* break below depth 1 is the derivation route:
`Qim^2 <= y^2 Wt(s^2-2)` reaches ratio `1.00438` at depth 1, and holds
asymptotically iff `4 sinh(y/2)^2 cos(1/sqrt2)^2/y^2 <= 5/8`, i.e. iff
`y <= 0.972659`. So a `k >= 3` pass at depth `2y <= 1` inherits a broken
proof, not a broken constant, and re-fitting `base_poly_le` for `y <= 1` is
the named obligation. Not closed: `s > 400` has no depth-1 enclosure (the
tail composes through the very lemma that fails), and the table's other
starred row (`no_damage`'s `28/5`) was not examined. Nothing bears on RH
(`docs/08`).

### depth_bound_selfterm/

**Status: measured.** Dual kernel `dual-x80.json` data[1]: $r(0)=0.125$,
$S(y)<r(0)$ first at $y \approx 0.9198925$, $S(y)<0$ first at $y \approx 0.9528774$,
numpy and `mp.workdps(40)` agree. In-band control (data[0], $z$ empty) has no
crossing on $[0, 1.5]$; $S$ rises ($1.012$ at $y=0.9$, $1.526$ at $y=1.0$).
Whether $y \approx 0.92$ is a depth an off-line zero can reach is unresolved:
the kernel's LP is unfolded (`configuration_lp.py` line 3), so the raw range
$(0,1/2)$ does not apply, and a factor 2 in the pair convention is open.
Strip mass forces a crossing at large $y$; the content is where.
Nothing bears on RH (`docs/08`).

### Hunt #134: the Turán margin is a Cauchy-Schwarz deficit, and positivity alone is not the criterion (`gauss_positivity/`)

> **Landed on main 2026-10-18.** Written on `pi/rh-resolve-20261003` as Hunt #120; on main #120 is
> `qrh_rival_step`, so this hunt is #134. Its forward pointer in `RESULTS.md` section 6 is
> corrected there: the explicit-threshold experiment it proposed was already done in the
> literature, and hunt #135 (`jensen_wedge/`) records the frontier it actually meets.

**Status: measured, instrument hardened, no RH statement claimed (2026-10-03).**
Asks whether the positivity of the heat-flow weight `Φ` (`zeta/heatflow.py`,
positive on the real axis) buys anything toward the real-rootedness of `Ξ`, via
a Pólya-type criterion. Two computed counterexamples settle the shape of the
question and neither is a statement about ζ.

The folklore criterion (positive even weight with a convex Fourier-side
exponent) is **false**: `φ(t)=e^{-t^4}` has a convex exponent and its transform
has complex zeros by argument-principle count, and `φ(t)=e^{-|t|}` is the
cheapest witness with zeros at `z=±i`. The sharper version, positivity of the
weight alone, is **also false**, and this is the consequential one:
`f(t) = 1 + cos t + cos 3t` is the cosine transform of the positive measure
`δ₀+δ₁+δ₃` and has the complex zero `t = 1.13662270206 + 0.319561426779j`. So
the target has to be Schoenberg's `PF_∞` of the weight (total positivity of
every translation kernel), not positivity.

What was built: from the module's own Mellin derivation, with
`w(u) = e^{u/4}ω(e^u) > 0`, the moments `I_k = ∫u^{2k}w` are moments of a
positive measure, so Cauchy-Schwarz gives `D_n := 1 − I_n²/(I_{n−1}I_{n+1}) ≥ 0`
automatically, and the Turán inequality is `r_n = [(n+2)/(n+1)](1−D_n)(1+O(1/n²))`,
i.e. exactly `D_n ≤ 1/(n+1)` up to a stated correction. Measured `0 < D_n < 1/(n+1)`
at n = 100, 400, 1600, 3200 with `nD_n` falling 0.495 → 0.292. A saddle
instrument (`πe^{u_*} = 1/4 + 2n/u_*`, `D_n ≈ 4/(u_*²A)`) reproduces the exact
quadrature to 4-6 digits with error falling like `1/n`; the two routes are the
hardening. The resulting law is `D_n ~ 2/(n log n)`, `r_n = 1 + 1/n − 2/(n log n) + o(1/(n log n))`,
`n(r_n−1) → 1`, measured to 10²⁰.

Recorded defects, in the hunt: a ratio routine that dropped an index offset and
was caught against the committed table before any large-n use; an uncalibrated
Fourier inversion that reported a positive weight for a rival and is **wrong**
(the relation is `Ξ(t) = 8∫Φ(u)cos(2tu)du`, calibrated to 14 digits); and a
**correction to the hunt's own Gate-3 claim**. An earlier version stated that
`Ξ_a` zeros sit at `t = 1/2 + i(γ±a)`, off the real axis, giving an
unconditional obstruction for the rival `W_a`. That was an algebra error (the
`a` moved inside the factor `-i(ρ−1/2)`); the correct zero is `t = γ − a`, real,
confirmed numerically (`|Ξ_a(13.884725141735)| = 9.9e-37` against `695.04` at
the claimed value). The algebraic fact is that for a completed
`Ξ_f(t) = F(1/2+it)` a zero `ρ = σ+iγ` of `F` gives a `t`-zero
`t = γ − i(σ−1/2)`, **real iff `σ = 1/2`**. So the real-rootedness of `Ξ_f` in
`t` *is* the critical-line statement transported, which makes `W_a` the **wrong
rival** here: its transported statement is zeta's own RH, which is not known to
fail. The correct rival is Davenport-Heilbronn, and the criterion genuinely
fails for it: its off-line zero at `σ = 0.80851718245663738...` gives the
complex `t`-zero `85.69934848537759 − 0.3085171824566374j` with
`|Ξ_DH(t₀)| = 4.74e-53`. The `PF_∞` obligation for DH itself is still open.

**A route closed by proof.** Newton's inequalities for the Jensen polynomial
`J^{d,n}`, at every degree and order, are **implied by** the classical `d = 2`
Turán inequality: Newton's normalised right-hand side is
`k(d−k)/((k+1)(d−k+1)) < 1` for every `d ≥ 2` and `1 ≤ k ≤ d−1` (max
`0.93548387` at `d = 59, k = 29`), while Turán makes the left-hand side `> 1`.
So the 495-cell Newton table's margins (down to `1.2e-40`) are the `C(d,k)`
normalisation counted repeatedly, not near-failures, and chasing Newton at
higher `d` is closed by computation rather than by a search that found nothing.
Hyperbolicity of `J^{d,n}` is strictly stronger than its Newton inequalities and
is **not** closed.

**Why the higher-degree version is closed from below, with a mechanism.**
`hunts/jensen_clock` measured that finite Jensen degree acts on the zeros as
de Bruijn-Newman heat with `t_eff(d) = |x0|/(8d)`, `x0 = (ρ−1/2)²` the pair's
image. The Davenport-Heilbronn pair (`σ = 0.80851718, γ = 85.69935`) lands only
at `d* = 20785.13` with `t* = 0.0441263`, and `|x0| = 7344.47351367`, so
`t_eff = 459.03` at `d = 2`, `28.69` at `d = 32`, `0.9181` at `d = 1000`: the
degree has already real-rooted the polynomial before it can be inspected, and a
low-degree hyperbolicity scan **cannot fail**. Measured directly on ζ:
`min|Im root|/|root|` over `J^{d,0}` is exactly `0.0` for every `d = 2..24`, so
the condition is slack throughout the reachable range. This refines `docs/12`'s
statement of the gap: at small `d` the unresolved set is not merely unresolved
but unfalsifiable by a scan at that `d`, and a certificate must operate above
`d*(x0) = |x0|/(8t*)`, which grows like `γ²` with height. The inherited null is
that the clock reads zero **configuration, not arithmetic**
(`jensen_clock` P5), the same information-class conclusion `epp_herglotz` and
`local_positivity` reach from other sides.
The Turán inequality is already known unconditionally (Csordas–Norfolk–Varga);
this hunt does not improve on it and claims no progress on RH. Nothing here
bears on RH (`docs/08`).

### Hunt #135: the polynomial hyperbolicity wedge for Jensen polynomials of xi (`jensen_wedge/`, opened 2026-10-18)

**Status: landed 2026-10-19 (phase 3) and closed the same day by owner decision; no kill condition met. Q1 had been answered in the
literature first; Q2 is answered by a derivation reviewed once internally, not a theorem,
pending external review.** Holland's wedge `n^3 log^2(n+2) >= K d^5` holds with
K = 17 900 when GORTTW Cor. 1.3 covers d <= 9.36e20, or K = 9.10e19 with no outside input;
the six-coefficient form `n^4 log^2(n+2) >= K' d^6 log^12(d+2)` holds with K' = 7.21e9 or
3.61e30; and c = 1 is admissible in GORTTW Theorem 1.1. Every numeric step is an Arb
enclosure. An independent session reproduced all four constants with its own code and broke
no step (`REVIEW_PHASE2.md`); its finding that three of four planted formula faults passed
the phase 2 suite is closed (seven tests added, all four plants now rejected), and a
misread looseness figure was corrected at landing (`RESULTS.md` section 18). **Credit:** the
2/3 wedge was posted first by Savva (Zenodo 10.5281/zenodo.22293642, 2026-09-03,
`n^2 log(n+2) >= K d^3`, stronger than the hunt's `log^12` form, K not computed), and the
Pade spine behind the sixth-coefficient match by Sarnowski (Zenodo Papers 134Z and 134AA,
2026-08-20). Both are unreviewed and their proofs were not checked here. The hunt's own
results with no prior instance in the searched set are the explicit constants (`RESULTS.md`
section 19, `NOVELTY.md`). The Davenport-Heilbronn gate held as predicted, so the
construction cannot tell an RH-true function from an RH-false one (section 15), and "The
doors" (section 20) leaves the small-n, large-d corridor untouched. Front door: `docs/44`.
Merged work: #304 (opened), #306 (phase 0), #307 (funding record), #308 (phase 1), #309
(review), #310 (DH gate), #311 (H1, H3), #312 (literature search), #313 (review), #314
(phase 2), #316 (review), #317 (landing); #305 and #315 are related corrections
outside the hunt. The status history below is kept as written.

**Status: phase 0 done 2026-10-18, measured; no kill condition met.** Holland's two sign
facts reproduce at every integer n = 50..3200 on the exact moment table (Laguerre defect
at R_3 positive, Jacobi defect at R_4 negative), and a saddle route that uses no
quadrature agrees in sign at 21 points; his stated constants (2, 2, 6/5, 1/3, 1/24) are
approached monotonically on the saddle route out to n = 1e20. One preset error rule for
the saddle route missed at n = 150 and is kept in `RESULTS.md` section 3. The phase 1
quantity, the R_5 defect after his five-coefficient match, is negative at his choice
D = B_J/2 at every n measured, but its sign flips as D varies, at a crossing where
(C - D)/D sits above the D/4 of his parameter window; measured, not claimed.
**Phase 1 done 2026-10-18; no kill condition met; Q1 graded attempt unresolved.**
Holland's PDF checks out line by line (four loose paraphrases corrected in `RESULTS.md`
section 9). Phase 0's R_5 crossing is the [2/2] Pade approximant of a Stieltjes function:
at leading order, matching R_0..R_(m-1) with Jacobi factors is rational approximation of
(1 - z)^(2/L - 1). So his own two-factor family matches R_0..R_5 with every parameter
positive and no third factor; its R_6 defect is negative at every n = 50..3200 and to
1e20, tending to -2/(n^5 L). The price is a second factor with (C - D)/C near 1/2, outside
his Lemma 9.1, and a third factor of his near-identity kind is obstructed at first order
in 1/L (a Cauchy-Schwarz argument; self-reviewed). A conditional derivation (section 12)
replaces Lemma 9.1 by a root-gap bound and would give n^4 log^2(n+2) >= K d^6 log^12(d+2),
pending two unproved inputs and review. **Phase 2 done 2026-10-19; no kill condition met;
Q2 answered by self-reviewed derivation.** Holland's wedge holds with K = 17 900 (with GORTTW
Cor. 1.3 for d <= 9.36e20) or K = 9.10e19 (standalone), and the six-coefficient wedge with
K' = 7.21e9 or 3.61e30, every numeric step in Arb balls (`EFFECTIVE.md`); 44 of 44 planted
weakenings turn the effectivity check red. Not reviewed by an independent session. A depth hunt
by owner decision, time-boxed to
2026-11-29, against Holland's wedge `n^3 log^2(n+2) >= K d^5` (arXiv:2608.08682,
August 2026). It asks whether the five-coefficient positive-root comparison extends
to six coefficients (`d <~ n^{2/3}`), and whether the standing wedge's constant can
be made explicit. It replaced the requested target, explicit thresholds at fixed
degree, because the literature had already met it: GORTTW (Adv. Math. 2022)
Corollary 1.3 gives all `n` for `d <= 9.36e20`. The Davenport-Heilbronn rival gate is
preregistered with the prediction that the construction also succeeds for DH, which
would make the wedge shared structure. Nothing here bears on RH (`docs/08`).

### Hunt #136: pushing the zero-free half-plane under 7/8 (`below_seven_eighths/`, opened 2026-10-21)

**Status: paused by allocation (proposed 2026-10-26; the owner decides). No improvement of
the half-plane is claimed.** The first wave (2026-10-21) found no row-count sharpening that
gains at the paper's inputs (part (a), attempt unresolved), priced but did not prove probes
of lower order (part (b), attempt unresolved), and checked the Euler-product step exactly on
stated ranges. By 2026-10-26 the smallest bound merged on QuasiRiemannTracker was 0.8746075
(PR 76), on tracker entries that keep the 13/15 floor model's geometry as far as their Lean
sources were read (inferred). The kill condition is not triggered, because the hunt has no
candidate to match. See the dated disposition section of `MISSION.md`.
The owner directed the laboratory on 2026-10-21 to
attack RH, and this is the campaign's first track. The question is whether the zero-free
half-plane for every Dirichlet L-function can go below the best public abscissa, 0.8748867
(Xu and Sang), either by strengthening the row-count inputs of OpenAI's Part II assembly,
whose ceiling hunt #139 places at 13/15, or by a probe whose constants are not tied to the
sextic pole. It builds on hunt #139 (`seven_eighths_pin/`, unlanded; opened as #134 on
`claude/hunt-134-seven-eighths-pin`), reads the pinned paper source by line number and
checks every printed constant in exact arithmetic. Nothing here bears on real part 1/2.

### Hunt #137: a kernel-checked RH to finite height for Mathlib's zeta (`rh_height_lean/`, opened 2026-10-21)

**Status: both targets closed by a clean Lean-kernel build; independent
`con-ron --verified` whole-closure acceptance.** On 2026-10-22 the height-50
theorem and exact count (ten zeros) compiled from source. On 2026-10-23
`RHHeight100.rh_height_hundred` and
`RHHeight100.zero_count_hundred` compiled from source and the final audit accepted
100 reports with only the three standard axioms. Every zero of Mathlib's
`riemannZeta` in `0 < Re rho < 1`, `0 < Im rho <= 100` is on the critical line,
has analytic order one, and there are exactly 29 distinct zeros in that window.
The build retained 102 objects. `CheckMain100.lean` pins the unfolded final
types; [RESULTS.md](rh_height_lean/RESULTS.md) records the build, reproduction,
limitations and inconclusive checker attempts. `con-ron --verified` timed out
at a 60,000/81,674 progress marker; a retry with `--progress=5000` showed no
further marker, not evidence of zero completed checks. A later 8-worker
`--progress=1` gate continued checking to 61,363/81,674 before its 1,200-second
wall stop; its local receipt is in the bundle's `evidence/gate8/`. NanoDa reached
a 43 GiB RSS bound, and Lean's `leanchecker --fresh` timed out. These are
inconclusive, not rejections. A subsequent 8-worker `con-ron --verified` run
on the same exported closure and checker binary exited 0 on 2026-10-24:
81,674/81,674 checks and 82,680 accepted declarations. Its receipt and
raw logs are kept in the local evidence bundle described in RESULTS.md.
The argument uses the vendored `zeta23` folded count, rigorous Lean enclosures,
and hunts #132 and #133's first ten located zeros plus nineteen new boxes.
The novelty search in RESULTS.md is bounded and makes no priority claim. This
finite theorem says nothing above 100 or about RH itself.

### Hunt #152: a ball-arithmetic Lehman localization of a sign change of pi(x) - li(x) (`skewes_enclosure/`, opened 2026-10-26)

**Status: open (2026-10-27).** Three outcomes, (1) to (3), all under the same
grade: a hardened computation on a cited derivation (Revers Theorem 3.1 and RH
to A), with rigorous completeness on Arb's Turing count alone, mpmath `nzeros`
agreeing on N(T) at float grade, and an mpmath second route for the zeros on a
sample. Item (4) is a post-hoc observation at measured grade.
(1) Target A, 2e6 zeros: the gate passed (Revers's S* inside the ball sum), and
pi(x) > li(x) for some x with log x in [727.9519119, 727.9521241].
(2) Target B, 2.2e7 zeros at the printed omega = 727.95134: the gate failed
(missing by 0.0122), recorded permanently.
(3) The pre-registered omega-grid rerun: hypothesis H (the printed omega is
727.951335792 rounded) is **not supported by its rule**. The gap shrinks to
3.37e-5, still over Revers's 2.60e-5 budget, so reproducing S* stays
unresolved. The pre-declared localization at 727.951335792 holds: pi(x) > li(x)
for some x with log x in [727.951319892, 727.9513517], with eta = 1.59e-5, as in
Revers ([RESULTS.md](skewes_enclosure/RESULTS.md) section 7). (Corrected
2026-10-27: the lower end was first quoted as 727.9513199, rounded inward from
the exact 727.951319892.) Neither interval is a new record.
(4) Post-hoc review, 2026-10-27, measured, not pre-registered: the 3.37e-5 gap
is twice the second-order sum S2. Revers's printed S* equals the
Saouter-Demichel first-order value he quotes, minus S2, to 1.0e-9, where his
Theorem 3.1 adds S2. Our first-order sum matches Saouter-Demichel's to 4.7e-8,
an end-to-end check of the 2.2e7 zeros. The verdict on H stands, but H's omega
was right in substance (RESULTS.md sections 3, 7 and 8). The review also
corrected the doors: A is a binding constant just above the R6 cliff, not a
free door. The question is whether a sign change of
pi(x) - li(x) can be localized with every computed step carried by Arb balls. The
method is Lehman's integral with Revers's 2025 error terms (arXiv:2501.04488,
JNT 2025) over the first ~2.2e7 zeros. The day-one read of three papers found
that Saouter-Trudgian-Demichel 2015 (submitted version) and Revers 2025 sum
their zeros in floating point. Both use an analytic zero-error budget, and
neither cites a rigorous zero source. Platt-Trudgian 2015 already carried the
analogous theta(x) - x sum in MPFI interval arithmetic with rigorous zeros, so
the method is not new to interval arithmetic and no novelty is claimed.
`skewes_terms.py` reproduces the R column of both of Revers's section-6
resizing tables from Theorem 3.1. It also found that the row printed as
eta = 1.55e-5 is the value at eta = 1.56e-5, a label slip with no effect on the
paper's conclusion. The day-one expected margin at the Saouter-Demichel
parameters was about 1.28e-4, from Revers's printed S*, and the zero precision
it needs (~62 bits) is far inside what Arb isolation delivers. The measured
margin at omega = 727.951335792 and eta = 2.28e-5 is 9.42e-5. Unit timings,
estimates and costs are in [RUNS.md](skewes_enclosure/RUNS.md), and the results
are in [RESULTS.md](skewes_enclosure/RESULTS.md). (Updated 2026-10-27: this
paragraph first ended "nothing is a result yet", which was written when the hunt
opened.)


### Hunt #155: the three pieces of the Weil functional and how deep they cancel (`arch_cover/`, 2026-10-30)

**Status: measured, no claim promoted.** Pole, archimedean and prime pieces are
evaluated separately with Arb enclosures for the Gaussian, Fejer and
autocorrelation families, and each value is checked against the zero side of the
explicit formula. The cancellation depth, the number of digits by which the three
O(1) pieces cancel to give W, equals `a (gamma_1^2 + 1/4) / ln 10` on the Gaussian
family to every recorded digit (17.375 at a = 0.2, 39.094 at a = 0.45), so the
statistic measures how far the test function sits from the first zero and nothing
deeper. (Corrected at landing, 2026-10-30: this entry first gave
`a gamma_1^2 / ln 10` with "predicted" values matching neither form; against that
form the hunt's own kill condition fired, now recorded in RESULTS.md 4(b). This
hunt was opened as #154, which `gabcke_remainder/` holds.) Two consequences are recorded: the prime side
grows with a where the zero sum collapses, so the hard regime sits inside the
family, and W goes to zero with every piece at O(1), so no inequality
`W >= c ||f||^2` with fixed `c > 0` holds over the class. The enclosure floor is 33
digits and is set by the prime truncation cap at `n_max = 2e6`, not by precision
(the 512-bit run behind "raising the bit count changes nothing" is not committed);
RESULTS.md ends with its doors. Nothing here is
evidence for RH. Record: [MISSION.md](arch_cover/MISSION.md),
[RESULTS.md](arch_cover/RESULTS.md).

### Hunt #156: the Gram matrix of the Weil form and its bottom eigenvalue (`weil_gram/`, 2026-10-30)

**Status: measured, no claim promoted.** The bilinear Gram `M_jk = W(h_jk)` on a
Gaussian basis, solved against the L2 Gram as a generalized eigenproblem, with
every entry checked against the zero side (residual at the zero table's 30 digit
floor; a dps 50 against dps 90 run is a null test, rerun at landing because the
first "dps 90" file had been computed at dps 50). Adding one concentrated
element drops the bottom eigenvalue by 18 orders, and the bottom eigenvector
there is the coordinate vector, so that drop is the single element degeneracy
`arch_cover` measured. Refining a purely broad span, where every element is
individually healthy at 3.1e-8 or better, still drops it from 2.4e-3 to 5.0e-22
across six dimensions, so the gap is created by the subspace choice and destroyed
by enlargement. The recorded consequence is that a gap bounded below uniformly in
the subspace cannot be had on these spans; nonnegativity on each subspace of an
exhausting sequence, which does pass to the limit, is untouched. (Scope and
numbering corrected at landing, 2026-10-30; opened as #155.) Nothing here is evidence for RH.
Record: [MISSION.md](weil_gram/MISSION.md), [RESULTS.md](weil_gram/RESULTS.md).

### Hunt #157: the prime side split by place, exactly, for a compact test function (`weil_split/`, 2026-10-30)

**Status: measured, one exact identity, no claim promoted.** For a rectangle test
function the shift operator has finitely many overlapping terms, so each place
carries an exact closed-form cost (not rational: it carries `log p` and
`p^{-1/2}`) and the per place sum reproduces the explicit formula prime term to
1e-16. Two monotone findings: the cost spreads from three places
carrying 98 percent at b=2 to 429 places with the top three carrying 13 percent at
b=8, and the covering margin falls from 3.0e-2 to 1.6e-4 over the same range,
about `b^{-3.8}`. That margin is `W_zeros` over the prime cost by construction, so
it normalizes `W` rather than testing the archimedean term separately. (Corrected
and renumbered at landing, 2026-10-30; opened as #156.) Compact support costs a slow quadrature, so every covering ratio is quoted
from the verified zeros with the prime side exact, and the quadrature column is
printed beside it rather than absorbed. Nothing here is evidence for RH. Record:
[MISSION.md](weil_split/MISSION.md), [RESULTS.md](weil_split/RESULTS.md).
