# Results: the public field, and why our barrier does not touch it

> Bounded outcome of the `field_audit` hunt. Labels: **VERIFIED** means recomputed
> here, on this host, from the primary source; **MEASURED** means a run completed
> here whose correctness rests on the competitor's own code; **REPORTED** means a
> figure taken from a repository's own documents and not replayed here;
> **INFERRED** means an extrapolation, with the gap stated.
>
> Nothing here is a proof and nothing here is machine-checked.

## 1. The sentence that matters

**This laboratory's number is not the leading one, and never was.** Our best
figure, `0.6730529829896288` (eight-point, bridge proved in Lean), is **tenth**
of fifteen public claims for this quantity. The leading public claim is
`AMTOPA/zeta-exact-pressure` at `0.6734164909714992949…`, which is ahead of us
by `0.00036350798187`, eight times the margin by which we are ahead of
`ainta/zeta-simple-zeros`, the repository we had believed we were chasing.

Three separate public constructions were already above our eventual figure
**before this laboratory began the seven-point hunt**. The earliest,
`trmdy/zeta-simple-zeros-673137`, first commit 2026-08-11 14:43 +0200 at
`0.673137630699`, was ahead of our final eight-point figure on its first day.

## 2. The ranking

Constants as published. VERIFIED where this hunt recomputed the figure from the
repository's own data; REPORTED otherwise. Ordering is exact decimal comparison,
VERIFIED (`rank.py`).

| # | claim | repository | first created | artifact | label |
|---:|---|---|---|---|---|
| 1 | `0.6734164909714992949…` | `AMTOPA/zeta-exact-pressure` | 2026-08-12 | mpmath.iv tables + C++ branch-and-bound, CI run recorded | REPORTED |
| 2 | `0.6733169771424713135…` | `yuhangshi888/zeta-simple-zeros-673316977` | 2026-08-14 | stdlib Python + a `sorry`-free Lean 4 audit layer, Zenodo DOI | REPORTED |
| 3 | `0.6733127422722459981…` | `trmdy/zeta-simple-zeros-673137` | 2026-08-11 | Arb via `python-flint`, replayed here | **VERIFIED** (§4) |
| 4 | `0.6732623755849780503…` | `AMTOPA/zeta-exact-pressure-673262` | 2026-08-12 | assembly only; imports `sxuff`'s finite run | REPORTED |
| 5 | `0.6732059784228011963…` | `sxuff/zeta-positioned-pressure` | 2026-08-11 | Python tables + C++ verifier | REPORTED |
| 6 | `0.673195198901…` | `npip99/zeta-zeros` | 2026-08-11 | Arb; verifier vendored from `trmdy` | REPORTED |
| 7 | `0.6731929114731422535…` | `tawanerguo-cn/zeta-simple-zeros` | 2026-08-11 | directed-MPFR + GMP exact LDL, Windows-only runner | REPORTED |
| 8 | `0.673130496905638432` | `hrx114514x/riemann-simple-zero-certificate` | 2026-08-16 | exact-rational / Bernstein; secondary figure of a ceiling programme | REPORTED |
| 9 | `0.6730732086087052768…` | `MichaelMobius/simple_zeros_of_the_riemann_zeta_function` | 2026-08-13 | Arb/FLINT, no top-level runner | REPORTED |
| **10** | **`0.6730529829896288869…`** | **`teal-sea/zeta-lab`, eight-point, ours** | 2026-08-02 | **Lean bridge proved, zero `sorry`s** | **VERIFIED** (§5) |
| **11** | **`0.6730295534796927114…`** | **`teal-sea/zeta-lab`, seven-point, ours** | 2026-08-02 | Lean bridge | **VERIFIED** (§5) |
| 12 | `0.6730266625438475497…` | `uwe-schwarz/zeta-simple-zeros-673026` | 2026-08-16 | Python + Lean build evidence; self-labelled unreviewed | REPORTED |
| 13 | `0.6730213619501665335…` | `learademacher/ai-refines-ai-zeta-bound` | 2026-08-11 | interval verifier, clean-room lemma reproduction | REPORTED |
| 14 | `0.673008527927…` | `ainta/zeta-simple-zeros` | 2026-08-11 | documented verifier | REPORTED |
|, | `0.672500703679411645734…` | `anthropics/zeta-23-lean`, Theorem D | 2026-08-06 | full Lean 4 + Mathlib, three standard axioms | REPORTED |

Every entry above `anthropics/zeta-23-lean` ships something runnable. **None of
them is a README assertion with no artifact behind it**, that was the outcome
this audit expected to find and did not. What separates them is not the presence
of a verifier but *what the verifier covers*: in every case the finite inequality
is machine-checked and the analytic bridge from that inequality to a statement
about zeros of zeta is taken on the authority of the Anthropic paper and Ainta's
stability refinement, unformalized. Ours is the exception in exactly one place:
the eight-point bridge is proved in Lean.

Claims deliberately excluded as different quantities, not comparable, and not
ranked: `JoshuaHKU/zeta-density-one-reproduction` (density one, 2026-08-23),
`JoshuaHKU/zeta-0.7947-reproduction` (0.7962), `Oliverds321/RH-72` (a Dirichlet
family average), `JBoss925/xi-prime-lower-bound-improvement` (ξ′, not ζ),
`zach7036/riemann-hypothesis-research` (multiplicity profiles). The first two
sit above the `0.6818286874638` bandwidth-one obstruction that
`anthropics/zeta-23-lean` itself proves, so they are either in a different
information class or wrong; this hunt did not examine them.

**No arXiv preprint exists for any of the `0.673x` follow-ups.** The whole race
is GitHub and one Zenodo DOI. The `riemannzeta.fun` leaderboard still records
`0.672500703679` as the standing record, so **not one of these fourteen claims
has passed a kernel-checked adversarial gate anywhere.** REPORTED.

## 3. Our barrier is not contradicted, and the reason is arithmetic before it is structural

Hunt #82 (`family_wall`) fixed `sup_n Phi_n <= 0.675142509660254` for the
`n`-point pressure family. The audit brief anticipated tension. **There is none,
and there could not have been:**

    leading public claim   0.6734164909714992949
    our family ceiling     0.675142509660254
    the leader sits BELOW the ceiling by 0.00172601868875              VERIFIED

The barrier is a ceiling. Every public claim, ours included, is under it. No
arrangement of these numbers produces a contradiction with Hunt #82. That is the
first and simplest thing to say, and it is worth saying before any structural
argument, because it does not depend on one.

**Structurally, `trmdy` is outside the family as well**, on two independent axes.
Compared definition by definition against `lean/bridge/Zeta23Ext/Bridge/Defs.lean`:

| | our family (`Bridge/Defs.lean`) | `trmdy` (`src/zeta_ext/`) | inside? |
|---|---|---|---|
| window | `Kfun x = ∫_{-1/2}^{1/2} cos(√2 t) cos(2πxt) dt`, the single term `ω = √2`, giving `HD 1 = 0.6725007036794116457` | `KernelSpec(coeffs=(1, 3322500/10⁹, −7609135/10⁹, 1190194/10⁹, −731476/10⁹, −1680572/10⁹, 1141360/10⁹), omega_pi_multiples=(2,4,6,8,10,12))`, i.e. `v(s) = cos(√2 s) + Σ_{k=1}^{6} c_k cos(2kπs)`, giving `H(v) = 0.67245704141454428878` | **NO** |
| pair weights | `F n p g` uses the uniform coefficient `2/(n − (j−i))` | arbitrary nonnegative rationals `a_ij` subject to `Σ_i a_{i,i+r} ≤ 2` per span | **contains ours** |
| block profile | `Phi_n` denominator `1 − c(m−(n−1))/m`, docstring: *"The block size `m` is capped by `c(m − (n−1)) ≤ 1`"* | `Φ_m(A) = 2√((m−1)A/m) − 1 + A/m` for `A ≥ m/(m−1)`, no cap | **NO** |

The window axis is decisive on its own. Their `H` is **lower** than ours by
`0.0000436622648673`: they gave up window constant to buy a kernel shape that
supports a larger floor `c`. VERIFIED: their `fast` lane, run here, prints
`H(v) = [0.67245704141454428878 +/- 4.25e-21]`.

The block-profile axis is decisive too, and visibly so: their seven-point
assembly runs at `m = 272` and their nine-point at `m = 177`, while our cap
`m ≤ (n−1) + ⌊1/c⌋` at their own `c` values allows only `m ≤ 230` and `m ≤ 172`.
They are operating past the cap our `Phi_n` requires. VERIFIED
(`c(m−6) = 1.185030` at their seven-point operating point, against the cap `≤ 1`).

The weight axis runs the other way and is worth recording: their uniform point
`uniform_weights(q) = 2/(q+1−(j−i))` **is our `F` exactly**, and our uniform
weights satisfy their span capacity with equality. Our functional is one vertex
of a polytope they optimise over. That is the one axis on which our family is a
strict special case of theirs.

**What this costs Hunt #82.** Nothing in its statement, and something in its
reach. The barrier remains true of the family it names. It does not cap the line
of attack the field is actually on, because that line changed the window and the
block profile. Whether the barrier's *mechanism*, bounding `c` by the
functional's value at a gap vector of total length `(n−1)/H`, survives the
substitution is not settled here. INFERRED, and flagged as the open question:
the `c`-bounding step is a statement about `F` and the window and looks
transportable, while the algebra that turned it into `H(1 + W)` used the linear
denominator that the `Φ_m` envelope replaces. Re-deriving the ceiling under the
envelope is the natural follow-on and was not attempted.

## 4. What was replayed, and what was not

Replayed here, from a scratch clone of `trmdy/zeta-simple-zeros-673137`, using
its own pinned `python-flint==0.9.0` (a wheel exists for this host's Python, so
nothing was built from source):

| check | result | label |
|---|---|---|
| `zeta-673200-verify fast`, window bounds, `H(v)`, exact deduction | passes, 0.6 s | **VERIFIED** |
| `min v ≥ 3/4`, `max v ≤ 1`, `v'(s)/s ≤ 0` on 8192 cells | `0.750213217018232`, `0.995632902191690`, `−0.776363621799489` | **VERIFIED** |
| `H(v) ≥ 3362285207/5·10⁹` | `0.67245704141454428878`, holds | **VERIFIED** |
| seven-point assembly `(mH − ηB_p(m−1))/(m−R)`, `m=272` | `0.6732001170127618568182`, matches their published `0.673200117012` | **VERIFIED** |
| refined assembly `(mH − (m−q)B_p)/(m−Φ_m(A))`, `m=235` | `0.6732425893558967029403`, matches their `0.673242589355` | **VERIFIED** |
| nine-point assembly, `m=177`, `q=8`, `ε=15211/2500000`, `p=1/2500` | `0.6733127422722459981438`, matches their headline `0.6733127422722459` | **VERIFIED** |
| span capacities `Σ_i a_{i,i+r}`, seven-point, exact rationals | all six exactly `2` | **VERIFIED** |
| span capacities, nine-point, exact rationals | all eight exactly `2` | **VERIFIED** |
| their unit suite, 23 tests | passes, 0.5 s | **VERIFIED** |
| `zeta-673200-verify main`, the finite inequality `F ≥ 891/200000` by exhaustive interval subdivision, 2,168,370 boxes to depth 50 | reproduces, 482.6 s, node count identical to theirs; one of the two table digests differs, see §7 | **MEASURED** |

Not replayed, and the reason: the nine-point run behind the headline
`0.6733127422722459` visits **116,272,426 nodes** by their own record. That is
out of reach on this host under the compute constraint, and it is the run that
carries the headline. **The headline figure is therefore assembly-VERIFIED and
finite-inequality REPORTED**, we checked that their published `ε = 15211/2500000`
assembles to their number, not that `ε` is a valid floor.

Also not replayed: every other repository in §2. `AMTOPA`'s leading claim was
read about, not run.

## 5. Our own constants, recomputed

An independent reimplementation of `Phi_n` from `Bridge/Defs.lean`, evaluated at
our own published floors, reproduces both of our figures:

    seven-point  c = 34697/10^7, p = 3400, m = 294 (= the cap)
        0.6730295534796927114     against published 0.6730295534796928     VERIFIED
    eight-point  c = 41763/10^7, p = 3200, m = 246 (= the cap)
        0.6730529829896288869     against published 0.6730529829896288     VERIFIED

Both optima sit **exactly at the cap** `m = (n−1) + ⌊1/c⌋`, which is the
structural reason the `Φ_m` envelope is worth something to us: the cap is
binding, and the envelope removes it.

**What the field's assembly would give us for free.** Applying the refined
assembly, `Φ_m` envelope plus window-in-frame pressure counting, to *our own*
existing floors, with no new search and no new window, changing nothing that is
already proved about `c`:

| our floor | our assembly | refined assembly | at | gain |
|---|---|---|---|---|
| seven-point `c = 34697/10⁷`, `p = 3400` | `0.6730295534796927` | `0.6730597710560009` | `m = 298` | `+3.0218e-5` |
| eight-point `c = 41763/10⁷`, `p = 3200` | `0.6730529829896289` | `0.6731067609396950` | `m = 250` | `+5.3778e-5` |

VERIFIED (`assembly_compare.py`, 300-bit Arb). This would move us from tenth to
ninth and no further; it does not close the `0.00036` deficit to the leader. The
deficit is in the floor `c`, not in the assembly. Recording it because it is the
cheapest available move and because it is honest about how little it buys.

Note also that the refined assembly is *not* proved here and is not proved in
Lean anywhere. Adopting it would trade our one genuine advantage, a bridge with
zero `sorry`s, for `5.4e-5`. **That trade looks bad and this hunt recommends
against it**, which is a position, not a finding.

## 6. Soundness read of `trmdy`'s verifier

The lab's actual specialty, applied to `src/zeta_ext/verify_general.py`,
`kernel.py`, `parallel.py` and `cli.py`, read in full.

**No defect found.** Specifically, and in the safe direction each time:

- **Acceptance is one-sided.** A box is discharged only when a rigorous *lower*
  bound on `F` over the box clears the target, and the comparison is against
  `_fmpq_upper(target)`, the target rounded **up**, so rounding cannot admit a
  box. `verify_general` raises `RuntimeError` at any terminal cell it cannot
  discharge; it never returns `verified=False`. Fails closed.
- **The interval tables are outward-rounded, and non-negative by construction.**
  `_nonnegative_lower` clamps the enclosure of `|K/K0|` at zero before squaring,
  so the `w`-table entries are `≥ 0`. This matters: `box_lower` multiplies table
  entries by the *lower* bound of each weight without a sign test, which would be
  unsound on a negative entry. It cannot be negative. The `w''` table can be, and
  there the code does use a sign-aware `signed_lower_product`. Checked
  deliberately; the pairing is correct.
- **The convexity gate is rigorous, with a float pre-filter.** The tangent prune
  is used only after an Arb LDL factorisation certifies the Hessian lower bound
  positive definite; `if not (pivot > 0): return False` is an Arb ball
  comparison, true only when the whole ball is positive. The `1e-12` float pivot
  threshold is a speed heuristic that can only *decline* to prune.
- **The `sinc` evaluation intersects two rigorous enclosures**: an alternating
  series with an explicit tail bound, and the closed form, and takes the
  intersection, which is rigorous whichever is tighter. The tail bound is
  `2 × the first omitted term`, honestly described in the source as crude; it is
  valid, since for `|z| ≤ 3/4` the term ratio is below `1/2` from `n = 2`.
- **The cyclic-shift and pressure cutoffs are exact rational reasoning**, not
  float. `cutoff_cell_count` is `⌈grid·target/pressure⌉ + 1`, with the `+1` a
  margin.
- **The parallel driver partitions initial boxes by `index % shard_count`, requires
  every shard to verify, and cross-checks the SHA-256 of both tables across
  workers.** It raises rather than returning a negative result. Sound.
- **The constants are thresholds, not answers.** `H_CERT = 3362285207/5·10⁹` and
  `FINAL_BOUND_RATIONAL = 1683/2500` are compared against computed enclosures
  (`h_val >= arb(H_CERT)`, `bound >= arb(FINAL_BOUND_RATIONAL)`), and the
  *assembly* then uses the rational `H_CERT`, which is below the computed `H(v)`,
  the conservative choice. **This is not the Ainta pattern**, where a constant
  was wired to the target. We looked for it specifically.

**Three things to hold against the top-line claim, none of them a code defect:**

0. **One of the two interval tables does not reproduce on this host**, and it is
   the one the tangent pruner rides on, the single component whose corruption
   could yield a false acceptance rather than a false failure. Every branch of
   the search nevertheless came out identical. Full accounting, both directions,
   in §7. VERIFIED here.


1. **The load-bearing new step is Lemma 2, not the code.** The refined assembly
   changes the pressure tax from `η·B_p·(m−1)/m` to `(m−q)·B_p/m` by a cyclic-shift
   averaging argument, a window of `q+1` consecutive points straddles a block
   boundary in exactly `q` of `m` offsets. That single off-by-`(q−1)` in the
   numerator is worth `+4.7e-5` of the `+4.25e-5` total refinement gain, i.e. it
   is essentially the whole refinement. The argument is standard-shaped and this
   hunt found nothing wrong with it, but it is not machine-checked anywhere, and
   it is exactly the kind of step where an off-by-one becomes a wrong theorem.
   Their own `docs/refined-deduction.md` credits it to `tawanerguo-cn` and says
   they re-derived it. VERIFIED that `Φ_m` is continuous at `A = m/(m−1)` and that
   the stated identity `A − Φ_m(A) = (√((m−1)A/m) − 1)²` holds, so `Φ_m(A) ≤ A`
   always, the envelope is at least internally consistent.
2. **Their own trust boundary is accurate and they state it.** `README.md`:
   *"this strengthened result is not yet end-to-end formalized in Lean"*, and the
   analytic interface comes from the Anthropic paper and Ainta. The repository
   describes its headline as *"a record candidate pending expert review"*. It does
   not overclaim. REPORTED.

The repository also credits its origin openly (a ChatGPT Work conversation with
OpenAI Codex, per `docs/provenance.md`) and defers authorship to the upstream
maintainer. Read alongside §2's AI-attribution pattern across the whole wave,
that is the norm in this field, not an outlier.

## 7. The long run

`zeta-673200-verify main --workers 6`, the exhaustive interval subdivision
proving `F ≥ 891/200000` over all nonnegative gap vectors for their seven-point
design at grid 4000. **It reproduces.** 482.6 s wall on this host, against
441.7 s on theirs at ten workers.

| field | their recorded run | this host | |
|---|---|---|---|
| `verified` | `True` | `True` | ✓ |
| `nodes` | `2168370` | `2168370` | ✓ |
| `pruned` / `splits` | `1084347` / `1084023` | `1084347` / `1084023` | ✓ |
| `maximum_depth` | `50` | `50` | ✓ |
| `initial_boxes` | `324` | `324` | ✓ |
| `cutoff_cells` | `48757` | `48757` | ✓ |
| `interval_pruned` | `625080` | `625080` | ✓ |
| `pressure_pruned` | `6131` | `6131` | ✓ |
| `tangent_pruned` | `453136` | `453136` | ✓ |
| `w_table_sha256` | `416ac41d…dbf9d06b` | `416ac41d…dbf9d06b` | ✓ |
| `w_second_table_sha256` | `2dc4743b66cb01cd1840ece1147a06659b42dc8fd9d7c5eff34428383b976bb0` | `e188bb3baa6d6ce69c354e95c8f20aa70529d670ae4bd2450b1e81702f0e1eb6` | **differs** |

MEASURED, the search is theirs; what this host contributes is an independent
replay of it.

**The `w''` table does not reproduce byte-for-byte, and that is worth stating
precisely, in both directions.**

Against them: the second-derivative table **is on the trust path** whenever the
tangent pruner is enabled, which it is by default and was here. A `w''` entry
that came out too *high* would let `arb_ldl_is_positive` accept a convexity
claim that is false, and the tangent bound derived from it would not be a lower
bound. Their own source knows this, the `use_tangent` flag is documented as a
hardening mode in which *"table errors can then only cause false failure, never
false certification"*. So the one component whose corruption could produce a
false acceptance is the one component that did not reproduce. Their repository
describes the nine-point figure as cross-host reproduced; on this host, one of
the two tables was not. Note that `tawanerguo-cn/zeta-simple-zeros` self-discloses
the same class of mismatch in its own derivative table, so this is a property of
the method, not of one repository. REPORTED for `tawanerguo-cn`, VERIFIED here
for `trmdy`.

For them, and it is the larger half: **every decision the search made came out
identical anyway.** Not merely the verdict, the node count, the split count,
the maximum depth, and each of the three prune counters separately, including
`tangent_pruned = 453136`, the counter that the differing table drives. A
regenerated `w''` table produced a bit-different digest and not one different
branch. The likely cause is arithmetic, not error: `w` needs only a lower bound
on `|K|` and barely cancels, while `w'' = 2(K'² + KK'')/K(0)²` cancels hard, so
its outward-rounded `binary64` floor is the component most sensitive to Arb's
internal precision choices and to the host's `libm`. This hunt did not isolate
the cause and does not claim one.

**The net reading is that this is a stronger reproduction than byte-identity
would have been,** because it shows the certificate does not depend on the exact
table the authors shipped. It is not, however, the reproduction their documents
claim, and a repository that pins a dependency specifically to make table hashes
comparable should be recording that one of its two hashes is host-dependent.

## 8. What our prior-art search missed, and why

This is the part of the record that is about us.

**What we missed.** Eleven public repositories carrying claims for this exact
quantity, ten of them above the figure we eventually produced, eight of them
created on 2026-08-11 and 2026-08-12, before our seven-point hunt opened. We
found `anthropics/zeta-23-lean` and `ainta/zeta-simple-zeros` and treated
`ainta`'s `0.673008527927` as the frontier to beat. It had been beaten by
`trmdy` within hours of being published, and by six more repositories within
four days.

**Why.** Four causes, in descending order of how much they cost:

1. **We searched for the prior art and not for the competition.** `ainta` and
   `zeta-23-lean` are what a search for *the standing result* returns. The wave
   that overtook it consists of repositories with no stars, no description, no
   preprint and no press, `npip99/zeta-zeros` has an empty description and zero
   stars while sitting at `0.673195`. Nothing about them surfaces unless you
   enumerate recent repositories by topic and date, which we never did.
2. **We took the leaderboard as the field.** `riemannzeta.fun` still shows
   `0.672500703679`, and press coverage stops at Anthropic's announcement. Both
   are accurate about *formally accepted* results and both are eight claims
   behind the actual state of GitHub. We read the absence of a leaderboard entry
   as the absence of a claim.
3. **We looked once, at the start, and never again.** The seven-point hunt ran
   over days during which the field moved. There was no re-check before the
   eight-point work, and none before the barrier hunt.
4. **We had no forward-citation pass.** `trmdy`'s own README carries a table
   naming `tawanerguo-cn` and `npip99`, and `AMTOPA`'s work is built on `sxuff`'s.
   Enumerating the forks of `zeta-23-lean` and reading the reference tables of
   the one competitor we did know about would have found most of the wave in a
   single pass. That pass cost one subagent and under seven minutes when it was
   finally run.

**What follows.** A recurring enumerate-by-date sweep, not a one-time search, and
the rule that a frontier figure in a `MISSION.md` carries the date it was checked.
Neither is implemented here; both are recorded as obligations rather than
pretended into a script.

**What does not follow.** None of this invalidates any result this laboratory
produced. The seven- and eight-point constants are what they are, the Lean bridge
is proved, and Hunt #82's barrier stands. What the miss cost is *position*: we
spent a week reaching tenth place while believing we were reaching first, and we
built a barrier around a family the field had already left.

Nothing here bears on RH (`docs/08`).
