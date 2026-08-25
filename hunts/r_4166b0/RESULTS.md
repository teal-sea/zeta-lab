# RESULTS: Hunt R-4166B0 (#109): the soundcalc numbers reproduce; the pins that name their sources do not

Read 2026-08-24. `ethereum/soundcalc` pinned at commit
`d9078d64c9c3ae15b0931f6d249b2dc073194f15` (2026-07-23). Vendor sources read at
the commits and tags the TOMLs name, and again at each vendor's current
release. Every artifact fetched is under `data/` with its sha256 and byte count;
`probe.py` re-runs the whole thing.

Labels are Hunt #80's: **VERIFIED** = re-derived here from the pinned artifacts;
**REPORTED** = stated by the artifact and taken as given; **INFERRED** = our
reading of what a measurement means.

Every statement below is scoped to **the artifact at the pinned commit**.
Nothing here is a statement about a vendor, a team, or the security of any
deployed system, and nothing here bears on RH (`docs/08`).

**No unit is held.** No unit produced a REPRODUCTION `mismatch` at all, so the
disclosure hold in `MISSION.md` never engaged. Everything found is published
below in full.

## The headline

**Every soundness parameter that could be re-derived, re-derived exactly.**
Across four units where the vendor's own source was reachable and the
derivation did not need a build, **51 of 51 numeric fields agree to the value**:
RISC0 7/7, Miden 5/5, OpenVM 9/9, SP1 30/30. Not one number was wrong. SP1's
thirty were derived twice, at two different vendor refs, and agree at both;
they are counted once. (`results.json` → `field_agreement_total`.)

**The failures are all in the pins, not the numbers.** Of eight provenance
pins the TOMLs name, **two do not resolve at all**: Airbender's cited commit is
not in the vendor's repository, and the branch the one executable regeneration
script clones has been deleted. A third, SP1's, resolves to a tag that does not
contain the generator the TOML says produced it.

**The strongest single result**: Airbender's parameters are **byte-identical**
to what the vendor's own generator emits at its current tip, six months after
the date stamped in soundcalc's copy, recovered at one hand intervention,
despite the cited commit being unfindable.

## The two verdicts, per unit

Kept apart throughout, as the mission requires. A drift is not a failed
reproduction and is not reported as one.

| unit | published (summary.md) | REPRODUCTION | FRESHNESS | interventions |
| --- | --- | --- | --- | --- |
| Airbender | **67** bits (JBR) | **unresolvable-pin** | **unchanged**, values byte-identical to the vendor's generator output at `dev` tip | 2 |
| Miden | *absent from summary* | **match**, 5/5 cited fields | **unable-to-regenerate**, cited file gone at v0.29.2 | 1 |
| OpenVM | **100** bits (UDR) | **match**, 9/9 fields over 3 circuits | **drifted**, 1.5.0 → v2.0.2 | 1 |
| OpenVM2 | **100** bits (mixed) | **no-generator** | **drifted**, 2.0.0 → v2.0.2 | 0 |
| Pico | **53** bits (JBR) | **unpinnable**, mutable branch, no commit | **drifted**, branch @ 2026-02-19 → v2.1.2 | 0 |
| RISC0 | *absent from summary* | **match**, 7/7 fields | **unchanged**, cited blob identical | 1 |
| SP1 | **100** bits (UDR) | **match**, 30/30 constant-derived; **unpinnable** at the named version | **unchanged**, every constant identical at v6.4.0 | 3 |
| Venus | **128** bits (JBR) | **no-generator** | **drifted**, 0.1.6 → v0.2.5 | 0 |
| ZisK | **128** bits (JBR) | **unable-to-regenerate**, script's branch deleted | **drifted**, 0.16.1 → v1.1.0-alpha | 1 |
| zkDTVM | **128** bits (mixed) | **no-public-source** | **unable-to-regenerate** | 0 |

VERIFIED throughout. The published bits column is REPORTED (it is soundcalc's
own figure at the pinned commit, reproduced byte-for-byte in stage 0).

**Vocabulary.** `match` = the fields checked follow from the vendor's own file
at the ref the TOML names. `unresolvable-pin` = the commit the TOML cites does
not exist in the vendor's repository. `unpinnable` = the TOML names a version
but nothing that identifies a unique tree. `no-generator` / `no-public-source` =
no documented regeneration path exists. `unable-to-regenerate` = a path is
documented and no longer runs.

## Stage 0: soundcalc reproduces its own reports, for eight of ten units

`python3 -m soundcalc` at the pinned commit, run unmodified on the checked-in
TOMLs, leaves `reports/` **byte-identical**, `git status --porcelain reports/`
is empty (VERIFIED). Kill condition 1 does not fire.

Two qualifications, both VERIFIED:

**It writes ten reports and the directory holds twelve.** `reports/risc0.md` and
`reports/miden.md` are **not regenerated**. Both units are dropped by the loader
for a missing `num_constraints`, so those two published reports are held-over
artifacts from an earlier commit, not output of the code at HEAD. They are the
two units absent from `summary.md`. The reports are byte-identical after a rerun
because nothing rewrote them, which is a different fact from reproducing.

**A config soundcalc cannot read produces a missing row, not a failure.** The
loader catches `KeyError`, prints a note, and continues. This is by design, and
it is the mechanism that leaves two stale reports in the tree, so it is worth
stating: absence from `summary.md` is not evidence a unit was analysed and found
wanting; it can mean the file did not load.

**`toml` is an undeclared dependency.** `pyproject.toml` sets
`dependencies = []`, and `soundcalc/zkvms/zkvm.py` imports `toml` (the PyPI
package, not stdlib `tomllib`). A clean interpreter raises
`ModuleNotFoundError`. This is the one intervention that is global rather than
per-unit, and it is the first thing an outside reproducer hits.

## The pins

Asked of git rather than of an API: `git fetch --depth 1 <url> <sha>` makes the
server resolve the object, and a server without it answers `not our ref`.

| unit | pin cited | resolves |
| --- | --- | --- |
| Airbender | commit `632d19b946d23180c2548626cbff4dbcce8ddb04` | **no** |
| Miden | commit `fde5256c7ea99112e7dc2677b4c57ad824f63dcb` | yes |
| RISC0 | commit `ebc18c770c4dd5a8e8dfdca1297edb181848405f` | yes |
| OpenVM | commit `0c33328916d95047325b60a8044ecf9468db84bb` | yes |
| OpenVM | commit `972f5dbecb6ab3ff7e3e978e9087235ad17c1de9` | yes |
| SP1 | tag `v6.1.0` | yes (but see below) |
| Pico | branch `soundcalc` | yes (a branch, not a commit) |
| ZisK | branch `pre-develop-0.17.0` of `pil2-proofman` | **no** |

Six of eight resolve; two do not (VERIFIED).

## Unit by unit, where there was something to find

### Airbender: the cited commit is gone, and the numbers are current anyway (VERIFIED)

`airbender.toml`'s header names commit `632d19b9…`, created 2026-02-24, produced
by `tools/pow_config_generator`. That commit is not in
`matter-labs/zksync-airbender`: the git server answers
`upload-pack: not our ref`, and GitHub's commit API returns 422. It is not in a
fork the code-search index can see either.

The generator does exist, on the `dev` branch (not `main`), and **it checks its
own output in** at `tools/pow_config_generator/airbender.toml`. That file is the
vendor's current answer, and diffing it against soundcalc's copy gives:

* two header lines (`Created: 2026-04-20`, `Commit: b4817570…`), and
* one key, `protocol_family = "FRI_STARK"`, which the vendor now emits under
  `[zkevm]` and soundcalc's loader expects under `[[circuits]]`.

**Nothing else differs. Every soundness parameter is identical.** Fed to
soundcalc unmodified, the vendor's current file is *skipped* (`missing
'protocol_family'`) and Airbender silently vanishes from `summary.md`. Move that
one key, one hand intervention, and soundcalc reproduces `reports/airbender.md`
and `reports/summary.md` **byte-for-byte**, 67 bits (JBR) included.

So: the pin is unresolvable and the accounting is current. Those are different
statements and the table keeps them apart. INFERRED, offered as a reading and
not as a fact: a squashed or force-pushed branch explains an unfindable commit
far more economically than anything else, and the identical parameters are
consistent with that.

### SP1: the version string does not name a tree (VERIFIED)

`sp1.toml` says `version = "6.1.0"` and that it was *"Auto-generated by
`cargo run --release -p sp1-prover --bin gen_soundcalc_toml`"*. At tag `v6.1.0`,
`crates/prover/scripts/gen_soundcalc_toml.rs` **does not exist**, the file was
added on 2026-04-22 (`0c027f9f`, PR #2735), eleven days after v6.1.0 was
released (2026-04-11). The documented reproduction path cannot be run at the
version the TOML names.

The generator reads its version from `env!("CARGO_PKG_VERSION")`, and the
workspace version string stayed `6.1.0` from the tag through at least
2026-04-28. So the TOML was generated from a main-branch tree carrying the
string `6.1.0`, which is a window of commits and not the release. **The pin is a
crate version, not a tree.** Nothing in the TOML narrows it further.

That leaves the numbers, and they are excellent. `gen_soundcalc_toml.rs`
computes most of its output from named constants plus arithmetic, so the
constant-derived half can be re-derived from source without a Rust build.
Reimplementing that arithmetic in Python (`sp1_expected` in `probe.py`) and
reading all sixteen constants from the five vendor files that hold them:

**30 of 30 fields agree**, at both refs tested, the tree where the TOML was
generated and the vendor's latest release v6.4.0. Including the two that are
real arithmetic rather than a copy:

* `core.dense_batch = 193` = `ELEMENT_THRESHOLD / 2^CORE_LOG_STACKING_HEIGHT + 1`
  = `((1<<28)+(1<<27)) / 2^21 + 1`.
* `num_queries` 124 (core, compress) and 94 (shrink), from
  `ceil(-(SP1_TARGET_BITS_OF_SECURITY - grinding) / log2(0.5 + rate/2))` with
  target 100 and grinding 16 / 22.

**Not checked, and named rather than guessed**: `trace_columns`,
`num_constraints`, `num_lookups_M`, `num_columns_S`. The generator derives these
from `machine.shape()` at runtime, and the only documented route is the Rust
build, which this run did not do (compute discipline: no heavy builds here).

FRESHNESS is therefore **unchanged** on a stated scope: every one of the sixteen
constants is identical at v6.4.0 and at the generation tree. The prior in the
brief, that the checked-in TOML predates v6.4.0, is correct about the version
string and, on the half that can be checked from source, makes no difference to
a single number.

### OpenVM: the values reproduce, two of three citations are stale (VERIFIED)

`openvm.toml` cites a source line per circuit. Read at the commits cited:

| circuit | citation | line actually at that ref | `num_queries` there | in the TOML |
| --- | --- | --- | --- | --- |
| app | `0c333289` L183 | `num_queries: 193,` | 193 | 193 ✓ |
| leaf | `972f5dbe` L65 | `1 => FriParameters {` | 100 | 193 ✗ |
| internal | `972f5dbe` L71 | `2 => FriParameters {` | 44 | 118 ✗ |

The leaf and internal citations point at `972f5dbe` (2025-12-08) and at
`standard_fri_params_with_100_bits_**conjectured**_security`, whose arms carry
100 and 44. The TOML's 193 and 118, with grinding 20/20 and 16/20, are exactly
`standard_fri_params_with_100_bits_security(1)` and `(2)` at `0c333289`, the
commit the *app* circuit cites, lines 183-185 and 190-192.

So all three circuits reproduce from one function at one commit, and two comment
URLs were not updated when the parameters were. The TOML uses the **higher**
query counts, so this is a stale citation and not a wrong number.

One further note, INFERRED: `0c333289` is dated 2026-02-28, twenty days *after*
OpenVM v1.5.0 was released (2026-02-08). The TOML declares version 1.5.0 and
sources its FRI parameters from a stark-backend commit that postdates it.

### RISC0: reproduces from the notebook, and the notebook has never been revised (VERIFIED)

`risc0.toml` cites one artifact, `risc0/zkp/src/docs/soundness.ipynb` at
`ebc18c77`, dated September 2024. Parsing its code cells:

| TOML field | value | notebook |
| --- | --- | --- |
| `rho` | 0.25 | `k = 2`, `rho = 1/(1<<k)` |
| `trace_length` | 2097152 | `h = 21`, `H = 1 << h` |
| `num_queries` | 50 | `s = 50` |
| `num_columns` | 279 | `num_control 16 + num_data 223 + num_accum 40` |
| `opening_points` | 9 | `max_combo = 9` |
| `batch_size` | 283 | `L = C + 4` |

Six read fields, plus the FRI schedule, which is arithmetic on them:
`D = trace_length/rho = 8388608`, folded by 16 four times, lands on
`fri_early_stop_degree = 128`. **7/7 agree.** Two deviations are documented at
the point of use (`air_max_degree = 4` against the notebook's `max_degree = 5`,
because DEEP-ALI uses `d-1`), and `hash_size_bits` carries the TOML's own
`TODO: check if that is actually true`.

FRESHNESS is the interesting part. The notebook's blob sha is
`c8c12fed0a51cdcadfb6defb651b39389bf3721c` at the pinned commit **and** at
v3.0.6, and it has exactly **one commit in its entire history**, the one that
added it, 2024-09-12. The cited artifact is verifiably unchanged.

That is a narrower claim than it looks, and it should not be read as reassurance
(INFERRED): "the cited artifact is unchanged" here means "a September 2024
document nobody has revised", while the vendor has shipped through v3.0.6 and
tagged a v5.0.0 release candidate. An unchanged source and an unchanged system
are not the same thing, and this measurement can only see the first.

### Miden: the cited constant reproduces, and it no longer exists (VERIFIED)

`miden.toml` cites `RECURSIVE_96_BITS` in `air/src/options.rs` at `fde5256c`.
The constructor takes positional arguments; mapping them:
`WinterProofOptions::new(27, 8, 16, Quadratic, 4, 127, Algebraic, Horner)`.

`num_queries = 27` ✓, `rho = 0.125` from `blowup_factor = 8` ✓,
`grinding_query_phase = 16` ✓, `field = "Goldilocks^2"` from `Quadratic` ✓,
folding factor 4 ✓. **5/5 agree**, with one documented deviation
(`fri_early_stop_degree = 128` against the constant's `127`, stated in the TOML).

FRESHNESS: **unable-to-regenerate**. At v0.29.2 (2026-08-20) `air/src/options.rs`
returns 404; the file was moved on 2026-01-22 (*"move … ProvingOptions to
`miden-prover`"*), and neither `RECURSIVE_96_BITS` nor `REGULAR_96_BITS` is
found anywhere in the repository today. Three weeks before that move, on
2026-01-02, Miden *"migrate[d] underlying proving system to Plonky3"* (#2472) , 
after the cited commit. The cited source is superseded, not merely older.

Note also that four of `miden.toml`'s inputs carry the TOML's own
`XXX need to check the numbers below by running the prover` or `XXX ???`. The
file is explicit that it is provisional, and this hunt does not upgrade it.

### ZisK: the only executable regeneration script in the repository, and it pins nothing (VERIFIED)

`soundcalc/zkvms/zisk/regenerate_zisk_config.sh` is the one place the repository
ships a runnable regeneration path. Read at the pinned commit, it:

1. runs `rustup default stable`, a moving toolchain;
2. `git clone --branch pre-develop-0.17.0 …/pil2-proofman`, a branch, not a
   commit, and **that branch no longer exists** (0 matches among the remote's
   417 heads; `pre-develop-0.17.0-v2`, `-0.18.0` and `-0.19.0` survive);
3. `wget …/zisk-provingkey-**0.16.0**.tar.gz`, a proving key whose version is
   not the version `zisk.toml` declares (`0.16.1`). The tarball is still served
   (HTTP 200).

So the script does not run today, and had it run it would not have been
reproducible tomorrow: two of its three inputs are moving references. The
mechanism survives, `proofman-cli soundness` is still present in
`pil2-proofman`, so this is a broken pin, not a removed capability.

FRESHNESS is **drifted** on any reading: `zisk.toml` declares 0.16.1
(2026-03-20) and the vendor is at v1.1.0-alpha (2026-08-18), with 0.17.0,
0.18.0 and 1.0.0-alpha in between.

### Venus: the header's equivalence claim does not hold (VERIFIED)

`venus.toml`'s header states: *"Cross-validated against ZisK upstream — identical
soundness parameters."* Both files carry 44 circuits under the same names in the
same order. Comparing field by field:

* three circuits (`SpecifiedRanges`, `VirtualTable0`, `VirtualTable1`) differ
  only in a `group` label, bookkeeping;
* one circuit, **`Final`**, differs numerically in seven fields:
  `num_columns` 135 vs 114, `num_columns_witness` 80 vs 68, `num_columns_fixed`
  55 vs 46, `num_constraints` 161 vs 154, `batch_size` 158 vs 139,
  `gap_to_radius`, and one lookup's `num_lookups_M` 33 vs 24.

**This moves no published security level, and it is published here for that
reason.** Every per-regime *total* is identical between the two reports, the
`Final` circuit is UDR 63 / JBR 128 in both, and each system's headline is 128
bits (JBR). The only bit that moves is the ALI component, 168 for Venus against
169 for ZisK, and ALI is not the binding term: the query phase binds, at 63 and
128. Venus's own figure follows from Venus's own parameters. What fails is the
header's claim of equivalence, not either published number.

The judgment that this is publishable rather than held is stated explicitly so a
reader can check it: the disclosure rule holds a REPRODUCTION `mismatch` whose
discrepancy could plausibly affect soundness. Venus's REPRODUCTION verdict is
`no-generator`, the TOML says its parameters were *"derived from Venus v0.1.6
proving key"* with no reproducible path, so no reproduction mismatch exists,
and the discrepancy that does exist provably does not move a bit.

### OpenVM2, Pico, zkDTVM: no reproduction path was found

* **OpenVM2** (`version = "2.0.0"`): no source citation of any kind in the
  file. `no-generator`.
* **Pico**: the header cites *"the `soundcalc` branch of pico"*. The branch
  exists (head `d4bf474d`, 2026-02-19) and carries the extraction output
  (`soundcalc-lookups-info.log`, timestamped the same day). No commit is
  recorded in the TOML, so what a rerun would reproduce depends on where a
  mutable branch points. `unpinnable`.
* **zkDTVM**: names `zkdtvm-suite/whir_config_koalabear_ext5.json` as its
  *"runtime source of truth"*. No public repository under `AntChainOpenLabs`
  carries that file. `no-public-source`, stated as not-found rather than
  not-existing.

## The vendor's own declared targets, recorded only

The mission asks for the vendor's published bits beside soundcalc's figure.
Where a vendor declares a target *in its own source*, that is a better artifact
than a blog post, so these are read from the pinned trees:

| unit | vendor's own declaration | where | soundcalc |
| --- | --- | --- | --- |
| SP1 | `SP1_TARGET_BITS_OF_SECURITY = 100` | `crates/primitives/src/fri_params.rs` | 100 (UDR) |
| OpenVM | `standard_fri_params_with_100_bits_security` | `stark-backend` `fri_params.rs` | 100 (UDR) |
| Miden | `RECURSIVE_96_BITS`, doc-commented *"96-bit conjectured security"* | `air/src/options.rs` @ `fde5256c` | report only, not in summary |
| zkDTVM | *"Target: 128-bit round-by-round soundness"* | `zkdtvm_v080.toml` | 128 (mixed) |

**Read this table with its scope.** A vendor constant labelled for *conjectured*
security and soundcalc's UDR/JBR regimes are different accountings, and a gap
between them is the expected, known thing the whole soundcalc exercise exists to
quantify. It is not a defect and this hunt did not establish it, it is
soundcalc's own published position at the pinned commit (REPORTED). No delta is
computed here, and none should be read into the table.

## The checks can fail: six planted faults, six reds

A check that cannot fail is not a check. Each fault is planted in a copy and the
stage that should notice it is re-run (`probe.py control`).

| planted fault | stage | expected | observed |
| --- | --- | --- | --- |
| `risc0.toml` `num_queries` 50 → 51 | RISC0 derivation | mismatch | **mismatch** |
| `miden.toml` `num_queries` 27 → 28 | Miden derivation | mismatch | **mismatch** |
| `sp1.toml` core `num_queries` 124 → 123 | SP1 derivation | mismatch | **mismatch** |
| `openvm.toml` internal `num_queries` 118 → 117 | OpenVM derivation | mismatch | **mismatch** |
| `airbender.toml` `num_queries` + 1 | stage 0 | does-not-reproduce | **does-not-reproduce** |
| `venus.toml` given ZisK's circuits verbatim | identity claim | claim-holds | **claim-holds** |

Six of six (VERIFIED). The last is a positive control: it fires only if the
comparison would have said *"identical"* had the files actually been identical,
which is what stops `claim-does-not-hold` from being vacuous.

**Two earlier lesions failed and are worth keeping.** The first tampered with
`reports/summary.md` and expected stage 0 to notice; it did not, because stage 0
*regenerates* the reports before diffing, so a tampered output is overwritten
before it can be seen. That is a real scope statement about this check and not a
bug in it: **stage 0 detects a perturbed input, never a perturbed output.** An
archive that wanted to publish a number its own inputs do not produce would be
caught; an archive whose committed report was edited after generation would not
be, by this check. The lesion was rewritten to move a TOML instead. The second
was a botched positive control that patched six of eight differing fields; it
was replaced with a structural one.

## What this cost, and the transfer measure

The mission's transfer measure is **hand interventions per unit**, with "above
about two per unit, the procedure has not crossed the domain yet."

| unit | interventions | what they were |
| --- | --- | --- |
| SP1 | 3 | locate the generator (not named in the TOML); locate the five vendor files holding its imported constants; reimplement its arithmetic in Python, the Rust build being out of scope |
| Airbender | 2 | find the vendor's generator directory and its checked-in output after the cited commit failed to resolve; move one key |
| Miden | 1 | map positional constructor arguments to field names |
| OpenVM | 1 | find the function that actually carries the values after two citations missed |
| RISC0 | 1 | parse notebook code cells; apply the two documented deviations |
| ZisK | 1 | establish that the pinned branch is deleted |
| OpenVM2, Pico, Venus, zkDTVM | 0 | no path existed to intervene in |

**Mean over the six units where a reproduction path existed at all: 1.5.** Plus
one global intervention (installing the undeclared `toml`) that is not
attributable to any unit.

This is a judgment count, not a machine count, nothing in `probe.py` measures
it, and a different worker would round some of these differently. Recorded as
INFERRED, with the itemisation above so the reader can re-count.

**On cost.** The brief budgeted ~12M agent tokens, 2-3 days wall clock and up to
10 runner-hours for vendor builds. The realised figure is far under that on
every axis: a single session, well inside the six-hour bound, and **zero build
minutes**. The reason is the finding above, the constant-reading route made
every build unnecessary, because a generator that computes its output from
named constants can be re-derived from source. That was not foreseen in the
budget and it is the main economic result of this instance.

## What could not be settled

* **The build-dependent half of SP1** (`trace_columns`, `num_constraints`,
  `num_lookups_M`, `num_columns_S`, four fields × three circuits). These need
  `cargo run --release -p sp1-prover --bin gen_soundcalc_toml` and are the one
  place a runner-hour would buy something this run did not get.
* **Pico, Venus, OpenVM2, zkDTVM** were not reproduced at all, and that is a
  property of the artifacts rather than of the budget: three name no source and
  the fourth names a private one. Adding compute does not change any of them.
* **ZisK** was not reproduced because its script's branch is gone. Repointing it
  at `pre-develop-0.17.0-v2` is a guess about intent, which the huntspec's kill
  conditions forbid, so it was not done.
* **Airbender's cited commit** could not be located anywhere public. Nothing
  distinguishes "squashed away" from "never pushed" from the outside.

## The doors

This hunt measured no ceiling: the brief explicitly excludes retuning and
ceiling computation from this instance, so `AGENTS.md`'s door-analysis
obligation does not attach. The nearest thing to a door here is the loose thread
list below.

## Close the loop

Per the operator's correction: this task came from `zeta-lab` issue #140, not
from a function in `harness/`. No `AttackOutcome`, `GuardRecord` or grave
corresponds to it, and none was manufactured to satisfy the instruction.

The ledger items that **are** genuinely open, read from
`harness/departments/` at this commit and named here rather than closed:

* `rf-c003-window`, no blind attack recorded; the review is not standing.
* `k2-far-constant-depth1`, no blind attack recorded; the review is not
  standing.
* guard `tests/test_doors.py`, power undemonstrated; no mutant recorded.
* Unguarded graves: none.

`harness/VERDICT.md` stands, and nothing here extends the demoted framework.

## Loose threads

Noticed and not chased.

1. **`reports/risc0.md` and `reports/miden.md` are unreachable output.** Neither
   can be regenerated by `python3 -m soundcalc` at HEAD, so two published
   reports in a repository whose whole point is executable accounting are
   held-over artifacts. *Why it might matter*: a reader has no way to tell,
   from the repository, which reports the current code produces. *First step*:
   compare each stale report against what the current code would emit if the
   missing `num_constraints` were supplied, and see whether the held-over
   numbers still hold.

2. **A skipped unit is silent in the artifact that gets read.** The loader's
   `KeyError` note goes to stdout; `summary.md` just has one fewer row, and the
   two skipped units are exactly the two with stale reports. *Why it might
   matter*: it is the same failure shape as Hunt #108's missing logs, absent
   evidence that presents as an absent row. *First step*: check whether any
   consumer of `summary.md` (the sprint's own reporting) treats a missing row as
   "not yet analysed" rather than "did not load".

3. **The soundcalc test suite was never run here.** `tests/` exists
   (`test_circuit.py`, `test_fri.py`, `test_grinding.py`, `test_swirl.py`,
   `test_swirl_loaders.py`) and this hunt tested the *inputs* to the calculator,
   never the calculator's mathematics. *Why it might matter*: every verdict above
   is conditional on soundcalc's arithmetic being right, and that was assumed.
   *First step*: `pytest` at the pinned commit, then ask what fraction of the
   soundness formulas the suite actually exercises.

4. **The `dummy_whir` unit is a fixture inside the published set.** It generates
   `reports/dummywhir.md` alongside the real ones and is excluded from
   `summary.md` by hand. *Why it might matter*: a demonstration artifact living
   in the same directory as vendor submissions is a naming hazard, nothing more.
   *First step*: none urgent; note it if the report directory is ever consumed
   programmatically.

5. **Two of eight pins are dead after roughly six months.** That is a decay rate,
   from one observation, and this hunt has no baseline to compare it against.
   *Why it might matter*: if it is typical, an M3 deadline in December 2026 will
   be met with an accounting whose sources have partly evaporated. *First step*:
   re-run `probe.py pins` monthly; three points make a rate, one does not.
