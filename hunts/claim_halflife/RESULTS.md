# Results: what happens to a claim after it is recorded

**2026-09-10. Grade: measured, and one headline is withdrawn by its own
control.** This is not mathematics and nothing in it bears on RH (`docs/08`).
It measures the laboratory, and the standing rule in `meta/README.md` applies:
a session with no mathematics and a tidy ledger produced nothing.

## 1. The verdict

    case-log entries in the corpus                    95
    entries asserting a finding                       80  (84.2%)
    entries named by any test                         19  (20.0%)
    entries never touched again                       22  (23.2%)

    (hunt, test) pairs where the hunt has a mutable
      numeric artifact and the test could be scored   25
      defending at least one of its numbers           19  (11 by value, 8 byte-pinned)
      reading none of them                             6

    strict revisions found by the classifier          73
      that installed a test in the same commit         1
    median latency from the hunt's first commit        1 day
    mean 1.8 days, longest 13

    the classifier's agreement with a blind hand audit  53% before repair,
                                                        73% after, on a
                                                        disjoint sample

Two things to read together. **The guard surface is narrow and, where it
exists, it mostly holds**: one recorded claim in five is named by any test at
all, and among the pairs that can be tested, three quarters defend at least one
number against a ten percent mutation. And **the tree almost never installs a
guard at the moment it corrects itself**: one of seventy-three revisions.

And a rate that had to be withdrawn, repaired and re-earned before it could be
stated at all: **15.3% of later commits revise a claim the hunt had already
recorded**, corrected for the measured precision and recall of the classifier
that found them. See section 5, which is the longer half of this hunt.

## 2. The corpus, and the thing that nearly ruined it

The unit is one entry in `hunts/README.md`'s case log, because that is the
granularity at which this tree decides what it believes. There are 95, frozen
at `2da62eb`, the tip of `main` before this hunt existed, so that this hunt does
not appear in its own denominator.

The container this ran in started with a **shallow clone**: 262 commits reaching
back to 2026-08-13, against 1084 reaching back to 2026-08-01. Nothing announced
it. Every count below would have been taken from a corpus missing three quarters
of its own history, and the study would have reported a number and called it the
answer.

Reconstructed deterministically by restricting the corpus to the newest `k`
commits:

| history depth | later commits seen | entries never revisited |
|---:|---:|---:|
| full (1084) | 414 | 22 (23.2%) |
| 800 | 367 | 23 (24.2%) |
| 500 | 229 | 23 (24.2%) |
| **262, the container's own** | 168 | 29 (30.5%) |
| 100 | 72 | 91 (95.8%) |

The live shallow measurement, taken once before `git fetch --unshallow` and not
reproducible afterwards, read 34 (35.8%).

This tree has met the hazard before. `tests/test_dossier_hardy_z.py` was found
in August comparing a file's date against a shallow checkout's own date, which
is true on the day of a re-observation and false every day after; the fix landed
was to ask `git rev-parse --is-shallow-repository` and skip with a reason.
`HANDOFF.md` records the better fix as "prepared and NOT landed": checking out
CI with `fetch-depth: 0` so the check runs instead of skipping. **It is still not
landed.** `checks.yml` has it; `tests.yml` and `full.yml` do not.

## 3. Guard coverage, measured by planting faults

A test naming a hunt is presence. Whether it would notice the hunt's numbers
changing is power, and the two are different.

Three rungs, each artifact the test names, all of them at once:

* **null**, a byte-identical rewrite through the same serialiser. If the test
  goes red here the artifact is **byte-pinned**, which is the strongest guard
  available: all eight such tests were checked and each computes a hash.
* **all leaves**, every numeric leaf in every artifact the test names scaled by
  1.1. A test that stays green is reading none of that hunt's numbers.
* **per leaf**, for the ones that fire, to estimate what fraction is held.

| outcome | count |
|---|---:|
| byte-pinned | 8 |
| reads numbers (fires on a 10% mutation) | 11 |
| reads none of them | 6 |
| hunt has no mutable numeric artifact | 14 |

The first version of this ladder mutated only the *first* artifact each test
names, and reported that 9 of 24 tests read the artifact they name. Twenty of
twenty-six targets name more than one artifact, up to thirty-seven, so that
number was measuring the instrument. It is corrected above and the earlier run
is kept in `artifacts/lesion2.json` rather than deleted.

**The ladder also broke the tree while measuring it.** Its first version
restored mutated files with `git checkout --`, a concurrent `git` in the same
working tree made one restore fail with exit 128, and a mutated artifact was
left behind until it was noticed. The operating playbook this laboratory keeps
already has the rule, "never background a job that does `git checkout` in the
shared tree". It is now obeyed rather than quoted: the ladder holds the original
bytes in memory and asserts the restore round-trips.

## 4. What the tree does when it corrects itself

Of 73 strict revisions, **one** touched `tests/` in the same commit.

This is the measurement that survives the classifier's problems, because it is
lopsided enough that classifier error cannot rescue it. Suppose only 40% of the
73 are real revisions, the precision measured against the blind audit before
repair. That is still 29 real corrections and at most one installed guard. A
false-negative rate does not help either: missing revisions means there were
more of them, not fewer.

Set against it: every `HANDOFF.md` record in this tree carries a field called
`Now caught by:`, and the tree's own operating playbook says a check that has
never fired has no power. The practice and the doctrine disagree, and the
disagreement is one line wide and 73 events deep.

Correction is fast. Median latency from a hunt's first commit to a revision of
its own claim files is **one day**, mean 1.8, longest 13.

## 5. The headline that had to be earned twice

The first version of this hunt reported that 21% of case-log entries were later
revised, at three strictness levels that agreed to within five points.

Thirty rows of that classification, stratified half positive and half negative,
were handed to a separate agent with the key moved out of the repository, told
to judge each commit from its own diff. **It agreed with the classifier on 16 of
30.** Precision 0.40, recall 0.55, against a balanced sample. That is close
enough to chance that the rate cannot be reported, and it is reported here as
withdrawn rather than quietly rescaled.

The audit's row notes named two structural defects, both defects on their own
terms rather than borderline judgement calls:

1. **The hunt's opening was counted as a revision of itself.** The first commit
   was taken to be the first one touching any of five hard-coded filenames, so a
   hunt that landed a `MISSION.md` first and its `RESULTS.md` second had that
   second commit scored as a later revision. Two sample rows are exactly this.
2. **A withdrawal in a differently-named file was invisible.** One row adds
   `BLOCKPOS-WITHDRAWN.md`, headed "WITHDRAWN / FALSIFIED", and the classifier
   scored it clean because the filename was not in its list.

`classify2.py` repairs both: the hunt's own first commit is excluded whatever it
touched, a claim file is any `.md` in the directory, and a revision needs
evidence of *replacement* rather than of addition.

Re-scored against the same 30 rows: **21 of 30**, precision 0.58, recall 0.64.
**That number is fitted, not measured**, because those 30 rows are what found
the defects.

So a disjoint sample of 30 was drawn from rows the first audit never saw,
stratified against the repaired classifier's own labels, and sent to a second
blind audit with its key again outside the repository.

| | agreement | precision | recall |
|---|---:|---:|---:|
| original, first sample | 16/30 (53.3%) | 0.40 | 0.55 |
| repaired, same sample (fitted) | 21/30 (70.0%) | 0.58 | 0.64 |
| **repaired, disjoint sample** | **22/30 (73.3%)** | **0.67** | **0.77** |

The repaired classifier holds its improvement on rows it was not tuned on. That
is the validation, and it is the reason a rate can be stated at all.

**The rate, with its correction stated.** Of 414 later commits, the classifier
flags 73 as strict revisions, `17.6%`. Scaling by the measured precision over
recall gives **`15.3%`**, and 15 of the 95 case-log entries carry at least one.
Both numbers rest on a classifier that disputes about a quarter of rows with a
careful reader, so they are worth one significant figure and no more.

`classify.py` is kept exactly as it was. A classifier that scored near chance is
evidence about how this kind of measurement fails, and deleting it would remove
the only record of that.

## 6. The doors

1. **Active constraints.** Two, and they bind in opposite directions.
   - *What counts as a revision* is the binding constraint on every rate in
     section 5, and its shadow price is the whole measurement: at 53% agreement
     nothing downstream survives. The blind audit is the only instrument here
     that prices it, and it costs one agent and thirty rows.
   - *What counts as a claim* is binding on the denominator. 95 case-log entries
     is a choice; the ledgers under `harness/departments/`, the `docs/` pages and
     the `HANDOFF.md` records are three other populations with three other
     answers.
2. **Frozen-constant inventory.**
   - **The 10% mutation size** in the ladder. A guard that catches 10% and not
     one part in `1e6` is a different guard, and the per-leaf rung already
     showed the distinction is real. The trade: finer mutations need tighter
     test tolerances to be meaningful, and the tolerances are what
     `tests/test_quotient_certificate.py` shows are loose (its expected value at
     `N = 100000` differs from the artifact it checks by `1.05e-6`, under a
     tolerance of `1e-4`, and one of the two numbers is the linear programme's
     optimum while the other is the rational certificate).
   - **Six probed leaves per artifact.** Coverage below is a lower bound; the
     probe strides through the leaves rather than finding the ones a test reads.
   - **The corpus frozen at one commit.** Every rate here is a snapshot of a
     tree that is still moving.
3. **Information class.** Everything above reads git and the working tree, and
   nothing reads what a person intended. The one question that needs more
   information is the one the attribution column cannot answer: *what made
   someone look*. Git records what a commit did. It does not record that a
   number looked wrong, and the tree's own `caught_by` field in
   `meta/interventions.jsonl` exists precisely because that has to be written
   down by hand at the time or it is gone. Nineteen of the seventy-three
   revisions here would be worth one line each in that ledger, and none of them
   has one.
