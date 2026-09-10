# 40. What happens to a claim after it is recorded

**Hunt #122, `hunts/claim_halflife/`.** The measurements, the controls and the
doors are in `hunts/claim_halflife/RESULTS.md`. This page is the front door.

Grade: **measured**, and the headline had to be withdrawn, repaired and
re-earned on fresh data before it could be stated. This is
not mathematics. Nothing here bears on RH (`docs/08`), and the standing rule in
`meta/README.md` applies: a session with no mathematics and a tidy ledger
produced nothing. This page is about the ledger, and the mathematics is
elsewhere in the same session.

## 1. The question

This laboratory publishes its working record, corrections included. That is a
policy, and a policy is a claim about behaviour. Nobody had measured the
behaviour.

The narrow, answerable version: once a claim is written into the case log, what
happens to it? How often is it revised, how fast, and how much of the record
has anything mechanical standing behind it. There are 95 entries in that log.

Three reasons it is worth asking, in descending order of how uncomfortable they
are. Every `HANDOFF.md` record in this tree carries a field called
`Now caught by:`, so whether that field is usually filled is a fact and it is
checkable. A claim nobody revisited looks identical, from outside, to a claim
that withstood scrutiny, so the denominator has to separate them. And a test
that names a hunt is presence, not power, which is a distinction the tree's own
playbook insists on and nobody had measured.

## 2. What the study nearly got wrong before it started

The container this ran in had a **shallow clone**. 262 commits reaching back to
2026-08-13, against 1084 reaching back to 2026-08-01. Nothing announced it.

Reconstructed at several depths:

| history depth | entries never revisited |
|---:|---:|
| full (1084) | 22 (23.2%) |
| **262, the container's own** | 29 (30.5%) |
| 100 | 91 (95.8%) |

A git-history study run on the default checkout would have reported 30.5% and
called it the answer.

This tree has met the hazard before, in August, and its record of that incident
ends with "the better fix, prepared and NOT landed": `fetch-depth: 0` in the
two CI workflows that still lack it. Still not landed. The first thing this
study measured was the reason its own subject exists.

## 3. What holds

**The guard surface is narrow.** One recorded claim in five, 19 of 95, is named
by any test at all.

**Where it exists, it mostly holds.** Of the 25 pairs of hunt and test that can
be scored by planting faults, 19 defend at least one of the hunt's numbers
against a ten percent mutation, and 8 of those are byte-pinned, which is the
strongest guard available. Six read none.

That second number is a correction of this hunt's own first attempt. The first
ladder mutated only the *first* artifact each test names, and reported 9 of 24.
Twenty of twenty-six tests name more than one artifact, up to thirty-seven, so
that figure was measuring the instrument rather than the tree.

**Almost nothing is guarded at the moment it is corrected.** Of 73 revisions the
classifier called strict, **one** touched `tests/` in the same commit.

This survives the classifier's problems below, because it is lopsided enough
that classifier error cannot rescue it. Suppose only 40% of the 73 are real,
which is the precision the blind audit measured before repair. That is still 29
real corrections and at most one installed guard. Missing revisions does not
help either: it means there were more of them.

**Correction is fast.** Median latency from a hunt's first commit to a revision
of its own claim files: one day. Mean 1.8. Longest 13.

## 4. The number that had to be earned twice

The first version of this hunt reported that 21% of case-log entries were later
revised, at three strictness levels that agreed to within five points. Three
agreeing levels look like robustness. They are three variations of one author's
idea of what a revision is.

Thirty rows, half classified positive and half negative, went to a separate
agent with the answer key moved out of the repository, told to judge each commit
from its own diff and nothing else.

**It agreed on 16 of 30.** Precision 0.40, recall 0.55, on a balanced sample.

That is close enough to chance that the rate cannot be reported, and it is
reported here as withdrawn rather than quietly rescaled. The audit's row notes
named two structural defects rather than borderline judgement calls:

- **The hunt's opening was counted as a revision of itself.** The first commit
  was taken to be the first one touching any of five hard-coded filenames, so a
  hunt that landed a mission statement first and its results second had that
  second commit scored as a later revision.
- **A withdrawal in a differently-named file was invisible.** One row adds a
  file headed "WITHDRAWN / FALSIFIED" and the classifier scored it clean,
  because the filename was not on the list.

Both are defects on their own terms, so they were repaired rather than tuned
around. Re-scored against the same 30 rows the repaired classifier reaches 21 of
30, precision 0.58. **That number is fitted, not measured**, because those rows
are what found the defects.

So a second sample of thirty was drawn from rows the first audit never saw, and
sent to a second blind audit with its key again outside the repository.

| | agreement | precision | recall |
|---|---:|---:|---:|
| original, first sample | 16/30 (53.3%) | 0.40 | 0.55 |
| repaired, same sample (fitted) | 21/30 (70.0%) | 0.58 | 0.64 |
| **repaired, disjoint sample** | **22/30 (73.3%)** | **0.67** | **0.77** |

The repair holds on rows it was not tuned on. That is what makes a rate
reportable: of 414 later commits the classifier flags 73, `17.6%`, and scaling
by the measured precision over recall gives **`15.3%`**. Fifteen of the
ninety-five entries carry at least one. Both numbers rest on a classifier that
still disputes about a quarter of rows with a careful reader, so they are worth
one significant figure and no more.

The original classifier is kept in the tree exactly as it was. A classifier that
scored near chance is evidence about how this kind of measurement fails.

## 5. The instrument broke the thing it was measuring

The planted-fault ladder mutates artifacts in the working tree and restores
them. Its first version restored with `git checkout --`. A concurrent `git`
command in the same tree made one restore fail with exit 128, and a mutated
artifact was left behind until someone noticed.

The operating playbook this laboratory keeps already contains the rule: never
background a job that does `git checkout` in the shared tree. It is now obeyed
rather than quoted. The ladder holds the original bytes in memory and asserts
that the restore round-trips.

Three things in this session went that way. A rule was written down, in a
comment or a playbook or a handoff note, and then the same failure happened
anyway to somebody who had not read that particular file. The measurement in
section 3, one guard installed per seventy-three corrections, is the same
shape counted rather than anecdoted.

## 6. What this does not measure

Git records what a commit did. It does not record what made someone look.

The attribution column here can say that a commit replaced a number and that it
did or did not add a test. It cannot say that a test went red, that a sibling
session found it, or that a person read the page and stopped. That has to be
written down at the time or it is gone, which is exactly why
`meta/interventions.jsonl` has a `caught_by` field. Nineteen of the
seventy-three revisions in this corpus would be worth one line each in that
ledger, and none of them has one.

That is the door, and it costs a habit rather than a system.
