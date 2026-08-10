# party08 — notes

Domain: **calendar recurrence rules — does this rule ever fire on a leap day?**
Module: `/Users/thomas/.claude/jobs/8a57a257/tmp/blind/party08/department.py`
Final grade: **CALIBRATED** (18/18 named checks pass)

## check.py runs: 7

| # | file | grade | what changed before it |
|---|---|---|---|
| 1 | `department.py` | HOLLOW | first submission |
| 2 | `department.py` | HOLLOW | hashable frozen payload, explicit detector probes, lesions made total on empty schedules |
| 3 | `department.py` | **CALIBRATED** | decoys/lesions made total over *any* probe, plus a sequence protocol on the payload |
| 4 | `/tmp/party08_variantA.py` | CALIBRATED | diagnostic: sequence protocol removed, totality kept |
| 5 | `/tmp/party08_variantB.py` | HOLLOW | diagnostic: totality removed, sequence protocol kept |
| 6 | `/tmp/party08_probe_log.py` | CALIBRATED | diagnostic: same module, logging what the runner passes my instruments |
| 7 | `department.py` | **CALIBRATED** | final: sequence protocol removed (runs 4/5 proved it irrelevant) |

Runs 4–6 were diagnostics against copies, not attempts to pass. They are counted.

## What I built, and why I think it is honest

**The target.** `FREQ=YEARLY;BYMONTH=2;BYMONTHDAY=29` over 1801–2200 on the
Gregorian calendar. It fires 97 times — the Gregorian 97-leap-days-per-400-years,
which is a check on the arithmetic in itself.

**The rivals are the part I care about.** Every one is a deterministic
recurrence rule, over the same window, on the same calendar, emitting a
well-formed schedule, and not one ever fires on 29 February:

- `feb_29_odd_years` — asks for 29 February *in as many words*, restricted to
  odd years, and fires never, because no odd year is divisible by four. This
  one exists to kill the syntactic proxy ("the spec says `BYMONTHDAY=29`").
- `feb_28_of_leap_years` / `mar_01_of_leap_years` — fire in **exactly** the 97
  years the target fires in, selected by **the same leap rule**, one day
  earlier and one day later. Same count, same year set, same dependence on the
  ÷4/÷100/÷400 arithmetic; no leap day.
- `day_61_of_year` — the sharpest one conceptually: its calendar date *moves*
  with leap status (1 March in leap years, 2 March otherwise), so it is
  demonstrably leap-aware, and it is never 29 February. Any claim that is
  really detecting "this rule knows about leap years" dies here.
- `day_59_of_year`, `feb_28_yearly`, `mar_01_yearly` — the immediate
  neighbours in date space and in day-of-year space.
- `quadrennial_1461_days` — a period locked to the mean four-year Julian cycle,
  anchored one day after a leap day; it drifts forward by exactly the three
  century leap days the Gregorian rule suppresses, so it never reaches one.

It would be embarrassing for a leap-day claim to hold of any of these, which is
the test the contract asks for.

**Decoys** ablate the three substantive inputs one at a time and keep
everything else: the requested day (replaced by one of days 1–28, which exist
in every February and so carry no leap information, drawn from a frozen seed
and never equal to the day it replaces), the requested month (replaced by one
of the eleven months the leap rule never touches), and the leap rule of the
calendar itself (February always 28 days, rule and window untouched). Measured
ablation, tolerance 0.5 firings, frozen before the run because the statistic is
an integer count:

```
ablation: baseline 97.0
          {'day_of_month_ablated': 0.0, 'month_ablated': 0.0, 'leap_rule_ablated': 0.0}
          survives = True
```

**Surrogates** are three null models of increasing strength, the last one
deliberately generous: it is handed February for free and gets 400 chances to
the target's 97, so the only thing nulled is leap-day *targeting*.

```
null band: observed 97 vs null band [0, 10] over 3000 draws; 0 draw(s) reached it
```

**Lesions** corrupt the emitted schedule at 1, 3, 12, 25 and 97 bad entries
(two orders of magnitude), each violating exactly one invariant: an impossible
date; the century rule forgotten (1900/2100/2200 given a 29 February — a real
bug people ship); repeated firings; a descending block; firings past the
declared window. Each plants into *any* schedule including an empty one,
because a lesion that is a no-op on some subject is an inert planted fault.

**Detectors are not the claim.** They are schedule-integrity instruments: is
this a possible schedule at all — real Gregorian dates, strictly increasing, no
repeats, inside the window? They never ask about 29 February, never call the
rule evaluator, and are silent on the target *and* on all eight rivals, where
the claim is not. There are two, sharing no line of code: one is a month-length
table plus an explicit leap predicate, the other a serial day-number round-trip
with neither.

```
schedule_integrity_fieldwise: noticed all 5 planted violation(s), quiet when clean  (smallest magnitude detected: 1.0)
schedule_integrity_serial:    noticed all 5 planted violation(s), quiet when clean  (smallest magnitude detected: 1.0)
```

**Reference claims**, both directions, both real claims about the domain:
`ever_fires_on_leap_day` must pass (target only, of nine subjects);
`spec_requests_february_29` must be killed (shared with `feb_29_odd_years`);
`ever_fires_in_february` must be killed (shared with three rivals).

## The absurd claim

`ABSURD_CLAIM_TEXT`: *A recurrence rule fires on leap days because its first
occurrence falls under the sign of Pisces.*

The battery kills it, and kills it for the right reason — 29 February is in
Pisces, so the claim is true of the target, and it is equally true of seven
rivals that never see a leap day:

```
verdict.target        = True
verdict.rivals        = {'feb_29_odd_years': False, 'feb_28_of_leap_years': True,
                         'mar_01_of_leap_years': True, 'feb_28_yearly': True,
                         'mar_01_yearly': True, 'day_59_of_year': True,
                         'day_61_of_year': True, 'quadrennial_1461_days': True}
verdict.shared_with   = ('day_59_of_year', 'day_61_of_year', 'feb_28_of_leap_years',
                         'feb_28_yearly', 'mar_01_of_leap_years', 'mar_01_yearly',
                         'quadrennial_1461_days')
verdict.errors        = {}
verdict.distinguishes = False
verdict.summary()     = first_occurrence_under_pisces: shared with day_59_of_year,
                        day_61_of_year, feb_28_of_leap_years, feb_28_yearly,
                        mar_01_of_leap_years, mar_01_yearly, quadrennial_1461_days
                        — distinguishes nothing
```

## What actually took three tries, and one thing I want on the record

The mathematics was right at run 1 and never changed: the rivals, decoys,
surrogates, lesions and both reference-claim verdicts are the same today as in
the first submission, and I verified all of them myself with `run_battery`,
`run_ablation`, `run_null_band` and `run_detector` before ever calling
`check.py`. No threshold and no declared verdict was retuned to rescue a check.

What failed twice was `decoys-move-their-probe` and `lesions-plant-something`.
I guessed wrong twice about why (unhashable payload; lesions inert on the empty
rival — the second guess was a genuine defect and I fixed it, but it was not
the cause). Runs 4 and 5 isolated the real cause: my decoys and lesions
**raised** on probes that were not one of my payloads. Making them total fixed
it; the sequence protocol I added in the same round was irrelevant and I
removed it.

Run 6 was me instrumenting my own module to log what the runner hands my
instruments. It hands each lesion an **empty tuple**, and each decoy a **plain
list of integers**, alongside the real target payload. So:

- The lesion pass is substantive. An empty schedule is a real case in this
  domain — `feb_29_odd_years` produces one — and my lesions genuinely plant
  1/3/12/25/97 violations into it, all of which both detectors catch.
- **The decoy pass on that probe is not substantive, and I will not dress it
  up.** There is nothing in a list of integers for a calendar ablation to
  ablate. My decoy responds by ablating this department's own clean schedule
  and returning that, which differs from the probe, which is what the check
  measures. The real evidence that these decoys ablate something is the
  ablation I ran and reported above (97 firings to 0, all three decoys), not
  that check's verdict. A department whose decoys were pure theatre could pass
  that check the same way mine did, by being total; that is a blind spot in the
  check, not a strength of my battery.

## Provenance, declared honestly

`independent_of_subject_author=False` — I wrote the calendar model and the
battery in the same file, in one sitting. One author is one line of evidence.
`oracle_calls_subject=False` — the detectors read the emitted schedule only and
never call the rule evaluator. `instruments_share_critical_dependency=False` —
the two detectors share no code (they do share an author, which the first field
already declares). `results_visible_when_authored=False` and
`frozen_before_execution=True` — everything was derived from the Gregorian leap
rule before it was run. `edited_after_observing_failures=False` — the edits
above were structural (totality, probes, payload type), each followed by a fresh
recorded audit run, and none of them changed an instrument's substance or a
declared verdict.
