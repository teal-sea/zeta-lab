# R-2969B0: the 2013 construction beats the AlphaEvolve value, under the repository's own definition

**Verdict: option 1 of the three the brief names.** Penman and Wells (2013)
reach a strictly higher value of exactly the quantity DeepMind's Problem 42
defines, and they do it with an explicit finite set that is *smaller* than the
AlphaEvolve one. The normalisations agree; this is not apples to oranges. The
challenger issue is right on its prior-art half, including its citation.

Everything below is exact finite-set arithmetic over the integers. No floating
point enters the verdict: the comparison `g(Q_36) > g(AlphaEvolve)` is decided
at 120 decimal digits (`probe.py:g_beats`), and the two sides differ in the
sixth digit.

## 1. The two statements, side by side (VERIFIED)

**DeepMind**, `problems/42.html`, title *"42. Sum-difference problem I"*:

> Let $C$ be the least constant such that $|A+A|/|A| \leq (|A-A|/|A|)^{C}$ for
> any non-empty finite set $A$ of integers. Establish upper and lower bounds
> for $C$ as strong as possible.

So `C = sup_A g(A)` with `g(A) = ln(|A+A|/|A|) / ln(|A-A|/|A|)`.

**Penman and Wells**, INTEGERS 13 (2013) A57, section 4, page 22:

> Some authors, e.g., Granville in [2], prefer to use
> `g(A) = ln(|A+A|/|A|)/ln(|A-A|/|A|)` for which the analogous bounds are
> `1/2 <= g(A) <= 2`.

and their **Theorem 21** (page 22), quoted whole:

> Given `eps > 0`, there is a set `C` of integers for which
> `g(C) = ln(|C+C|/|C|)/ln(|C-C|/|C|) > ln(32/5)/ln(26/5) - eps ~= 1.125944426`.
> *Proof.* Take `Q_j` for `j` sufficiently large.

**The normalisations are identical, character for character.** This is the step
the brief said everyone skips, and it is the one that decides the outcome. It
was worth checking, because the same paper carries a *different* quantity in
its abstract, `f(A) = ln|A+A|/ln|A-A|`, which is where the paper's headline
"previous record" claim lives, and which is **not** Problem 42's `C`. Confusing
the two is the obvious way to get this wrong in either direction. On the
AlphaEvolve set, `f = 1.0229` and `g = 1.1219`; on `Q_1000`, `f = 1.0212` and
`g = 1.1258`. Ranking by `f` would reverse the answer, so the distinction is
load-bearing and is stated here rather than assumed.

That we are computing the paper's `g` and not something adjacent is pinned by
four numbers the paper prints and this probe recomputes, none of which were
used to build anything:

| paper | printed | recomputed |
| --- | --- | --- |
| `g(A_15)`, page 22 | `1.0717` | `1.071702` |
| `f(X)`, Lemma 19 | `ln(51)/ln(47) = 1.021214` | `1.021214` |
| `f(Q_10)`, Theorem 20 | `1.030597781...` | `1.0305978805` |
| `f-hat(Q_19)`, Theorem 20 | `1.028377107...` | `1.0283771072` |

## 2. The AlphaEvolve construction, evaluated (VERIFIED)

Taken from the repository's own notebook,
`experiments/sums_differences_problems/sums_differences_problems.ipynb`, cell 1
(`best_list`), and re-counted by enumeration:

| `|A|` | `|A+A|` | `|A-A|` | `g(A)` |
| --- | --- | --- | --- |
| 309 | 1367 | 1163 | **1.1219357375** |

which is the 1.1219 the issue attributes to it. All 309 listed values are
distinct.

One thing found on the way, MEASURED and not part of the verdict: the notebook
carries **three** different score functions for this problem, and two of them
are not the quantity the problem page defines.

- Cell 2 (the prompt AlphaEvolve was given) returns
  `log(|A-A|/|A|) / log(|A+A|/|A|)`: the **reciprocal**, 0.8913 on `best_list`.
  Maximising it would minimise `g`.
- Cell 5 ("Verification function used") returns the right ratio **plus a size
  bonus** `(1 - 1/|A|)/100`, i.e. 1.1319 on `best_list`, inflated by 0.00998.
- Cell 1 (the "Data and verification" cell, run last) returns the clean ratio.

The published 1.1219 is the clean one, so the bonus did not leak into the
reported record. But a bonus of up to 0.01 sitting inside a scorer whose whole
scale of interest is 1.06 to 1.13 is worth naming, since the *search* was
steered by it.

## 3. The Penman-Wells family, instantiated (VERIFIED)

`Q_j` is Theorem 12, page 14, transcribed into `probe.py:Q`:

```
Q_j = {0,2,4,12} u {1,5,...,1+4(4j+8)} u {24,40,...,8+16j}
      u {4+16(j+1), 12+16(j+1), 14+16(j+1), 16(j+2)},   j >= 1
```

Corollary 13 (page 17) states `|Q_j| = 5j+17`, `|Q_j+Q_j| = 32j+63`,
`|Q_j-Q_j| = 26j+61`, `|Q_j (+) Q_j| = 32j+56` for the restricted sumset.
Recomputed by enumeration for **64 values of `j`** (all of 1..60, plus 80, 120,
200, 400) and again for every `j <= 36` inside the search loop:
**zero mismatches**, all four counts, every `j`. The corollary is not being
quoted here, it is being reproduced.

| `j` | `|Q_j|` | `|Q_j+Q_j|` | `|Q_j-Q_j|` | `g(Q_j)` |
| --- | --- | --- | --- | --- |
| 1 | 22 | 95 | 87 | 1.063983540 |
| 10 | 67 | 383 | 321 | 1.112713601 |
| **36** | **197** | **1215** | **997** | **1.121950570** |
| 37 | 202 | 1247 | 1023 | 1.122055157 |
| 60 | 317 | 1983 | 1621 | 1.123517378 |
| 200 | 1017 | 6463 | 5261 | 1.125206565 |
| 1000 | 5017 | 32063 | 26061 | 1.125796184 |
| `-> inf` | | | | `ln(32/5)/ln(26/5) = 1.125944426` |

`g(Q_j)` increases monotonically toward the limit and does not attain it, which
is why Theorem 21 is stated with an `eps`. That costs nothing: `C` is defined as
the *least* constant valid for all `A`, so `C >= g(Q_j)` for every `j` and hence
`C >= 1.125944426`.

## 4. The head-to-head (VERIFIED)

| | `|A|` | `|A+A|` | `|A-A|` | `g` |
| --- | --- | --- | --- | --- |
| AlphaEvolve `best_list` | 309 | 1367 | 1163 | 1.1219357375 |
| Penman-Wells `Q_36` | 197 | 1215 | 997 | **1.1219505699** |
| Penman-Wells, `sup_j` | | | | **1.125944426** |

`Q_36` is the smallest member of the 2013 family that beats the 2026 machine
search: **197 integers against 309**, margin `+1.48e-05`, decided exactly. Every
`Q_j` with `j >= 36` also beats it, so this is a family and not a coincidence.
The supremum clears the AlphaEvolve value by `+0.00401`, about 33× the `Q_36`
margin.

For the record's other end: Granville's bounds `1/2 <= g <= 2`, quoted by Penman
and Wells, put `C <= 2`, so nothing here is near closing the problem. The
finding is about the *lower* bound only.

## 5. What this settles, and what it does not

**Settled.** The `world_record` marking on Problem 42 in `status.json` does not
hold as a record for the lower bound on `C`: a 2013 paper, published, human, and
cited as best known by Staps (INTEGERS 15 (2015) A42, per the issue, a claim
this hunt did **not** independently verify), gives a strictly better value under
DeepMind's own definition, and gives it as a theorem about an explicit infinite
family rather than as one searched set. The challenger issue's prior-art half is
correct, and its attribution to Theorem 21 is exact.

**Not settled here, deliberately.** The same issue's `C = 2` claim, which is the
large one. It is untouched, per the brief. Nothing in this hunt supports or
weakens it; anything read off this page about it would be INFERRED at best.

**Not checked.** That Staps (2015) records the value as best known, taken from
the issue, not read. That no construction published between 2013 and now beats
`ln(32/5)/ln(26/5)`; this hunt establishes a floor for the 2013 result, not the
current state of the art. And whether the AlphaEvolve authors were aware of the
Penman-Wells paper; the repository cites arXiv:2511.02864 section 6.25, which
was not read.

**A note on what "beats" means.** The comparison is between a *number reported
as a record* and a *number provable from a 2013 theorem*. AlphaEvolve's search
found a 309-element set achieving 1.12194 in 1000 seconds; that is a real
artifact and this hunt reproduces it exactly. What fails is the classification,
not the search.

## Loose threads

1. **The stated baseline 1.0598 does not match anything in the 2013 paper.**
   Penman and Wells list the suprema of `g` over their four families on page 22:
   `ln(16/3)/ln(14/3) ~= 1.0867` (`T_j`, `T'_j`), `ln(23/4)/ln(11/2) ~= 1.0261`
   (`R_j`), `ln(11/2)/ln(5) ~= 1.0592` (`M_j`). The issue reports AlphaEvolve's
   baseline as 1.0598, six units in the fourth decimal off the `M_j` value and
   not equal to any of the others. *Why it might matter:* if the baseline was
   taken from this paper at all, then the paper was in hand and the 1.12594 on
   page 22 was passed over; if it came from elsewhere, the provenance of the
   baseline is a separate unknown. *First step:* read section 6.25 of
   arXiv:2511.02864 and find what 1.0598 is cited to.

2. **The reciprocal scorer in the AlphaEvolve prompt (cell 2).** The prompt
   AlphaEvolve was given asks it to maximise `log(|A-A|/|A|)/log(|A+A|/|A|)`,
   the reciprocal of the target, while the final verification cell uses the
   right ratio. *Why it might matter:* Problem 43 in the same notebook genuinely
   *is* the reciprocal quantity (`|A-A| <= |A+A|^C`), and it is classified
   `worse_than_record`. A crossed scorer between two adjacent problems is a
   cheap explanation for one of those two outcomes. *First step:* re-score the
   Problem 43 published set under both ratios and see which one its reported
   value matches.

3. **The size bonus `(1 - 1/|A|)/100` inside the search scorer.** It rewards
   larger sets by up to 0.01 on a scale where the whole contested range is 0.06
   wide. *Why it might matter:* it may explain why the machine landed on a
   309-element set when a 197-element member of a 2013 family does better. *First
   step:* re-run a short local search on the clean ratio and see whether it
   prefers smaller sets.

4. **`f` and `g` rank these sets in opposite directions.** `Q_1000` beats
   `best_list` on `g` and loses to it on `f`. *Why it might matter:* both
   quantities appear in this literature under the same words "sum-difference",
   and Problem 42's page does not say which. It happens to define `g`
   unambiguously in its formula, but a reader going by the title alone could
   pick either. *First step:* nothing needed here; it is a caution for whoever
   drafts an upstream reply.

5. **The upper bound side is untouched.** `C <= 2` is what Granville's bounds
   give and what the issue's `C = 2` claim would make sharp. This hunt says
   nothing about it. *First step:* it is the issue's part 1, and it is the
   expensive half; treat it as its own hunt.

---

Reproduce: `python3 hunts/r_2969b0/probe.py` (standard library only, ~4 s).
Nothing here is evidence for or against RH (`docs/08`).
