# Retraction: RF-C008's 0.9578, and the corrected table it rested on

**2026-08-19, on reconciling with main.** `docs/31` (Hunt #65,
`hunts/r_2ac05f/`) establishes an erratum to Bian's Lemma 12: the second
regular coefficient is

    C_{kappa,2} = -4 kappa,     not  -4.

This campaign carried `C_{kappa,2} = -4` as given, and said so explicitly:
`RESULTS_LEDGER.md` RF-C006 recorded "C_{kappa,1} = 1, C_{kappa,2} = -4,
C_{kappa,3} = 4, C_{kappa,4} = -16 (kappa >= 2) survive" and "Lemma 12
survives". That was wrong.

## What is retracted

**RF-C008's headline is withdrawn.** The claim was "at least 0.9578 of the
zeros of xi'' are simple, exceeding the thesis's printed 0.9544". It was
computed from this campaign's corrected table, which inherits the Lemma 12
error. Measured against main's authoritative row
(`hunts/higher_xi/C2_EXACT.json`), this campaign's row agrees at **i = 1
and nowhere else**:

    i             1     2     3     4      5       6        7
    main        1    -8    24   -32   64/3   -64/3   1216/45
    this camp.  1    -4     4   -16   52/3    16/3    208/45

Re-running this campaign's own (11.5) evaluation on main's corrected row
gives, at truncation 11:

    alpha -> 1        0.8675127341794009   (exact 50242/57915)
    alpha-optimised   0.8701519603784389   at alpha = 0.98

Conrey 1983's unconditional bound for xi'' is 0.9314. So the corrected
route does not beat Conrey either, and the campaign's xi'' claim says
nothing. **The error was in this campaign's favour**, which is the
direction that survives review longest and is the reason to say so
loudly.

**RF-C006(c) is superseded.** The "corrected table, validated two
independent ways" is not the true table. Its two validations were
internally consistent and both downstream of the same wrong Lemma 12
input, so they could not see it.

## What survives, stated narrowly

- **The three code defects in Bian's Mathematica** (assembly truncation
  from i = 7; phantom slots; the `prod alpha_i!` overcount). Each is
  pinned by a finite exact witness about what his code computes versus
  what his printed formulas say. They are defects in the code and remain
  so; main's erratum is a fourth and independent error, in the analytic
  lemma upstream of all of them.
- **RF-C007.** That his printed headline constants do not follow from his
  printed table by his printed formula is a statement about his table and
  his formula, and does not depend on which table is true. The controls
  (Montgomery 2/3, Farmer-Gonek 0.858384) still reproduce.
- **The resolvent machinery.** It computed correctly from the inputs it
  was given; the inputs were wrong. Re-running it on corrected inputs is
  a live and cheap next step.
- **Untouched by this:** RF-C001 to RF-C005, RF-C009 (Davenport-Heilbronn
  positivity failure), RF-C010 (the kernel-checked pairing count),
  RF-C011 (the Erdos-Pomerance table).

**Not asserted:** that the Gevrey-1/2 tail bound survives. It was derived
from the machinery's grading structure rather than from particular
coefficient values, so it plausibly does, but it has not been re-checked
against the corrected row and is therefore carried as open rather than as
surviving.

## The lesson, which this campaign had already written down about someone else

RF-C006 says of Bian's three defects: "The kappa = 1 row, the only
externally validated one, is immune to all three, which is why nothing
caught them since 2008." Every control this campaign ran was also at
kappa = 1, where `-4 kappa` and `-4` are the same number. The campaign
diagnosed the failure mode precisely and then committed it.

`docs/31` §4 states the general rule, and demonstrates it by planting the
defect and watching the kappa = 1 control pass anyway: **when a claim
asserts a quantity is invariant in a parameter, the control must vary
that parameter.** A control that passes while the defect under audit is
planted has no power over that defect.
